// Copyright 2018 Niklas Fiekas <niklas.fiekas@backscattering.de>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! [Huffman compression](https://en.wikipedia.org/wiki/Huffman_coding)
//! given a probability distribution over arbitrary symbols.
//!
//! # Examples
//!
//! ```rust
//! extern crate bit_vec;
//! extern crate huffman_compress;
//!
//! # use std::error::Error;
//! #
//! # fn try_main() -> Result<(), Box<Error>> {
//! use std::iter::FromIterator;
//! use std::collections::HashMap;
//! use bit_vec::BitVec;
//! use huffman_compress::{CodeBuilder, Book, Tree};
//!
//! let mut weights = HashMap::new();
//! weights.insert("CG", 293);
//! weights.insert("AG", 34);
//! weights.insert("AT", 4);
//! weights.insert("CT", 4);
//! weights.insert("TG", 1);
//!
//! // Construct a Huffman code based on the weights (e.g. counts or relative
//! // frequencies).
//! let (book, tree) = CodeBuilder::from_iter(weights).finish();
//!
//! // More frequent symbols will be encoded with fewer bits.
//! assert!(book.get("CG").map_or(0, |cg| cg.len()) <
//!         book.get("AG").map_or(0, |ag| ag.len()));
//!
//! // Encode some symbols using the book.
//! let mut buffer = BitVec::new();
//! let example = vec!["AT", "CG", "AT", "TG", "AG", "CT", "CT", "AG", "CG"];
//! for symbol in &example {
//!     book.encode(&mut buffer, symbol);
//! }
//!
//! // Decode the symbols using the tree.
//! let decoded: Vec<&str> = tree.decoder(&buffer, example.len()).collect();
//! assert_eq!(decoded, example);
//! #     Ok(())
//! # }
//! #
//! # fn main() {
//! #     try_main().unwrap();
//! # }
//! ```

#![doc(html_root_url = "https://docs.rs/huffman-compress/0.6.1")]
#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(missing_debug_implementations)]

extern crate bit_vec;
extern crate num_traits;

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

use std::borrow::Borrow;
use std::cmp;
use std::cmp::Reverse;
use std::collections::{btree_map, BTreeMap, BinaryHeap};
use std::error::Error;
use std::fmt;
use std::iter::{FromIterator, Take};

use bit_vec::BitVec;

use num_traits::ops::saturating::Saturating;

#[cfg(feature = "serde")]
extern crate serde;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A trie used for decoding.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone)]
pub struct Tree<K> {
    root: usize,
    arena: Vec<Node<K>>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone)]
struct Node<K> {
    parent: Option<usize>,
    data: NodeData<K>,
}

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone)]
enum NodeData<K> {
    Leaf { symbol: K },
    Branch { left: usize, right: usize },
}

impl<K: Clone> Tree<K> {
    /// An iterator decoding symbols from a source of bits.
    ///
    /// In pathologic cases the iterator is unbounded: If there is only one
    /// symbol the iterator will yield that symbol **infinitely** often without
    /// consuming any bits.
    ///
    /// If there are no symbols the decoded sequence is empty without consuming
    /// any bits.
    ///
    /// If the source is exhausted no further symbols will be decoded
    /// (not even incomplete ones).
    pub fn unbounded_decoder<I>(&self, iterable: I) -> UnboundedDecoder<K, I>
    where
        I: IntoIterator<Item = bool>,
    {
        UnboundedDecoder {
            tree: self,
            iter: iterable.into_iter(),
        }
    }

    /// An iterator decoding up to `num_symbols` symbols from a source of bits.
    ///
    /// Also see [`unbounded_decoder()`](#method.unbounded_decoder).
    ///
    /// If there are no symbols the decoded sequence is empty without consuming
    /// any bits.
    ///
    /// If the source is exhausted no further symbols will be decoded
    /// (not even incomplete ones).
    pub fn decoder<I>(&self, iterable: I, num_symbols: usize) -> Decoder<K, I>
    where
        I: IntoIterator<Item = bool>,
    {
        self.unbounded_decoder(iterable).take(num_symbols)
    }
}

/// A bounded [decoder](struct.UnboundedDecoder.html), decoding symbols from
/// a source of bits.
pub type Decoder<'a, K, I> = Take<UnboundedDecoder<'a, K, I>>;

/// Decodes symbols from a source of bits.
#[derive(Debug)]
pub struct UnboundedDecoder<'a, K: 'a, I: IntoIterator<Item = bool>> {
    tree: &'a Tree<K>,
    iter: I::IntoIter,
}

impl<'a, K: Clone, I: IntoIterator<Item = bool>> Iterator for UnboundedDecoder<'a, K, I> {
    type Item = K;

    fn next(&mut self) -> Option<K> {
        let mut node = match self.tree.arena.get(self.tree.root) {
            Some(root) => root,
            None => return None, // empty tree
        };

        loop {
            match node.data {
                NodeData::Leaf { ref symbol } => return Some(symbol.clone()),
                NodeData::Branch { left, right } => {
                    node = match self.iter.next() {
                        Some(true) => &self.tree.arena[left],
                        Some(false) => &self.tree.arena[right],
                        None => return None,
                    };
                }
            }
        }
    }
}

/// A codebook used for encoding.
#[derive(Clone, Debug)]
pub struct Book<K> {
    book: BTreeMap<K, BitVec>,
}

impl<K: Ord + Clone> Book<K> {
    /// Returns the underlying B-Tree.
    pub fn into_inner(self) -> BTreeMap<K, BitVec> {
        self.book
    }

    /// An iterator over all symbols in sorted order.
    pub fn symbols(&self) -> btree_map::Keys<K, BitVec> {
        self.book.keys()
    }

    /// An iterator over all symbol and code word pairs, sorted by symbol.
    pub fn iter(&self) -> btree_map::Iter<K, BitVec> {
        self.book.iter()
    }

    /// Returns the number of symbols in the book.
    pub fn len(&self) -> usize {
        self.book.len()
    }

    /// Returns true if the map has no symbols.
    pub fn is_empty(&self) -> bool {
        self.book.is_empty()
    }

    /// Returns the code word for a given symbol.
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&BitVec>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.book.get(k)
    }

    /// Returns true if the book contains the specified symbol.
    pub fn contains_symbol<Q: ?Sized>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.book.contains_key(k)
    }

    /// Writes the code word for the given key to a bit vector.
    ///
    /// # Errors
    ///
    /// Returns [`EncodeError`] if `k` is not in the codebook.
    ///
    /// [`EncodeError`]: struct.EncodeError.html
    pub fn encode<Q: ?Sized>(&self, buffer: &mut BitVec, k: &Q) -> Result<(), EncodeError>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        match self.book.get(k) {
            Some(code) => buffer.extend(code),
            None => return Err(EncodeError {}),
        }

        Ok(())
    }

    fn new() -> Book<K> {
        Book {
            book: BTreeMap::new(),
        }
    }

    fn build(&mut self, arena: &[Node<K>], node: &Node<K>, word: BitVec) {
        match node.data {
            NodeData::Leaf { ref symbol } => {
                self.book.insert(symbol.clone(), word);
            }
            NodeData::Branch { left, right } => {
                let mut left_word = word.clone();
                left_word.push(true);
                self.build(arena, &arena[left], left_word);

                let mut right_word = word;
                right_word.push(false);
                self.build(arena, &arena[right], right_word);
            }
        }
    }
}

/// Tried to encode an unknown symbol.
#[derive(Debug, Clone)]
pub struct EncodeError;

impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        "encode error: tried to encode an unknown symbol".fmt(f)
    }
}

impl Error for EncodeError {
    fn description(&self) -> &str {
        "encode error: tried to encode an unknown symbol"
    }
}

/// Collects information about symbols and their weights used to construct
/// a Huffman code.
///
/// # Stability
///
/// The constructed code is guaranteed to be deterministic and stable across
/// semver compatible releases if:
///
/// * There is a strict order on the symbols `K`.
/// * No duplicate symbols are added.
///
/// The ordering of symbols will be used to break ties when weights are equal.
#[derive(Debug, Clone)]
pub struct CodeBuilder<K: Ord + Clone, W: Saturating + Ord> {
    heap: BinaryHeap<HeapData<K, W>>,
    arena: Vec<Node<K>>,
}

impl<K: Ord + Clone, W: Saturating + Ord> CodeBuilder<K, W> {
    /// Creates a new, empty `CodeBuilder<K, W>`.
    pub fn new() -> CodeBuilder<K, W> {
        CodeBuilder {
            heap: BinaryHeap::new(),
            arena: Vec::new(),
        }
    }

    /// Creates a new, empty `CodeBuilder<K, W>` and preallocates space
    /// for `capacity` symbols.
    pub fn with_capacity(capacity: usize) -> CodeBuilder<K, W> {
        CodeBuilder {
            heap: BinaryHeap::with_capacity(capacity),
            arena: Vec::with_capacity(2 * capacity),
        }
    }

    /// Adds a symbol and weight pair.
    pub fn push(&mut self, symbol: K, weight: W) {
        self.heap.push(HeapData {
            weight: Reverse(weight),
            symbol: symbol.clone(),
            id: self.arena.len(),
        });

        self.arena.push(Node {
            parent: None,
            data: NodeData::Leaf { symbol },
        });
    }

    /// Constructs a [book](struct.Book.html) and [tree](struct.Tree.html) pair
    /// for encoding and decoding.
    pub fn finish(mut self) -> (Book<K>, Tree<K>) {
        let mut book = Book::new();

        let root = loop {
            let left = match self.heap.pop() {
                Some(left) => left,
                None => {
                    return (
                        book,
                        Tree {
                            root: 0,
                            arena: self.arena,
                        },
                    )
                }
            };

            let right = match self.heap.pop() {
                Some(right) => right,
                None => break left,
            };

            let id = self.arena.len();

            self.arena[left.id].parent = Some(id);
            self.arena[right.id].parent = Some(id);

            self.heap.push(HeapData {
                weight: Reverse(left.weight.0.saturating_add(right.weight.0)),
                symbol: cmp::min(left.symbol, right.symbol),
                id,
            });

            self.arena.push(Node {
                parent: None,
                data: NodeData::Branch {
                    left: left.id,
                    right: right.id,
                },
            });
        };

        book.build(&self.arena, &self.arena[root.id], BitVec::new());
        (
            book,
            Tree {
                root: root.id,
                arena: self.arena,
            },
        )
    }
}

impl<K: Ord + Clone, W: Saturating + Ord> Default for CodeBuilder<K, W> {
    fn default() -> CodeBuilder<K, W> {
        CodeBuilder::new()
    }
}

impl<K: Ord + Clone, W: Saturating + Ord> FromIterator<(K, W)> for CodeBuilder<K, W> {
    fn from_iter<T>(weights: T) -> CodeBuilder<K, W>
    where
        T: IntoIterator<Item = (K, W)>,
    {
        let iter = weights.into_iter();
        let (size_hint, _) = iter.size_hint();
        let mut code = CodeBuilder::with_capacity(size_hint);
        code.extend(iter);
        code
    }
}

impl<K: Ord + Clone, W: Saturating + Ord> Extend<(K, W)> for CodeBuilder<K, W> {
    fn extend<T>(&mut self, weights: T)
    where
        T: IntoIterator<Item = (K, W)>,
    {
        for (symbol, weight) in weights {
            self.push(symbol, weight);
        }
    }
}

impl<'a, K: Ord + Clone, W: Saturating + Ord + Clone> FromIterator<(&'a K, &'a W)>
    for CodeBuilder<K, W>
{
    fn from_iter<T>(weights: T) -> CodeBuilder<K, W>
    where
        T: IntoIterator<Item = (&'a K, &'a W)>,
    {
        CodeBuilder::from_iter(weights.into_iter().map(|(k, v)| (k.clone(), v.clone())))
    }
}

impl<'a, K: Ord + Clone, W: Saturating + Ord + Clone> Extend<(&'a K, &'a W)> for CodeBuilder<K, W> {
    fn extend<T>(&mut self, weights: T)
    where
        T: IntoIterator<Item = (&'a K, &'a W)>,
    {
        self.extend(weights.into_iter().map(|(k, v)| (k.clone(), v.clone())));
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Debug)]
struct HeapData<K, W> {
    weight: Reverse<W>,
    symbol: K, // tie breaker
    id: usize,
}

impl<K: Clone, W: Clone> Clone for HeapData<K, W> {
    fn clone(&self) -> HeapData<K, W> {
        HeapData {
            weight: Reverse(self.weight.0.clone()),
            symbol: self.symbol.clone(),
            id: self.id,
        }
    }
}

/// Shortcut for
/// [`CodeBuilder::from_iter(weights).finish()`](struct.CodeBuilder.html).
pub fn codebook<'a, I, K, W>(weights: I) -> (Book<K>, Tree<K>)
where
    I: IntoIterator<Item = (&'a K, &'a W)>,
    K: 'a + Ord + Clone,
    W: 'a + Saturating + Ord + Clone,
{
    CodeBuilder::from_iter(weights).finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_uniform() {
        let mut sample = HashMap::new();
        sample.insert(1, 1);
        sample.insert(2, 1);
        sample.insert(3, 1);
        sample.insert(4, 1);
        sample.insert(5, 1);
        let (book, tree) = CodeBuilder::from_iter(sample).finish();

        let mut buffer = BitVec::new();
        book.encode(&mut buffer, &1).unwrap();
        book.encode(&mut buffer, &2).unwrap();
        book.encode(&mut buffer, &3).unwrap();
        book.encode(&mut buffer, &4).unwrap();
        book.encode(&mut buffer, &5).unwrap();

        let mut decoder = tree.unbounded_decoder(buffer);
        assert_eq!(decoder.next(), Some(1));
        assert_eq!(decoder.next(), Some(2));
        assert_eq!(decoder.next(), Some(3));
        assert_eq!(decoder.next(), Some(4));
        assert_eq!(decoder.next(), Some(5));
        assert_eq!(decoder.next(), None);
    }

    #[test]
    fn test_uniform_from_static() {
        const WEIGHTS: &[(&char, &usize)] = &[(&'a', &1), (&'b', &1), (&'c', &1), (&'d', &1)];
        let (book, tree) = codebook(WEIGHTS.iter().cloned());

        let mut buffer = BitVec::new();
        book.encode(&mut buffer, &'a').unwrap();
        book.encode(&mut buffer, &'b').unwrap();
        book.encode(&mut buffer, &'c').unwrap();
        book.encode(&mut buffer, &'d').unwrap();

        let mut decoder = tree.unbounded_decoder(buffer);
        assert_eq!(decoder.next(), Some('a'));
        assert_eq!(decoder.next(), Some('b'));
        assert_eq!(decoder.next(), Some('c'));
        assert_eq!(decoder.next(), Some('d'));
        assert_eq!(decoder.next(), None);
    }

    #[test]
    fn test_empty() {
        let (book, tree) = CodeBuilder::<&str, i32>::new().finish();

        let mut buffer = BitVec::new();
        assert!(book.encode(&mut buffer, "hello").is_err());

        let mut decoder = tree.unbounded_decoder(buffer);
        assert_eq!(decoder.next(), None);
    }

    #[test]
    fn test_single() {
        let mut builder = CodeBuilder::new();
        builder.push("hello", 1);
        let (book, tree) = builder.finish();

        let mut buffer = BitVec::new();
        book.encode(&mut buffer, "hello").unwrap();

        let mut decoder = tree.unbounded_decoder(buffer);
        assert_eq!(decoder.next(), Some("hello"));
        assert_eq!(decoder.next(), Some("hello")); // repeats
    }

    quickcheck! {
        fn efficient_order(ag: u32, at: u32, cg: u32, ct: u32, tg: u32) -> bool {
            let mut builder = CodeBuilder::new();
            builder.push("CG", cg);
            builder.push("AG", ag);
            builder.push("AT", at);
            builder.push("CT", ct);
            builder.push("TG", tg);
            let (book, _) = builder.finish();

            let len = |symbol| {
                book.get(symbol).map_or(0, |code| code.len())
            };

            at >= ct || len("CT") <= len("AT") ||
            ag.saturating_add(at).saturating_add(cg).saturating_add(ct).saturating_add(tg) >= u32::MAX
        }

        fn encode_decode_bytes(symbols: Vec<u8>) -> bool {
            let mut counts = [0; 256];
            for symbol in &symbols {
                counts[usize::from(*symbol)] += 1;
            }

            let (book, tree) = counts.iter()
                .enumerate()
                .map(|(k, v)| (k as u8, *v))
                .collect::<CodeBuilder<_, _>>()
                .finish();

            let mut buffer = BitVec::new();
            for symbol in &symbols {
                book.encode(&mut buffer, symbol).unwrap();
            }

            tree.unbounded_decoder(&buffer).eq(symbols)
        }
    }
}
