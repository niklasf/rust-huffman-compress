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
//! use std::collections::HashMap;
//! use bit_vec::BitVec;
//! use huffman_compress::{Book, Tree, codebook};
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
//! let (book, tree) = codebook(&weights);
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
//! let decoded: Vec<&str> = tree.decoder(&buffer).collect();
//! assert_eq!(decoded, example);
//! #     Ok(())
//! # }
//! #
//! # fn main() {
//! #     try_main().unwrap();
//! # }
//! ```

#![doc(html_root_url = "https://docs.rs/huffman-compress/0.2.0")]

#![deny(missing_docs)]
#![deny(warnings)]
#![deny(missing_debug_implementations)]

extern crate bit_vec;
extern crate num_traits;

use std::borrow::Borrow;
use std::cmp;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, BTreeMap, btree_map};
use std::error::Error;
use std::fmt;

use bit_vec::BitVec;

pub use num_traits::ops::saturating::Saturating;

/// A trie used for decoding.
#[derive(Debug, Clone)]
pub struct Tree<K> {
    root: usize,
    arena: Vec<Node<K>>,
}

#[derive(Debug, Clone)]
struct Node<K> {
    parent: Option<usize>,
    data: NodeData<K>
}

#[derive(Debug, Clone)]
enum NodeData<K> {
    Leaf { symbol: K },
    Branch { left: usize, right: usize },
}

impl<K: Clone> Tree<K> {
    /// An iterator decoding symbols from source of bits.
    ///
    /// If there are no symbols the decoded sequence is empty without consuming
    /// any bits.
    ///
    /// If there is only one symbol the iterator will yield that symbol
    /// **infinitely** often without consuming any bits.
    ///
    /// # Errors
    ///
    /// If the source is exhausted no further symbols will be decoded
    /// (not even incomplete ones).
    pub fn decoder<I>(&self, iterable: I) -> Decoder<K, I>
        where I: IntoIterator<Item=bool>
    {
        Decoder {
            tree: self,
            iter: iterable.into_iter(),
        }
    }
}

/// Decodes symbols from a source of bits.
#[derive(Debug)]
pub struct Decoder<'a, K: 'a, I: IntoIterator<Item=bool>> {
    tree: &'a Tree<K>,
    iter: I::IntoIter,
}

impl<'a, K: Clone, I: IntoIterator<Item=bool>> Iterator for Decoder<'a, K, I> {
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
                    let bit = match self.iter.next() {
                        Some(bit) => bit,
                        None => return None,
                    };

                    node = if bit {
                        &self.tree.arena[left]
                    } else {
                        &self.tree.arena[right]
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
        where K: Borrow<Q>,
              Q: Ord
    {
        self.book.get(k)
    }

    /// Returns true if the book contains the specified symbol.
    pub fn contains_symbol<Q: ?Sized>(&self, k: &Q) -> bool
        where K: Borrow<Q>,
              Q: Ord
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
        where K: Borrow<Q>,
              Q: Ord
    {
        match self.book.get(k) {
            Some(code) => buffer.extend(code),
            None => return Err(EncodeError { }),
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
            },
            NodeData::Branch  { left, right } => {
                let mut left_word = word.clone();
                left_word.push(true);
                self.build(arena, &arena[left], left_word);

                let mut right_word = word;
                right_word.push(false);
                self.build(arena, &arena[right], right_word);
            },
        }
    }
}

/// Tried to encode an unknown symbol.
#[derive(Debug, Clone)]
pub struct EncodeError;

impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.description().fmt(f)
    }
}

impl Error for EncodeError {
    fn description(&self) -> &str {
        "encode error: tried to encode an unknown symbol"
    }
}

/// Constructs a [book](struct.Book.html) and [tree](struct.Tree.html) pair
/// from a map of symbols and their weights.
///
/// # Implementation details
///
/// The output is guaranteed to be deterministic and stable across semver
/// compatible releases if:
///
/// * There is a strict order on the symbols `K`
/// * `weights` yields no duplicate symbols
///
/// The ordering of symbols will be used to break ties when weights are equal.
pub fn codebook<'a, I, K, W>(weights: I) -> (Book<K>, Tree<K>)
    where I: IntoIterator<Item = (&'a K, &'a W)>,
          K: 'a + Ord + Clone,
          W: 'a + Saturating + Ord + Clone
{
    let weights = weights.into_iter();
    let (size_hint, _) = weights.size_hint();
    let mut heap = BinaryHeap::with_capacity(size_hint);
    let mut arena: Vec<Node<K>> = Vec::with_capacity(size_hint);

    for (symbol, weight) in weights {
        heap.push(HeapData {
            weight: Reverse(weight.clone()),
            symbol: symbol.clone(),
            id: arena.len(),
        });

        arena.push(Node {
            parent: None,
            data: NodeData::Leaf {
                symbol: symbol.clone()
            }
        });
    }

    while heap.len() >= 2 {
        let id = arena.len();

        let left = heap.pop().unwrap();
        let right = heap.pop().unwrap();

        arena[left.id].parent = Some(id);
        arena[right.id].parent = Some(id);

        heap.push(HeapData {
            weight: Reverse(left.weight.0.saturating_add(right.weight.0)),
            symbol: cmp::max(left.symbol, right.symbol),
            id
        });

        arena.push(Node {
            parent: None,
            data: NodeData::Branch {
                left: left.id,
                right: right.id
            }
        });
    }

    let mut book = Book::new();

    match heap.pop() {
        Some(HeapData { id: root, .. }) => {
            book.build(&arena, &arena[root], BitVec::new());
            (book, Tree { root, arena })
        },
        None => (book, Tree { root: 0, arena })
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd)]
struct HeapData<K, W> {
    weight: Reverse<W>,
    symbol: K, // tie breaker
    id: usize,
}

impl<K: Clone, W: Clone> Clone for HeapData<K, W> {
    fn clone(&self) -> Self {
        HeapData {
            weight: Reverse(self.weight.0.clone()),
            symbol: self.symbol.clone(),
            id: self.id
        }
    }
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
        let (book, tree) = codebook(&sample);

        let mut buffer = BitVec::new();
        book.encode(&mut buffer, &1).unwrap();
        book.encode(&mut buffer, &2).unwrap();
        book.encode(&mut buffer, &3).unwrap();
        book.encode(&mut buffer, &4).unwrap();
        book.encode(&mut buffer, &5).unwrap();

        let mut decoder = tree.decoder(buffer);
        assert_eq!(decoder.next(), Some(1));
        assert_eq!(decoder.next(), Some(2));
        assert_eq!(decoder.next(), Some(3));
        assert_eq!(decoder.next(), Some(4));
        assert_eq!(decoder.next(), Some(5));
        assert_eq!(decoder.next(), None);
    }

    #[test]
    fn test_uniform_from_static() {
        const WEIGHTS: &[(&char, &usize)] = &[
            (&'a', &1),
            (&'b', &1),
            (&'c', &1),
            (&'d', &1),
        ];
        let (book, tree) = codebook(WEIGHTS.iter().cloned());

        let mut buffer = BitVec::new();
        book.encode(&mut buffer, &'a').unwrap();
        book.encode(&mut buffer, &'b').unwrap();
        book.encode(&mut buffer, &'c').unwrap();
        book.encode(&mut buffer, &'d').unwrap();

        let mut decoder = tree.decoder(buffer);
        assert_eq!(decoder.next(), Some('a'));
        assert_eq!(decoder.next(), Some('b'));
        assert_eq!(decoder.next(), Some('c'));
        assert_eq!(decoder.next(), Some('d'));
        assert_eq!(decoder.next(), None);
    }

    #[test]
    fn test_single() {
        let mut sample = HashMap::new();
        sample.insert("hello", 1);
        let (book, tree) = codebook(&sample);

        let mut buffer = BitVec::new();
        book.encode(&mut buffer, "hello").unwrap();

        let mut decoder = tree.decoder(buffer);
        assert_eq!(decoder.next(), Some("hello"));
    }

    #[test]
    fn test_empty() {
        let sample: HashMap<&str, u8> = HashMap::new();
        let (book, tree) = codebook(&sample);

        let mut buffer = BitVec::new();
        assert!(book.encode(&mut buffer, "hello").is_err());

        let mut decoder = tree.decoder(buffer);
        assert_eq!(decoder.next(), None);
    }
}
