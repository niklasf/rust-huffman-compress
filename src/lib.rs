#![doc(html_root_url = "https://docs.rs/huffman-compress/0.1.0")]

#![warn(missing_debug_implementations)]

extern crate bit_vec;
extern crate num_traits;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::BinaryHeap;
use std::error::Error;
use std::hash::Hash;
use std::fmt;

use bit_vec::BitVec;

pub use num_traits::ops::saturating::Saturating;

/// A binary tree used for decoding.
#[derive(Debug)]
pub struct Tree<K> {
    root: usize,
    arena: Vec<Node<K>>,
}

#[derive(Debug)]
struct Node<K> {
    parent: Option<usize>,
    data: NodeData<K>
}

#[derive(Debug)]
enum NodeData<K> {
    Leaf { symbol: K },
    Branch { left: usize, right: usize },
}

impl<K: Clone> Tree<K> {
    pub fn decoder<'a, I>(&'a self, iterable: I) -> Decoder<'a, K, I>
        where I: IntoIterator<Item=bool>
    {
        Decoder {
            tree: self,
            iter: iterable.into_iter(),
        }
    }
}

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
pub struct Book<K> {
    book: HashMap<K, BitVec>,
}

impl<K: Eq + Hash + fmt::Debug> fmt::Debug for Book<K> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Book")
            .field("book", &self.book)
            .finish()
    }
}

impl<K: Eq + Hash + Clone> Book<K> {
    pub fn into_inner(self) -> HashMap<K, BitVec> {
        self.book
    }

    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&BitVec>
        where K: Borrow<Q>, Q: Hash + Eq
    {
        self.book.get(k)
    }

    pub fn encode<Q: ?Sized>(&self, buffer: &mut BitVec, k: &Q) -> Result<(), EncodeError>
        where K: Borrow<Q>, Q: Hash + Eq
    {
        match self.book.get(k) {
            Some(code) => Ok(buffer.extend(code)),
            None => Err(EncodeError { }),
        }
    }

    fn with_capacity(num_symbols: usize) -> Book<K> {
        Book {
            book: HashMap::with_capacity(num_symbols),
        }
    }

    fn build(&mut self, arena: &Vec<Node<K>>, node: &Node<K>, word: BitVec) {
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
#[derive(Debug)]
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

/// Creates a book and tree pair from a map of symbols and their weights.
pub fn codebook<K: Eq + Hash + Clone, W: Saturating + Clone + Ord>(weights: &HashMap<K, W>) -> (Book<K>, Tree<K>) {
    let num_symbols = weights.len();
    let mut heap = BinaryHeap::with_capacity(num_symbols);
    let mut arena: Vec<Node<K>> = Vec::with_capacity(num_symbols);

    for (symbol, weight) in weights {
        heap.push(HeapData {
            weight: weight.clone(),
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
            weight: left.weight.saturating_add(right.weight),
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

    let mut book = Book::with_capacity(num_symbols);

    match heap.pop() {
        Some(HeapData { id: root, .. }) => {
            book.build(&arena, &arena[root], BitVec::new());
            (book, Tree { root, arena })
        },
        None => (book, Tree { root: 0, arena })
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone)]
struct HeapData<W: Saturating + Clone + Ord> {
    weight: W,
    id: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

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
