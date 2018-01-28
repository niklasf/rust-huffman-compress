extern crate bit_vec;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::BinaryHeap;
use std::error::Error;
use std::hash::Hash;
use std::fmt;

use bit_vec::BitVec;

pub struct Tree<K> {
    root: usize,
    arena: Vec<Node<K>>,
}

impl<'a, K: Eq + Hash + Clone + 'a> Tree<K> {
    pub fn decoder<I>(&'a self, iterable: I) -> Decoder<'a, I, K>
        where I: IntoIterator<Item=bool>
    {
        Decoder {
            tree: self,
            iter: iterable.into_iter(),
        }
    }
}

pub struct Decoder<'a, I: IntoIterator<Item=bool>, K: 'a> {
    tree: &'a Tree<K>,
    iter: I::IntoIter,
}

pub struct Book<K> {
    book: HashMap<K, BitVec>,
}

impl<K: Eq + Hash + Clone> Book<K> {
    pub fn into_inner(self) -> HashMap<K, BitVec> {
        self.book
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&BitVec>
        where K: Borrow<Q>, Q: Hash + Eq
    {
        self.book.get(k)
    }

    pub fn encode<Q>(&self, buffer: &mut BitVec, k: &Q) -> Result<(), EncodeError>
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

#[derive(Debug)]
pub struct EncodeError;

impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        "encode error".fmt(f)
    }
}

impl Error for EncodeError {
    fn description(&self) -> &str {
        "encode error"
    }
}

struct Node<K> {
    weight: u64,
    parent: Option<usize>,
    data: NodeData<K>
}

enum NodeData<K> {
    Leaf { symbol: K },
    Branch { left: usize, right: usize },
}

#[derive(Eq, PartialEq, Ord, PartialOrd)]
struct HeapData {
    weight: u64,
    id: usize,
}

pub fn codebook<K: Eq + Hash + Clone>(weights: &HashMap<K, u64>) -> (Tree<K>, Book<K>) {
    let num_symbols = weights.len();

    let mut heap = BinaryHeap::new();

    let mut arena: Vec<Node<K>> = Vec::with_capacity(num_symbols);

    for (symbol, weight) in weights {
        let id = arena.len();

        heap.push(HeapData {
            weight: *weight,
            id,
        });

        arena.push(Node {
            weight: *weight,
            //id,
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
            weight: left.weight + right.weight,
            id
        });

        arena.push(Node {
            weight: left.weight + right.weight,
            parent: None,
            //id,
            data: NodeData::Branch {
                left: left.id,
                right: right.id
            }
        });
    }

    let mut book = Book::with_capacity(num_symbols);

    let root = heap.pop().unwrap().id;
    book.build(&arena, &arena[root], BitVec::new());

    let tree = Tree {
        root,
        arena,
    };

    (tree, book)
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

        let (tree, book) = codebook(&sample);

        let mut buffer = BitVec::new();
        book.encode(&mut buffer, &1).unwrap();
        book.encode(&mut buffer, &2).unwrap();
        book.encode(&mut buffer, &3).unwrap();
        book.encode(&mut buffer, &4).unwrap();
        book.encode(&mut buffer, &5).unwrap();
    }
}
