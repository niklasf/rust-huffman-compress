use std::hash::Hash;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::BinaryHeap;

struct Node<K> {
    //id: usize,
    weight: u64,
    parent: Option<usize>,
    data: NodeData<K>
}

enum NodeData<K> {
    Leaf { symbol: K },
    Twig { left: usize, right: usize },
}

#[derive(Eq, PartialEq, Ord, PartialOrd)]
struct HeapData {
    weight: u64,
    id: usize,
}

fn codebook<K: Eq + Hash>(weights: HashMap<K, u64>) {
    let mut heap = BinaryHeap::new();

    let mut arena: Vec<Node<K>> = Vec::with_capacity(weights.len());

    for (symbol, weight) in weights {
        let id = arena.len();

        heap.push(HeapData {
            weight,
            id,
        });

        arena.push(Node {
            weight,
            //id,
            parent: None,
            data: NodeData::Leaf {
                symbol
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
            data: NodeData::Twig {
                left: left.id,
                right: right.id
            }
        });
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
