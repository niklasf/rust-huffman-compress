huffman-compress
================

[Huffman compression](https://en.wikipedia.org/wiki/Huffman_coding)
given a probability distribution over arbitrary symbols.

[![Build Status](https://travis-ci.org/niklasf/rust-huffman-compress.svg?branch=master)](https://travis-ci.org/niklasf/rust-huffman-compress)
[![crates.io](https://img.shields.io/crates/v/huffman-compress.svg)](https://crates.io/crates/huffman-compress)

Examples
--------

```rust
extern crate bit_vec;
extern crate huffman_compress;

use std::collections::HashMap;
use bit_vec::BitVec;
use huffman_compress::{ Book, Tree, codebook };

let mut weights = HashMap::new();
weights.insert("CG", 293);
weights.insert("AG", 34);
weights.insert("AT", 4);
weights.insert("CT", 4);
weights.insert("TG", 1);

// Construct a Huffman code based on the weights (e.g. counts or relative
// frequencies).
let (book, tree) = codebook(&weights);

// More frequent symbols will be encoded with fewer bits.
assert!(book.get("CG").map_or(0, |cg| cg.len()) <
        book.get("TG").map_or(0, |ag| ag.len()));

// Encode some symbols using the book.
let mut buffer = BitVec::new();
let example = vec!["AT", "CG", "AT", "TG", "AG", "CT", "CT", "AG", "CG"];
for symbol in &example {
    book.encode(&mut buffer, symbol);
}

// Decode the symbols using the tree.
let decoded: Vec<&str> = tree.decoder(&buffer).collect();
assert_eq!(decoded, example);
```

Documentation
-------------

[Read the documentation](https://docs.rs/huffman-compress)

Changelog
---------

* 0.1.0
  - Initial release.

License
-------

huffman-compress is dual licensed under the [Apache 2.0](http://www.apache.org/licenses/LICENSE-2.0)
and [MIT](http://opensource.org/licenses/MIT) license, at your option.
