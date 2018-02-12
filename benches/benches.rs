#[macro_use]
extern crate bencher;
extern crate bit_vec;
extern crate huffman_compress;

use std::collections::HashMap;
use bencher::{Bencher, black_box};
use bit_vec::BitVec;
use huffman_compress::codebook;

fn bench_encode_decode(b: &mut Bencher) {
    let mut weights = HashMap::new();
    weights.insert("CG", 293);
    weights.insert("AG", 34);
    weights.insert("AT", 4);
    weights.insert("CT", 4);
    weights.insert("TG", 1);

    let (book, tree) = codebook(&weights);

    let example = black_box(vec!["AT", "CG", "AT", "TG", "AG", "CT", "CT", "AG", "CG"]);

    b.iter(|| {
        let mut buffer = BitVec::new();
        for symbol in &example {
            book.encode(&mut buffer, symbol).unwrap();
        }

        example.iter().zip(tree.decoder(&buffer)).all(|(l, r)| l == &r);
    });
}

benchmark_group!(benches,
    bench_encode_decode);

benchmark_main!(benches);
