use bit_vec::BitVec;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use huffman_compress::codebook;
use std::collections::HashMap;

fn bench_encode_decode(c: &mut Criterion) {
    let mut weights = HashMap::new();
    weights.insert("CG", 293);
    weights.insert("AG", 34);
    weights.insert("AT", 4);
    weights.insert("CT", 4);
    weights.insert("TG", 1);

    let (book, tree) = codebook(&weights);

    let example = black_box(vec!["AT", "CG", "AT", "TG", "AG", "CT", "CT", "AG", "CG"]);

    c.bench_function("encode-decode", |b| {
        b.iter(|| {
            let mut buffer = BitVec::new();
            for symbol in &example {
                book.encode(&mut buffer, symbol).unwrap();
            }

            assert!(example
                .iter()
                .zip(tree.unbounded_decoder(&buffer))
                .all(|(l, r)| l == &r));
        })
    });
}

criterion_group!(benches, bench_encode_decode);

criterion_main!(benches);
