#![feature(test)]

use snowflaked::sync::Generator;
use test::Bencher;

extern crate test;

#[bench]
fn test_generate_u64(b: &mut Bencher) {
    let generator = Generator::new(0);

    b.iter(|| {
        generator.generate::<u64>();
    });
}
