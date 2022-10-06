#![feature(test)]

extern crate test;

use snowflaked::Generator;
use test::Bencher;

#[bench]
fn test_generate_u64(b: &mut Bencher) {
    let mut generator = Generator::new(0);

    b.iter(|| {
        generator.generate::<u64>();
    });
}
