//! Benchmarks for exact arithmetic operations
//!
//! Verifies that exact rational arithmetic has acceptable performance
//! for Atlas computations. From certified Python implementation:
//! Fraction arithmetic must be fast enough for root system operations.

#![allow(missing_docs)] // Benchmark internal functions don't need docs

use atlas_embeddings::arithmetic::{HalfInteger, Rational, Vector8};
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_half_integer_arithmetic(c: &mut Criterion) {
    let a = HalfInteger::new(5);
    let b = HalfInteger::new(7);

    c.bench_function("half_integer_addition", |b_iter| {
        b_iter.iter(|| {
            let sum = black_box(a) + black_box(b);
            black_box(sum)
        });
    });

    c.bench_function("half_integer_subtraction", |b_iter| {
        b_iter.iter(|| {
            let diff = black_box(a) - black_box(b);
            black_box(diff)
        });
    });

    c.bench_function("half_integer_multiplication", |b_iter| {
        b_iter.iter(|| {
            let prod = black_box(a) * black_box(b);
            black_box(prod)
        });
    });

    c.bench_function("half_integer_square", |b_iter| {
        b_iter.iter(|| {
            let sq = black_box(a).square();
            black_box(sq)
        });
    });
}

fn bench_rational_arithmetic(c: &mut Criterion) {
    let a = Rational::new(3, 5);
    let b = Rational::new(2, 7);

    c.bench_function("rational_addition", |b_iter| {
        b_iter.iter(|| {
            let sum = black_box(a) + black_box(b);
            black_box(sum)
        });
    });

    c.bench_function("rational_multiplication", |b_iter| {
        b_iter.iter(|| {
            let prod = black_box(a) * black_box(b);
            black_box(prod)
        });
    });

    c.bench_function("rational_division", |b_iter| {
        b_iter.iter(|| {
            let quot = black_box(a) / black_box(b);
            black_box(quot)
        });
    });
}

fn bench_vector8_operations(c: &mut Criterion) {
    // Use integer coordinates (even numerators) so rational scaling works
    let v = Vector8::new([
        HalfInteger::from_integer(1),
        HalfInteger::from_integer(-1),
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(1),
        HalfInteger::from_integer(-1),
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(1),
        HalfInteger::from_integer(-1),
    ]);

    let w = Vector8::new([
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(1),
        HalfInteger::from_integer(-1),
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(1),
        HalfInteger::from_integer(-1),
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(1),
    ]);

    c.bench_function("vector8_addition", |b| {
        b.iter(|| {
            let sum = black_box(v) + black_box(w);
            black_box(sum)
        });
    });

    c.bench_function("vector8_inner_product", |b| {
        b.iter(|| {
            let ip = black_box(v).inner_product(&black_box(w));
            black_box(ip)
        });
    });

    c.bench_function("vector8_norm_squared", |b| {
        b.iter(|| {
            let norm_sq = black_box(v).norm_squared();
            black_box(norm_sq)
        });
    });

    c.bench_function("vector8_scale", |b| {
        b.iter(|| {
            let scaled = black_box(v).scale(black_box(3));
            black_box(scaled)
        });
    });

    c.bench_function("vector8_scale_rational", |b| {
        b.iter(|| {
            // Use 1/2 which preserves half-integer structure
            // (half-integer × 1/2 = quarter-integer, but 1/2 × even = integer)
            let r = Rational::new(1, 2);
            let scaled = black_box(v).scale_rational(black_box(r));
            black_box(scaled)
        });
    });
}

criterion_group!(
    benches,
    bench_half_integer_arithmetic,
    bench_rational_arithmetic,
    bench_vector8_operations
);
criterion_main!(benches);
