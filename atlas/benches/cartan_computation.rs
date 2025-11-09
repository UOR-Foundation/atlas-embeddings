//! Benchmarks for Cartan matrix operations
//!
//! Measures performance of Cartan matrix verification and computation.
//! From certified Python implementation: Cartan operations must be efficient
//! for group classification and verification.

#![allow(missing_docs)] // Benchmark internal functions don't need docs

use atlas_embeddings::arithmetic::{HalfInteger, Vector8};
use atlas_embeddings::cartan::CartanMatrix;
use atlas_embeddings::weyl::{SimpleReflection, WeylGroup};
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_cartan_construction(c: &mut Criterion) {
    c.bench_function("cartan_g2_new", |b| {
        b.iter(|| {
            let g2 = CartanMatrix::g2();
            black_box(g2)
        });
    });

    c.bench_function("cartan_f4_new", |b| {
        b.iter(|| {
            let f4 = CartanMatrix::f4();
            black_box(f4)
        });
    });

    c.bench_function("cartan_e6_new", |b| {
        b.iter(|| {
            let e6 = CartanMatrix::e6();
            black_box(e6)
        });
    });

    c.bench_function("cartan_e8_new", |b| {
        b.iter(|| {
            let e8 = CartanMatrix::e8();
            black_box(e8)
        });
    });
}

fn bench_cartan_properties(c: &mut Criterion) {
    let e6 = CartanMatrix::e6();

    c.bench_function("cartan_is_valid", |b| {
        b.iter(|| {
            let valid = black_box(e6).is_valid();
            black_box(valid)
        });
    });

    c.bench_function("cartan_is_simply_laced", |b| {
        b.iter(|| {
            let simply_laced = black_box(e6).is_simply_laced();
            black_box(simply_laced)
        });
    });

    c.bench_function("cartan_is_symmetric", |b| {
        b.iter(|| {
            let symmetric = black_box(e6).is_symmetric();
            black_box(symmetric)
        });
    });

    c.bench_function("cartan_is_connected", |b| {
        b.iter(|| {
            let connected = black_box(e6).is_connected();
            black_box(connected)
        });
    });
}

fn bench_cartan_determinants(c: &mut Criterion) {
    let g2 = CartanMatrix::g2();
    let e6 = CartanMatrix::e6();

    c.bench_function("cartan_g2_determinant", |b| {
        b.iter(|| {
            let det = black_box(g2).determinant();
            black_box(det)
        });
    });

    c.bench_function("cartan_e6_determinant", |b| {
        b.iter(|| {
            let det = black_box(e6).determinant();
            black_box(det)
        });
    });
}

fn bench_weyl_construction(c: &mut Criterion) {
    c.bench_function("weyl_g2_new", |b| {
        b.iter(|| {
            let weyl = WeylGroup::g2();
            black_box(weyl)
        });
    });

    c.bench_function("weyl_f4_new", |b| {
        b.iter(|| {
            let weyl = WeylGroup::f4();
            black_box(weyl)
        });
    });

    c.bench_function("weyl_e8_new", |b| {
        b.iter(|| {
            let weyl = WeylGroup::e8();
            black_box(weyl)
        });
    });
}

fn bench_weyl_reflections(c: &mut Criterion) {
    let root = Vector8::new([
        HalfInteger::from_integer(1),
        HalfInteger::from_integer(-1),
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(0),
    ]);

    let v = Vector8::new([
        HalfInteger::from_integer(1),
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(1),
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(1),
        HalfInteger::from_integer(0),
        HalfInteger::from_integer(1),
        HalfInteger::from_integer(0),
    ]);

    c.bench_function("weyl_simple_reflection_new", |b| {
        b.iter(|| {
            let refl = SimpleReflection::from_root(&black_box(root));
            black_box(refl)
        });
    });

    let reflection = SimpleReflection::from_root(&root);

    c.bench_function("weyl_simple_reflection_apply", |b| {
        b.iter(|| {
            let reflected = black_box(&reflection).apply(&black_box(v));
            black_box(reflected)
        });
    });

    c.bench_function("weyl_involution_check", |b| {
        b.iter(|| {
            let is_involution = black_box(&reflection).verify_involution(&black_box(v));
            black_box(is_involution)
        });
    });
}

fn bench_coxeter_numbers(c: &mut Criterion) {
    let g2 = WeylGroup::g2();
    let f4 = WeylGroup::f4();

    c.bench_function("weyl_coxeter_number_g2", |b| {
        b.iter(|| {
            let m = black_box(&g2).coxeter_number(black_box(0), black_box(1));
            black_box(m)
        });
    });

    c.bench_function("weyl_coxeter_number_f4", |b| {
        b.iter(|| {
            let m = black_box(&f4).coxeter_number(black_box(1), black_box(2));
            black_box(m)
        });
    });
}

criterion_group!(
    benches,
    bench_cartan_construction,
    bench_cartan_properties,
    bench_cartan_determinants,
    bench_weyl_construction,
    bench_weyl_reflections,
    bench_coxeter_numbers
);
criterion_main!(benches);
