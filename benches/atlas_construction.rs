//! Benchmarks for Atlas construction
//!
//! Measures performance of core Atlas operations to ensure
//! efficient computation while maintaining exact arithmetic.
//!
//! From certified Python implementation: Atlas operations must be fast enough
//! for interactive use while maintaining mathematical exactness.

#![allow(missing_docs)] // Benchmark internal functions don't need docs

use atlas_embeddings::{Atlas, E8RootSystem};
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_atlas_construction(c: &mut Criterion) {
    c.bench_function("atlas_new", |b| {
        b.iter(|| {
            let atlas = Atlas::new();
            black_box(atlas)
        });
    });
}

fn bench_atlas_vertex_operations(c: &mut Criterion) {
    let atlas = Atlas::new();

    c.bench_function("atlas_num_vertices", |b| {
        b.iter(|| {
            let n = atlas.num_vertices();
            black_box(n)
        });
    });

    c.bench_function("atlas_degree", |b| {
        b.iter(|| {
            let deg = atlas.degree(black_box(42));
            black_box(deg)
        });
    });

    c.bench_function("atlas_mirror_pair", |b| {
        b.iter(|| {
            let mirror = atlas.mirror_pair(black_box(42));
            black_box(mirror)
        });
    });
}

fn bench_atlas_adjacency(c: &mut Criterion) {
    let atlas = Atlas::new();

    c.bench_function("atlas_is_adjacent", |b| {
        b.iter(|| {
            let adj = atlas.is_adjacent(black_box(10), black_box(20));
            black_box(adj)
        });
    });

    c.bench_function("atlas_neighbors", |b| {
        b.iter(|| {
            let neighbors = atlas.neighbors(black_box(42));
            black_box(neighbors)
        });
    });
}

fn bench_e8_construction(c: &mut Criterion) {
    c.bench_function("e8_new", |b| {
        b.iter(|| {
            let e8 = E8RootSystem::new();
            black_box(e8)
        });
    });
}

fn bench_e8_operations(c: &mut Criterion) {
    let e8 = E8RootSystem::new();

    c.bench_function("e8_num_roots", |b| {
        b.iter(|| {
            let n = e8.num_roots();
            black_box(n)
        });
    });

    c.bench_function("e8_inner_product", |b| {
        b.iter(|| {
            let ip = e8.inner_product(black_box(0), black_box(100));
            black_box(ip)
        });
    });

    c.bench_function("e8_are_negatives", |b| {
        b.iter(|| {
            let neg = e8.are_negatives(black_box(0), black_box(120));
            black_box(neg)
        });
    });
}

criterion_group!(
    benches,
    bench_atlas_construction,
    bench_atlas_vertex_operations,
    bench_atlas_adjacency,
    bench_e8_construction,
    bench_e8_operations
);
criterion_main!(benches);
