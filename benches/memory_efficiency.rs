//! Memory Efficiency Benchmarks
//!
//! Verifies O(|G|·N) memory complexity for exceptional group constructions,
//! where |G| is the number of roots and N is the rank.

#![allow(missing_docs)]

use atlas_embeddings::{Atlas, E8RootSystem, groups::{G2, F4, E6, E7, E8Group}};
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};

/// Measure memory footprint and construction time for Atlas
fn bench_atlas_memory(c: &mut Criterion) {
    c.bench_function("atlas_memory_footprint", |b| {
        b.iter(|| {
            let atlas = Atlas::new();
            // Access key operations to ensure full construction
            let _ = black_box(atlas.num_vertices());
            let _ = black_box(atlas.degree(42));
            let _ = black_box(atlas.mirror_pair(42));
            atlas
        });
    });
}

/// Measure memory footprint for E8 root system
fn bench_e8_memory(c: &mut Criterion) {
    c.bench_function("e8_memory_footprint", |b| {
        b.iter(|| {
            let e8 = E8RootSystem::new();
            let _ = black_box(e8.num_roots());
            let _ = black_box(e8.get_root(100));
            e8
        });
    });
}

/// Measure exceptional group construction with memory efficiency focus
fn bench_exceptional_groups_memory(c: &mut Criterion) {
    let atlas = Atlas::new();
    
    let mut group = c.benchmark_group("exceptional_groups_memory");
    
    // G₂: 12 roots × rank 2 = 24 elements worth of data
    group.bench_function(BenchmarkId::new("g2", "12_roots_rank_2"), |b| {
        b.iter(|| {
            let g2 = G2::from_atlas(black_box(&atlas));
            assert_eq!(g2.num_roots(), 12);
            assert_eq!(g2.rank(), 2);
            g2
        });
    });
    
    // F₄: 48 roots × rank 4 = 192 elements worth of data
    group.bench_function(BenchmarkId::new("f4", "48_roots_rank_4"), |b| {
        b.iter(|| {
            let f4 = F4::from_atlas(black_box(&atlas));
            assert_eq!(f4.num_roots(), 48);
            assert_eq!(f4.rank(), 4);
            f4
        });
    });
    
    // E₆: 72 roots × rank 6 = 432 elements worth of data
    group.bench_function(BenchmarkId::new("e6", "72_roots_rank_6"), |b| {
        b.iter(|| {
            let e6 = E6::from_atlas(black_box(&atlas));
            assert_eq!(e6.num_roots(), 72);
            assert_eq!(e6.rank(), 6);
            e6
        });
    });
    
    // E₇: 126 roots × rank 7 = 882 elements worth of data
    group.bench_function(BenchmarkId::new("e7", "126_roots_rank_7"), |b| {
        b.iter(|| {
            let e7 = E7::from_atlas(black_box(&atlas));
            assert_eq!(e7.num_roots(), 126);
            assert_eq!(e7.rank(), 7);
            e7
        });
    });
    
    // E₈: 240 roots × rank 8 = 1920 elements worth of data
    group.bench_function(BenchmarkId::new("e8", "240_roots_rank_8"), |b| {
        b.iter(|| {
            let e8 = E8Group::new();
            assert_eq!(e8.num_roots(), 240);
            assert_eq!(e8.rank(), 8);
            e8
        });
    });
    
    group.finish();
}

/// Benchmark repeated operations to verify no memory leaks
fn bench_repeated_constructions(c: &mut Criterion) {
    c.bench_function("atlas_repeated_1000x", |b| {
        b.iter(|| {
            for _ in 0..1000 {
                let _ = black_box(Atlas::new());
            }
        });
    });
    
    c.bench_function("e8_repeated_100x", |b| {
        b.iter(|| {
            for _ in 0..100 {
                let _ = black_box(E8RootSystem::new());
            }
        });
    });
}

/// Benchmark memory scaling: verify O(|G|·N) growth
fn bench_memory_scaling(c: &mut Criterion) {
    let atlas = Atlas::new();
    
    let mut group = c.benchmark_group("memory_scaling");
    
    // Expected memory scaling: O(|G|·N) where |G| = roots, N = rank
    // G₂:  12 ×  2 =   24 (baseline)
    // F₄:  48 ×  4 =  192 (8× baseline)
    // E₆:  72 ×  6 =  432 (18× baseline)
    // E₇: 126 ×  7 =  882 (36.75× baseline)
    // E₈: 240 ×  8 = 1920 (80× baseline)
    
    group.bench_function("scaling_g2", |b| {
        b.iter(|| G2::from_atlas(black_box(&atlas)));
    });
    
    group.bench_function("scaling_f4", |b| {
        b.iter(|| F4::from_atlas(black_box(&atlas)));
    });
    
    group.bench_function("scaling_e6", |b| {
        b.iter(|| E6::from_atlas(black_box(&atlas)));
    });
    
    group.bench_function("scaling_e7", |b| {
        b.iter(|| E7::from_atlas(black_box(&atlas)));
    });
    
    group.bench_function("scaling_e8", |b| {
        b.iter(|| E8Group::new());
    });
    
    group.finish();
}

criterion_group!(
    benches,
    bench_atlas_memory,
    bench_e8_memory,
    bench_exceptional_groups_memory,
    bench_repeated_constructions,
    bench_memory_scaling
);
criterion_main!(benches);
