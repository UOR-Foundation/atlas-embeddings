//! Canonicalization Performance Benchmarks
//!
//! Measures the performance of parsing and pattern-based rewriting.
//! Focus on compilation pipeline performance (parse → canonicalize).

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use hologram_compiler::Canonicalizer;

/// Benchmark simple expression parsing
fn bench_parse_simple(c: &mut Criterion) {
    c.bench_function("parse_simple", |b| {
        b.iter(|| hologram_compiler::parse(black_box("mark@c21")).unwrap());
    });
}

/// Benchmark sequential expression parsing
fn bench_parse_sequential(c: &mut Criterion) {
    let expr = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";

    c.bench_function("parse_sequential", |b| {
        b.iter(|| hologram_compiler::parse(black_box(expr)).unwrap());
    });
}

/// Benchmark H² canonicalization
fn bench_h_squared_canonicalization(c: &mut Criterion) {
    let expr = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";

    c.bench_function("h_squared_canonicalization", |b| {
        b.iter(|| Canonicalizer::parse_and_canonicalize(black_box(expr)).unwrap());
    });
}

/// Benchmark H⁴ canonicalization (multiple iterations)
fn bench_h_fourth_canonicalization(c: &mut Criterion) {
    let expr = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 . \
                copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";

    c.bench_function("h_fourth_canonicalization", |b| {
        b.iter(|| Canonicalizer::parse_and_canonicalize(black_box(expr)).unwrap());
    });
}

/// Benchmark canonicalization with varying circuit sizes
fn bench_canonicalization_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("canonicalization_scaling");

    for size in [1, 2, 4, 8, 16].iter() {
        let expr = generate_repeated_h_squared(*size);

        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), &expr, |b, expr| {
            b.iter(|| Canonicalizer::parse_and_canonicalize(black_box(expr)).unwrap());
        });
    }

    group.finish();
}

/// Generate expression with repeated H² patterns
fn generate_repeated_h_squared(count: usize) -> String {
    let h2 = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";
    (0..count).map(|_| h2).collect::<Vec<_>>().join(" . ")
}

/// Benchmark parallel circuit canonicalization
fn bench_parallel_canonicalization(c: &mut Criterion) {
    let expr = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 || \
                mark@c21 . mark@c21 || \
                mark@c42 . mark@c42";

    c.bench_function("parallel_canonicalization", |b| {
        b.iter(|| Canonicalizer::parse_and_canonicalize(black_box(expr)).unwrap());
    });
}

/// Benchmark complex reduction scenario
fn bench_complex_reduction(c: &mut Criterion) {
    let expr = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 . \
                mark@c21 . mark@c21 . \
                mark@c42 . mark@c42 . \
                mark@c00";

    c.bench_function("complex_reduction", |b| {
        b.iter(|| Canonicalizer::parse_and_canonicalize(black_box(expr)).unwrap());
    });
}

/// Benchmark canonical form generation
fn bench_canonical_form(c: &mut Criterion) {
    let expr = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";

    c.bench_function("canonical_form", |b| {
        b.iter(|| Canonicalizer::canonical_form(black_box(expr)).unwrap());
    });
}

/// Benchmark rewrite rule matching
fn bench_pattern_matching(c: &mut Criterion) {
    let mut group = c.benchmark_group("pattern_matching");

    group.bench_function("h_squared", |b| {
        let expr = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";
        b.iter(|| {
            let phrase = hologram_compiler::parse(black_box(expr)).unwrap();
            let engine = hologram_compiler::RewriteEngine::new();
            engine.rewrite(black_box(&phrase))
        });
    });

    group.bench_function("x_squared", |b| {
        let expr = "mark@c21 . mark@c21";
        b.iter(|| {
            let phrase = hologram_compiler::parse(black_box(expr)).unwrap();
            let engine = hologram_compiler::RewriteEngine::new();
            engine.rewrite(black_box(&phrase))
        });
    });

    group.bench_function("no_match", |b| {
        let expr = "mark@c05 . mark@c07 . mark@c12";
        b.iter(|| {
            let phrase = hologram_compiler::parse(black_box(expr)).unwrap();
            let engine = hologram_compiler::RewriteEngine::new();
            engine.rewrite(black_box(&phrase))
        });
    });

    group.finish();
}

/// Benchmark SigmaticsCompiler compilation
fn bench_compiler(c: &mut Criterion) {
    let mut group = c.benchmark_group("compiler");

    group.bench_function("simple", |b| {
        let expr = "mark@c21";
        b.iter(|| hologram_compiler::SigmaticsCompiler::compile(black_box(expr)).unwrap());
    });

    group.bench_function("h_squared", |b| {
        let expr = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";
        b.iter(|| hologram_compiler::SigmaticsCompiler::compile(black_box(expr)).unwrap());
    });

    group.bench_function("complex", |b| {
        let expr = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 . mark@c21 . mark@c21";
        b.iter(|| hologram_compiler::SigmaticsCompiler::compile(black_box(expr)).unwrap());
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_parse_simple,
    bench_parse_sequential,
    bench_h_squared_canonicalization,
    bench_h_fourth_canonicalization,
    bench_canonicalization_scaling,
    bench_parallel_canonicalization,
    bench_complex_reduction,
    bench_canonical_form,
    bench_pattern_matching,
    bench_compiler,
);

criterion_main!(benches);
