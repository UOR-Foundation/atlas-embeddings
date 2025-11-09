//! Benchmarks for Backend Compilation
//!
//! Compares performance of canonical vs non-canonical circuits when compiled
//! to backend generator sequences.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use hologram_compiler::{SigmaticsCompiler, VectorCircuits, VectorOperation};

/// Benchmark compilation time for different circuits
fn bench_compilation(c: &mut Criterion) {
    let mut group = c.benchmark_group("compilation");

    let h_squared = VectorCircuits::h_squared();
    let x_squared = VectorCircuits::x_squared();
    let hxh = VectorCircuits::hxh_conjugation();

    let circuits: Vec<(&str, &str)> = vec![
        ("Simple Mark", "mark@c21"),
        ("Sequential Marks", "mark@c00 . mark@c01 . mark@c02"),
        ("H² (Canonical)", &h_squared),
        ("X² (Canonical)", &x_squared),
        ("HXH Conjugation", &hxh),
    ];

    for (name, circuit) in circuits {
        group.bench_with_input(BenchmarkId::from_parameter(name), &circuit, |b, &circuit| {
            b.iter(|| SigmaticsCompiler::compile(black_box(circuit)));
        });
    }

    group.finish();
}

/// Benchmark the optimization ratio achieved by canonicalization
fn bench_optimization_ratio(c: &mut Criterion) {
    let mut group = c.benchmark_group("optimization");

    // H² should reduce from 4 ops to 1 op
    group.bench_function("H² Reduction", |b| {
        b.iter(|| {
            let circuit = VectorCircuits::h_squared();
            let op = VectorOperation::new("H²", black_box(&circuit)).unwrap();
            black_box(op.reduction_pct());
        });
    });

    // HXH should reduce from 5 ops to 1 op (80% reduction)
    group.bench_function("HXH Reduction", |b| {
        b.iter(|| {
            let circuit = VectorCircuits::hxh_conjugation();
            let op = VectorOperation::new("HXH", black_box(&circuit)).unwrap();
            black_box(op.reduction_pct());
        });
    });

    group.finish();
}

/// Benchmark raw compilation without canonicalization
fn bench_raw_compilation(c: &mut Criterion) {
    let mut group = c.benchmark_group("raw_compilation");

    let circuits = vec![
        ("mark@c21", "Simple Mark"),
        ("mark@c00 . mark@c01 . mark@c02", "Sequential"),
    ];

    for (circuit, name) in circuits {
        group.bench_with_input(BenchmarkId::from_parameter(name), &circuit, |b, &circuit| {
            b.iter(|| SigmaticsCompiler::compile_raw(black_box(circuit)));
        });
    }

    group.finish();
}

/// Benchmark number of generator calls for canonical vs non-canonical
fn bench_generator_call_count(c: &mut Criterion) {
    let mut group = c.benchmark_group("call_count");

    // Compare H² canonical vs explicit
    group.bench_function("H² Canonical Calls", |b| {
        let circuit = VectorCircuits::h_squared();
        let compiled = SigmaticsCompiler::compile(&circuit).unwrap();
        b.iter(|| black_box(compiled.calls.len()));
    });

    // HXH conjugation
    group.bench_function("HXH Canonical Calls", |b| {
        let circuit = VectorCircuits::hxh_conjugation();
        let compiled = SigmaticsCompiler::compile(&circuit).unwrap();
        b.iter(|| black_box(compiled.calls.len()));
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_compilation,
    bench_optimization_ratio,
    bench_raw_compilation,
    bench_generator_call_count,
);
criterion_main!(benches);
