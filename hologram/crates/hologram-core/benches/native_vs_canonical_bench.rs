//! Comprehensive benchmarks comparing Native CPU vs Sigmatics Canonical implementations
//!
//! Tests two execution paths:
//! 1. **Native CPU**: Raw loops (non-canonical, baseline)
//! 2. **Sigmatics Canonical**: Generator-based execution with canonical circuit compilation
//!
//! ## Test Sizes
//!
//! - 256 elements (small)
//! - 4,096 elements (medium)
//! - 65,536 elements (large)
//! - 262,144 elements (very large)
//! - 1,048,576 elements (1M - stress test)
//!
//! ## Expected Results
//!
//! - Native competitive at small sizes (<1K elements)
//! - Sigmatics canonical wins at medium/large sizes (>4K elements)
//! - Canonical compilation reduces operation count by 75%+
//! - Consistent ~5.8µs base latency for canonical operations

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use hologram_core::{ops, Executor};

// ============================================================================
// Native CPU Implementations (Non-Canonical Baseline)
// ============================================================================

/// Native CPU vector addition: c[i] = a[i] + b[i]
#[inline(never)]
fn native_vector_add(a: &[f32], b: &[f32], c: &mut [f32]) {
    for i in 0..a.len() {
        c[i] = a[i] + b[i];
    }
}

/// Native CPU vector multiplication: c[i] = a[i] * b[i]
#[inline(never)]
fn native_vector_mul(a: &[f32], b: &[f32], c: &mut [f32]) {
    for i in 0..a.len() {
        c[i] = a[i] * b[i];
    }
}

/// Native CPU vector subtraction: c[i] = a[i] - b[i]
#[inline(never)]
fn native_vector_sub(a: &[f32], b: &[f32], c: &mut [f32]) {
    for i in 0..a.len() {
        c[i] = a[i] - b[i];
    }
}

/// Native CPU vector division: c[i] = a[i] / b[i]
#[inline(never)]
fn native_vector_div(a: &[f32], b: &[f32], c: &mut [f32]) {
    for i in 0..a.len() {
        c[i] = a[i] / b[i];
    }
}

/// Native CPU absolute value: b[i] = |a[i]|
#[inline(never)]
fn native_abs(a: &[f32], b: &mut [f32]) {
    for i in 0..a.len() {
        b[i] = a[i].abs();
    }
}

/// Native CPU negation: b[i] = -a[i]
#[inline(never)]
fn native_neg(a: &[f32], b: &mut [f32]) {
    for i in 0..a.len() {
        b[i] = -a[i];
    }
}

/// Native CPU ReLU: b[i] = max(0, a[i])
#[inline(never)]
fn native_relu(a: &[f32], b: &mut [f32]) {
    for i in 0..a.len() {
        b[i] = a[i].max(0.0);
    }
}

/// Native CPU sum reduction
#[inline(never)]
fn native_sum(a: &[f32]) -> f32 {
    let mut sum = 0.0;
    for &x in a {
        sum += x;
    }
    sum
}

/// Native CPU min value
#[inline(never)]
fn native_min(a: &[f32], b: &[f32], c: &mut [f32]) {
    for i in 0..a.len() {
        c[i] = a[i].min(b[i]);
    }
}

/// Native CPU max value
#[inline(never)]
fn native_max(a: &[f32], b: &[f32], c: &mut [f32]) {
    for i in 0..a.len() {
        c[i] = a[i].max(b[i]);
    }
}

// ============================================================================
// Binary Operations: Native vs Canonical
// ============================================================================

fn benchmark_binary_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("binary_ops");

    // Test sizes from 256 to 1M elements
    for size in [256, 4_096, 65_536, 262_144, 1_048_576].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        // ========================================================================
        // Vector Addition: a + b
        // ========================================================================

        group.bench_with_input(BenchmarkId::new("add/native", size), size, |bencher, &size| {
            let a = vec![1.0f32; size];
            let b = vec![2.0f32; size];
            let mut c = vec![0.0f32; size];

            bencher.iter(|| {
                native_vector_add(black_box(&a), black_box(&b), black_box(&mut c));
            });
        });

        group.bench_with_input(BenchmarkId::new("add/canonical", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let b = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::vector_add(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // ========================================================================
        // Vector Multiplication: a * b
        // ========================================================================

        group.bench_with_input(BenchmarkId::new("mul/native", size), size, |bencher, &size| {
            let a = vec![1.5f32; size];
            let b = vec![2.0f32; size];
            let mut c = vec![0.0f32; size];

            bencher.iter(|| {
                native_vector_mul(black_box(&a), black_box(&b), black_box(&mut c));
            });
        });

        group.bench_with_input(BenchmarkId::new("mul/canonical", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let b = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::vector_mul(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // ========================================================================
        // Vector Subtraction: a - b
        // ========================================================================

        group.bench_with_input(BenchmarkId::new("sub/native", size), size, |bencher, &size| {
            let a = vec![3.0f32; size];
            let b = vec![1.0f32; size];
            let mut c = vec![0.0f32; size];

            bencher.iter(|| {
                native_vector_sub(black_box(&a), black_box(&b), black_box(&mut c));
            });
        });

        group.bench_with_input(BenchmarkId::new("sub/canonical", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let b = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::vector_sub(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // ========================================================================
        // Vector Division: a / b
        // ========================================================================

        group.bench_with_input(BenchmarkId::new("div/native", size), size, |bencher, &size| {
            let a = vec![10.0f32; size];
            let b = vec![2.0f32; size];
            let mut c = vec![0.0f32; size];

            bencher.iter(|| {
                native_vector_div(black_box(&a), black_box(&b), black_box(&mut c));
            });
        });

        group.bench_with_input(BenchmarkId::new("div/canonical", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let b = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::vector_div(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // ========================================================================
        // Min: min(a, b)
        // ========================================================================

        group.bench_with_input(BenchmarkId::new("min/native", size), size, |bencher, &size| {
            let a = vec![1.0f32; size];
            let b = vec![2.0f32; size];
            let mut c = vec![0.0f32; size];

            bencher.iter(|| {
                native_min(black_box(&a), black_box(&b), black_box(&mut c));
            });
        });

        group.bench_with_input(BenchmarkId::new("min/canonical", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let b = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::min(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // ========================================================================
        // Max: max(a, b)
        // ========================================================================

        group.bench_with_input(BenchmarkId::new("max/native", size), size, |bencher, &size| {
            let a = vec![1.0f32; size];
            let b = vec![2.0f32; size];
            let mut c = vec![0.0f32; size];

            bencher.iter(|| {
                native_max(black_box(&a), black_box(&b), black_box(&mut c));
            });
        });

        group.bench_with_input(BenchmarkId::new("max/canonical", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let b = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::max(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });
    }

    group.finish();
}

// ============================================================================
// Unary Operations: Native vs Canonical
// ============================================================================

fn benchmark_unary_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("unary_ops");

    for size in [256, 4_096, 65_536, 262_144, 1_048_576].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        // ========================================================================
        // Absolute Value: |a|
        // ========================================================================

        group.bench_with_input(BenchmarkId::new("abs/native", size), size, |bencher, &size| {
            let a = vec![-1.5f32; size];
            let mut b = vec![0.0f32; size];

            bencher.iter(|| {
                native_abs(black_box(&a), black_box(&mut b));
            });
        });

        group.bench_with_input(BenchmarkId::new("abs/canonical", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let mut b = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::abs(&mut exec, &a, &mut b, size).unwrap();
            });
        });

        // ========================================================================
        // Negation: -a
        // ========================================================================

        group.bench_with_input(BenchmarkId::new("neg/native", size), size, |bencher, &size| {
            let a = vec![2.5f32; size];
            let mut b = vec![0.0f32; size];

            bencher.iter(|| {
                native_neg(black_box(&a), black_box(&mut b));
            });
        });

        group.bench_with_input(BenchmarkId::new("neg/canonical", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let mut b = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::neg(&mut exec, &a, &mut b, size).unwrap();
            });
        });

        // ========================================================================
        // ReLU: max(0, a)
        // ========================================================================

        group.bench_with_input(BenchmarkId::new("relu/native", size), size, |bencher, &size| {
            let a = vec![-0.5f32; size];
            let mut b = vec![0.0f32; size];

            bencher.iter(|| {
                native_relu(black_box(&a), black_box(&mut b));
            });
        });

        group.bench_with_input(BenchmarkId::new("relu/canonical", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let mut b = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::relu(&mut exec, &a, &mut b, size).unwrap();
            });
        });
    }

    group.finish();
}

// ============================================================================
// Reduction Operations: Native vs Canonical
// ============================================================================

fn benchmark_reductions(c: &mut Criterion) {
    let mut group = c.benchmark_group("reductions");

    for size in [256, 4_096, 65_536, 262_144, 1_048_576].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        // ========================================================================
        // Sum Reduction
        // ========================================================================

        group.bench_with_input(BenchmarkId::new("sum/native", size), size, |bencher, &size| {
            let a = vec![1.0f32; size];

            bencher.iter(|| {
                let result = native_sum(black_box(&a));
                black_box(result);
            });
        });

        group.bench_with_input(BenchmarkId::new("sum/canonical", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let mut result = exec.allocate::<f32>(3).unwrap(); // Needs 3 elements for temporaries

            bencher.iter(|| {
                ops::reduce::sum(&mut exec, &a, &mut result, size).unwrap();
            });
        });
    }

    group.finish();
}

criterion_group!(benches, benchmark_binary_ops, benchmark_unary_ops, benchmark_reductions,);
criterion_main!(benches);
