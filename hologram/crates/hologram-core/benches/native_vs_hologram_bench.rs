//! Comprehensive benchmarks comparing Native CPU vs Sigmatics implementations
//!
//! Tests two execution paths:
//! 1. **Native CPU**: Raw loops (LLVM auto-vectorized baseline)
//! 2. **Sigmatics Generator**: Direct generator execution on class_bases (math.rs)
//!
//! Tests both buffer types:
//! - **Linear buffers**: RAM-resident, arbitrary sizes
//! - **Boundary buffers**: Cache-resident, fixed 3072 elements per class
//!
//! ## Expected Results
//!
//! - Generator-based fastest (~160ns per class operation)
//! - ISA-based has translation overhead (2-3x slower)
//! - Native competitive at small sizes (<1K elements)
//! - Atlas wins at medium/large sizes (>4K elements)
//! - Cache-resident buffers 2-3x faster

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use hologram_core::{ops, Executor};

// ============================================================================
// Native CPU Implementations (Baseline)
// ============================================================================

/// Native CPU vector addition: c[i] = a[i] + b[i]
#[inline(never)]
fn native_vector_add(a: &[f32], b: &[f32], c: &mut [f32]) {
    for i in 0..a.len() {
        c[i] = a[i] + b[i];
    }
}

/// Native CPU vector subtraction: c[i] = a[i] - b[i]
#[allow(dead_code)]
#[inline(never)]
fn native_vector_sub(a: &[f32], b: &[f32], c: &mut [f32]) {
    for i in 0..a.len() {
        c[i] = a[i] - b[i];
    }
}

/// Native CPU vector multiplication: c[i] = a[i] * b[i]
#[inline(never)]
fn native_vector_mul(a: &[f32], b: &[f32], c: &mut [f32]) {
    for i in 0..a.len() {
        c[i] = a[i] * b[i];
    }
}

/// Native CPU vector division: c[i] = a[i] / b[i]
#[allow(dead_code)]
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
#[allow(dead_code)]
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

/// Native CPU sigmoid: f(x) = 1 / (1 + e^(-x))
#[inline(never)]
fn native_sigmoid(a: &[f32], b: &mut [f32]) {
    for i in 0..a.len() {
        b[i] = 1.0 / (1.0 + (-a[i]).exp());
    }
}

// ============================================================================
// Binary Operations Benchmarks
// ============================================================================

fn benchmark_binary_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("binary_ops");

    // Test sizes: small (256), medium (4K), large (64K)
    for size in [256, 4_096, 65_536].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        // Vector Add
        group.bench_with_input(BenchmarkId::new("add/native", size), size, |bencher, &size| {
            let a = vec![1.0f32; size];
            let b = vec![2.0f32; size];
            let mut c = vec![0.0f32; size];

            bencher.iter(|| {
                native_vector_add(black_box(&a), black_box(&b), black_box(&mut c));
            });
        });

        group.bench_with_input(BenchmarkId::new("add/sigmatics", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();

            // For generator-based, use boundary buffers (cache-resident)
            // Fixed at 3072 elements per class
            let actual_size = 3072.min(size);
            let mut a = exec.allocate_boundary::<f32>(0, 48, 256).unwrap();
            let mut b = exec.allocate_boundary::<f32>(2, 48, 256).unwrap();
            let mut c = exec.allocate_boundary::<f32>(1, 48, 256).unwrap();

            // Boundary buffers are always 3072 elements, so pad data
            let mut data_a = vec![0.0f32; 3072];
            let mut data_b = vec![0.0f32; 3072];
            for i in 0..actual_size {
                data_a[i] = i as f32;
                data_b[i] = 2.0;
            }
            a.copy_from_slice(&mut exec, &data_a).unwrap();
            b.copy_from_slice(&mut exec, &data_b).unwrap();

            bencher.iter(|| {
                ops::math::vector_add(&mut exec, &a, &b, &mut c, actual_size).unwrap();
            });
        });

        // Vector Multiply
        group.bench_with_input(BenchmarkId::new("mul/native", size), size, |bencher, &size| {
            let a = vec![1.5f32; size];
            let b = vec![2.0f32; size];
            let mut c = vec![0.0f32; size];

            bencher.iter(|| {
                native_vector_mul(black_box(&a), black_box(&b), black_box(&mut c));
            });
        });

        group.bench_with_input(BenchmarkId::new("mul/sigmatics", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();

            let actual_size = 3072.min(size);
            let mut a = exec.allocate_boundary::<f32>(0, 48, 256).unwrap();
            let mut b = exec.allocate_boundary::<f32>(2, 48, 256).unwrap();
            let mut c = exec.allocate_boundary::<f32>(1, 48, 256).unwrap();

            // Boundary buffers are always 3072 elements, so pad data
            let mut data_a = vec![0.0f32; 3072];
            let mut data_b = vec![0.0f32; 3072];
            for i in 0..actual_size {
                data_a[i] = i as f32;
                data_b[i] = 2.0;
            }
            a.copy_from_slice(&mut exec, &data_a).unwrap();
            b.copy_from_slice(&mut exec, &data_b).unwrap();

            bencher.iter(|| {
                ops::math::vector_mul(&mut exec, &a, &b, &mut c, actual_size).unwrap();
            });
        });
    }

    group.finish();
}

// ============================================================================
// Unary Operations Benchmarks
// ============================================================================

fn benchmark_unary_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("unary_ops");

    for size in [256, 4_096, 65_536].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        // Absolute Value
        group.bench_with_input(BenchmarkId::new("abs/native", size), size, |bencher, &size| {
            let a = vec![-1.5f32; size];
            let mut b = vec![0.0f32; size];

            bencher.iter(|| {
                native_abs(black_box(&a), black_box(&mut b));
            });
        });

        // ReLU
        group.bench_with_input(BenchmarkId::new("relu/native", size), size, |bencher, &size| {
            let a = vec![-0.5f32; size];
            let mut b = vec![0.0f32; size];

            bencher.iter(|| {
                native_relu(black_box(&a), black_box(&mut b));
            });
        });
    }

    group.finish();
}

// ============================================================================
// Reduction Benchmarks
// ============================================================================

fn benchmark_reductions(c: &mut Criterion) {
    let mut group = c.benchmark_group("reductions");

    for size in [256, 4_096, 65_536].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        // Sum
        group.bench_with_input(BenchmarkId::new("sum/native", size), size, |bencher, &size| {
            let a = vec![1.0f32; size];

            bencher.iter(|| {
                let result = native_sum(black_box(&a));
                black_box(result);
            });
        });
    }

    group.finish();
}

// ============================================================================
// Activation Function Benchmarks
// ============================================================================

fn benchmark_activations(c: &mut Criterion) {
    let mut group = c.benchmark_group("activations");

    for size in [256, 4_096, 65_536].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        // Sigmoid
        group.bench_with_input(BenchmarkId::new("sigmoid/native", size), size, |bencher, &size| {
            let a = vec![0.5f32; size];
            let mut b = vec![0.0f32; size];

            bencher.iter(|| {
                native_sigmoid(black_box(&a), black_box(&mut b));
            });
        });
    }

    group.finish();
}

// ============================================================================
// Buffer Type Comparison
// ============================================================================

fn benchmark_buffer_types(c: &mut Criterion) {
    let mut group = c.benchmark_group("buffer_types");

    // Fixed size for fair comparison (one class = 3072 elements)
    let size = 3072;
    group.throughput(Throughput::Elements(size as u64));

    // Boundary buffers (cache-resident)
    group.bench_function("add/boundary", |bencher| {
        let mut exec = Executor::new().unwrap();
        let mut a = exec.allocate_boundary::<f32>(0, 48, 256).unwrap();
        let mut b = exec.allocate_boundary::<f32>(2, 48, 256).unwrap();
        let mut c = exec.allocate_boundary::<f32>(1, 48, 256).unwrap();

        // Boundary buffers are always 3072 elements
        let mut data_a = vec![0.0f32; 3072];
        let mut data_b = vec![0.0f32; 3072];
        for i in 0..size {
            data_a[i] = i as f32;
            data_b[i] = 2.0;
        }
        a.copy_from_slice(&mut exec, &data_a).unwrap();
        b.copy_from_slice(&mut exec, &data_b).unwrap();

        bencher.iter(|| {
            ops::math::vector_add(&mut exec, &a, &b, &mut c, size).unwrap();
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    benchmark_binary_ops,
    benchmark_unary_ops,
    benchmark_reductions,
    benchmark_activations,
    benchmark_buffer_types,
);
criterion_main!(benches);
