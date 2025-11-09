//! Benchmarks for ops::math operations
//!
//! Measures performance of mathematical operations (add, sub, mul, div, etc.)
//! Tests both PhiCoordinate (cache-resident) and BufferOffset (DRAM) addressing

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use hologram_core::{ops, Executor};

/// Calculate width (pages) and height (bytes/page) for boundary pool allocation
/// size = number of elements, element_size = sizeof(T)
/// Returns (width, height) where width × height >= size × element_size
fn calc_boundary_dims(size: usize, element_size: usize) -> (usize, usize) {
    let size_bytes = size * element_size;
    let height = 256; // Fixed: bytes per page
    let width = (size_bytes + height - 1) / height; // Round up to pages
    (width, height)
}

/// PhiCoordinate benchmarks (cache-resident) - uses boundary pool
fn benchmark_binary_ops_phi(c: &mut Criterion) {
    let mut group = c.benchmark_group("math_binary_ops_phi");

    // Only test sizes that fit in boundary pool (12,288 bytes per class)
    // f32 = 4 bytes, so max 3,072 elements per class
    for size in [256, 1024, 3072].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        // Vector Add (PhiCoordinate)
        group.bench_with_input(BenchmarkId::new("vector_add", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let (w, h) = calc_boundary_dims(size, 4); // f32 = 4 bytes

            // Allocate from boundary pool for PhiCoordinate addressing
            let a = exec.allocate_boundary::<f32>(0, w, h).unwrap();
            let b = exec.allocate_boundary::<f32>(1, w, h).unwrap();
            let mut c = exec.allocate_boundary::<f32>(2, w, h).unwrap();

            bencher.iter(|| {
                ops::math::vector_add(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // Vector Sub (PhiCoordinate)
        group.bench_with_input(BenchmarkId::new("vector_sub", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let (w, h) = calc_boundary_dims(size, 4);
            let a = exec.allocate_boundary::<f32>(0, w, h).unwrap();
            let b = exec.allocate_boundary::<f32>(1, w, h).unwrap();
            let mut c = exec.allocate_boundary::<f32>(2, w, h).unwrap();

            bencher.iter(|| {
                ops::math::vector_sub(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // Vector Mul (PhiCoordinate)
        group.bench_with_input(BenchmarkId::new("vector_mul", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let (w, h) = calc_boundary_dims(size, 4);
            let a = exec.allocate_boundary::<f32>(0, w, h).unwrap();
            let b = exec.allocate_boundary::<f32>(1, w, h).unwrap();
            let mut c = exec.allocate_boundary::<f32>(2, w, h).unwrap();

            bencher.iter(|| {
                ops::math::vector_mul(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // Vector Div (PhiCoordinate)
        group.bench_with_input(BenchmarkId::new("vector_div", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let (w, h) = calc_boundary_dims(size, 4);
            let a = exec.allocate_boundary::<f32>(0, w, h).unwrap();
            let b = exec.allocate_boundary::<f32>(1, w, h).unwrap();
            let mut c = exec.allocate_boundary::<f32>(2, w, h).unwrap();

            bencher.iter(|| {
                ops::math::vector_div(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // Min (PhiCoordinate)
        group.bench_with_input(BenchmarkId::new("min", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let (w, h) = calc_boundary_dims(size, 4);
            let a = exec.allocate_boundary::<f32>(0, w, h).unwrap();
            let b = exec.allocate_boundary::<f32>(1, w, h).unwrap();
            let mut c = exec.allocate_boundary::<f32>(2, w, h).unwrap();

            bencher.iter(|| {
                ops::math::min(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // Max (PhiCoordinate)
        group.bench_with_input(BenchmarkId::new("max", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let (w, h) = calc_boundary_dims(size, 4);
            let a = exec.allocate_boundary::<f32>(0, w, h).unwrap();
            let b = exec.allocate_boundary::<f32>(1, w, h).unwrap();
            let mut c = exec.allocate_boundary::<f32>(2, w, h).unwrap();

            bencher.iter(|| {
                ops::math::max(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });
    }

    group.finish();
}

/// BufferOffset benchmarks (DRAM) - uses regular allocate()
fn benchmark_binary_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("math_binary_ops");

    for size in [256, 1024, 4096, 16384].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        // Vector Add
        group.bench_with_input(BenchmarkId::new("vector_add", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let b = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::vector_add(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // Vector Sub
        group.bench_with_input(BenchmarkId::new("vector_sub", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let b = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::vector_sub(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // Vector Mul
        group.bench_with_input(BenchmarkId::new("vector_mul", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let b = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::vector_mul(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // Vector Div
        group.bench_with_input(BenchmarkId::new("vector_div", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let b = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::vector_div(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // Min
        group.bench_with_input(BenchmarkId::new("min", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let b = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::min(&mut exec, &a, &b, &mut c, size).unwrap();
            });
        });

        // Max
        group.bench_with_input(BenchmarkId::new("max", size), size, |bencher, &size| {
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

fn benchmark_unary_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("math_unary_ops");

    for size in [256, 1024, 4096, 16384].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        // Abs
        group.bench_with_input(BenchmarkId::new("abs", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(size).unwrap();
            let mut output = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::abs(&mut exec, &input, &mut output, size).unwrap();
            });
        });

        // Neg
        group.bench_with_input(BenchmarkId::new("neg", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(size).unwrap();
            let mut output = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::neg(&mut exec, &input, &mut output, size).unwrap();
            });
        });

        // ReLU
        group.bench_with_input(BenchmarkId::new("relu", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(size).unwrap();
            let mut output = exec.allocate::<f32>(size).unwrap();

            bencher.iter(|| {
                ops::math::relu(&mut exec, &input, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

fn benchmark_scalar_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("math_scalar_ops");

    for size in [256, 1024, 4096, 16384].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        // Scalar Add
        group.bench_with_input(BenchmarkId::new("scalar_add", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();
            let scalar = 2.5f32;

            bencher.iter(|| {
                ops::math::scalar_add(&mut exec, &a, &mut c, black_box(scalar), size).unwrap();
            });
        });

        // Scalar Mul
        group.bench_with_input(BenchmarkId::new("scalar_mul", size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();
            let a = exec.allocate::<f32>(size).unwrap();
            let mut c = exec.allocate::<f32>(size).unwrap();
            let scalar = 2.5f32;

            bencher.iter(|| {
                ops::math::scalar_mul(&mut exec, &a, &mut c, black_box(scalar), size).unwrap();
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    benchmark_binary_ops_phi, // PhiCoordinate (cache-resident)
    benchmark_binary_ops,     // BufferOffset (DRAM)
    benchmark_unary_ops,
    benchmark_scalar_ops
);
criterion_main!(benches);
