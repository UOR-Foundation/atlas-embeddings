//! Benchmarks for ops::reduce operations
//!
//! Measures performance of reduction operations (sum, min, max)
//! Compares performance across different input sizes to observe
//! sequential vs parallel reduction behavior.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use hologram_core::{ops, Executor};

fn benchmark_reduce_sum(c: &mut Criterion) {
    let mut group = c.benchmark_group("reduce_sum");

    // Test sizes: small (fits in single REDUCE), medium, large (requires tree reduction)
    for size in [64, 128, 256, 512, 1024, 4096, 16384].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(size).unwrap();
            let mut output = exec.allocate::<f32>(3).unwrap(); // Needs 3 elements

            b.iter(|| {
                ops::reduce::sum(&mut exec, &input, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

fn benchmark_reduce_min(c: &mut Criterion) {
    let mut group = c.benchmark_group("reduce_min");

    for size in [64, 128, 256, 512, 1024, 4096, 16384].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(size).unwrap();
            let mut output = exec.allocate::<f32>(3).unwrap();

            b.iter(|| {
                ops::reduce::min(&mut exec, &input, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

fn benchmark_reduce_max(c: &mut Criterion) {
    let mut group = c.benchmark_group("reduce_max");

    for size in [64, 128, 256, 512, 1024, 4096, 16384].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(size).unwrap();
            let mut output = exec.allocate::<f32>(3).unwrap();

            b.iter(|| {
                ops::reduce::max(&mut exec, &input, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

fn benchmark_parallel_threshold(c: &mut Criterion) {
    let mut group = c.benchmark_group("reduce_parallel_threshold");

    // Test around the CHUNK_SIZE = 128 threshold
    // Sizes below 128 use single-pass reduction
    // Sizes above 128 use multi-pass tree reduction
    for size in [100, 128, 150, 200, 256].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::new("sum", size), size, |b, &size| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(size).unwrap();
            let mut output = exec.allocate::<f32>(3).unwrap();

            b.iter(|| {
                ops::reduce::sum(&mut exec, &input, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    benchmark_reduce_sum,
    benchmark_reduce_min,
    benchmark_reduce_max,
    benchmark_parallel_threshold
);
criterion_main!(benches);
