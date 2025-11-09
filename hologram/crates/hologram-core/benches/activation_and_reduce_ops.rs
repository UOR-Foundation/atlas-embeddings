//! Benchmarks for activation and reduction operations with Phase 4 optimizations

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use hologram_core::{
    ops::{activation, math, reduce},
    Executor,
};

/// Benchmark ReLU activation for various sizes
fn bench_relu(c: &mut Criterion) {
    let mut group = c.benchmark_group("relu");

    let sizes = vec![256, 1024, 8192, 32768, 131072];

    for n in sizes {
        group.throughput(Throughput::Elements(n as u64));

        group.bench_with_input(BenchmarkId::new("f32", n), &n, |bencher, &n| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(n).unwrap();
            let mut output = exec.allocate::<f32>(n).unwrap();

            bencher.iter(|| {
                math::relu(&mut exec, &input, &mut output, n).unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark softmax activation for various sizes
fn bench_softmax(c: &mut Criterion) {
    let mut group = c.benchmark_group("softmax");

    let sizes = vec![10, 64, 256, 1024, 4096];

    for n in sizes {
        group.throughput(Throughput::Elements(n as u64));

        group.bench_with_input(BenchmarkId::new("f32", n), &n, |bencher, &n| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(n).unwrap();
            let mut output = exec.allocate::<f32>(n).unwrap();

            bencher.iter(|| {
                activation::softmax(&mut exec, &input, &mut output, n).unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark sum reduction for various sizes
fn bench_reduce_sum(c: &mut Criterion) {
    let mut group = c.benchmark_group("reduce_sum");

    let sizes = vec![256, 1024, 8192, 32768, 131072];

    for n in sizes {
        group.throughput(Throughput::Elements(n as u64));

        group.bench_with_input(BenchmarkId::new("f32", n), &n, |bencher, &n| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(n).unwrap();
            let mut output = exec.allocate::<f32>(3).unwrap(); // Need 3 elements for reduce

            bencher.iter(|| {
                reduce::sum(&mut exec, &input, &mut output, n).unwrap();
            });
        });
    }

    group.finish();
}

criterion_group!(benches, bench_relu, bench_softmax, bench_reduce_sum);
criterion_main!(benches);
