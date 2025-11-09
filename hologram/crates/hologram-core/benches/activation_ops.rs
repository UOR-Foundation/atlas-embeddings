//! Benchmarks for ops::activation operations
//!
//! Measures performance of neural network activation functions
//! (sigmoid, tanh, gelu, softmax)

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use hologram_core::{ops, Executor};

fn benchmark_sigmoid(c: &mut Criterion) {
    let mut group = c.benchmark_group("activation_sigmoid");

    for size in [256, 1024, 4096, 16384].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(size).unwrap();
            let mut output = exec.allocate::<f32>(size).unwrap();

            b.iter(|| {
                ops::activation::sigmoid(&mut exec, &input, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

fn benchmark_tanh(c: &mut Criterion) {
    let mut group = c.benchmark_group("activation_tanh");

    for size in [256, 1024, 4096, 16384].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(size).unwrap();
            let mut output = exec.allocate::<f32>(size).unwrap();

            b.iter(|| {
                ops::activation::tanh(&mut exec, &input, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

fn benchmark_gelu(c: &mut Criterion) {
    let mut group = c.benchmark_group("activation_gelu");

    for size in [256, 1024, 4096, 16384].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(size).unwrap();
            let mut output = exec.allocate::<f32>(size).unwrap();

            b.iter(|| {
                ops::activation::gelu(&mut exec, &input, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

fn benchmark_softmax(c: &mut Criterion) {
    let mut group = c.benchmark_group("activation_softmax");

    // Softmax uses reduction, so test sizes around the reduction threshold
    for size in [64, 128, 256, 512, 1024, 2048].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let mut exec = Executor::new().unwrap();
            let input = exec.allocate::<f32>(size).unwrap();
            let mut output = exec.allocate::<f32>(size).unwrap();

            b.iter(|| {
                ops::activation::softmax(&mut exec, &input, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

fn benchmark_activation_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("activation_comparison");
    let size = 1024;
    group.throughput(Throughput::Elements(size as u64));

    let mut exec = Executor::new().unwrap();
    let input = exec.allocate::<f32>(size).unwrap();
    let mut output = exec.allocate::<f32>(size).unwrap();

    group.bench_function("sigmoid", |b| {
        b.iter(|| {
            ops::activation::sigmoid(&mut exec, &input, &mut output, size).unwrap();
        });
    });

    group.bench_function("tanh", |b| {
        b.iter(|| {
            ops::activation::tanh(&mut exec, &input, &mut output, size).unwrap();
        });
    });

    group.bench_function("gelu", |b| {
        b.iter(|| {
            ops::activation::gelu(&mut exec, &input, &mut output, size).unwrap();
        });
    });

    group.bench_function("softmax", |b| {
        b.iter(|| {
            ops::activation::softmax(&mut exec, &input, &mut output, size).unwrap();
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    benchmark_sigmoid,
    benchmark_tanh,
    benchmark_gelu,
    benchmark_softmax,
    benchmark_activation_comparison
);
criterion_main!(benches);
