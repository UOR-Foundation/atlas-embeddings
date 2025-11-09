//! Generator Microbenchmarks
//!
//! Measures performance of individual generators and Sigmatics operations.
//! Simplified to match existing benchmark patterns.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use hologram_core::{ops, Executor};

/// Benchmark vector_add (merge generator)
fn benchmark_vector_add(c: &mut Criterion) {
    let mut group = c.benchmark_group("generator_add");

    // Note: operations work on boundary buffers (3072 f32 elements per class)
    for size in [1024, 2048, 3072].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();

            // Allocate boundary buffers with topology-valid class arrangement
            let mut input_a = exec.allocate_boundary::<f32>(0, 48, 256).unwrap();
            let mut input_b = exec.allocate_boundary::<f32>(2, 48, 256).unwrap();
            let mut output = exec.allocate_boundary::<f32>(1, 48, 256).unwrap();

            // Initialize data (boundary buffers hold 3072 f32 elements)
            let data_a: Vec<f32> = (0..3072).map(|i| i as f32).collect();
            let data_b: Vec<f32> = (0..3072).map(|i| (i as f32) * 2.0).collect();
            input_a.copy_from_slice(&mut exec, &data_a).unwrap();
            input_b.copy_from_slice(&mut exec, &data_b).unwrap();

            bencher.iter(|| {
                ops::math::vector_add(&mut exec, &input_a, &input_b, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark vector_mul (merge generator)
fn benchmark_vector_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("generator_mul");

    for size in [1024, 2048, 3072].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();

            let mut input_a = exec.allocate_boundary::<f32>(0, 48, 256).unwrap();
            let mut input_b = exec.allocate_boundary::<f32>(2, 48, 256).unwrap();
            let mut output = exec.allocate_boundary::<f32>(1, 48, 256).unwrap();

            let data_a: Vec<f32> = (0..3072).map(|i| i as f32).collect();
            let data_b: Vec<f32> = (0..3072).map(|i| (i as f32) * 2.0).collect();
            input_a.copy_from_slice(&mut exec, &data_a).unwrap();
            input_b.copy_from_slice(&mut exec, &data_b).unwrap();

            bencher.iter(|| {
                ops::math::vector_mul(&mut exec, &input_a, &input_b, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark vector_sub (split generator)
fn benchmark_vector_sub(c: &mut Criterion) {
    let mut group = c.benchmark_group("generator_sub");

    for size in [1024, 2048, 3072].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();

            // Sub uses split generator: a → c, need them as neighbors
            let mut input_a = exec.allocate_boundary::<f32>(3, 48, 256).unwrap();
            let mut input_b = exec.allocate_boundary::<f32>(5, 48, 256).unwrap();
            let mut output = exec.allocate_boundary::<f32>(4, 48, 256).unwrap();

            let data_a: Vec<f32> = (0..3072).map(|i| i as f32).collect();
            let data_b: Vec<f32> = (0..3072).map(|i| (i as f32) * 2.0).collect();
            input_a.copy_from_slice(&mut exec, &data_a).unwrap();
            input_b.copy_from_slice(&mut exec, &data_b).unwrap();

            bencher.iter(|| {
                ops::math::vector_sub(&mut exec, &input_a, &input_b, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark vector_div (split generator)
fn benchmark_vector_div(c: &mut Criterion) {
    let mut group = c.benchmark_group("generator_div");

    for size in [1024, 2048, 3072].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();

            let mut input_a = exec.allocate_boundary::<f32>(6, 48, 256).unwrap();
            let mut input_b = exec.allocate_boundary::<f32>(8, 48, 256).unwrap();
            let mut output = exec.allocate_boundary::<f32>(7, 48, 256).unwrap();

            let data_a: Vec<f32> = (0..3072).map(|i| i as f32 + 1.0).collect();
            let data_b: Vec<f32> = (0..3072).map(|i| (i as f32) * 2.0 + 1.0).collect();
            input_a.copy_from_slice(&mut exec, &data_a).unwrap();
            input_b.copy_from_slice(&mut exec, &data_b).unwrap();

            bencher.iter(|| {
                ops::math::vector_div(&mut exec, &input_a, &input_b, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark relu
fn benchmark_vector_relu(c: &mut Criterion) {
    let mut group = c.benchmark_group("generator_relu");

    for size in [1024, 2048, 3072].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();

            let mut input = exec.allocate_boundary::<f32>(9, 48, 256).unwrap();
            let mut output = exec.allocate_boundary::<f32>(10, 48, 256).unwrap();

            let data: Vec<f32> = (0..3072).map(|i| i as f32 - 1536.0).collect();
            input.copy_from_slice(&mut exec, &data).unwrap();

            bencher.iter(|| {
                ops::math::relu(&mut exec, &input, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark reduce sum
fn benchmark_reduce_sum(c: &mut Criterion) {
    let mut group = c.benchmark_group("generator_reduce_sum");

    for size in [1024, 2048, 3072].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &_size| {
            let mut exec = Executor::new().unwrap();

            let mut input = exec.allocate_boundary::<f32>(11, 48, 256).unwrap();
            let mut output = exec.allocate_boundary::<f32>(12, 48, 256).unwrap();

            let data: Vec<f32> = (0..3072).map(|i| i as f32).collect();
            input.copy_from_slice(&mut exec, &data).unwrap();

            bencher.iter(|| {
                ops::reduce::sum(&mut exec, &input, &mut output, 3072).unwrap();
            });
        });
    }

    group.finish();
}

criterion_group!(
    generator_benches,
    benchmark_vector_add,
    benchmark_vector_mul,
    benchmark_vector_sub,
    benchmark_vector_div,
    benchmark_vector_relu,
    benchmark_reduce_sum
);

criterion_main!(generator_benches);
