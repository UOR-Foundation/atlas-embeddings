//! Operation Chain Macrobenchmarks
//!
//! Measures performance of typical operation sequences to track
//! fusion optimization and whole-program optimization impact.
//!
//! These benchmarks form the foundation for Phase A.1.1 (macrobenchmarks)
//! and will be used to verify Phase B.2 (fusion) and Phase D.3 (whole-program fusion).

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use hologram_core::{ops, Executor};

/// Benchmark: add + mul chain (FMA pattern)
/// This is a prime candidate for fusion optimization
fn benchmark_add_mul_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("chain_add_mul");

    for size in [1024, 4096, 12288].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();

            // Input buffers
            let mut a = exec.allocate_boundary::<f32>(0, 48, 256).unwrap();
            let mut b = exec.allocate_boundary::<f32>(2, 48, 256).unwrap();
            let mut x = exec.allocate_boundary::<f32>(3, 48, 256).unwrap();

            // Intermediate and output
            let mut temp = exec.allocate_boundary::<f32>(1, 48, 256).unwrap();
            let mut output = exec.allocate_boundary::<f32>(4, 48, 256).unwrap();

            // Initialize data
            let data_a: Vec<f32> = (0..3072).map(|i| i as f32).collect();
            let data_b: Vec<f32> = (0..3072).map(|_i| 2.0).collect();
            let data_x: Vec<f32> = (0..3072).map(|_i| 3.0).collect();

            a.copy_from_slice(&mut exec, &data_a).unwrap();
            b.copy_from_slice(&mut exec, &data_b).unwrap();
            x.copy_from_slice(&mut exec, &data_x).unwrap();

            bencher.iter(|| {
                // temp = a + b
                ops::math::vector_add(&mut exec, &a, &b, &mut temp, size).unwrap();
                // output = temp * x = (a + b) * x
                ops::math::vector_mul(&mut exec, &temp, &x, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark: add + relu chain (common in neural networks)
/// This is a fusion candidate: fused_add_relu
fn benchmark_add_relu_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("chain_add_relu");

    for size in [1024, 4096, 12288].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();

            let mut a = exec.allocate_boundary::<f32>(0, 48, 256).unwrap();
            let mut bias = exec.allocate_boundary::<f32>(2, 48, 256).unwrap();
            let mut temp = exec.allocate_boundary::<f32>(1, 48, 256).unwrap();
            let mut output = exec.allocate_boundary::<f32>(3, 48, 256).unwrap();

            let data_a: Vec<f32> = (0..3072).map(|i| (i as f32 - 1536.0) / 100.0).collect();
            let data_bias: Vec<f32> = (0..3072).map(|_i| 0.5).collect();

            a.copy_from_slice(&mut exec, &data_a).unwrap();
            bias.copy_from_slice(&mut exec, &data_bias).unwrap();

            bencher.iter(|| {
                // temp = a + bias
                ops::math::vector_add(&mut exec, &a, &bias, &mut temp, size).unwrap();
                // output = relu(temp)
                ops::math::relu(&mut exec, &temp, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark: Neural network layer (matmul + add + relu)
/// This represents a complete dense layer forward pass
fn benchmark_dense_layer(c: &mut Criterion) {
    let mut group = c.benchmark_group("chain_dense_layer");

    // Use smaller sizes since this is more expensive
    for size in [1024, 4096].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();

            let mut input = exec.allocate_boundary::<f32>(0, 48, 256).unwrap();
            let mut bias = exec.allocate_boundary::<f32>(2, 48, 256).unwrap();
            let mut multiplier = exec.allocate_boundary::<f32>(4, 48, 256).unwrap();
            let mut temp1 = exec.allocate_boundary::<f32>(1, 48, 256).unwrap();
            let mut temp2 = exec.allocate_boundary::<f32>(5, 48, 256).unwrap();
            let mut output = exec.allocate_boundary::<f32>(3, 48, 256).unwrap();

            let data_input: Vec<f32> = (0..3072).map(|i| (i as f32 - 1536.0) / 100.0).collect();
            let data_bias: Vec<f32> = (0..3072).map(|_i| 0.1).collect();
            let data_mult: Vec<f32> = vec![2.0; 3072];

            input.copy_from_slice(&mut exec, &data_input).unwrap();
            bias.copy_from_slice(&mut exec, &data_bias).unwrap();
            multiplier.copy_from_slice(&mut exec, &data_mult).unwrap();

            bencher.iter(|| {
                // In real impl would do matmul, here we simulate with mul
                // temp1 = input * multiplier (simulating matmul output)
                ops::math::vector_mul(&mut exec, &input, &multiplier, &mut temp1, size).unwrap();

                // temp2 = temp1 + bias
                ops::math::vector_add(&mut exec, &temp1, &bias, &mut temp2, size).unwrap();

                // output = relu(temp2)
                ops::math::relu(&mut exec, &temp2, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark: Reduction pipeline (abs + sum)
/// Common pattern in loss functions
fn benchmark_reduction_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("chain_reduction_pipeline");

    for size in [1024, 4096, 12288].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();

            let mut input = exec.allocate_boundary::<f32>(0, 48, 256).unwrap();
            let mut temp = exec.allocate_boundary::<f32>(1, 48, 256).unwrap();
            let mut output = exec.allocate_boundary::<f32>(2, 48, 256).unwrap();

            let data: Vec<f32> = (0..3072).map(|i| (i as f32 - 1536.0) / 100.0).collect();
            input.copy_from_slice(&mut exec, &data).unwrap();

            bencher.iter(|| {
                // temp = abs(input)
                ops::math::abs(&mut exec, &input, &mut temp, size).unwrap();
                // output = sum(temp)
                ops::reduce::sum(&mut exec, &temp, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark: Long chain (5 operations)
/// Tests cross-operation fusion and whole-program optimization
fn benchmark_long_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("chain_long_5ops");

    for size in [1024, 4096].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
            let mut exec = Executor::new().unwrap();

            let mut input = exec.allocate_boundary::<f32>(0, 48, 256).unwrap();
            let mut const2 = exec.allocate_boundary::<f32>(6, 48, 256).unwrap();
            let mut const1 = exec.allocate_boundary::<f32>(7, 48, 256).unwrap();
            let mut const05 = exec.allocate_boundary::<f32>(8, 48, 256).unwrap();
            let mut temp1 = exec.allocate_boundary::<f32>(1, 48, 256).unwrap();
            let mut temp2 = exec.allocate_boundary::<f32>(2, 48, 256).unwrap();
            let mut temp3 = exec.allocate_boundary::<f32>(3, 48, 256).unwrap();
            let mut temp4 = exec.allocate_boundary::<f32>(4, 48, 256).unwrap();
            let mut output = exec.allocate_boundary::<f32>(5, 48, 256).unwrap();

            let data: Vec<f32> = (0..3072).map(|i| i as f32 + 1.0).collect();
            let c2 = vec![2.0; 3072];
            let c1 = vec![1.0; 3072];
            let c05 = vec![0.5; 3072];

            input.copy_from_slice(&mut exec, &data).unwrap();
            const2.copy_from_slice(&mut exec, &c2).unwrap();
            const1.copy_from_slice(&mut exec, &c1).unwrap();
            const05.copy_from_slice(&mut exec, &c05).unwrap();

            bencher.iter(|| {
                // Chain: mul → add → abs → mul → relu
                ops::math::vector_mul(&mut exec, &input, &const2, &mut temp1, size).unwrap();
                ops::math::vector_add(&mut exec, &temp1, &const1, &mut temp2, size).unwrap();
                ops::math::abs(&mut exec, &temp2, &mut temp3, size).unwrap();
                ops::math::vector_mul(&mut exec, &temp3, &const05, &mut temp4, size).unwrap();
                ops::math::relu(&mut exec, &temp4, &mut output, size).unwrap();
            });
        });
    }

    group.finish();
}

/// Benchmark: Native CPU baseline for comparison
fn benchmark_native_chain_add_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("native_chain_add_mul");

    for size in [1024, 4096, 12288].iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |bencher, &size| {
            let a = vec![1.0f32; size];
            let b = vec![2.0f32; size];
            let x = vec![3.0f32; size];
            let mut output = vec![0.0f32; size];

            bencher.iter(|| {
                for i in 0..size {
                    let temp = black_box(a[i]) + black_box(b[i]);
                    output[i] = temp * black_box(x[i]);
                }
                black_box(&output);
            });
        });
    }

    group.finish();
}

criterion_group!(
    operation_chain_benches,
    benchmark_add_mul_chain,
    benchmark_add_relu_chain,
    benchmark_dense_layer,
    benchmark_reduction_pipeline,
    benchmark_long_chain,
    benchmark_native_chain_add_mul
);

criterion_main!(operation_chain_benches);
