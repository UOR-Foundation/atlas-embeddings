//! Comprehensive kernel benchmark suite
//!
//! Benchmarks all kernel functions including:
//! - Vector operations (add, mul, sub) with SIMD
//! - Matrix operations (gemv, gemm)
//! - Activation functions (sigmoid, tanh, gelu, softmax)
//! - Quantum search operations

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use hologram_core::kernel::inline;

fn benchmark_vector_add(c: &mut Criterion) {
    let mut group = c.benchmark_group("vector_add");

    for size in [100, 1_000, 3_072, 10_000, 1_000_000] {
        // Native Rust baseline
        group.bench_with_input(BenchmarkId::new("native_rust", size), &size, |b, &n| {
            let data_a: Vec<f32> = (0..n).map(|i| i as f32).collect();
            let data_b: Vec<f32> = (0..n).map(|i| (i as f32) * 2.0).collect();

            b.iter(|| {
                let mut c = vec![0.0f32; n];
                for i in 0..n {
                    c[i] = data_a[i] + data_b[i];
                }
                black_box(c);
            });
        });

        // Inline kernel with SIMD
        group.bench_with_input(BenchmarkId::new("inline_simd", size), &size, |b, &n| {
            let data_a: Vec<f32> = (0..n).map(|i| i as f32).collect();
            let data_b: Vec<f32> = (0..n).map(|i| (i as f32) * 2.0).collect();

            b.iter(|| {
                let mut c = vec![0.0f32; n];
                inline::vector_add(data_a.as_ptr(), data_b.as_ptr(), c.as_mut_ptr(), n);
                black_box(c);
            });
        });
    }

    group.finish();
}

fn benchmark_vector_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("vector_mul");

    for size in [100, 1_000, 3_072, 10_000, 1_000_000] {
        // Native Rust baseline
        group.bench_with_input(BenchmarkId::new("native_rust", size), &size, |b, &n| {
            let data_a: Vec<f32> = (0..n).map(|i| i as f32).collect();
            let data_b: Vec<f32> = (0..n).map(|i| (i as f32) * 2.0).collect();

            b.iter(|| {
                let mut c = vec![0.0f32; n];
                for i in 0..n {
                    c[i] = data_a[i] * data_b[i];
                }
                black_box(c);
            });
        });

        // Inline kernel with SIMD
        group.bench_with_input(BenchmarkId::new("inline_simd", size), &size, |b, &n| {
            let data_a: Vec<f32> = (0..n).map(|i| i as f32).collect();
            let data_b: Vec<f32> = (0..n).map(|i| (i as f32) * 2.0).collect();

            b.iter(|| {
                let mut c = vec![0.0f32; n];
                inline::vector_mul(data_a.as_ptr(), data_b.as_ptr(), c.as_mut_ptr(), n);
                black_box(c);
            });
        });
    }

    group.finish();
}

fn benchmark_vector_sub(c: &mut Criterion) {
    let mut group = c.benchmark_group("vector_sub");

    for size in [100, 1_000, 3_072, 10_000, 1_000_000] {
        // Native Rust baseline
        group.bench_with_input(BenchmarkId::new("native_rust", size), &size, |b, &n| {
            let data_a: Vec<f32> = (0..n).map(|i| i as f32).collect();
            let data_b: Vec<f32> = (0..n).map(|i| (i as f32) * 2.0).collect();

            b.iter(|| {
                let mut c = vec![0.0f32; n];
                for i in 0..n {
                    c[i] = data_a[i] - data_b[i];
                }
                black_box(c);
            });
        });

        // Inline kernel with SIMD
        group.bench_with_input(BenchmarkId::new("inline_simd", size), &size, |b, &n| {
            let data_a: Vec<f32> = (0..n).map(|i| i as f32).collect();
            let data_b: Vec<f32> = (0..n).map(|i| (i as f32) * 2.0).collect();

            b.iter(|| {
                let mut c = vec![0.0f32; n];
                inline::vector_sub(data_a.as_ptr(), data_b.as_ptr(), c.as_mut_ptr(), n);
                black_box(c);
            });
        });
    }

    group.finish();
}

fn benchmark_activation_sigmoid(c: &mut Criterion) {
    let mut group = c.benchmark_group("sigmoid");

    for size in [100, 1_000, 3_072, 10_000, 1_000_000] {
        // Native Rust baseline
        group.bench_with_input(BenchmarkId::new("native_rust", size), &size, |b, &n| {
            let data_a: Vec<f32> = (0..n).map(|i| i as f32).collect();

            b.iter(|| {
                let mut c = vec![0.0f32; n];
                for i in 0..n {
                    c[i] = 1.0 / (1.0 + (-data_a[i]).exp());
                }
                black_box(c);
            });
        });

        // Inline kernel
        group.bench_with_input(BenchmarkId::new("inline", size), &size, |b, &n| {
            let data_a: Vec<f32> = (0..n).map(|i| i as f32).collect();

            b.iter(|| {
                let mut c = vec![0.0f32; n];
                unsafe {
                    inline::sigmoid(data_a.as_ptr(), c.as_mut_ptr(), n);
                }
                black_box(c);
            });
        });
    }

    group.finish();
}

fn benchmark_activation_tanh(c: &mut Criterion) {
    let mut group = c.benchmark_group("tanh");

    for size in [100, 1_000, 3_072, 10_000, 1_000_000] {
        // Native Rust baseline
        group.bench_with_input(BenchmarkId::new("native_rust", size), &size, |b, &n| {
            let data_a: Vec<f32> = (0..n).map(|i| i as f32).collect();

            b.iter(|| {
                let mut c = vec![0.0f32; n];
                for i in 0..n {
                    c[i] = data_a[i].tanh();
                }
                black_box(c);
            });
        });

        // Inline kernel
        group.bench_with_input(BenchmarkId::new("inline", size), &size, |b, &n| {
            let data_a: Vec<f32> = (0..n).map(|i| i as f32).collect();

            b.iter(|| {
                let mut c = vec![0.0f32; n];
                unsafe {
                    inline::tanh(data_a.as_ptr(), c.as_mut_ptr(), n);
                }
                black_box(c);
            });
        });
    }

    group.finish();
}

fn benchmark_matrix_gemv(c: &mut Criterion) {
    let mut group = c.benchmark_group("gemv");

    for size in [32, 64, 128].iter() {
        group.bench_with_input(BenchmarkId::new("inline", size), size, |b, &s| {
            let m = s;
            let n = s;
            let a: Vec<f32> = (0..m * n).map(|i| i as f32).collect();
            let x: Vec<f32> = (0..n).map(|i| i as f32).collect();

            b.iter(|| {
                let mut y = vec![0.0f32; m];
                unsafe {
                    inline::gemv_f32(
                        a.as_ptr(),
                        x.as_ptr(),
                        y.as_mut_ptr(),
                        m,
                        n,
                        n, // lda
                    );
                }
                black_box(y);
            });
        });
    }

    group.finish();
}

fn benchmark_matrix_gemm(c: &mut Criterion) {
    let mut group = c.benchmark_group("gemm");

    for size in [16, 32, 64].iter() {
        group.bench_with_input(BenchmarkId::new("inline", size), size, |b, &s| {
            let m = s;
            let n = s;
            let k = s;
            let a: Vec<f32> = (0..m * k).map(|i| i as f32).collect();
            let b_vec: Vec<f32> = (0..k * n).map(|i| i as f32).collect();

            b.iter(|| {
                let mut c = vec![0.0f32; m * n];
                unsafe {
                    inline::gemm_f32(
                        a.as_ptr(),
                        b_vec.as_ptr(),
                        c.as_mut_ptr(),
                        m,
                        n,
                        k,
                        k, // lda
                        n, // ldb
                        n, // ldc
                    );
                }
                black_box(c);
            });
        });
    }

    group.finish();
}

fn benchmark_quantum_search(c: &mut Criterion) {
    let mut group = c.benchmark_group("quantum_search");

    for size in [100, 1_000, 3_072, 10_000, 1_000_000] {
        // Native linear search baseline
        group.bench_with_input(BenchmarkId::new("native_linear", size), &size, |b, &n| {
            let data: Vec<f32> = (0..n).map(|i| i as f32).collect();
            let target = (n / 2) as f32;

            b.iter(|| {
                let mut results = Vec::new();
                for i in 0..n {
                    if data[i] == target {
                        results.push(i);
                    }
                }
                black_box(results);
            });
        });

        // Quantum search
        group.bench_with_input(BenchmarkId::new("quantum", size), &size, |b, &n| {
            let data: Vec<f32> = (0..n).map(|i| i as f32).collect();
            let target = (n / 2) as f32;

            b.iter(|| {
                let mut results = vec![0.0f32; n];
                let mut total_results = 0usize;
                let max_iterations = (n as f32).sqrt() as usize;
                unsafe {
                    inline::quantum_search(
                        data.as_ptr(),
                        target,
                        results.as_mut_ptr(),
                        &mut total_results,
                        n,
                        max_iterations,
                    );
                }
                black_box((results, total_results));
            });
        });
    }

    group.finish();
}

// Configure Criterion with longer measurement time for large datasets
fn custom_criterion() -> Criterion {
    Criterion::default()
        .measurement_time(std::time::Duration::from_secs(10)) // 10 seconds per sample
        .warm_up_time(std::time::Duration::from_secs(3))
        .sample_size(100) // Keep 100 samples even with larger datasets
}

criterion_group!(
    name = benches;
    config = custom_criterion();
    targets =
        benchmark_vector_add,
        benchmark_vector_mul,
        benchmark_vector_sub,
        benchmark_activation_sigmoid,
        benchmark_activation_tanh,
        benchmark_matrix_gemv,
        benchmark_matrix_gemm,
        benchmark_quantum_search
);
criterion_main!(benches);
