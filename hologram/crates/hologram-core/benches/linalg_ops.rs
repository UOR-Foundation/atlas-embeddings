//! Benchmarks for linear algebra operations (GEMM, matvec)

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use hologram_core::{ops::linalg, Executor};

/// Benchmark GEMM (matrix multiplication) for various sizes
fn bench_gemm(c: &mut Criterion) {
    let mut group = c.benchmark_group("gemm");

    // Test various matrix sizes
    let sizes = vec![
        (16, 16, 16),    // Tiny
        (32, 512, 256),  // Performance example size (Layer 1)
        (64, 64, 64),    // Small
        (128, 128, 128), // Medium
        (256, 256, 256), // Large
    ];

    for (m, k, n) in sizes {
        let flops = 2 * m * k * n;
        group.throughput(Throughput::Elements(flops as u64));

        group.bench_with_input(
            BenchmarkId::new("f32", format!("{}x{}x{}", m, k, n)),
            &(m, k, n),
            |bencher, &(m, k, n)| {
                let mut exec = Executor::new().unwrap();
                let a = exec.allocate::<f32>(m * k).unwrap();
                let b = exec.allocate::<f32>(k * n).unwrap();
                let mut c = exec.allocate::<f32>(m * n).unwrap();

                bencher.iter(|| {
                    linalg::gemm(&mut exec, &a, &b, &mut c, m, k, n).unwrap();
                });
            },
        );
    }

    group.finish();
}

/// Benchmark matrix-vector multiply for various sizes
fn bench_matvec(c: &mut Criterion) {
    let mut group = c.benchmark_group("matvec");

    // Test various sizes
    let sizes = vec![
        (16, 16),    // Tiny
        (128, 128),  // Small
        (256, 512),  // Medium
        (512, 1024), // Large
    ];

    for (m, n) in sizes {
        let flops = 2 * m * n;
        group.throughput(Throughput::Elements(flops as u64));

        group.bench_with_input(
            BenchmarkId::new("f32", format!("{}x{}", m, n)),
            &(m, n),
            |bencher, &(m, n)| {
                let mut exec = Executor::new().unwrap();
                let a = exec.allocate::<f32>(m * n).unwrap();
                let x = exec.allocate::<f32>(n).unwrap();
                let mut y = exec.allocate::<f32>(m).unwrap();

                bencher.iter(|| {
                    linalg::matvec(&mut exec, &a, &x, &mut y, m, n).unwrap();
                });
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_gemm, bench_matvec);
criterion_main!(benches);
