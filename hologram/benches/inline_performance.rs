use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use hologram_core::{ops, Executor};

fn benchmark_vector_add_inline(c: &mut Criterion) {
    let mut group = c.benchmark_group("vector_add_inline");

    for size in [100, 1_000, 3_072, 10_000, 100_000, 1_000_000].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &n| {
            let mut exec = Executor::new().unwrap();
            let mut a = exec.allocate::<f32>(n).unwrap();
            let mut b_buffer = exec.allocate::<f32>(n).unwrap();
            let mut c = exec.allocate::<f32>(n).unwrap();

            // Pre-fill with test data
            let data_a: Vec<f32> = (0..n).map(|i| i as f32).collect();
            let data_b: Vec<f32> = (0..n).map(|i| (i as f32) * 2.0).collect();
            a.copy_from_slice(&mut exec, &data_a).unwrap();
            b_buffer.copy_from_slice(&mut exec, &data_b).unwrap();

            b.iter(|| {
                // This should use inline kernel for f32
                ops::math::vector_add(&mut exec, &a, &b_buffer, &mut c, n).unwrap();
                black_box(c.len());
            });
        });
    }

    group.finish();
}

criterion_group!(benches, benchmark_vector_add_inline);
criterion_main!(benches);
