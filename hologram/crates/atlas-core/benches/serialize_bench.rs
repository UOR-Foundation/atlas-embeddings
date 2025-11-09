//! Benchmark for resonance data serialization
//!
//! This benchmark measures the size and performance of serializing
//! resonance metadata for CUDA consumption.

use atlas_core::serialize::*;
use atlas_core::{AtlasClassMask, AtlasPhaseWindow};
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_serialization(c: &mut Criterion) {
    let data = ResonanceData::new();

    c.bench_function("to_json", |b| {
        b.iter(|| {
            let json = data.to_json().unwrap();
            black_box(json);
        })
    });

    c.bench_function("to_binary", |b| {
        b.iter(|| {
            let binary = data.to_binary();
            black_box(binary);
        })
    });

    let json = data.to_json().unwrap();
    c.bench_function("from_json", |b| {
        b.iter(|| {
            let restored = ResonanceData::from_json(black_box(&json)).unwrap();
            black_box(restored);
        })
    });

    let binary = data.to_binary();
    c.bench_function("from_binary", |b| {
        b.iter(|| {
            let restored = ResonanceData::from_binary(black_box(&binary)).unwrap();
            black_box(restored);
        })
    });
}

fn benchmark_with_additional_data(c: &mut Criterion) {
    let mut data = ResonanceData::new();

    // Add typical kernel metadata
    for _ in 0..10 {
        data.add_class_mask(AtlasClassMask::empty());
        data.add_phase_window(AtlasPhaseWindow { begin: 0, span: 100 });
    }

    c.bench_function("to_binary_with_metadata", |b| {
        b.iter(|| {
            let binary = data.to_binary();
            black_box(binary);
        })
    });

    let binary = data.to_binary();
    c.bench_function("from_binary_with_metadata", |b| {
        b.iter(|| {
            let restored = ResonanceData::from_binary(black_box(&binary)).unwrap();
            black_box(restored);
        })
    });
}

fn measure_sizes(_c: &mut Criterion) {
    // This is a measurement function, not a performance benchmark
    let data = ResonanceData::new();

    let json = data.to_json().unwrap();
    let binary = data.to_binary();

    println!("\n=== Serialization Size Measurements ===");
    println!("Base data (48 mirror pairs + 2 unity classes):");
    println!("  JSON:   {} bytes", json.len());
    println!("  Binary: {} bytes", binary.len());
    println!("  Computed size: {} bytes", data.size_bytes());

    // Test with typical kernel metadata
    let mut data_with_meta = ResonanceData::new();
    for _ in 0..10 {
        data_with_meta.add_class_mask(AtlasClassMask::empty());
        data_with_meta.add_phase_window(AtlasPhaseWindow { begin: 0, span: 100 });
    }

    let json_with_meta = data_with_meta.to_json().unwrap();
    let binary_with_meta = data_with_meta.to_binary();

    println!("\nWith 10 class masks + 10 phase windows:");
    println!("  JSON:   {} bytes", json_with_meta.len());
    println!("  Binary: {} bytes", binary_with_meta.len());
    println!("  Computed size: {} bytes", data_with_meta.size_bytes());

    // Test with maximum reasonable data
    let mut data_max = ResonanceData::new();
    for i in 0..100 {
        data_max.add_class_mask(AtlasClassMask::all());
        data_max.add_phase_window(AtlasPhaseWindow { begin: i, span: 10 });
    }

    let binary_max = data_max.to_binary();
    println!("\nWith 100 class masks + 100 phase windows:");
    println!("  Binary: {} bytes", binary_max.len());
    println!("  Computed size: {} bytes", data_max.size_bytes());
    println!(
        "  % of 64KB constant memory: {:.1}%",
        (binary_max.len() as f64 / (64.0 * 1024.0)) * 100.0
    );

    assert!(
        binary_max.len() < 64 * 1024,
        "Serialized data exceeds 64KB CUDA constant memory limit!"
    );
}

criterion_group!(
    benches,
    benchmark_serialization,
    benchmark_with_additional_data,
    measure_sizes
);
criterion_main!(benches);
