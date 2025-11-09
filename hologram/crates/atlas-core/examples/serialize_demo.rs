//! Example demonstrating serialization of resonance data for CUDA
//!
//! This example shows how to:
//! 1. Create a ResonanceData package with precomputed invariants
//! 2. Serialize to JSON for tooling
//! 3. Serialize to binary for CUDA upload
//! 4. Measure sizes and validate data
//!
//! Run with: cargo run --example serialize_demo

use atlas_core::serialize::*;
use atlas_core::{AtlasClassMask, AtlasPhaseWindow};

fn main() {
    println!("=== Atlas Resonance Data Serialization Demo ===\n");

    // 1. Create base resonance data package
    println!("1. Creating base resonance data...");
    let data = ResonanceData::new();
    println!("   - Mirror pairs: {}", data.mirror_pairs.len());
    println!("   - Unity classes: {}", data.unity_classes.len());
    println!("   - Size: {} bytes\n", data.size_bytes());

    // 2. Serialize to JSON
    println!("2. Serializing to JSON...");
    let json = data.to_json().expect("Failed to serialize to JSON");
    println!("   - JSON size: {} bytes", json.len());
    println!("   - First 200 chars:\n{}\n", &json[..200.min(json.len())]);

    // 3. Serialize to binary
    println!("3. Serializing to binary...");
    let binary = data.to_binary();
    println!("   - Binary size: {} bytes", binary.len());
    println!("   - First 16 bytes: {:02x?}\n", &binary[..16.min(binary.len())]);

    // 4. Roundtrip validation
    println!("4. Validating roundtrip...");
    let from_json = ResonanceData::from_json(&json).expect("Failed to deserialize JSON");
    let from_binary = ResonanceData::from_binary(&binary).expect("Failed to deserialize binary");
    println!("   - JSON roundtrip: {}", if data == from_json { "✓" } else { "✗" });
    println!("   - Binary roundtrip: {}", if data == from_binary { "✓" } else { "✗" });
    println!();

    // 5. Add typical kernel metadata
    println!("5. Adding kernel metadata...");
    let mut kernel_data = ResonanceData::new();

    // Example: kernel uses specific classes
    let mut mask = AtlasClassMask::empty();
    mask.low = (1u64 << 10) | (1u64 << 20) | (1u64 << 30);
    kernel_data.add_class_mask(mask);

    // Example: kernel has phase window constraint
    kernel_data.add_phase_window(AtlasPhaseWindow { begin: 100, span: 200 });

    println!(
        "   - With 1 class mask + 1 phase window: {} bytes",
        kernel_data.size_bytes()
    );

    // 6. Demonstrate typical usage scenario
    println!("\n6. Typical usage scenario:");
    let mut production_data = ResonanceData::new();

    // Add metadata for 5 different kernel configurations
    for i in 0..5 {
        let mut mask = AtlasClassMask::empty();
        mask.low = 1u64 << (i * 10);
        production_data.add_class_mask(mask);

        production_data.add_phase_window(AtlasPhaseWindow {
            begin: i * 150,
            span: 100,
        });
    }

    let prod_binary = production_data.to_binary();
    println!("   - 5 kernels metadata: {} bytes", prod_binary.len());
    println!(
        "   - % of 64KB constant memory: {:.2}%",
        (prod_binary.len() as f64 / (64.0 * 1024.0)) * 100.0
    );

    // 7. Validate data integrity
    println!("\n7. Validating data integrity...");
    match production_data.validate() {
        Ok(_) => println!("   - Validation: ✓"),
        Err(e) => println!("   - Validation error: {}", e),
    }

    // 8. Display mirror pair data
    println!("\n8. Sample mirror pairs (first 5):");
    for (i, pair) in data.mirror_pairs.iter().take(5).enumerate() {
        println!("   - Pair {}: class {} ↔ class {}", i, pair.class_a, pair.class_b);
    }

    // 9. Display unity classes
    println!("\n9. Unity classes:");
    for class_id in &data.unity_classes {
        println!("   - Class {}", class_id);
    }

    // 10. Show packing helpers
    println!("\n10. Using C-compatible packing helpers:");
    let mut mirror_buffer = vec![atlas_core::AtlasMirrorPair::new(0, 0); 48];
    let count = pack_mirror_pairs(&mut mirror_buffer);
    println!("   - Packed {} mirror pairs", count);

    let mut unity_buffer = vec![0u8; 10];
    let unity_count = pack_unity_classes(&mut unity_buffer);
    println!("   - Packed {} unity classes", unity_count);

    println!("\n=== Demo Complete ===");
}
