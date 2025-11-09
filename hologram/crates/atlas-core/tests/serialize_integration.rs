//! Integration tests for resonance data serialization
//!
//! These tests verify that serialized resonance data maintains stability
//! across releases and is suitable for CUDA consumption.

use atlas_core::serialize::*;
use atlas_core::{AtlasClassMask, AtlasMirrorPair, AtlasPhaseWindow};

#[test]
fn test_serialization_format_stability() {
    // This test ensures that the binary format remains stable
    // Changes to the format should trigger a test failure
    let data = ResonanceData::new();
    let binary = data.to_binary();

    // Check header: mirror pair count should be first 4 bytes (48 pairs = 0x30)
    assert_eq!(&binary[0..4], &[48, 0, 0, 0]);

    // After 48 pairs (2 bytes each = 96 bytes), we should have unity count
    assert_eq!(&binary[100..104], &[2, 0, 0, 0]);

    // Verify total size: base format now includes validation presence flag (4 bytes)
    // Mirror pairs: 4 + 96 = 100
    // Unity classes: 4 + 2 = 6
    // Class masks: 4 + 0 = 4
    // Phase windows: 4 + 0 = 4
    // Validation flag: 4 (present=0)
    // Total: 118 bytes
    assert_eq!(binary.len(), 118);
}

#[test]
fn test_cross_format_consistency() {
    // Verify JSON and binary formats represent the same data
    let mut data = ResonanceData::new();
    data.add_class_mask(AtlasClassMask::all());
    data.add_phase_window(AtlasPhaseWindow { begin: 100, span: 50 });

    let json = data.to_json().unwrap();
    let binary = data.to_binary();

    let from_json = ResonanceData::from_json(&json).unwrap();
    let from_binary = ResonanceData::from_binary(&binary).unwrap();

    assert_eq!(from_json, from_binary);
    assert_eq!(from_json, data);
}

#[test]
fn test_cuda_memory_constraints() {
    // Verify that reasonable configurations fit in CUDA constant memory
    const CUDA_CONSTANT_MEMORY: usize = 64 * 1024; // 64KB typical limit

    // Test various realistic scenarios
    let scenarios = [
        ("minimal", 0, 0),
        ("single_kernel", 1, 1),
        ("small_app", 10, 10),
        ("medium_app", 50, 50),
        ("large_app", 100, 100),
    ];

    for (name, num_masks, num_windows) in scenarios {
        let mut data = ResonanceData::new();
        for _ in 0..num_masks {
            data.add_class_mask(AtlasClassMask::all());
        }
        for i in 0..num_windows {
            data.add_phase_window(AtlasPhaseWindow {
                begin: (i * 10) % 768,
                span: 50,
            });
        }

        let size = data.size_bytes();
        let percentage = (size as f64 / CUDA_CONSTANT_MEMORY as f64) * 100.0;

        println!("{}: {} bytes ({:.2}% of constant memory)", name, size, percentage);

        assert!(
            size < CUDA_CONSTANT_MEMORY,
            "Scenario '{}' exceeds CUDA constant memory: {} bytes",
            name,
            size
        );
    }
}

#[test]
fn test_mirror_pairs_completeness() {
    // Verify all 96 classes are represented in mirror pairs
    let data = ResonanceData::new();
    let mut classes_seen = [false; 96];

    for pair in &data.mirror_pairs {
        assert!(pair.class_a < 96);
        assert!(pair.class_b < 96);
        assert_ne!(pair.class_a, pair.class_b);

        classes_seen[pair.class_a as usize] = true;
        classes_seen[pair.class_b as usize] = true;
    }

    // All classes should appear exactly once
    assert_eq!(
        classes_seen.iter().filter(|&&x| x).count(),
        96,
        "Not all classes covered by mirror pairs"
    );
}

#[test]
fn test_unity_classes_validity() {
    // Verify unity classes are valid
    let data = ResonanceData::new();

    assert_eq!(data.unity_classes.len(), 2);

    for class_id in &data.unity_classes {
        assert!(*class_id < 96);
        assert!(atlas_core::is_unity(*class_id));
    }

    // Verify they are distinct
    assert_ne!(data.unity_classes[0], data.unity_classes[1]);
}

#[test]
fn test_c_compatible_buffer_packing() {
    // Test that C-compatible packing matches serialization
    let data = ResonanceData::new();

    // Pack mirror pairs using C-compatible function
    let mut mirror_buffer = vec![AtlasMirrorPair::new(0, 0); 48];
    let mirror_count = pack_mirror_pairs(&mut mirror_buffer);

    assert_eq!(mirror_count, 48);
    assert_eq!(mirror_count, data.mirror_pairs.len());

    // Verify contents match
    for (i, pair) in data.mirror_pairs.iter().enumerate() {
        assert_eq!(mirror_buffer[i].class_a, pair.class_a);
        assert_eq!(mirror_buffer[i].class_b, pair.class_b);
    }

    // Pack unity classes
    let mut unity_buffer = vec![0u8; 10];
    let unity_count = pack_unity_classes(&mut unity_buffer);

    assert_eq!(unity_count, 2);
    assert_eq!(unity_count, data.unity_classes.len());

    for (i, class_id) in data.unity_classes.iter().enumerate() {
        assert_eq!(unity_buffer[i], *class_id);
    }
}

#[test]
fn test_deserialization_error_handling() {
    // Test various malformed inputs
    let empty: &[u8] = &[];
    assert!(ResonanceData::from_binary(empty).is_err());

    let truncated = &[48, 0, 0, 0]; // Just the count, no data
    assert!(ResonanceData::from_binary(truncated).is_err());

    let malformed_json = "{ invalid json }";
    assert!(ResonanceData::from_json(malformed_json).is_err());

    let incomplete_json = r#"{"mirror_pairs": []}"#; // Missing unity_classes
    assert!(ResonanceData::from_json(incomplete_json).is_err());
}

#[test]
fn test_validation_catches_errors() {
    // Test that validation catches invalid data
    let mut data = ResonanceData::new();

    // Add invalid mirror pair
    data.mirror_pairs.push(SerializedMirrorPair {
        class_a: 200, // Invalid: >= 96
        class_b: 50,
    });
    assert!(data.validate().is_err());

    // Reset and test invalid unity class
    let mut data = ResonanceData::new();
    data.unity_classes.push(150); // Invalid: >= 96
    assert!(data.validate().is_err());

    // Reset and test invalid phase window
    let mut data = ResonanceData::new();
    data.add_phase_window(AtlasPhaseWindow {
        begin: 1000, // Invalid: >= 768
        span: 50,
    });
    assert!(data.validate().is_err());
}

#[test]
fn test_size_calculation_accuracy() {
    // Verify size_bytes() matches actual binary size

    for num_items in [0, 1, 10, 50] {
        let mut test_data = ResonanceData::new();
        for _ in 0..num_items {
            test_data.add_class_mask(AtlasClassMask::empty());
            test_data.add_phase_window(AtlasPhaseWindow::full());
        }

        let calculated_size = test_data.size_bytes();
        let actual_size = test_data.to_binary().len();

        assert_eq!(
            calculated_size, actual_size,
            "Size mismatch with {} items: calculated {}, actual {}",
            num_items, calculated_size, actual_size
        );
    }
}

#[test]
fn test_serialization_idempotency() {
    // Verify that serialization is deterministic
    let data1 = ResonanceData::new();
    let data2 = ResonanceData::new();

    let binary1 = data1.to_binary();
    let binary2 = data2.to_binary();

    assert_eq!(binary1, binary2);

    let json1 = data1.to_json().unwrap();
    let json2 = data2.to_json().unwrap();

    assert_eq!(json1, json2);
}

#[test]
fn test_complex_roundtrip() {
    // Test roundtrip with complex data
    let mut data = ResonanceData::new();

    // Add various class masks
    data.add_class_mask(AtlasClassMask::empty());
    data.add_class_mask(AtlasClassMask::all());

    let mut custom_mask = AtlasClassMask::empty();
    custom_mask.low = 0x1234567890ABCDEF;
    custom_mask.high = 0x12345678;
    data.add_class_mask(custom_mask);

    // Add various phase windows
    data.add_phase_window(AtlasPhaseWindow { begin: 0, span: 100 });
    data.add_phase_window(AtlasPhaseWindow { begin: 700, span: 100 }); // Wrapping window
    data.add_phase_window(AtlasPhaseWindow::full());

    // JSON roundtrip
    let json = data.to_json().unwrap();
    let from_json = ResonanceData::from_json(&json).unwrap();
    assert_eq!(data, from_json);

    // Binary roundtrip
    let binary = data.to_binary();
    let from_binary = ResonanceData::from_binary(&binary).unwrap();
    assert_eq!(data, from_binary);

    // Cross-format consistency
    assert_eq!(from_json, from_binary);
}
