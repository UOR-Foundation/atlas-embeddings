//! Snapshot tests for resonance data serialization stability (AC4)
//!
//! These tests verify that serialized resonance representations round-trip correctly
//! and remain stable across releases, preventing desynchronization with CUDA runtime
//! expectations.
//!
//! Tests use `insta` for snapshot testing to detect breaking changes in serialization
//! format. When tests fail due to intentional format changes, reviewers must:
//! 1. Review the impact on downstream CUDA runtime compatibility
//! 2. Ensure version bump is appropriate
//! 3. Update documentation to note breaking changes
//! 4. Accept the new snapshots with `cargo insta review`

use atlas_core::serialize::*;
use atlas_core::{AtlasClassMask, AtlasPhaseWindow};

/// Test binary format stability with base configuration
///
/// This snapshot captures the binary layout of a minimal ResonanceData package.
/// Changes to this format indicate potential breaking changes for CUDA runtime.
#[test]
fn test_binary_format_snapshot_base() {
    let data = ResonanceData::new();
    let binary = data.to_binary();

    // Create a hex representation for human-readable diffs
    let hex_repr: Vec<String> = binary
        .chunks(16)
        .enumerate()
        .map(|(i, chunk)| {
            let hex = chunk.iter().map(|b| format!("{:02x}", b)).collect::<Vec<_>>().join(" ");
            format!("{:04x}: {}", i * 16, hex)
        })
        .collect();

    insta::assert_yaml_snapshot!("binary_format_base", hex_repr);

    // Also verify exact size hasn't changed
    insta::assert_snapshot!("binary_size_base", binary.len().to_string());
}

/// Test binary format stability with class masks and phase windows
#[test]
fn test_binary_format_snapshot_with_metadata() {
    let mut data = ResonanceData::new();

    // Add representative metadata
    data.add_class_mask(AtlasClassMask::empty());
    data.add_class_mask(AtlasClassMask::all());
    data.add_phase_window(AtlasPhaseWindow { begin: 100, span: 50 });
    data.add_phase_window(AtlasPhaseWindow { begin: 200, span: 100 });

    let binary = data.to_binary();

    let hex_repr: Vec<String> = binary
        .chunks(16)
        .enumerate()
        .map(|(i, chunk)| {
            let hex = chunk.iter().map(|b| format!("{:02x}", b)).collect::<Vec<_>>().join(" ");
            format!("{:04x}: {}", i * 16, hex)
        })
        .collect();

    insta::assert_yaml_snapshot!("binary_format_with_metadata", hex_repr);
    insta::assert_snapshot!("binary_size_with_metadata", binary.len().to_string());
}

/// Test binary format stability with validation data
#[test]
fn test_binary_format_snapshot_with_validation() {
    let data = ResonanceData::with_validation();
    let binary = data.to_binary();

    let hex_repr: Vec<String> = binary
        .chunks(16)
        .enumerate()
        .map(|(i, chunk)| {
            let hex = chunk.iter().map(|b| format!("{:02x}", b)).collect::<Vec<_>>().join(" ");
            format!("{:04x}: {}", i * 16, hex)
        })
        .collect();

    insta::assert_yaml_snapshot!("binary_format_with_validation", hex_repr);
    insta::assert_snapshot!("binary_size_with_validation", binary.len().to_string());
}

/// Test JSON format stability with base configuration
#[test]
fn test_json_format_snapshot_base() {
    let data = ResonanceData::new();
    let json = data.to_json().expect("Failed to serialize to JSON");

    insta::assert_snapshot!("json_format_base", json);
}

/// Test JSON format stability with metadata
#[test]
fn test_json_format_snapshot_with_metadata() {
    let mut data = ResonanceData::new();
    data.add_class_mask(AtlasClassMask::empty());
    data.add_class_mask(AtlasClassMask::all());
    data.add_phase_window(AtlasPhaseWindow { begin: 100, span: 50 });

    let json = data.to_json().expect("Failed to serialize to JSON");

    insta::assert_snapshot!("json_format_with_metadata", json);
}

/// Test JSON format stability with validation data
#[test]
fn test_json_format_snapshot_with_validation() {
    let data = ResonanceData::with_validation();
    let json = data.to_json().expect("Failed to serialize to JSON");

    insta::assert_snapshot!("json_format_with_validation", json);
}

/// Verify binary roundtrip preserves exact data
///
/// This test ensures that deserializing and re-serializing produces identical output,
/// preventing data corruption or loss during roundtrips.
#[test]
fn test_binary_roundtrip_stability() {
    let original = ResonanceData::new();
    let binary1 = original.to_binary();

    let restored = ResonanceData::from_binary(&binary1).expect("Failed to deserialize");
    let binary2 = restored.to_binary();

    // Roundtrip must produce identical bytes
    assert_eq!(binary1, binary2, "Binary roundtrip produced different output");

    // Snapshot the roundtrip result
    let hex_repr: Vec<String> = binary2
        .chunks(16)
        .enumerate()
        .map(|(i, chunk)| {
            let hex = chunk.iter().map(|b| format!("{:02x}", b)).collect::<Vec<_>>().join(" ");
            format!("{:04x}: {}", i * 16, hex)
        })
        .collect();

    insta::assert_yaml_snapshot!("binary_roundtrip_stable", hex_repr);
}

/// Verify JSON roundtrip preserves exact data
#[test]
fn test_json_roundtrip_stability() {
    let mut original = ResonanceData::new();
    original.add_class_mask(AtlasClassMask::all());
    original.add_phase_window(AtlasPhaseWindow { begin: 100, span: 50 });

    let json1 = original.to_json().expect("Failed to serialize to JSON");
    let restored = ResonanceData::from_json(&json1).expect("Failed to deserialize from JSON");
    let json2 = restored.to_json().expect("Failed to re-serialize to JSON");

    // Roundtrip must produce identical JSON
    assert_eq!(json1, json2, "JSON roundtrip produced different output");

    insta::assert_snapshot!("json_roundtrip_stable", json2);
}

/// Verify complex data roundtrip through both formats
#[test]
fn test_cross_format_roundtrip_stability() {
    let mut original = ResonanceData::with_validation();
    original.add_class_mask(AtlasClassMask::empty());
    original.add_class_mask(AtlasClassMask::all());
    original.add_phase_window(AtlasPhaseWindow { begin: 0, span: 100 });
    original.add_phase_window(AtlasPhaseWindow { begin: 200, span: 150 });
    original.add_phase_window(AtlasPhaseWindow { begin: 500, span: 200 });

    // Binary roundtrip
    let binary = original.to_binary();
    let from_binary = ResonanceData::from_binary(&binary).expect("Failed binary deserialization");

    // JSON roundtrip
    let json = original.to_json().expect("Failed JSON serialization");
    let from_json = ResonanceData::from_json(&json).expect("Failed JSON deserialization");

    // Both should be equal to original
    assert_eq!(original, from_binary, "Binary roundtrip failed");
    assert_eq!(original, from_json, "JSON roundtrip failed");
    assert_eq!(from_binary, from_json, "Binary and JSON roundtrips differ");

    // Snapshot the final state
    let final_json = from_binary.to_json().expect("Failed to serialize final state");
    insta::assert_snapshot!("cross_format_roundtrip_stable", final_json);
}

/// Test that mirror pairs serialization is stable
///
/// Mirror pairs are critical for CUDA runtime, so their serialization must be stable.
#[test]
fn test_mirror_pairs_serialization_stability() {
    let data = ResonanceData::new();

    // Extract mirror pairs in deterministic order
    let pairs: Vec<String> = data
        .mirror_pairs
        .iter()
        .map(|p| format!("({}, {})", p.class_a, p.class_b))
        .collect();

    insta::assert_yaml_snapshot!("mirror_pairs_stable", pairs);
}

/// Test that unity classes serialization is stable
#[test]
fn test_unity_classes_serialization_stability() {
    let data = ResonanceData::new();

    insta::assert_yaml_snapshot!("unity_classes_stable", &data.unity_classes);
}

/// Verify validation data serialization stability
#[test]
fn test_validation_data_serialization_stability() {
    let data = ResonanceData::with_validation();

    // Verify validation data is present
    assert!(data.validation_data.is_some(), "Validation data should be present");

    let validation = data.validation_data.as_ref().unwrap();

    // Snapshot the validation data structure
    insta::assert_yaml_snapshot!("validation_data_unity_flags", &validation.unity_flags);
    insta::assert_yaml_snapshot!("validation_data_mirror_table", &validation.mirror_table);
}

/// Test serialization version compatibility marker
///
/// This test serves as a canary for serialization format changes.
/// When this test fails, it indicates the serialization format has changed.
/// Reviewers must:
/// 1. Assess impact on CUDA runtime compatibility
/// 2. Update version number if needed
/// 3. Document breaking changes
/// 4. Accept new snapshot with `cargo insta review`
#[test]
fn test_serialization_format_version_marker() {
    // Create a comprehensive test case covering all features
    let mut data = ResonanceData::with_validation();
    data.add_class_mask(AtlasClassMask::empty());
    data.add_class_mask(AtlasClassMask::all());
    data.add_phase_window(AtlasPhaseWindow { begin: 100, span: 50 });

    let json = data.to_json().expect("Failed to serialize");
    let binary = data.to_binary();

    // Create a version marker that captures format characteristics
    let version_marker = format!(
        "Format Version Marker:\n\
         - Mirror pairs count: {}\n\
         - Unity classes count: {}\n\
         - Class masks count: {}\n\
         - Phase windows count: {}\n\
         - Has validation data: {}\n\
         - Binary size: {} bytes\n\
         - JSON size: {} bytes",
        data.mirror_pairs.len(),
        data.unity_classes.len(),
        data.class_masks.len(),
        data.phase_windows.len(),
        data.validation_data.is_some(),
        binary.len(),
        json.len()
    );

    insta::assert_snapshot!("serialization_format_version", version_marker);
}

/// Test backward compatibility with old binary format (without validation data)
#[test]
fn test_backward_compatibility_snapshot() {
    // Create data without validation (old format)
    let mut data = ResonanceData::new();
    data.add_class_mask(AtlasClassMask::all());
    data.add_phase_window(AtlasPhaseWindow { begin: 100, span: 50 });

    let binary = data.to_binary();

    // Verify old format can be read
    let restored = ResonanceData::from_binary(&binary).expect("Failed to deserialize");
    assert_eq!(data, restored);
    assert!(
        restored.validation_data.is_none(),
        "Old format should not have validation data"
    );

    let hex_repr: Vec<String> = binary
        .chunks(16)
        .enumerate()
        .map(|(i, chunk)| {
            let hex = chunk.iter().map(|b| format!("{:02x}", b)).collect::<Vec<_>>().join(" ");
            format!("{:04x}: {}", i * 16, hex)
        })
        .collect();

    insta::assert_yaml_snapshot!("backward_compat_old_format", hex_repr);
}

/// Test that deserializing from old snapshots still works
///
/// This ensures we maintain backward compatibility with previously serialized data.
#[test]
fn test_deserialize_legacy_format() {
    // This represents a binary format from an earlier version (base format)
    // Structure: mirror_pairs(48) + unity_classes(2) + no masks/windows + validation_flag(0)
    let legacy_binary: Vec<u8> = {
        let mut buf = Vec::new();

        // Mirror pair count (48 pairs)
        buf.extend_from_slice(&48u32.to_le_bytes());

        // Generate 48 mirror pairs (using known mirror relationships)
        for i in 0..48u8 {
            let class_a = i * 2;
            let class_b = if class_a < 47 { 95 - class_a } else { class_a };
            buf.push(class_a);
            buf.push(class_b);
        }

        // Unity class count (2 classes)
        buf.extend_from_slice(&2u32.to_le_bytes());
        buf.push(47); // Unity class 1
        buf.push(48); // Unity class 2

        // Class mask count (0)
        buf.extend_from_slice(&0u32.to_le_bytes());

        // Phase window count (0)
        buf.extend_from_slice(&0u32.to_le_bytes());

        // Validation present (0 = not present, old format)
        buf.extend_from_slice(&0u32.to_le_bytes());

        buf
    };

    // Should be able to deserialize legacy format
    let result = ResonanceData::from_binary(&legacy_binary);
    assert!(
        result.is_ok(),
        "Failed to deserialize legacy format: {:?}",
        result.err()
    );

    let data = result.unwrap();
    assert_eq!(data.mirror_pairs.len(), 48);
    assert_eq!(data.unity_classes.len(), 2);
    assert_eq!(data.class_masks.len(), 0);
    assert_eq!(data.phase_windows.len(), 0);
    assert!(data.validation_data.is_none());
}
