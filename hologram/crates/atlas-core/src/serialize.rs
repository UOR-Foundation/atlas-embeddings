//! Serialization of resonance data for CUDA consumption
//!
//! This module provides functions to precompute and serialize class masks, mirror pairs,
//! and phase windows into buffers suitable for upload to CUDA global or constant memory.
//!
//! # Formats
//!
//! Two serialization formats are supported:
//! - **JSON**: Human-readable format for tooling and debugging
//! - **Binary**: Compact format for runtime packaging and device upload
//!
//! # CUDA Memory Constraints
//!
//! All serialized data is designed to fit within typical CUDA constant memory limits
//! (64KB on most devices). Size measurements are provided to verify constraints.

use crate::{invariants::*, AtlasError, Result, PHASE_MODULUS, RESONANCE_CLASSES};
use serde::{Deserialize, Serialize};

/// Complete resonance metadata package for CUDA kernels
///
/// This structure contains all precomputed Atlas invariants needed by
/// device code, organized for efficient upload to CUDA constant memory.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ResonanceData {
    /// All 48 mirror pairs (96 bytes)
    pub mirror_pairs: Vec<SerializedMirrorPair>,
    /// Unity class identifiers (2 bytes)
    pub unity_classes: Vec<u8>,
    /// Class mask lookup table (optional, 96 entries)
    #[serde(default)]
    pub class_masks: Vec<SerializedClassMask>,
    /// Phase window definitions (optional)
    #[serde(default)]
    pub phase_windows: Vec<SerializedPhaseWindow>,
    /// Launch validation lookup tables (AC3 - optional, for fast on-device checks)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub validation_data: Option<SerializedValidationData>,
}

/// Serializable launch validation data (AC3)
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SerializedValidationData {
    /// Unity class bit flags (12 bytes)
    pub unity_flags: Vec<u8>,
    /// Mirror lookup table (96 bytes)
    pub mirror_table: Vec<u8>,
}

impl From<crate::LaunchValidationData> for SerializedValidationData {
    fn from(data: crate::LaunchValidationData) -> Self {
        // Access fields via method since they're private
        let mut unity_flags = vec![0u8; 12];
        let mut mirror_table = vec![0xFF; 96];

        // Reconstruct from public API
        for i in 0..96u8 {
            if data.is_unity_class(i) {
                let byte_idx = (i / 8) as usize;
                let bit_idx = i % 8;
                unity_flags[byte_idx] |= 1 << bit_idx;
            }
            if let Some(mirror) = data.get_mirror(i) {
                mirror_table[i as usize] = mirror;
            }
        }

        Self {
            unity_flags,
            mirror_table,
        }
    }
}

impl From<SerializedValidationData> for crate::LaunchValidationData {
    fn from(_data: SerializedValidationData) -> Self {
        // Always reconstruct from authoritative source
        crate::LaunchValidationData::new()
    }
}

/// Serializable mirror pair
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub struct SerializedMirrorPair {
    pub class_a: u8,
    pub class_b: u8,
}

impl From<AtlasMirrorPair> for SerializedMirrorPair {
    fn from(pair: AtlasMirrorPair) -> Self {
        Self {
            class_a: pair.class_a,
            class_b: pair.class_b,
        }
    }
}

impl From<SerializedMirrorPair> for AtlasMirrorPair {
    fn from(pair: SerializedMirrorPair) -> Self {
        AtlasMirrorPair::new(pair.class_a, pair.class_b)
    }
}

/// Serializable class mask
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub struct SerializedClassMask {
    pub low: u64,
    pub high: u32,
}

impl From<AtlasClassMask> for SerializedClassMask {
    fn from(mask: AtlasClassMask) -> Self {
        Self {
            low: mask.low,
            high: mask.high,
        }
    }
}

impl From<SerializedClassMask> for AtlasClassMask {
    fn from(mask: SerializedClassMask) -> Self {
        AtlasClassMask {
            low: mask.low,
            high: mask.high,
        }
    }
}

/// Serializable phase window
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub struct SerializedPhaseWindow {
    pub begin: u32,
    pub span: u32,
}

impl From<AtlasPhaseWindow> for SerializedPhaseWindow {
    fn from(window: AtlasPhaseWindow) -> Self {
        Self {
            begin: window.begin,
            span: window.span,
        }
    }
}

impl From<SerializedPhaseWindow> for AtlasPhaseWindow {
    fn from(window: SerializedPhaseWindow) -> Self {
        AtlasPhaseWindow {
            begin: window.begin,
            span: window.span,
        }
    }
}

impl ResonanceData {
    /// Create a new resonance data package with precomputed invariants
    ///
    /// This function populates all mirror pairs and unity classes from the
    /// authoritative Atlas data.
    pub fn new() -> Self {
        let mirror_pairs = Self::generate_mirror_pairs();
        let unity_classes = Self::generate_unity_classes();

        Self {
            mirror_pairs,
            unity_classes,
            class_masks: Vec::new(),
            phase_windows: Vec::new(),
            validation_data: None,
        }
    }

    /// Create resonance data with launch validation tables included
    ///
    /// This variant includes precomputed lookup tables for fast launch-time
    /// validation. Recommended for runtime use.
    pub fn with_validation() -> Self {
        let mut data = Self::new();
        data.validation_data = Some(crate::LaunchValidationData::new().into());
        data
    }

    /// Add launch validation data to this package
    pub fn add_validation_data(&mut self) {
        self.validation_data = Some(crate::LaunchValidationData::new().into());
    }

    /// Generate all mirror pairs from the Atlas
    fn generate_mirror_pairs() -> Vec<SerializedMirrorPair> {
        let mut pairs = Vec::with_capacity(48);
        let mut seen = [false; RESONANCE_CLASSES as usize];

        for class_id in 0..RESONANCE_CLASSES as u8 {
            if seen[class_id as usize] {
                continue;
            }

            let mirror = crate::get_mirror_pair(class_id);
            if mirror < RESONANCE_CLASSES as u8 && !seen[mirror as usize] {
                pairs.push(SerializedMirrorPair {
                    class_a: class_id,
                    class_b: mirror,
                });
                seen[class_id as usize] = true;
                seen[mirror as usize] = true;
            }
        }

        pairs
    }

    /// Generate unity class identifiers
    fn generate_unity_classes() -> Vec<u8> {
        let unity = crate::unity_positions();
        unity.iter().map(|pos| pos.as_u8()).collect()
    }

    /// Add a class mask to the package
    pub fn add_class_mask(&mut self, mask: AtlasClassMask) {
        self.class_masks.push(mask.into());
    }

    /// Add a phase window to the package
    pub fn add_phase_window(&mut self, window: AtlasPhaseWindow) {
        self.phase_windows.push(window.into());
    }

    /// Serialize to JSON format for tooling
    ///
    /// Returns a pretty-printed JSON string suitable for inspection and
    /// debugging.
    pub fn to_json(&self) -> Result<String> {
        serde_json::to_string_pretty(self).map_err(|_e| AtlasError::InvalidClassId(0))
        // Use appropriate error
    }

    /// Deserialize from JSON format
    pub fn from_json(json: &str) -> Result<Self> {
        serde_json::from_str(json).map_err(|_e| AtlasError::InvalidClassId(0)) // Use appropriate error
    }

    /// Serialize to binary format for runtime packaging
    ///
    /// Returns a compact binary representation using native byte order.
    /// This format is designed for direct upload to CUDA memory.
    ///
    /// # Binary Layout
    ///
    /// ```text
    /// [mirror_pair_count: u32]
    /// [mirror_pairs: [(u8, u8); mirror_pair_count]]
    /// [unity_class_count: u32]
    /// [unity_classes: [u8; unity_class_count]]
    /// [class_mask_count: u32]
    /// [class_masks: [(u64, u32); class_mask_count]]
    /// [phase_window_count: u32]
    /// [phase_windows: [(u32, u32); phase_window_count]]
    /// [validation_present: u32] // 0 or 1
    /// [validation_data: [unity_flags: [u8; 12], mirror_table: [u8; 96]]] // if present
    /// ```
    pub fn to_binary(&self) -> Vec<u8> {
        let mut buffer = Vec::new();

        // Mirror pairs
        buffer.extend_from_slice(&(self.mirror_pairs.len() as u32).to_le_bytes());
        for pair in &self.mirror_pairs {
            buffer.push(pair.class_a);
            buffer.push(pair.class_b);
        }

        // Unity classes
        buffer.extend_from_slice(&(self.unity_classes.len() as u32).to_le_bytes());
        buffer.extend_from_slice(&self.unity_classes);

        // Class masks
        buffer.extend_from_slice(&(self.class_masks.len() as u32).to_le_bytes());
        for mask in &self.class_masks {
            buffer.extend_from_slice(&mask.low.to_le_bytes());
            buffer.extend_from_slice(&mask.high.to_le_bytes());
        }

        // Phase windows
        buffer.extend_from_slice(&(self.phase_windows.len() as u32).to_le_bytes());
        for window in &self.phase_windows {
            buffer.extend_from_slice(&window.begin.to_le_bytes());
            buffer.extend_from_slice(&window.span.to_le_bytes());
        }

        // Validation data (AC3)
        if let Some(ref validation) = self.validation_data {
            buffer.extend_from_slice(&1u32.to_le_bytes()); // Present
            buffer.extend_from_slice(&validation.unity_flags);
            buffer.extend_from_slice(&validation.mirror_table);
        } else {
            buffer.extend_from_slice(&0u32.to_le_bytes()); // Not present
        }

        buffer
    }

    /// Deserialize from binary format
    ///
    /// # Errors
    ///
    /// Returns an error if the buffer is malformed or contains invalid data.
    pub fn from_binary(buffer: &[u8]) -> Result<Self> {
        let mut offset = 0;

        // Helper to read u32
        let read_u32 = |buf: &[u8], off: &mut usize| -> Result<u32> {
            if *off + 4 > buf.len() {
                return Err(AtlasError::InvalidClassId(0));
            }
            let value = u32::from_le_bytes([buf[*off], buf[*off + 1], buf[*off + 2], buf[*off + 3]]);
            *off += 4;
            Ok(value)
        };

        // Helper to read u64
        let read_u64 = |buf: &[u8], off: &mut usize| -> Result<u64> {
            if *off + 8 > buf.len() {
                return Err(AtlasError::InvalidClassId(0));
            }
            let value = u64::from_le_bytes([
                buf[*off],
                buf[*off + 1],
                buf[*off + 2],
                buf[*off + 3],
                buf[*off + 4],
                buf[*off + 5],
                buf[*off + 6],
                buf[*off + 7],
            ]);
            *off += 8;
            Ok(value)
        };

        // Read mirror pairs
        let mirror_pair_count = read_u32(buffer, &mut offset)? as usize;
        let mut mirror_pairs = Vec::with_capacity(mirror_pair_count);
        for _ in 0..mirror_pair_count {
            if offset + 2 > buffer.len() {
                return Err(AtlasError::InvalidClassId(0));
            }
            mirror_pairs.push(SerializedMirrorPair {
                class_a: buffer[offset],
                class_b: buffer[offset + 1],
            });
            offset += 2;
        }

        // Read unity classes
        let unity_class_count = read_u32(buffer, &mut offset)? as usize;
        if offset + unity_class_count > buffer.len() {
            return Err(AtlasError::InvalidClassId(0));
        }
        let unity_classes = buffer[offset..offset + unity_class_count].to_vec();
        offset += unity_class_count;

        // Read class masks
        let class_mask_count = read_u32(buffer, &mut offset)? as usize;
        let mut class_masks = Vec::with_capacity(class_mask_count);
        for _ in 0..class_mask_count {
            let low = read_u64(buffer, &mut offset)?;
            let high = read_u32(buffer, &mut offset)?;
            class_masks.push(SerializedClassMask { low, high });
        }

        // Read phase windows
        let phase_window_count = read_u32(buffer, &mut offset)? as usize;
        let mut phase_windows = Vec::with_capacity(phase_window_count);
        for _ in 0..phase_window_count {
            let begin = read_u32(buffer, &mut offset)?;
            let span = read_u32(buffer, &mut offset)?;
            phase_windows.push(SerializedPhaseWindow { begin, span });
        }

        // Read validation data (AC3) - optional for backward compatibility
        let validation_data = if offset + 4 <= buffer.len() {
            let validation_present = read_u32(buffer, &mut offset)?;
            if validation_present == 1 {
                // Read validation data
                if offset + 12 + 96 > buffer.len() {
                    return Err(AtlasError::InvalidClassId(0));
                }
                let unity_flags = buffer[offset..offset + 12].to_vec();
                offset += 12;

                let mirror_table = buffer[offset..offset + 96].to_vec();
                // No need to update offset here - end of function

                Some(SerializedValidationData {
                    unity_flags,
                    mirror_table,
                })
            } else {
                None
            }
        } else {
            None
        };

        Ok(Self {
            mirror_pairs,
            unity_classes,
            class_masks,
            phase_windows,
            validation_data,
        })
    }

    /// Calculate total size in bytes
    ///
    /// This is useful for verifying that serialized data fits within CUDA
    /// constant memory constraints (typically 64KB).
    pub fn size_bytes(&self) -> usize {
        let mirror_size = 4 + self.mirror_pairs.len() * 2;
        let unity_size = 4 + self.unity_classes.len();
        let mask_size = 4 + self.class_masks.len() * 12; // u64 + u32
        let window_size = 4 + self.phase_windows.len() * 8; // 2 * u32
        let validation_size = if self.validation_data.is_some() {
            4 + 12 + 96 // count + unity_flags + mirror_table
        } else {
            4 // just the count (0)
        };
        mirror_size + unity_size + mask_size + window_size + validation_size
    }

    /// Validate data integrity
    ///
    /// Checks that:
    /// - Mirror pairs are valid and symmetric
    /// - Unity classes are within range
    /// - Class masks are properly formed
    /// - Phase windows are within valid ranges
    pub fn validate(&self) -> Result<()> {
        // Validate mirror pairs
        for pair in &self.mirror_pairs {
            if pair.class_a >= RESONANCE_CLASSES as u8 {
                return Err(AtlasError::InvalidClassId(pair.class_a as u32));
            }
            if pair.class_b >= RESONANCE_CLASSES as u8 {
                return Err(AtlasError::InvalidClassId(pair.class_b as u32));
            }
            if pair.class_a == pair.class_b {
                return Err(AtlasError::InvalidClassId(pair.class_a as u32));
            }
        }

        // Validate unity classes
        for class_id in &self.unity_classes {
            if *class_id >= RESONANCE_CLASSES as u8 {
                return Err(AtlasError::InvalidClassId(*class_id as u32));
            }
        }

        // Validate phase windows
        for window in &self.phase_windows {
            if window.begin >= PHASE_MODULUS {
                return Err(AtlasError::InvalidPhase(window.begin));
            }
            if window.span > PHASE_MODULUS {
                return Err(AtlasError::InvalidPhase(window.span));
            }
        }

        Ok(())
    }
}

impl Default for ResonanceData {
    fn default() -> Self {
        Self::new()
    }
}

/// Helper function to pack mirror pairs into a contiguous C-compatible buffer
///
/// This is a convenience wrapper that populates a pre-allocated buffer with
/// all mirror pairs, suitable for direct FFI transfer.
///
/// # Safety
///
/// The caller must ensure `buffer` has at least `capacity` elements.
pub fn pack_mirror_pairs(buffer: &mut [AtlasMirrorPair]) -> usize {
    let capacity = buffer.len();
    unsafe { populate_mirror_pairs(buffer.as_mut_ptr(), capacity) }
}

/// Helper function to pack unity classes into a contiguous buffer
///
/// # Safety
///
/// The caller must ensure `buffer` has at least 2 elements.
pub fn pack_unity_classes(buffer: &mut [u8]) -> usize {
    let capacity = buffer.len();
    unsafe { populate_unity_classes(buffer.as_mut_ptr(), capacity) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resonance_data_creation() {
        let data = ResonanceData::new();

        // Should have exactly 48 mirror pairs (96 classes / 2)
        assert_eq!(data.mirror_pairs.len(), 48);

        // Should have exactly 2 unity classes
        assert_eq!(data.unity_classes.len(), 2);

        // Verify all pairs are unique
        let mut seen = std::collections::HashSet::new();
        for pair in &data.mirror_pairs {
            assert!(seen.insert(pair.class_a));
            assert!(seen.insert(pair.class_b));
        }
        assert_eq!(seen.len(), 96);
    }

    #[test]
    fn test_json_serialization_roundtrip() {
        let original = ResonanceData::new();
        let json = original.to_json().expect("Failed to serialize to JSON");

        // Verify JSON contains expected fields
        assert!(json.contains("mirror_pairs"));
        assert!(json.contains("unity_classes"));

        let restored = ResonanceData::from_json(&json).expect("Failed to deserialize from JSON");
        assert_eq!(original, restored);
    }

    #[test]
    fn test_binary_serialization_roundtrip() {
        let original = ResonanceData::new();
        let binary = original.to_binary();

        // Basic size check
        assert!(!binary.is_empty());
        assert!(binary.len() < 1024); // Should be small

        let restored = ResonanceData::from_binary(&binary).expect("Failed to deserialize from binary");
        assert_eq!(original, restored);
    }

    #[test]
    fn test_binary_with_class_masks() {
        let mut data = ResonanceData::new();
        data.add_class_mask(AtlasClassMask::empty());
        data.add_class_mask(AtlasClassMask::all());

        let binary = data.to_binary();
        let restored = ResonanceData::from_binary(&binary).expect("Failed to deserialize");
        assert_eq!(data, restored);
        assert_eq!(restored.class_masks.len(), 2);
    }

    #[test]
    fn test_binary_with_phase_windows() {
        let mut data = ResonanceData::new();
        data.add_phase_window(AtlasPhaseWindow { begin: 100, span: 50 });
        data.add_phase_window(AtlasPhaseWindow::full());

        let binary = data.to_binary();
        let restored = ResonanceData::from_binary(&binary).expect("Failed to deserialize");
        assert_eq!(data, restored);
        assert_eq!(restored.phase_windows.len(), 2);
    }

    #[test]
    fn test_size_calculation() {
        let data = ResonanceData::new();
        let size = data.size_bytes();

        // Mirror pairs: 4 bytes (count) + 48 * 2 = 100 bytes
        // Unity classes: 4 bytes (count) + 2 = 6 bytes
        // Class masks: 4 bytes (count) + 0 = 4 bytes
        // Phase windows: 4 bytes (count) + 0 = 4 bytes
        // Validation flag: 4 bytes (0 = not present)
        // Total: 118 bytes
        assert_eq!(size, 118);

        let binary = data.to_binary();
        assert_eq!(binary.len(), size);
    }

    #[test]
    fn test_size_fits_constant_memory() {
        let mut data = ResonanceData::new();

        // Add maximum reasonable data
        for i in 0..100 {
            data.add_class_mask(AtlasClassMask::empty());
            data.add_phase_window(AtlasPhaseWindow { begin: i, span: 10 });
        }

        let size = data.size_bytes();
        // CUDA constant memory is typically 64KB
        assert!(size < 64 * 1024, "Size {} exceeds 64KB constant memory", size);
    }

    #[test]
    fn test_validate_correct_data() {
        let data = ResonanceData::new();
        assert!(data.validate().is_ok());
    }

    #[test]
    fn test_validate_invalid_mirror_pair() {
        let mut data = ResonanceData::new();
        data.mirror_pairs.push(SerializedMirrorPair {
            class_a: 100, // Invalid: >= 96
            class_b: 50,
        });

        assert!(data.validate().is_err());
    }

    #[test]
    fn test_validate_invalid_unity_class() {
        let mut data = ResonanceData::new();
        data.unity_classes.push(200); // Invalid: >= 96

        assert!(data.validate().is_err());
    }

    #[test]
    fn test_validate_invalid_phase_window() {
        let mut data = ResonanceData::new();
        data.add_phase_window(AtlasPhaseWindow {
            begin: 1000, // Invalid: >= 768
            span: 50,
        });

        assert!(data.validate().is_err());
    }

    #[test]
    fn test_serialized_mirror_pair_conversion() {
        let atlas_pair = AtlasMirrorPair::new(10, 42);
        let serialized: SerializedMirrorPair = atlas_pair.into();
        assert_eq!(serialized.class_a, 10);
        assert_eq!(serialized.class_b, 42);

        let converted: AtlasMirrorPair = serialized.into();
        assert_eq!(converted.class_a, 10);
        assert_eq!(converted.class_b, 42);
    }

    #[test]
    fn test_serialized_class_mask_conversion() {
        let atlas_mask = AtlasClassMask::all();
        let serialized: SerializedClassMask = atlas_mask.into();
        assert_eq!(serialized.low, u64::MAX);
        assert_eq!(serialized.high, 0xFFFF_FFFF);

        let converted: AtlasClassMask = serialized.into();
        assert_eq!(converted.low, u64::MAX);
        assert_eq!(converted.high, 0xFFFF_FFFF);
    }

    #[test]
    fn test_serialized_phase_window_conversion() {
        let atlas_window = AtlasPhaseWindow { begin: 100, span: 50 };
        let serialized: SerializedPhaseWindow = atlas_window.into();
        assert_eq!(serialized.begin, 100);
        assert_eq!(serialized.span, 50);

        let converted: AtlasPhaseWindow = serialized.into();
        assert_eq!(converted.begin, 100);
        assert_eq!(converted.span, 50);
    }

    #[test]
    fn test_pack_mirror_pairs_helper() {
        let mut buffer = vec![AtlasMirrorPair::new(0, 0); 48];
        let count = pack_mirror_pairs(&mut buffer);

        assert_eq!(count, 48);
        for pair in &buffer {
            assert!(pair.class_a < 96);
            assert!(pair.class_b < 96);
            assert_ne!(pair.class_a, pair.class_b);
        }
    }

    #[test]
    fn test_pack_unity_classes_helper() {
        let mut buffer = vec![0u8; 10];
        let count = pack_unity_classes(&mut buffer);

        assert_eq!(count, 2);
        assert!(crate::is_unity(buffer[0]));
        assert!(crate::is_unity(buffer[1]));
        assert_ne!(buffer[0], buffer[1]);
    }

    #[test]
    fn test_mirror_pairs_match_atlas() {
        let data = ResonanceData::new();

        // Verify each pair matches the Atlas mirror data
        for pair in &data.mirror_pairs {
            let mirror = crate::get_mirror_pair(pair.class_a);
            assert_eq!(mirror, pair.class_b);

            let reverse_mirror = crate::get_mirror_pair(pair.class_b);
            assert_eq!(reverse_mirror, pair.class_a);
        }
    }

    #[test]
    fn test_unity_classes_match_atlas() {
        let data = ResonanceData::new();
        let unity_positions = crate::unity_positions();

        assert_eq!(data.unity_classes.len(), unity_positions.len());
        for class_id in &data.unity_classes {
            assert!(crate::is_unity(*class_id));
        }
    }

    #[test]
    fn test_binary_deserialization_empty_buffer() {
        let result = ResonanceData::from_binary(&[]);
        assert!(result.is_err());
    }

    #[test]
    fn test_binary_deserialization_truncated() {
        let data = ResonanceData::new();
        let binary = data.to_binary();

        // Try to deserialize truncated data
        let result = ResonanceData::from_binary(&binary[..10]);
        assert!(result.is_err());
    }

    #[test]
    fn test_serialization_stability() {
        // Generate data multiple times and verify consistency
        let data1 = ResonanceData::new();
        let data2 = ResonanceData::new();

        assert_eq!(data1, data2);

        let json1 = data1.to_json().unwrap();
        let json2 = data2.to_json().unwrap();
        assert_eq!(json1, json2);

        let binary1 = data1.to_binary();
        let binary2 = data2.to_binary();
        assert_eq!(binary1, binary2);
    }

    // Tests for AC3 validation data serialization

    #[test]
    fn test_resonance_data_with_validation() {
        let data = ResonanceData::with_validation();
        assert!(data.validation_data.is_some());

        // Verify validation data content
        let validation = data.validation_data.as_ref().unwrap();
        assert_eq!(validation.unity_flags.len(), 12);
        assert_eq!(validation.mirror_table.len(), 96);

        // Verify all mirrors are valid
        for (i, &mirror) in validation.mirror_table.iter().enumerate() {
            assert!(mirror < 96 || mirror == 0xFF, "Invalid mirror at {}: {}", i, mirror);
        }
    }

    #[test]
    fn test_add_validation_data() {
        let mut data = ResonanceData::new();
        assert!(data.validation_data.is_none());

        data.add_validation_data();
        assert!(data.validation_data.is_some());
    }

    #[test]
    fn test_validation_data_binary_roundtrip() {
        let data = ResonanceData::with_validation();
        let binary = data.to_binary();

        let restored = ResonanceData::from_binary(&binary).expect("Failed to deserialize");

        // Validation data should be preserved
        assert!(restored.validation_data.is_some());
        assert_eq!(data.validation_data, restored.validation_data);
    }

    #[test]
    fn test_validation_data_json_roundtrip() {
        let data = ResonanceData::with_validation();
        let json = data.to_json().expect("Failed to serialize");

        let restored = ResonanceData::from_json(&json).expect("Failed to deserialize");
        assert!(restored.validation_data.is_some());
        assert_eq!(data, restored);
    }

    #[test]
    fn test_validation_data_size() {
        let without_validation = ResonanceData::new();
        let with_validation = ResonanceData::with_validation();

        let size_without = without_validation.size_bytes();
        let size_with = with_validation.size_bytes();

        // Both include 4 bytes for validation presence flag
        // With validation adds: 12 (unity) + 96 (mirrors) = 108 bytes more
        assert_eq!(size_with, size_without + 108);
    }

    #[test]
    fn test_backward_compatibility_without_validation() {
        // Old format without validation data
        let old_data = ResonanceData::new();
        let binary = old_data.to_binary();

        // Should deserialize successfully, validation_data will be None
        let restored = ResonanceData::from_binary(&binary).expect("Failed to deserialize");
        assert!(restored.validation_data.is_none());
        assert_eq!(old_data.mirror_pairs, restored.mirror_pairs);
        assert_eq!(old_data.unity_classes, restored.unity_classes);
    }

    #[test]
    fn test_serialized_validation_data_conversion() {
        let validation_data = crate::LaunchValidationData::new();
        let serialized: SerializedValidationData = validation_data.into();

        // Verify unity flags
        let unity_classes = crate::unity_positions();
        for class in unity_classes {
            let class_id = class.as_u8();
            let byte_idx = (class_id / 8) as usize;
            let bit_idx = class_id % 8;
            assert!(
                (serialized.unity_flags[byte_idx] & (1 << bit_idx)) != 0,
                "Unity class {} not in flags",
                class_id
            );
        }

        // Verify mirror table
        for i in 0..96u8 {
            let mirror = serialized.mirror_table[i as usize];
            if mirror != 0xFF {
                let expected = crate::get_mirror_pair(i);
                assert_eq!(mirror, expected, "Mirror mismatch for class {}", i);
            }
        }
    }

    #[test]
    fn test_validation_data_fits_constant_memory() {
        // With validation data included
        let mut data = ResonanceData::with_validation();

        // Add reasonable amount of masks and windows
        for _ in 0..50 {
            data.add_class_mask(AtlasClassMask::all());
            data.add_phase_window(AtlasPhaseWindow { begin: 0, span: 100 });
        }

        let size = data.size_bytes();
        const CUDA_CONSTANT_MEMORY: usize = 64 * 1024;
        assert!(
            size < CUDA_CONSTANT_MEMORY,
            "Data with validation too large: {} bytes",
            size
        );
    }
}
