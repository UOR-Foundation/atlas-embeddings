//! UOR (Universal Object Repository) mathematical primitives
//!
//! This module provides the core mathematical operations from atlas-12288.
//! These functions provide the mathematical oracle for computational invariants.

use atlas_embeddings::atlas::Label as GraphLabel;

use crate::{atlas, constants::*, AtlasError, AtlasLabel, Result};
use std::convert::TryFrom;

/// Map a raw byte into the canonical Atlas label.
fn label_from_byte(byte: u8) -> AtlasLabel {
    let binary = byte & 0x1F; // bits 0..=4 → five binary coordinates
    let e1 = (binary & 0b00001) as i8;
    let e2 = ((binary >> 1) & 0b00001) as i8;
    let e3 = ((binary >> 2) & 0b00001) as i8;
    let e6 = ((binary >> 3) & 0b00001) as i8;
    let e7 = ((binary >> 4) & 0b00001) as i8;

    let ternary_idx = ((byte >> 5) & 0b00011) % 3;
    let d45 = match ternary_idx {
        0 => -1,
        1 => 0,
        _ => 1,
    };

    AtlasLabel::new(e1, e2, e3, d45, e6, e7)
}

/// Internal helper: classify byte to (class_id, label).
fn classify_internal(byte: u8) -> Option<(u8, AtlasLabel)> {
    let label = label_from_byte(byte);
    let graph_label = to_graph_label(&label);
    atlas().find_vertex(&graph_label).map(|idx| {
        debug_assert!(idx < RESONANCE_CLASSES as usize);
        (idx as u8, label)
    })
}

fn to_graph_label(label: &AtlasLabel) -> GraphLabel {
    GraphLabel::new(
        label.e1 as u8,
        label.e2 as u8,
        label.e3 as u8,
        label.d45,
        label.e6 as u8,
        label.e7 as u8,
    )
}

fn to_foundation_label(label: GraphLabel) -> AtlasLabel {
    AtlasLabel::new(
        label.e1 as i8,
        label.e2 as i8,
        label.e3 as i8,
        label.d45,
        label.e6 as i8,
        label.e7 as i8,
    )
}

/// Classify a byte value to its R96 resonance class [0, 96)
///
/// This implements the R96 classifier from atlas-12288, which maps
/// 256 byte values to 96 resonance classes with 3/8 compression.
///
/// # C ABI
///
/// Called from JIT-compiled code as: `u8 atlas_core_r96_classify(u8 byte)`
///
/// # Example
///
/// ```
/// use atlas_core::r96_classify;
///
/// let byte_val = 42u8;
/// let class = r96_classify(byte_val);
/// assert!(class < 96);
/// ```
#[no_mangle]
pub extern "C" fn r96_classify(byte: u8) -> u8 {
    match classify_internal(byte) {
        Some((class_id, _)) => class_id,
        None => {
            debug_assert!(false, "byte {byte} did not map to a valid Atlas label");
            u8::MAX
        }
    }
}

/// Get the mirror pair of a resonance class
///
/// # C ABI
///
/// Called from JIT as: `u8 atlas_core_get_mirror_pair(u8 class_id)`
#[no_mangle]
pub extern "C" fn get_mirror_pair(class_id: u8) -> u8 {
    let atlas = atlas();
    let vertex = class_id as usize;
    if vertex < atlas.num_vertices() {
        atlas.mirror_pair(vertex) as u8
    } else {
        debug_assert!(false, "invalid class id: {class_id}");
        u8::MAX
    }
}

/// Check if a class is in the unity set
///
/// # C ABI
///
/// Called from JIT as: `bool atlas_core_is_unity(u8 class_id)`
#[no_mangle]
pub extern "C" fn is_unity(class_id: u8) -> bool {
    let atlas = atlas();
    let vertex = class_id as usize;
    if vertex >= atlas.num_vertices() {
        return false;
    }

    atlas.unity_positions().contains(&vertex)
}

/// Encode (page, byte) boundary coordinates into a single u32 value
///
/// Uses Φ (Phi) boundary encoding for compact representation of
/// coordinates on the (48 × 256) torus.
///
/// # C ABI
///
/// Called from JIT as: `u32 atlas_core_phi_encode(u8 page, u8 byte)`
#[no_mangle]
pub extern "C" fn phi_encode(page: u8, byte: u8) -> u32 {
    debug_assert!(page < PAGES as u8, "page must be < 48");
    // Encoding: upper 16 bits for byte, lower 16 bits for page
    ((byte as u32) << 16) | (page as u32)
}

/// FFI-safe coordinate pair
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct PhiPair {
    pub page: u8,
    pub byte: u8,
}

/// Decode a Φ-encoded coordinate back to (page, byte)
///
/// # C ABI
///
/// Called from JIT as: `PhiPair atlas_core_phi_decode(u32 encoded)`
///
/// # Returns
///
/// PhiPair with page and byte
#[no_mangle]
pub extern "C" fn phi_decode(encoded: u32) -> PhiPair {
    let page = (encoded & 0xFFFF) as u8;
    let byte = (encoded >> 16) as u8;
    PhiPair { page, byte }
}

/// Get linear index from coordinate
///
/// # C ABI
///
/// Called from JIT as: `usize atlas_core_linear_index(u8 page, u8 byte)`
#[no_mangle]
pub extern "C" fn linear_index(page: u8, byte: u8) -> usize {
    (page as usize * BYTES_PER_PAGE as usize) + byte as usize
}

/// Safe Rust types for ergonomic use (not part of C ABI).
///
/// Resonance class [0, 96)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ResonanceClass {
    id: u8,
    label: AtlasLabel,
}

impl ResonanceClass {
    /// Create a new resonance class, validating range
    pub fn new(value: u8) -> Result<Self> {
        if value >= RESONANCE_CLASSES as u8 {
            return Err(AtlasError::InvalidClassId(value as u32));
        }
        let atlas = atlas();
        let label = atlas.labels()[value as usize];
        Ok(Self {
            id: value,
            label: to_foundation_label(label),
        })
    }

    /// Create resonance class without validation (unsafe)
    ///
    /// # Safety
    ///
    /// Caller must ensure `value < 96`.
    pub unsafe fn new_unchecked(value: u8) -> Self {
        match Self::new(value) {
            Ok(class) => class,
            Err(_) => std::hint::unreachable_unchecked(),
        }
    }

    /// Construct directly from raw parts without validation.
    ///
    /// # Safety
    ///
    /// Caller must ensure both `value < 96` and `label` matches the canonical Atlas label at `value`.
    pub const unsafe fn from_parts_unchecked(value: u8, label: AtlasLabel) -> Self {
        Self { id: value, label }
    }

    /// Get the underlying u8 value
    pub const fn as_u8(self) -> u8 {
        self.id
    }

    /// Get the canonical class identifier.
    pub const fn id(self) -> u8 {
        self.id
    }

    /// Get the associated Atlas label.
    pub const fn label(self) -> AtlasLabel {
        self.label
    }

    /// Classify a byte to its resonance class
    pub fn classify(byte: u8) -> Self {
        let (id, label) =
            classify_internal(byte).unwrap_or_else(|| panic!("byte {byte} did not map to a valid Atlas class"));
        Self { id, label }
    }

    /// Get the mirror pair of this class
    pub fn mirror(self) -> Self {
        let atlas = atlas();
        let mirror = atlas.mirror_pair(self.id as usize) as u8;
        let label = atlas.labels()[mirror as usize];
        Self {
            id: mirror,
            label: to_foundation_label(label),
        }
    }

    /// Check if this class is in the unity set
    pub fn is_unity(self) -> bool {
        is_unity(self.id)
    }

    /// Degree of the resonance class within the Atlas graph.
    pub fn degree(self) -> usize {
        atlas().degree(self.id as usize)
    }

    /// Immediate neighbors for this resonance class.
    pub fn neighbors(self) -> Vec<ResonanceClass> {
        let atlas = atlas();
        atlas
            .neighbors(self.id as usize)
            .iter()
            .copied()
            .map(|idx| {
                let label = atlas.label(idx);
                ResonanceClass {
                    id: idx as u8,
                    label: to_foundation_label(label),
                }
            })
            .collect()
    }
}

/// Return the two unity resonance classes.
pub fn unity_positions() -> [ResonanceClass; 2] {
    let atlas = atlas();
    let unity = atlas.unity_positions();
    assert_eq!(unity.len(), 2, "Atlas must expose exactly two unity positions");

    let first = u8::try_from(unity[0]).expect("unity index fits in u8");
    let second = u8::try_from(unity[1]).expect("unity index fits in u8");

    [
        ResonanceClass::new(first).expect("unity class id valid"),
        ResonanceClass::new(second).expect("unity class id valid"),
    ]
}

/// Enumerate all mirror pairs without duplication (48 pairs).
pub fn mirror_pairs() -> Vec<(ResonanceClass, ResonanceClass)> {
    let atlas = atlas();
    let mut pairs = Vec::with_capacity(atlas.num_vertices() / 2);

    for idx in 0..atlas.num_vertices() {
        let mirror = atlas.mirror_pair(idx);
        if idx < mirror {
            let left = u8::try_from(idx).expect("class id fits in u8");
            let right = u8::try_from(mirror).expect("mirror id fits in u8");
            pairs.push((
                ResonanceClass::new(left).expect("class id valid"),
                ResonanceClass::new(right).expect("mirror id valid"),
            ));
        }
    }

    pairs
}

impl PartialOrd for ResonanceClass {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ResonanceClass {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

/// Boundary coordinate (page, byte) on the (48 × 256) torus
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PhiCoordinate {
    pub page: u8,
    pub byte: u8,
}

impl PhiCoordinate {
    /// Create a new coordinate
    pub fn new(page: u8, byte: u8) -> Result<Self> {
        if page >= PAGES as u8 {
            return Err(AtlasError::InvalidPage(page as u32));
        }
        Ok(Self { page, byte })
    }

    /// Create coordinate without validation (unsafe)
    ///
    /// # Safety
    ///
    /// Caller must ensure page < 48
    pub const unsafe fn new_unchecked(page: u8, byte: u8) -> Self {
        Self { page, byte }
    }

    /// Encode this coordinate using Φ encoding
    pub fn encode(self) -> u32 {
        phi_encode(self.page, self.byte)
    }

    /// Decode from Φ-encoded value
    pub fn decode(encoded: u32) -> Self {
        let pair = phi_decode(encoded);
        Self {
            page: pair.page,
            byte: pair.byte,
        }
    }

    /// Get linear index into the 12,288-element array
    pub fn linear_index(self) -> usize {
        linear_index(self.page, self.byte)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_r96_classify_range() {
        for byte in 0..=255u8 {
            let class = r96_classify(byte);
            assert!(class < 96, "class {} out of range for byte {}", class, byte);
        }
    }

    #[test]
    fn test_resonance_class_label_lookup() {
        for byte in 0..=255u8 {
            let class = ResonanceClass::classify(byte);
            let atlas = atlas();
            let expected = atlas.label(class.id() as usize);
            assert_eq!(to_foundation_label(expected), class.label());
        }
    }

    #[test]
    fn test_phi_encode_decode_roundtrip() {
        for page in 0..PAGES as u8 {
            for byte in (0..=255u8).step_by(17) {
                let encoded = phi_encode(page, byte);
                let pair = phi_decode(encoded);
                assert_eq!(page, pair.page);
                assert_eq!(byte, pair.byte);
            }
        }
    }

    #[test]
    fn test_mirror_symmetry() {
        for class_id in 0..96u8 {
            let mirror = get_mirror_pair(class_id);
            let mirror_mirror = get_mirror_pair(mirror);
            assert_eq!(class_id, mirror_mirror);
        }
    }

    #[test]
    fn test_unity_detection() {
        let atlas = atlas();
        let unity: std::collections::HashSet<_> = atlas.unity_positions().iter().map(|&idx| idx as u8).collect();

        for class_id in 0..96u8 {
            let expected = unity.contains(&class_id);
            assert_eq!(expected, is_unity(class_id), "unity mismatch for class {class_id}");
        }
    }

    #[test]
    fn test_resonance_class_degree_matches_atlas() {
        let atlas = atlas();
        for class_id in 0..96u8 {
            let class = ResonanceClass::new(class_id).unwrap();
            assert_eq!(class.degree(), atlas.degree(class_id as usize));
        }
    }

    #[test]
    fn test_resonance_class_neighbors_match() {
        let atlas = atlas();
        for class_id in 0..96u8 {
            let class = ResonanceClass::new(class_id).unwrap();
            let neighbors = class.neighbors();
            let atlas_neighbors = atlas.neighbors(class_id as usize);

            assert_eq!(neighbors.len(), atlas_neighbors.len());
            for neighbor in neighbors {
                assert!(atlas_neighbors.contains(&(neighbor.id() as usize)));
            }
        }
    }

    #[test]
    fn test_unity_positions_helper() {
        let atlas = atlas();
        let positions = unity_positions();
        let atlas_unity: std::collections::HashSet<_> = atlas.unity_positions().iter().map(|&idx| idx as u8).collect();

        assert_eq!(positions.len(), 2);
        for class in positions {
            assert!(atlas_unity.contains(&class.id()));
        }
    }

    #[test]
    fn test_mirror_pairs_cover_vertices() {
        let atlas = atlas();
        let pairs = mirror_pairs();
        assert_eq!(pairs.len(), atlas.num_vertices() / 2);

        let mut seen = std::collections::HashSet::new();
        for (a, b) in pairs {
            assert!(seen.insert(a.id()));
            assert!(seen.insert(b.id()));
            assert!(atlas.is_mirror_pair(a.id() as usize, b.id() as usize));
        }

        assert_eq!(seen.len(), atlas.num_vertices());
    }

    #[test]
    fn test_linear_index() {
        assert_eq!(linear_index(0, 0), 0);
        assert_eq!(linear_index(0, 255), 255);
        assert_eq!(linear_index(1, 0), 256);
        assert_eq!(linear_index(47, 255), 12287);
    }
}
