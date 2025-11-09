//! Atlas Invariant Enforcement
//!
//! This module provides functions to check and enforce Atlas mathematical invariants.
//! These are called by the JIT engine to ensure correctness is never compromised.
//!
//! # C-Compatible Structures
//!
//! This module exposes lightweight `#[repr(C)]` structures for resonance metadata and
//! invariants so CUDA kernels can consume Atlas facts without depending on Rust-specific
//! layouts. All structures use fixed-size types suitable for FFI.

use crate::{AtlasError, Result, PHASE_MODULUS, RESONANCE_CLASSES};
use num_rational::Ratio;
use num_traits::Zero;

/// Rational value used for unity neutrality checks across the ABI boundary.
///
/// # Representation
///
/// The value is interpreted as `numer / denom`. Denominators must be non-zero;
/// the sign is canonicalised by `num_rational::Ratio` when converted.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AtlasRatio {
    pub numer: i64,
    pub denom: i64,
}

impl AtlasRatio {
    /// Construct a new ratio. Caller must ensure `denom != 0`.
    pub const fn new_raw(numer: i64, denom: i64) -> Self {
        Self { numer, denom }
    }

    pub fn to_ratio(self) -> Result<Ratio<i64>> {
        if self.denom == 0 {
            return Err(AtlasError::InvalidDenominator(self.denom));
        }

        Ok(Ratio::new(self.numer, self.denom))
    }
}

/// C-compatible 96-bit class mask for CUDA kernels.
///
/// Represents which resonance classes (0-95) are active. Uses fixed-size
/// integers suitable for device code.
///
/// # Layout
///
/// - `low`: bits 0-63 represent classes 0-63
/// - `high`: bits 0-31 represent classes 64-95
///
/// # Ownership
///
/// This is a plain-old-data (POD) type that can be safely copied.
/// No heap allocations or lifetime constraints.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AtlasClassMask {
    pub low: u64,
    pub high: u32,
}

impl AtlasClassMask {
    /// Create empty mask (no classes active)
    pub const fn empty() -> Self {
        Self { low: 0, high: 0 }
    }

    /// Create mask with all classes active
    pub const fn all() -> Self {
        Self {
            low: u64::MAX,
            high: 0xFFFF_FFFF,
        }
    }

    /// Check if a class is set in the mask
    pub const fn is_set(&self, class_id: u8) -> bool {
        if class_id < 64 {
            (self.low & (1u64 << class_id)) != 0
        } else if (class_id as u32) < RESONANCE_CLASSES {
            (self.high & (1u32 << (class_id - 64))) != 0
        } else {
            false
        }
    }

    /// Count number of active classes
    pub const fn count(&self) -> u32 {
        self.low.count_ones() + self.high.count_ones()
    }
}

/// C-compatible phase window for CUDA kernels.
///
/// Defines the phase window [begin, begin+span) modulo 768 during which
/// a kernel can execute.
///
/// # Ownership
///
/// Plain-old-data type with no heap allocations.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AtlasPhaseWindow {
    pub begin: u32,
    pub span: u32,
}

impl AtlasPhaseWindow {
    /// Create window covering all phases
    pub const fn full() -> Self {
        Self {
            begin: 0,
            span: PHASE_MODULUS,
        }
    }

    /// Check if a phase is within this window (mod 768)
    pub const fn contains(&self, phase: u32) -> bool {
        let phase = phase % PHASE_MODULUS;
        if self.span >= PHASE_MODULUS {
            return true;
        }

        let end = (self.begin + self.span) % PHASE_MODULUS;
        if self.begin < end {
            // No wrap: [begin, end)
            phase >= self.begin && phase < end
        } else {
            // Wraps: [begin, 768) ∪ [0, end)
            phase >= self.begin || phase < end
        }
    }
}

/// C-compatible boundary footprint for CUDA kernels.
///
/// Defines the (page, byte) coordinate range a kernel accesses.
///
/// # Ownership
///
/// Plain-old-data type with no heap allocations.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AtlasBoundaryFootprint {
    pub page_min: u8,
    pub page_max: u8,
    pub byte_min: u8,
    pub byte_max: u8,
}

impl AtlasBoundaryFootprint {
    /// Create footprint covering entire boundary
    pub const fn full() -> Self {
        Self {
            page_min: 0,
            page_max: 47,
            byte_min: 0,
            byte_max: 255,
        }
    }

    /// Check if (page, byte) is within this footprint
    pub const fn contains(&self, page: u8, byte: u8) -> bool {
        page >= self.page_min && page <= self.page_max && byte >= self.byte_min && byte <= self.byte_max
    }
}

/// C-compatible mirror pair for CUDA kernels.
///
/// Represents a pair of resonance classes that are mirrors of each other.
///
/// # Ownership
///
/// Plain-old-data type with no heap allocations.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AtlasMirrorPair {
    pub class_a: u8,
    pub class_b: u8,
}

impl AtlasMirrorPair {
    /// Create a new mirror pair
    pub const fn new(class_a: u8, class_b: u8) -> Self {
        Self { class_a, class_b }
    }

    /// Check if a class is in this pair
    pub const fn contains(&self, class_id: u8) -> bool {
        self.class_a == class_id || self.class_b == class_id
    }

    /// Get the mirror of a class in this pair
    pub const fn mirror_of(&self, class_id: u8) -> Option<u8> {
        if self.class_a == class_id {
            Some(self.class_b)
        } else if self.class_b == class_id {
            Some(self.class_a)
        } else {
            None
        }
    }
}

/// Check unity neutrality: sum of resonance deltas must be zero
///
/// # C ABI
///
/// Called from JIT as: `bool atlas_core_check_unity_neutrality(const AtlasRatio* deltas, usize count)`
///
/// # Safety
///
/// `deltas` must point to an array of at least `count` valid [`AtlasRatio`] values for
/// the duration of the call.
#[no_mangle]
pub unsafe extern "C" fn check_unity_neutrality(deltas: *const AtlasRatio, count: usize) -> bool {
    if deltas.is_null() {
        return false;
    }

    let slice = std::slice::from_raw_parts(deltas, count);
    verify_unity_neutrality(slice).is_ok()
}

/// Validate phase value is in [0, 768)
///
/// # C ABI
///
/// Called from JIT as: `bool atlas_core_check_phase(u32 phase)`
#[no_mangle]
pub extern "C" fn check_phase(phase: u32) -> bool {
    phase < PHASE_MODULUS
}

/// Check if phase is within a window [begin, end)
///
/// # C ABI
///
/// Called from JIT as: `bool atlas_core_check_phase_window(u32 phase, u32 begin, u32 end)`
#[no_mangle]
pub extern "C" fn check_phase_window(phase: u32, begin: u32, end: u32) -> bool {
    if !check_phase(phase) || !check_phase(begin) || !check_phase(end) {
        return false;
    }

    if begin <= end {
        phase >= begin && phase < end
    } else {
        // Wrapped window
        phase >= begin || phase < end
    }
}

/// Get mirror pair for a resonance class
///
/// # C ABI
///
/// Called from JIT/CUDA as: `AtlasMirrorPair atlas_core_get_mirror_pair(u8 class_id)`
///
/// # Returns
///
/// Mirror pair containing the class and its mirror. If class_id is invalid (>= 96),
/// returns a pair with both values set to 0xFF.
#[no_mangle]
pub extern "C" fn get_mirror_pair_c(class_id: u8) -> AtlasMirrorPair {
    if class_id >= RESONANCE_CLASSES as u8 {
        return AtlasMirrorPair::new(0xFF, 0xFF);
    }

    let mirror = crate::get_mirror_pair(class_id);
    if mirror >= RESONANCE_CLASSES as u8 {
        return AtlasMirrorPair::new(0xFF, 0xFF);
    }

    AtlasMirrorPair::new(class_id, mirror)
}

/// Populate all mirror pairs into a pre-allocated array
///
/// # C ABI
///
/// Called from CUDA as: `void atlas_core_populate_mirror_pairs(AtlasMirrorPair* pairs, usize capacity)`
///
/// # Safety
///
/// `pairs` must point to an array with at least `capacity` elements.
/// Returns the actual number of pairs written. Since there are 96 classes forming 48 pairs,
/// the caller should provide capacity >= 48.
#[no_mangle]
pub unsafe extern "C" fn populate_mirror_pairs(pairs: *mut AtlasMirrorPair, capacity: usize) -> usize {
    if pairs.is_null() || capacity == 0 {
        return 0;
    }

    let slice = std::slice::from_raw_parts_mut(pairs, capacity);
    let mut written = 0;

    for class_id in 0..RESONANCE_CLASSES as u8 {
        if written >= capacity {
            break;
        }

        let mirror = crate::get_mirror_pair(class_id);
        // Only write each pair once (when class_id < mirror)
        if class_id < mirror && mirror < RESONANCE_CLASSES as u8 {
            slice[written] = AtlasMirrorPair::new(class_id, mirror);
            written += 1;
        }
    }

    written
}

/// Check if a class is in the unity set
///
/// # C ABI
///
/// Called from CUDA as: `bool atlas_core_is_unity_class(u8 class_id)`
#[no_mangle]
pub extern "C" fn is_unity_class(class_id: u8) -> bool {
    crate::is_unity(class_id)
}

/// Populate unity classes into a pre-allocated array
///
/// # C ABI
///
/// Called from CUDA as: `usize atlas_core_populate_unity_classes(u8* classes, usize capacity)`
///
/// # Safety
///
/// `classes` must point to an array with at least `capacity` elements.
/// Returns the actual number of unity classes written (should be 2).
#[no_mangle]
pub unsafe extern "C" fn populate_unity_classes(classes: *mut u8, capacity: usize) -> usize {
    if classes.is_null() || capacity == 0 {
        return 0;
    }

    let slice = std::slice::from_raw_parts_mut(classes, capacity);
    let unity = crate::unity_positions();
    let count = std::cmp::min(unity.len(), capacity);

    for (i, class) in unity.iter().take(count).enumerate() {
        slice[i] = class.as_u8();
    }

    count
}

/// Check if class mask overlaps with another
///
/// # C ABI
///
/// Called from CUDA as: `bool atlas_core_class_mask_overlaps(const AtlasClassMask* a, const AtlasClassMask* b)`
///
/// # Safety
///
/// Both pointers must be valid for the duration of the call.
#[no_mangle]
pub unsafe extern "C" fn class_mask_overlaps(a: *const AtlasClassMask, b: *const AtlasClassMask) -> bool {
    if a.is_null() || b.is_null() {
        return false;
    }

    let a = &*a;
    let b = &*b;
    (a.low & b.low) != 0 || (a.high & b.high) != 0
}

/// Check if phase is within window
///
/// # C ABI
///
/// Called from CUDA as: `bool atlas_core_phase_window_contains(const AtlasPhaseWindow* window, u32 phase)`
///
/// # Safety
///
/// `window` must be valid for the duration of the call.
#[no_mangle]
pub unsafe extern "C" fn phase_window_contains(window: *const AtlasPhaseWindow, phase: u32) -> bool {
    if window.is_null() {
        return false;
    }

    let window = &*window;
    window.contains(phase)
}

/// Safe Rust API.
///
/// Check unity neutrality for ratios provided via the ABI.
pub fn verify_unity_neutrality(deltas: &[AtlasRatio]) -> Result<()> {
    let sum = deltas
        .iter()
        .try_fold(Ratio::new(0, 1), |acc, delta| Ok(acc + delta.to_ratio()?))?;
    if sum.is_zero() {
        Ok(())
    } else {
        Err(AtlasError::UnityNeutralityViolated(sum))
    }
}

/// Check unity neutrality using exact rational arithmetic.
pub fn verify_unity_neutrality_exact(deltas: &[Ratio<i64>]) -> Result<()> {
    let sum = deltas.iter().cloned().fold(Ratio::new(0, 1), |acc, term| acc + term);
    if sum.is_zero() {
        Ok(())
    } else {
        Err(AtlasError::UnityNeutralityViolated(sum))
    }
}

/// Validate phase value
pub fn verify_phase(phase: u32) -> Result<()> {
    if phase < PHASE_MODULUS {
        Ok(())
    } else {
        Err(AtlasError::InvalidPhase(phase))
    }
}

/// Verify phase is in window
pub fn verify_phase_window(phase: u32, begin: u32, end: u32) -> Result<()> {
    verify_phase(phase)?;
    verify_phase(begin)?;
    verify_phase(end)?;

    let in_window = if begin <= end {
        phase >= begin && phase < end
    } else {
        phase >= begin || phase < end
    };

    if in_window {
        Ok(())
    } else {
        Err(AtlasError::PhaseWindowIncompatible {
            current: phase,
            begin,
            end,
        })
    }
}

//
// Launch-Time Validation APIs (AC3)
//
// These APIs provide precomputed lookup tables and minimal data structures
// for efficient on-device or host-side launch validation.
//

/// Compact launch validation data package
///
/// This structure contains precomputed lookup tables for fast launch-time
/// validation of Atlas invariants. It's designed to be uploaded to CUDA
/// constant memory or consulted by host validation code.
///
/// # Usage
///
/// ```rust
/// use atlas_core::LaunchValidationData;
///
/// // Create validation data (precompute at build time)
/// let validation_data = LaunchValidationData::new();
///
/// // Query at launch time - O(1) lookups
/// let mirror = validation_data.get_mirror(10).expect("Valid class");
/// assert!(mirror < 96); // Mirror is valid
///
/// // Verify mirror symmetry
/// assert_eq!(validation_data.get_mirror(mirror), Some(10));
///
/// // Check if kernel is mirror-safe (all classes paired)
/// let classes = [10, mirror];
/// assert!(validation_data.are_mirror_pairs(&classes));
/// ```
///
/// # Memory Layout
///
/// The structure uses exactly 112 bytes:
/// - `unity_flags`: 96 bits (12 bytes) for unity class lookup
/// - `mirror_table`: 96 bytes for mirror pair lookup
/// - Total: 108 bytes + 4 bytes padding = 112 bytes
///
/// This fits comfortably in CUDA constant memory alongside other metadata.
#[repr(C)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LaunchValidationData {
    /// Bit flags for unity class membership (96 classes = 12 bytes)
    /// Bit i set means class i is a unity class
    unity_flags: [u8; 12],
    /// Mirror lookup table: mirror_table[i] = mirror of class i
    /// Value 0xFF indicates invalid/no mirror
    mirror_table: [u8; 96],
}

impl LaunchValidationData {
    /// Create new validation data with precomputed lookup tables
    pub fn new() -> Self {
        let mut data = Self {
            unity_flags: [0; 12],
            mirror_table: [0xFF; 96],
        };

        // Populate unity flags
        let unity_classes = crate::unity_positions();
        for class in unity_classes {
            let class_id = class.as_u8();
            let byte_idx = (class_id / 8) as usize;
            let bit_idx = class_id % 8;
            data.unity_flags[byte_idx] |= 1 << bit_idx;
        }

        // Populate mirror table
        for class_id in 0..RESONANCE_CLASSES as u8 {
            let mirror = crate::get_mirror_pair(class_id);
            if mirror < RESONANCE_CLASSES as u8 {
                data.mirror_table[class_id as usize] = mirror;
            }
        }

        data
    }

    /// Check if a class is in the unity set (O(1) lookup)
    ///
    /// # Example
    /// ```
    /// # use atlas_core::{LaunchValidationData, unity_positions};
    /// let data = LaunchValidationData::new();
    /// let unity = unity_positions();
    /// assert!(data.is_unity_class(unity[0].as_u8()));
    /// assert!(data.is_unity_class(unity[1].as_u8()));
    /// ```
    pub const fn is_unity_class(&self, class_id: u8) -> bool {
        if class_id >= RESONANCE_CLASSES as u8 {
            return false;
        }
        let byte_idx = (class_id / 8) as usize;
        let bit_idx = class_id % 8;
        (self.unity_flags[byte_idx] & (1 << bit_idx)) != 0
    }

    /// Get mirror of a class (O(1) lookup)
    ///
    /// Returns `None` if class_id is invalid.
    ///
    /// # Example
    /// ```
    /// # use atlas_core::LaunchValidationData;
    /// let data = LaunchValidationData::new();
    /// let mirror = data.get_mirror(10).unwrap();
    /// assert_eq!(data.get_mirror(mirror), Some(10)); // Symmetric
    /// ```
    pub const fn get_mirror(&self, class_id: u8) -> Option<u8> {
        if class_id >= RESONANCE_CLASSES as u8 {
            return None;
        }
        let mirror = self.mirror_table[class_id as usize];
        if mirror == 0xFF {
            None
        } else {
            Some(mirror)
        }
    }

    /// Check if all classes in a set form valid mirror pairs
    ///
    /// A kernel is "mirror-safe" if all its classes appear in pairs
    /// (each class's mirror is also in the set).
    ///
    /// # Example
    /// ```
    /// # use atlas_core::LaunchValidationData;
    /// let data = LaunchValidationData::new();
    ///
    /// // Get a mirror pair dynamically
    /// let class_a = 10u8;
    /// let class_b = data.get_mirror(class_a).unwrap();
    ///
    /// // Mirror pair: safe
    /// assert!(data.are_mirror_pairs(&[class_a, class_b]));
    ///
    /// // Odd number of classes: cannot be mirror-safe
    /// assert!(!data.are_mirror_pairs(&[10]));
    /// ```
    pub fn are_mirror_pairs(&self, classes: &[u8]) -> bool {
        if classes.is_empty() {
            return true;
        }

        // Must have even number of classes to form pairs
        if !classes.len().is_multiple_of(2) {
            return false;
        }

        let mut paired = [false; RESONANCE_CLASSES as usize];

        for &class_id in classes {
            if class_id >= RESONANCE_CLASSES as u8 {
                return false;
            }
            paired[class_id as usize] = true;
        }

        // Check that for each class, its mirror is also present
        for &class_id in classes {
            if let Some(mirror) = self.get_mirror(class_id) {
                if !paired[mirror as usize] {
                    return false;
                }
            } else {
                return false;
            }
        }

        true
    }

    /// Validate launch against current phase
    ///
    /// Returns `true` if the phase is within the given window.
    /// This is a convenience wrapper around `AtlasPhaseWindow::contains`.
    ///
    /// # Example
    /// ```
    /// # use atlas_core::{LaunchValidationData, AtlasPhaseWindow};
    /// let data = LaunchValidationData::new();
    /// let window = AtlasPhaseWindow { begin: 100, span: 50 };
    ///
    /// assert!(data.is_phase_valid(125, &window));
    /// assert!(!data.is_phase_valid(200, &window));
    /// ```
    pub const fn is_phase_valid(&self, phase: u32, window: &AtlasPhaseWindow) -> bool {
        window.contains(phase)
    }

    /// Check if two class masks have conflicts
    ///
    /// Returns `true` if the masks share any classes, indicating potential
    /// scheduling conflicts.
    ///
    /// # Example
    /// ```
    /// # use atlas_core::{LaunchValidationData, AtlasClassMask};
    /// let data = LaunchValidationData::new();
    ///
    /// let mut mask_a = AtlasClassMask::empty();
    /// mask_a.low = 1 << 10; // Class 10
    ///
    /// let mut mask_b = AtlasClassMask::empty();
    /// mask_b.low = 1 << 10; // Also class 10
    ///
    /// assert!(data.masks_conflict(&mask_a, &mask_b));
    ///
    /// mask_b.low = 1 << 20; // Different class
    /// assert!(!data.masks_conflict(&mask_a, &mask_b));
    /// ```
    pub const fn masks_conflict(&self, mask_a: &AtlasClassMask, mask_b: &AtlasClassMask) -> bool {
        (mask_a.low & mask_b.low) != 0 || (mask_a.high & mask_b.high) != 0
    }

    /// Get size in bytes for memory allocation planning
    ///
    /// Returns the exact size of the structure for upload to device memory.
    pub const fn size_bytes() -> usize {
        std::mem::size_of::<Self>()
    }
}

impl Default for LaunchValidationData {
    fn default() -> Self {
        Self::new()
    }
}

/// C ABI: Create launch validation data
///
/// Allocates and populates a validation data structure.
/// Caller is responsible for freeing with `launch_validation_data_free`.
///
/// # Safety
///
/// The returned pointer must be freed exactly once using
/// `launch_validation_data_free`.
#[no_mangle]
pub extern "C" fn launch_validation_data_new() -> *mut LaunchValidationData {
    Box::into_raw(Box::new(LaunchValidationData::new()))
}

/// C ABI: Free launch validation data
///
/// # Safety
///
/// `ptr` must be a valid pointer returned by `launch_validation_data_new`
/// and must not be used after this call.
#[no_mangle]
pub unsafe extern "C" fn launch_validation_data_free(ptr: *mut LaunchValidationData) {
    if !ptr.is_null() {
        drop(Box::from_raw(ptr));
    }
}

/// C ABI: Check if class is unity
///
/// # Safety
///
/// `data` must be a valid pointer to `LaunchValidationData`.
#[no_mangle]
pub unsafe extern "C" fn launch_validation_is_unity(data: *const LaunchValidationData, class_id: u8) -> bool {
    if data.is_null() {
        return false;
    }
    (*data).is_unity_class(class_id)
}

/// C ABI: Get mirror of class
///
/// Returns the mirror class, or 0xFF if invalid.
///
/// # Safety
///
/// `data` must be a valid pointer to `LaunchValidationData`.
#[no_mangle]
pub unsafe extern "C" fn launch_validation_get_mirror(data: *const LaunchValidationData, class_id: u8) -> u8 {
    if data.is_null() {
        return 0xFF;
    }
    (*data).get_mirror(class_id).unwrap_or(0xFF)
}

/// C ABI: Check if phase is valid for window
///
/// # Safety
///
/// Both pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn launch_validation_is_phase_valid(
    data: *const LaunchValidationData,
    phase: u32,
    window: *const AtlasPhaseWindow,
) -> bool {
    if data.is_null() || window.is_null() {
        return false;
    }
    (*data).is_phase_valid(phase, &*window)
}

/// C ABI: Check if masks conflict
///
/// # Safety
///
/// All pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn launch_validation_masks_conflict(
    data: *const LaunchValidationData,
    mask_a: *const AtlasClassMask,
    mask_b: *const AtlasClassMask,
) -> bool {
    if data.is_null() || mask_a.is_null() || mask_b.is_null() {
        return false;
    }
    (*data).masks_conflict(&*mask_a, &*mask_b)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unity_neutrality() {
        let deltas = [
            AtlasRatio::new_raw(1, 1),
            AtlasRatio::new_raw(-1, 1),
            AtlasRatio::new_raw(1, 2),
            AtlasRatio::new_raw(-1, 2),
        ];
        assert!(verify_unity_neutrality(&deltas).is_ok());

        let bad_deltas = [AtlasRatio::new_raw(1, 2), AtlasRatio::new_raw(1, 3)];
        assert!(verify_unity_neutrality(&bad_deltas).is_err());
    }

    #[test]
    fn test_unity_neutrality_exact() {
        use num_rational::Ratio;

        let deltas = vec![Ratio::new(1, 3), Ratio::new(-2, 6)];
        assert!(verify_unity_neutrality_exact(&deltas).is_ok());

        let bad = vec![Ratio::new(1, 2), Ratio::new(1, 3)];
        assert!(verify_unity_neutrality_exact(&bad).is_err());
    }

    #[test]
    fn test_phase_validation() {
        assert!(verify_phase(0).is_ok());
        assert!(verify_phase(767).is_ok());
        assert!(verify_phase(768).is_err());
    }

    #[test]
    fn test_phase_window() {
        // Normal window
        assert!(verify_phase_window(100, 50, 150).is_ok());
        assert!(verify_phase_window(49, 50, 150).is_err());
        assert!(verify_phase_window(150, 50, 150).is_err());

        // Wrapped window
        assert!(verify_phase_window(700, 650, 50).is_ok());
        assert!(verify_phase_window(10, 650, 50).is_ok());
        assert!(verify_phase_window(100, 650, 50).is_err());
    }

    // New tests for C-compatible structures

    #[test]
    fn test_atlas_class_mask_layout() {
        // Verify struct has expected size and alignment
        assert_eq!(std::mem::size_of::<AtlasClassMask>(), 16); // 8 + 4 + padding
        assert_eq!(std::mem::align_of::<AtlasClassMask>(), 8);
    }

    #[test]
    fn test_atlas_class_mask_empty_and_all() {
        let empty = AtlasClassMask::empty();
        assert_eq!(empty.count(), 0);
        assert!(!empty.is_set(0));
        assert!(!empty.is_set(50));
        assert!(!empty.is_set(95));

        let all = AtlasClassMask::all();
        assert_eq!(all.count(), 96);
        for i in 0..96 {
            assert!(all.is_set(i));
        }
    }

    #[test]
    fn test_atlas_class_mask_set_check() {
        let mut mask = AtlasClassMask::empty();

        // Test low bits (0-63)
        mask.low = 1u64 << 10;
        assert!(mask.is_set(10));
        assert!(!mask.is_set(11));

        // Test high bits (64-95)
        mask.high = 1u32 << 5; // Class 69
        assert!(mask.is_set(69));
        assert!(!mask.is_set(70));
    }

    #[test]
    fn test_atlas_phase_window_layout() {
        assert_eq!(std::mem::size_of::<AtlasPhaseWindow>(), 8); // Two u32s
        assert_eq!(std::mem::align_of::<AtlasPhaseWindow>(), 4);
    }

    #[test]
    fn test_atlas_phase_window_contains() {
        let window = AtlasPhaseWindow { begin: 100, span: 50 };
        assert!(window.contains(100));
        assert!(window.contains(125));
        assert!(window.contains(149));
        assert!(!window.contains(150));
        assert!(!window.contains(99));
    }

    #[test]
    fn test_atlas_phase_window_wraps() {
        // Window [700, 50) wraps: [700, 768) ∪ [0, 50)
        let window = AtlasPhaseWindow { begin: 700, span: 118 };
        assert!(window.contains(700));
        assert!(window.contains(750));
        assert!(window.contains(0));
        assert!(window.contains(49));
        assert!(!window.contains(50));
        assert!(!window.contains(699));
    }

    #[test]
    fn test_atlas_phase_window_full() {
        let full = AtlasPhaseWindow::full();
        assert_eq!(full.begin, 0);
        assert_eq!(full.span, PHASE_MODULUS);

        // Full window should contain all phases
        for phase in 0..768 {
            assert!(full.contains(phase));
        }
    }

    #[test]
    fn test_atlas_boundary_footprint_layout() {
        assert_eq!(std::mem::size_of::<AtlasBoundaryFootprint>(), 4); // Four u8s
        assert_eq!(std::mem::align_of::<AtlasBoundaryFootprint>(), 1);
    }

    #[test]
    fn test_atlas_boundary_footprint_contains() {
        let footprint = AtlasBoundaryFootprint {
            page_min: 10,
            page_max: 20,
            byte_min: 50,
            byte_max: 150,
        };

        assert!(footprint.contains(15, 100));
        assert!(footprint.contains(10, 50)); // Boundaries inclusive
        assert!(footprint.contains(20, 150));
        assert!(!footprint.contains(9, 100));
        assert!(!footprint.contains(21, 100));
        assert!(!footprint.contains(15, 49));
        assert!(!footprint.contains(15, 151));
    }

    #[test]
    fn test_atlas_boundary_footprint_full() {
        let full = AtlasBoundaryFootprint::full();
        assert_eq!(full.page_min, 0);
        assert_eq!(full.page_max, 47);
        assert_eq!(full.byte_min, 0);
        assert_eq!(full.byte_max, 255);

        // Should contain all valid coordinates
        assert!(full.contains(0, 0));
        assert!(full.contains(47, 255));
        assert!(full.contains(23, 128));
    }

    #[test]
    fn test_atlas_mirror_pair_layout() {
        assert_eq!(std::mem::size_of::<AtlasMirrorPair>(), 2); // Two u8s
        assert_eq!(std::mem::align_of::<AtlasMirrorPair>(), 1);
    }

    #[test]
    fn test_atlas_mirror_pair_operations() {
        let pair = AtlasMirrorPair::new(10, 42);

        assert!(pair.contains(10));
        assert!(pair.contains(42));
        assert!(!pair.contains(20));

        assert_eq!(pair.mirror_of(10), Some(42));
        assert_eq!(pair.mirror_of(42), Some(10));
        assert_eq!(pair.mirror_of(20), None);
    }

    #[test]
    fn test_get_mirror_pair_c() {
        // Valid class
        let pair = get_mirror_pair_c(10);
        assert_eq!(pair.class_a, 10);
        assert!(pair.class_b < 96);

        // Verify symmetry
        let mirror = crate::get_mirror_pair(10);
        assert_eq!(pair.class_b, mirror);

        // Invalid class
        let invalid = get_mirror_pair_c(96);
        assert_eq!(invalid.class_a, 0xFF);
        assert_eq!(invalid.class_b, 0xFF);
    }

    #[test]
    fn test_populate_mirror_pairs() {
        let mut pairs = vec![AtlasMirrorPair::new(0, 0); 48];
        let count = unsafe { populate_mirror_pairs(pairs.as_mut_ptr(), pairs.len()) };

        assert_eq!(count, 48); // 96 classes form 48 pairs

        // Verify all pairs are unique and valid
        for pair in pairs.iter().take(count) {
            assert!(pair.class_a < 96);
            assert!(pair.class_b < 96);
            assert_ne!(pair.class_a, pair.class_b);

            // Verify they are actually mirrors
            let mirror = crate::get_mirror_pair(pair.class_a);
            assert_eq!(pair.class_b, mirror);
        }
    }

    #[test]
    fn test_populate_unity_classes() {
        let mut classes = vec![0u8; 10];
        let count = unsafe { populate_unity_classes(classes.as_mut_ptr(), classes.len()) };

        assert_eq!(count, 2); // Two unity classes

        // Verify both are valid unity classes
        assert!(crate::is_unity(classes[0]));
        assert!(crate::is_unity(classes[1]));
        assert_ne!(classes[0], classes[1]);
    }

    #[test]
    fn test_is_unity_class() {
        let unity = crate::unity_positions();

        // Unity classes should return true
        assert!(is_unity_class(unity[0].as_u8()));
        assert!(is_unity_class(unity[1].as_u8()));

        // Find a non-unity class
        for i in 0..96u8 {
            if !is_unity_class(i) {
                // Verify it's actually not unity
                assert!(!crate::is_unity(i));
                break;
            }
        }
    }

    #[test]
    fn test_class_mask_overlaps() {
        let mut mask_a = AtlasClassMask::empty();
        mask_a.low = (1u64 << 10) | (1u64 << 20);

        let mut mask_b = AtlasClassMask::empty();
        mask_b.low = (1u64 << 20) | (1u64 << 30);

        let overlaps = unsafe { class_mask_overlaps(&mask_a, &mask_b) };
        assert!(overlaps); // Both have class 20

        let mut mask_c = AtlasClassMask::empty();
        mask_c.low = 1u64 << 50;

        let no_overlap = unsafe { class_mask_overlaps(&mask_a, &mask_c) };
        assert!(!no_overlap);
    }

    #[test]
    fn test_phase_window_contains_c() {
        let window = AtlasPhaseWindow { begin: 100, span: 50 };

        assert!(unsafe { phase_window_contains(&window, 125) });
        assert!(!unsafe { phase_window_contains(&window, 200) });
    }

    #[test]
    fn test_atlas_ratio_layout() {
        // Verify existing AtlasRatio is properly C-compatible
        assert_eq!(std::mem::size_of::<AtlasRatio>(), 16); // Two i64s
        assert_eq!(std::mem::align_of::<AtlasRatio>(), 8);
    }

    // Tests for LaunchValidationData (AC3)

    #[test]
    fn test_launch_validation_data_size() {
        // Verify size fits in constant memory
        let size = LaunchValidationData::size_bytes();
        assert!(size <= 256, "Validation data too large: {} bytes", size);
        assert_eq!(std::mem::size_of::<LaunchValidationData>(), size);
    }

    #[test]
    fn test_launch_validation_data_unity_lookup() {
        let data = LaunchValidationData::new();
        let unity_classes = crate::unity_positions();

        // Unity classes should return true
        for class in unity_classes {
            let class_id = class.as_u8();
            assert!(data.is_unity_class(class_id), "Class {} should be unity", class_id);
        }

        // Find non-unity classes and verify they return false
        let mut found_non_unity = false;
        for i in 0..96u8 {
            if !data.is_unity_class(i) {
                found_non_unity = true;
                // Double-check with authoritative source
                assert!(!crate::is_unity(i), "Class {} marked non-unity but is unity", i);
            }
        }
        assert!(found_non_unity, "Should have non-unity classes");
    }

    #[test]
    fn test_launch_validation_data_mirror_lookup() {
        let data = LaunchValidationData::new();

        // Test all classes have valid mirrors
        for class_id in 0..96u8 {
            let mirror = data.get_mirror(class_id);
            assert!(mirror.is_some(), "Class {} has no mirror", class_id);

            let mirror = mirror.unwrap();
            assert!(mirror < 96, "Mirror {} out of range", mirror);

            // Verify symmetry
            let reverse_mirror = data.get_mirror(mirror);
            assert_eq!(
                reverse_mirror,
                Some(class_id),
                "Mirror symmetry broken for class {}",
                class_id
            );

            // Verify against authoritative source
            let expected_mirror = crate::get_mirror_pair(class_id);
            assert_eq!(
                mirror, expected_mirror,
                "Mirror mismatch for class {}: got {}, expected {}",
                class_id, mirror, expected_mirror
            );
        }
    }

    #[test]
    fn test_launch_validation_data_invalid_class() {
        let data = LaunchValidationData::new();

        // Invalid class IDs
        assert!(!data.is_unity_class(96));
        assert!(!data.is_unity_class(200));
        assert_eq!(data.get_mirror(96), None);
        assert_eq!(data.get_mirror(255), None);
    }

    #[test]
    fn test_launch_validation_are_mirror_pairs() {
        let data = LaunchValidationData::new();

        // Empty set is trivially mirror-safe
        assert!(data.are_mirror_pairs(&[]));

        // Single class cannot be mirror-safe (odd count)
        assert!(!data.are_mirror_pairs(&[10]));

        // Valid mirror pair
        let mirror_10 = data.get_mirror(10).unwrap();
        assert!(data.are_mirror_pairs(&[10, mirror_10]));

        // Two pairs
        let mirror_20 = data.get_mirror(20).unwrap();
        assert!(data.are_mirror_pairs(&[10, mirror_10, 20, mirror_20]));

        // Even count but not paired
        assert!(!data.are_mirror_pairs(&[10, 20]));

        // Invalid class
        assert!(!data.are_mirror_pairs(&[96, 97]));
    }

    #[test]
    fn test_launch_validation_phase_window() {
        let data = LaunchValidationData::new();

        // Normal window [100, 150)
        let window = AtlasPhaseWindow { begin: 100, span: 50 };
        assert!(data.is_phase_valid(100, &window));
        assert!(data.is_phase_valid(125, &window));
        assert!(data.is_phase_valid(149, &window));
        assert!(!data.is_phase_valid(150, &window));
        assert!(!data.is_phase_valid(99, &window));

        // Wrapping window [700, 50) wraps at 768
        let wrapping = AtlasPhaseWindow { begin: 700, span: 118 };
        assert!(data.is_phase_valid(700, &wrapping));
        assert!(data.is_phase_valid(750, &wrapping));
        assert!(data.is_phase_valid(0, &wrapping));
        assert!(data.is_phase_valid(49, &wrapping));
        assert!(!data.is_phase_valid(50, &wrapping));
        assert!(!data.is_phase_valid(699, &wrapping));

        // Full window
        let full = AtlasPhaseWindow::full();
        for phase in 0..768 {
            assert!(data.is_phase_valid(phase, &full));
        }
    }

    #[test]
    fn test_launch_validation_masks_conflict() {
        let data = LaunchValidationData::new();

        let mut mask_a = AtlasClassMask::empty();
        mask_a.low = (1u64 << 10) | (1u64 << 20);

        let mut mask_b = AtlasClassMask::empty();
        mask_b.low = (1u64 << 20) | (1u64 << 30);

        // Overlapping at class 20
        assert!(data.masks_conflict(&mask_a, &mask_b));

        let mut mask_c = AtlasClassMask::empty();
        mask_c.low = 1u64 << 50;

        // No overlap
        assert!(!data.masks_conflict(&mask_a, &mask_c));

        // High bits overlap
        let mut mask_d = AtlasClassMask::empty();
        mask_d.high = 1u32 << 5; // Class 69

        let mut mask_e = AtlasClassMask::empty();
        mask_e.high = 1u32 << 5; // Also class 69

        assert!(data.masks_conflict(&mask_d, &mask_e));
    }

    #[test]
    fn test_launch_validation_c_api() {
        // Test C API functions
        let data_ptr = launch_validation_data_new();
        assert!(!data_ptr.is_null());

        unsafe {
            // Test unity lookup
            let unity_classes = crate::unity_positions();
            assert!(launch_validation_is_unity(data_ptr, unity_classes[0].as_u8()));

            // Test mirror lookup
            let mirror = launch_validation_get_mirror(data_ptr, 10);
            assert!(mirror < 96);
            assert_eq!(launch_validation_get_mirror(data_ptr, mirror), 10);

            // Test phase validation
            let window = AtlasPhaseWindow { begin: 100, span: 50 };
            assert!(launch_validation_is_phase_valid(data_ptr, 125, &window));
            assert!(!launch_validation_is_phase_valid(data_ptr, 200, &window));

            // Test mask conflict
            let mut mask_a = AtlasClassMask::empty();
            mask_a.low = 1u64 << 10;
            let mut mask_b = AtlasClassMask::empty();
            mask_b.low = 1u64 << 10;
            assert!(launch_validation_masks_conflict(data_ptr, &mask_a, &mask_b));

            mask_b.low = 1u64 << 20;
            assert!(!launch_validation_masks_conflict(data_ptr, &mask_a, &mask_b));

            // Free
            launch_validation_data_free(data_ptr);
        }
    }

    #[test]
    fn test_launch_validation_c_api_null_safety() {
        unsafe {
            // All C functions should handle null gracefully
            assert!(!launch_validation_is_unity(std::ptr::null(), 0));
            assert_eq!(launch_validation_get_mirror(std::ptr::null(), 0), 0xFF);

            let window = AtlasPhaseWindow::full();
            assert!(!launch_validation_is_phase_valid(std::ptr::null(), 0, &window));

            let mask = AtlasClassMask::empty();
            assert!(!launch_validation_masks_conflict(std::ptr::null(), &mask, &mask));

            // Free null should be safe (no-op)
            launch_validation_data_free(std::ptr::null_mut());
        }
    }

    #[test]
    fn test_launch_validation_deterministic() {
        // Verify data is deterministic
        let data1 = LaunchValidationData::new();
        let data2 = LaunchValidationData::new();

        assert_eq!(data1, data2);
        assert_eq!(data1.unity_flags, data2.unity_flags);
        assert_eq!(data1.mirror_table, data2.mirror_table);
    }

    #[test]
    fn test_launch_validation_completeness() {
        let data = LaunchValidationData::new();

        // Verify all 96 classes have mirrors
        for i in 0..96u8 {
            assert!(data.get_mirror(i).is_some(), "Class {} missing mirror", i);
        }

        // Verify exactly 2 unity classes
        let unity_count = (0..96u8).filter(|&i| data.is_unity_class(i)).count();
        assert_eq!(unity_count, 2, "Expected 2 unity classes, found {}", unity_count);
    }
}
