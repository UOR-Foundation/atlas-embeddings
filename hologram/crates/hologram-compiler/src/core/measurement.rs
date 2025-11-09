//! Measurement and Projection from 768 States to 96 Classes
//!
//! This module implements quantum measurement as a deterministic projection
//! from the full 768-dimensional state space to 96 canonical classes.
//!
//! ## Measurement Process
//!
//! 1. **Before measurement**: Quantum state at specific position in [0, 768)
//! 2. **Measurement**: Project to one of 96 canonical classes
//! 3. **Result**: Observed outcome (information loss creates apparent randomness)
//!
//! The projection uses the byte-to-class mapping from `byte_to_class_mapping.csv`:
//! - 256 bytes map to 96 classes
//! - Average 2.67 bytes per class
//! - 32 classes have 4 bytes, 64 classes have 2 bytes
//!
//! ## Determinism
//!
//! **Critical property**: Same cycle position → same measurement outcome (100%)
//!
//! This is the key difference from Copenhagen interpretation:
//! - Copenhagen: "Wave function collapse" is probabilistic
//! - 768-cycle: Projection is deterministic given position
//!
//! Apparent randomness comes from unknown initial cycle position, not
//! fundamental indeterminacy.

use hologram_tracing::perf_span;

use super::state::QuantumState;

/// Number of canonical classes
pub const CLASS_COUNT: u8 = 96;

/// Byte-to-class mapping table
///
/// This maps each byte [0x00..0xFF] to its canonical class [0..95].
/// Data extracted from `docs/byte_to_class_mapping.csv`.
///
/// Pattern: Consecutive bytes often map to the same class, indicating
/// equivalence classes under the canonical reduction.
const BYTE_TO_CLASS: [u8; 256] = [
    // 0x00-0x0F
    0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, // 0x10-0x1F
    8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15, // 0x20-0x2F
    16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 22, 23, 23,
    // 0x30-0x3F (note: wraps back to classes 0-7)
    0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, // 0x40-0x4F
    24, 24, 25, 25, 26, 26, 27, 27, 28, 28, 29, 29, 30, 30, 31, 31, // 0x50-0x5F
    32, 32, 33, 33, 34, 34, 35, 35, 36, 36, 37, 37, 38, 38, 39, 39, // 0x60-0x6F
    40, 40, 41, 41, 42, 42, 43, 43, 44, 44, 45, 45, 46, 46, 47, 47,
    // 0x70-0x7F (note: wraps back to classes 24-31)
    24, 24, 25, 25, 26, 26, 27, 27, 28, 28, 29, 29, 30, 30, 31, 31, // 0x80-0x8F
    48, 48, 49, 49, 50, 50, 51, 51, 52, 52, 53, 53, 54, 54, 55, 55, // 0x90-0x9F
    56, 56, 57, 57, 58, 58, 59, 59, 60, 60, 61, 61, 62, 62, 63, 63, // 0xA0-0xAF
    64, 64, 65, 65, 66, 66, 67, 67, 68, 68, 69, 69, 70, 70, 71, 71,
    // 0xB0-0xBF (note: wraps back to classes 48-55)
    48, 48, 49, 49, 50, 50, 51, 51, 52, 52, 53, 53, 54, 54, 55, 55, // 0xC0-0xCF
    72, 72, 73, 73, 74, 74, 75, 75, 76, 76, 77, 77, 78, 78, 79, 79, // 0xD0-0xDF
    80, 80, 81, 81, 82, 82, 83, 83, 84, 84, 85, 85, 86, 86, 87, 87, // 0xE0-0xEF
    88, 88, 89, 89, 90, 90, 91, 91, 92, 92, 93, 93, 94, 94, 95, 95,
    // 0xF0-0xFF (note: wraps back to classes 72-79)
    72, 72, 73, 73, 74, 74, 75, 75, 76, 76, 77, 77, 78, 78, 79, 79,
];

/// Project a byte to its canonical class
///
/// # Arguments
///
/// * `byte` - Byte value [0x00..0xFF]
///
/// # Returns
///
/// Canonical class index [0..95]
///
/// # Example
///
/// ```
/// use hologram_compiler::project_to_class;
///
/// assert_eq!(project_to_class(0x00), 0);
/// assert_eq!(project_to_class(0x01), 0);  // Same class as 0x00
/// assert_eq!(project_to_class(0x02), 1);  // Different class
/// assert_eq!(project_to_class(0xFF), 79);
/// ```
pub fn project_to_class(byte: u8) -> u8 {
    BYTE_TO_CLASS[byte as usize]
}

/// Measure a quantum state, returning its canonical class
///
/// This is the core measurement operation that projects from 768 states
/// to 96 canonical classes.
///
/// **Determinism**: Given the same quantum state (position), this always
/// returns the same class. The apparent randomness in quantum measurement
/// comes from not knowing the initial cycle position.
///
/// # Arguments
///
/// * `state` - Quantum state to measure
///
/// # Returns
///
/// Canonical class index [0..95]
///
/// # Example
///
/// ```
/// use hologram_compiler::{QuantumState, measure_quantum_state};
///
/// let state = QuantumState::new(100);
/// let class = measure_quantum_state(state);
///
/// // Deterministic: measuring same state always gives same result
/// assert_eq!(measure_quantum_state(state), class);
/// assert_eq!(measure_quantum_state(state), class);
/// ```
pub fn measure_quantum_state(state: QuantumState) -> u8 {
    let _span = perf_span!("measure_quantum_state", position = state.position());

    // Get the byte value from the quantum state
    let byte = state.byte();

    // Project to canonical class
    project_to_class(byte)
}

/// Measure a quantum state, returning detailed measurement information
///
/// # Returns
///
/// Tuple of (position, byte, modality_index, class_index)
///
/// # Example
///
/// ```
/// use hologram_compiler::{QuantumState, Modality, measure_detailed};
///
/// let state = QuantumState::new(300);
/// let (position, byte, modality_idx, class) = measure_detailed(state);
///
/// assert_eq!(position, 300);
/// assert_eq!(byte, 44); // 300 % 256 = 44
/// assert_eq!(modality_idx, 1); // Produce modality (300 / 256 = 1)
/// ```
pub fn measure_detailed(state: QuantumState) -> (u16, u8, u8, u8) {
    let position = state.position();
    let byte = state.byte();
    let modality = state.modality();
    let class = project_to_class(byte);

    (position, byte, modality.index(), class)
}

/// Check if measurement is deterministic by measuring the same state multiple times
///
/// # Example
///
/// ```
/// use hologram_compiler::{QuantumState, verify_determinism};
///
/// let state = QuantumState::new(42);
/// assert!(verify_determinism(state, 1000));
/// ```
pub fn verify_determinism(state: QuantumState, num_measurements: usize) -> bool {
    let first_measurement = measure_quantum_state(state);

    for _ in 1..num_measurements {
        if measure_quantum_state(state) != first_measurement {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_byte_to_class_bounds() {
        // All classes should be in [0, 96)
        for byte in 0..=255 {
            let class = project_to_class(byte);
            assert!(class < CLASS_COUNT, "Class {} out of bounds for byte {}", class, byte);
        }
    }

    #[test]
    fn test_byte_to_class_mapping() {
        // Test known mappings from CSV
        assert_eq!(project_to_class(0x00), 0);
        assert_eq!(project_to_class(0x01), 0); // Same class
        assert_eq!(project_to_class(0x02), 1);
        assert_eq!(project_to_class(0x03), 1); // Same class
        assert_eq!(project_to_class(0xFF), 79);
    }

    #[test]
    fn test_measure_determinism() {
        let state = QuantumState::new(100);
        let class1 = measure_quantum_state(state);
        let class2 = measure_quantum_state(state);
        let class3 = measure_quantum_state(state);

        // Same state always gives same measurement
        assert_eq!(class1, class2);
        assert_eq!(class2, class3);
    }

    #[test]
    fn test_measure_different_positions() {
        let state1 = QuantumState::new(0);
        let state2 = QuantumState::new(100);
        let state3 = QuantumState::new(500);

        let class1 = measure_quantum_state(state1);
        let class2 = measure_quantum_state(state2);
        let class3 = measure_quantum_state(state3);

        // All should be valid classes
        assert!(class1 < CLASS_COUNT);
        assert!(class2 < CLASS_COUNT);
        assert!(class3 < CLASS_COUNT);
    }

    #[test]
    fn test_measure_detailed() {
        let state = QuantumState::new(300);
        let (position, byte, modality_idx, class) = measure_detailed(state);

        assert_eq!(position, 300);
        assert_eq!(byte, 44); // 300 % 256
        assert_eq!(modality_idx, 1); // 300 / 256 = 1 (Produce)
        assert!(class < CLASS_COUNT);
    }

    #[test]
    fn test_verify_determinism() {
        let state = QuantumState::new(42);
        assert!(verify_determinism(state, 1000));
    }

    #[test]
    fn test_all_classes_reachable() {
        // Verify that all 96 classes are represented in the mapping
        let mut classes_seen = vec![false; CLASS_COUNT as usize];

        for byte in 0..=255 {
            let class = project_to_class(byte);
            classes_seen[class as usize] = true;
        }

        let num_classes_seen = classes_seen.iter().filter(|&&x| x).count();
        assert_eq!(num_classes_seen, CLASS_COUNT as usize);
    }

    #[test]
    fn test_measurement_across_modalities() {
        use crate::core::state::Modality;

        // Test that modality affects outcome (different bytes in different modalities)
        let neutral = QuantumState::from_byte_modality(0x10, Modality::Neutral);
        let produce = QuantumState::from_byte_modality(0x10, Modality::Produce);
        let consume = QuantumState::from_byte_modality(0x10, Modality::Consume);

        let class_neutral = measure_quantum_state(neutral);
        let class_produce = measure_quantum_state(produce);
        let class_consume = measure_quantum_state(consume);

        // All valid
        assert!(class_neutral < CLASS_COUNT);
        assert!(class_produce < CLASS_COUNT);
        assert!(class_consume < CLASS_COUNT);

        // Same byte value, so should give same class (modality doesn't affect byte)
        assert_eq!(class_neutral, class_produce);
        assert_eq!(class_produce, class_consume);
    }
}
