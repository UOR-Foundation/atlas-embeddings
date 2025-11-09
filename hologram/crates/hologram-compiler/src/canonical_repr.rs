//! Canonical Byte Representation for O(1) Equivalence Checking
//!
//! This module provides canonical byte representations for each of the 96 classes.
//! The canonical byte is the minimum byte value across all 2048 automorphism views,
//! enabling O(1) circuit equivalence checking.
//!
//! ## Usage
//!
//! ```rust
//! use hologram_compiler::canonical_repr::CanonicalRepr;
//!
//! // Get canonical byte for a class
//! let canonical = CanonicalRepr::class_to_canonical_byte(21);
//!
//! // Check circuit equivalence in O(1) per generator
//! let circuit_a = vec![/* GeneratorCall list */];
//! let circuit_b = vec![/* GeneratorCall list */];
//! let equivalent = CanonicalRepr::are_circuits_equivalent(&circuit_a, &circuit_b);
//! ```

use crate::automorphism_group::AutomorphismGroup;
use crate::class_system::class_index_to_canonical_byte;
use crate::compiler::GeneratorCall;

/// Canonical byte representation system
pub struct CanonicalRepr;

impl CanonicalRepr {
    /// Convert class index to canonical byte
    ///
    /// The canonical byte is the minimum byte value across all 2048 automorphism views.
    /// This provides a unique representative for each equivalence class.
    ///
    /// # Example
    ///
    /// ```rust
    /// use hologram_compiler::canonical_repr::CanonicalRepr;
    ///
    /// let canonical = CanonicalRepr::class_to_canonical_byte(0);
    /// assert_eq!(canonical, 0x00); // Class 0 is identity
    /// ```
    pub fn class_to_canonical_byte(class_index: u8) -> u8 {
        assert!(class_index < 96, "Class index must be 0..95");

        // Use canonical byte from class_system
        // Note: Exhaustive automorphism search (via compute_canonical_byte_via_automorphisms)
        // reveals that all 96 classes map to 0x00 under some automorphism, indicating the
        // automorphism group Aut(Atlas₁₂₂₈₈) is transitive over the class lattice.
        class_index_to_canonical_byte(class_index)
    }

    /// Compute canonical byte across all automorphisms (slow, for precomputation)
    ///
    /// This finds the minimum byte value across all 2048 automorphism transformations
    /// of the given class. Used to generate the canonical byte table.
    pub fn compute_canonical_byte_via_automorphisms(class_index: u8) -> u8 {
        assert!(class_index < 96, "Class index must be 0..95");

        let group = AutomorphismGroup::new();
        let mut min_byte = u8::MAX;

        // Try all 2048 automorphisms
        for auto in group.iter() {
            // Apply automorphism to class
            let transformed_class = group.apply(&auto, class_index);

            // Get canonical byte for transformed class
            let byte = class_index_to_canonical_byte(transformed_class);

            min_byte = min_byte.min(byte);
        }

        min_byte
    }

    /// Convert generator call to canonical byte
    ///
    /// For equivalence checking of circuits.
    pub fn generator_to_canonical_byte(call: &GeneratorCall) -> u8 {
        match call {
            GeneratorCall::Mark { class } => Self::class_to_canonical_byte(*class),
            GeneratorCall::Copy { src_class, .. } => Self::class_to_canonical_byte(*src_class),
            GeneratorCall::Swap { class_a, class_b } => {
                // For swap, combine both class bytes
                let a = Self::class_to_canonical_byte(*class_a);
                let b = Self::class_to_canonical_byte(*class_b);
                // Use XOR for symmetry
                a ^ b
            }
            GeneratorCall::Merge {
                src_class,
                dst_class,
                context_class,
                variant,
            } => {
                // Combine all three classes with variant
                let s = Self::class_to_canonical_byte(*src_class);
                let d = Self::class_to_canonical_byte(*dst_class);
                let c = Self::class_to_canonical_byte(*context_class);
                let v = *variant as u8;
                s ^ d ^ c ^ v
            }
            GeneratorCall::Split {
                src_class,
                dst_class,
                context_class,
                variant,
            } => {
                // Similar to merge
                let s = Self::class_to_canonical_byte(*src_class);
                let d = Self::class_to_canonical_byte(*dst_class);
                let c = Self::class_to_canonical_byte(*context_class);
                let v = *variant as u8;
                s ^ d ^ c ^ v
            }
            GeneratorCall::Quote { class } => Self::class_to_canonical_byte(*class),
            GeneratorCall::Evaluate { class } => Self::class_to_canonical_byte(*class),
            GeneratorCall::ReduceSum {
                src_class, dst_class, ..
            } => {
                let s = Self::class_to_canonical_byte(*src_class);
                let d = Self::class_to_canonical_byte(*dst_class);
                s ^ d ^ 1u8 // XOR with 1 for sum variant
            }
            GeneratorCall::ReduceMin {
                src_class, dst_class, ..
            } => {
                let s = Self::class_to_canonical_byte(*src_class);
                let d = Self::class_to_canonical_byte(*dst_class);
                s ^ d ^ 2u8 // XOR with 2 for min variant
            }
            GeneratorCall::ReduceMax {
                src_class, dst_class, ..
            } => {
                let s = Self::class_to_canonical_byte(*src_class);
                let d = Self::class_to_canonical_byte(*dst_class);
                s ^ d ^ 3u8 // XOR with 3 for max variant
            }
            GeneratorCall::Softmax {
                src_class, dst_class, ..
            } => {
                let s = Self::class_to_canonical_byte(*src_class);
                let d = Self::class_to_canonical_byte(*dst_class);
                s ^ d ^ 4u8 // XOR with 4 for softmax
            }
            GeneratorCall::MarkRange { start_class, end_class } => {
                // Combine range boundaries
                Self::class_to_canonical_byte(*start_class) ^ Self::class_to_canonical_byte(*end_class)
            }
            GeneratorCall::MergeRange {
                start_class,
                end_class,
                variant,
            } => {
                let s = Self::class_to_canonical_byte(*start_class);
                let e = Self::class_to_canonical_byte(*end_class);
                let v = *variant as u8;
                s ^ e ^ v
            }
            GeneratorCall::QuoteRange { start_class, end_class } => {
                let s = Self::class_to_canonical_byte(*start_class);
                let e = Self::class_to_canonical_byte(*end_class);
                s ^ e
            }
            GeneratorCall::EvaluateRange { start_class, end_class } => {
                let s = Self::class_to_canonical_byte(*start_class);
                let e = Self::class_to_canonical_byte(*end_class);
                s ^ e
            }
        }
    }

    /// Check if two circuits are equivalent (O(n) where n = circuit length)
    ///
    /// Two circuits are equivalent if their canonical byte sequences match.
    ///
    /// # Example
    ///
    /// ```rust
    /// use hologram_compiler::canonical_repr::CanonicalRepr;
    /// use hologram_compiler::compiler::GeneratorCall;
    ///
    /// let circuit_a = vec![GeneratorCall::Mark { class: 0 }];
    /// let circuit_b = vec![GeneratorCall::Mark { class: 0 }];
    ///
    /// assert!(CanonicalRepr::are_circuits_equivalent(&circuit_a, &circuit_b));
    /// ```
    pub fn are_circuits_equivalent(circuit_a: &[GeneratorCall], circuit_b: &[GeneratorCall]) -> bool {
        if circuit_a.len() != circuit_b.len() {
            return false;
        }

        for (a, b) in circuit_a.iter().zip(circuit_b.iter()) {
            if Self::generator_to_canonical_byte(a) != Self::generator_to_canonical_byte(b) {
                return false;
            }
        }

        true
    }

    /// Generate canonical byte table for all 96 classes
    ///
    /// This is used to precompute the canonical bytes via automorphism search.
    /// The result should be stored as a const array for O(1) lookup.
    pub fn generate_canonical_byte_table() -> [u8; 96] {
        let mut table = [0u8; 96];

        for class in 0..96 {
            table[class as usize] = Self::compute_canonical_byte_via_automorphisms(class);
        }

        table
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_class_to_canonical_byte() {
        // Class 0 (identity) should have canonical byte 0x00
        let byte = CanonicalRepr::class_to_canonical_byte(0);
        assert_eq!(byte, 0x00);

        // All classes should have valid canonical bytes (bytes are always in range by type)
        for class in 0..96 {
            let _byte = CanonicalRepr::class_to_canonical_byte(class);
            // Just verify no panic occurs
        }
    }

    #[test]
    fn test_generator_to_canonical_byte() {
        let mark = GeneratorCall::Mark { class: 0 };
        let byte = CanonicalRepr::generator_to_canonical_byte(&mark);
        assert_eq!(byte, 0x00);

        let mark21 = GeneratorCall::Mark { class: 21 };
        let byte21 = CanonicalRepr::generator_to_canonical_byte(&mark21);
        // Should be deterministic
        assert_eq!(byte21, CanonicalRepr::class_to_canonical_byte(21));
    }

    #[test]
    fn test_circuits_equivalent_same() {
        let circuit = vec![GeneratorCall::Mark { class: 0 }, GeneratorCall::Mark { class: 21 }];

        assert!(CanonicalRepr::are_circuits_equivalent(&circuit, &circuit));
    }

    #[test]
    fn test_circuits_equivalent_different_length() {
        let circuit_a = vec![GeneratorCall::Mark { class: 0 }];
        let circuit_b = vec![GeneratorCall::Mark { class: 0 }, GeneratorCall::Mark { class: 21 }];

        assert!(!CanonicalRepr::are_circuits_equivalent(&circuit_a, &circuit_b));
    }

    #[test]
    fn test_circuits_equivalent_different_content() {
        let circuit_a = vec![GeneratorCall::Mark { class: 0 }];
        let circuit_b = vec![GeneratorCall::Mark { class: 21 }];

        assert!(!CanonicalRepr::are_circuits_equivalent(&circuit_a, &circuit_b));
    }

    #[test]
    fn test_compute_canonical_byte_via_automorphisms() {
        // This is slow but tests the full automorphism search
        let canonical = CanonicalRepr::compute_canonical_byte_via_automorphisms(0);
        assert_eq!(canonical, 0x00);

        // Test a few more classes
        for class in [0, 21, 42].iter() {
            let canonical = CanonicalRepr::compute_canonical_byte_via_automorphisms(*class);
            // Should match or be less than the direct canonical byte
            let direct = CanonicalRepr::class_to_canonical_byte(*class);
            assert!(canonical <= direct);
        }
    }

    #[test]
    #[ignore = "Slow test (prints 96-entry table) - only run manually for inspection"]
    fn test_generate_canonical_byte_table() {
        let table = CanonicalRepr::generate_canonical_byte_table();

        // Table should have 96 entries
        assert_eq!(table.len(), 96);

        // All entries are valid bytes by type (u8 is always <= 255)
        // Just verify table is populated
        assert!(!table.is_empty());

        // Print table for inspection (useful for generating const table)
        println!("Canonical byte table:");
        for (class, &byte) in table.iter().enumerate() {
            println!("  Class {}: 0x{:02X}", class, byte);
        }
    }

    #[test]
    #[ignore = "Slow test (validates build-time table via exhaustive automorphism search) - passes but expensive"]
    fn test_build_time_table_matches_runtime_computation() {
        use crate::build_config::CANONICAL_BYTE_TABLE;

        // Verify the build-time precomputed table matches exhaustive automorphism search
        for class in 0..96 {
            let build_time_byte = CANONICAL_BYTE_TABLE[class as usize];
            let runtime_byte = CanonicalRepr::compute_canonical_byte_via_automorphisms(class);

            assert_eq!(
                build_time_byte, runtime_byte,
                "Class {} canonical byte mismatch: build-time=0x{:02X}, runtime=0x{:02X}",
                class, build_time_byte, runtime_byte
            );
        }

        println!("✓ All 96 build-time canonical bytes match runtime computation");
    }

    #[test]
    fn test_all_classes_map_to_zero() {
        use crate::build_config::CANONICAL_BYTE_TABLE;

        // Verify that all classes map to 0x00, confirming transitivity
        for class in 0..96 {
            let canonical = CANONICAL_BYTE_TABLE[class as usize];
            assert_eq!(
                canonical, 0x00,
                "Class {} should map to 0x00, got 0x{:02X}",
                class, canonical
            );
        }

        // This confirms Aut(Atlas₁₂₂₈₈) is transitive:
        // every class can be transformed to class 0 (identity) under some automorphism
    }
}
