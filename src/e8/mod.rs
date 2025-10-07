//! E₈ Root System
//!
//! This module provides the complete E₈ root system with all 240 roots in exact arithmetic.
//!
//! # Structure
//!
//! The E₈ root system consists of:
//! - **112 integer roots**: ±eᵢ ± eⱼ for i ≠ j (all pairs)
//! - **128 half-integer roots**: All coordinates ±1/2 with even number of minus signs
//!
//! All coordinates are represented exactly using [`HalfInteger`].
//!
//! # Examples
//!
//! ```
//! use atlas_embeddings::e8::E8RootSystem;
//!
//! let e8 = E8RootSystem::new();
//! assert_eq!(e8.num_roots(), 240);
//!
//! // Check root properties
//! for i in 0..e8.num_roots() {
//!     let root = e8.get_root(i);
//!     assert!(root.is_root()); // norm² = 2
//! }
//! ```

use crate::arithmetic::{HalfInteger, Rational, Vector8};
use std::collections::HashMap;

/// Total number of E₈ roots
pub const E8_ROOT_COUNT: usize = 240;

/// Number of integer-coordinate roots
pub const E8_INTEGER_ROOT_COUNT: usize = 112;

/// Number of half-integer-coordinate roots
pub const E8_HALF_INTEGER_ROOT_COUNT: usize = 128;

/// E₈ Root System
///
/// Encapsulates all 240 roots of E₈ with exact arithmetic.
///
/// # Invariants
///
/// - Exactly 240 roots total
/// - Exactly 112 integer roots
/// - Exactly 128 half-integer roots
/// - Every root has norm² = 2
/// - Every root r has negation -r in the system
#[derive(Debug, Clone)]
pub struct E8RootSystem {
    /// All 240 roots
    roots: Vec<Vector8>,

    /// Map from root to its index (for fast lookup)
    root_index: HashMap<Vector8, usize>,

    /// Negation table: `negation_table[i]` = index of `-roots[i]`
    negation_table: Vec<usize>,
}

impl E8RootSystem {
    /// Create new E₈ root system
    ///
    /// Generates all 240 roots and verifies invariants.
    #[must_use]
    pub fn new() -> Self {
        let roots = Self::generate_all_roots();
        let root_index = Self::create_root_index(&roots);
        let negation_table = Self::compute_negation_table(&roots, &root_index);

        let system = Self { roots, root_index, negation_table };

        system.verify_invariants();
        system
    }

    /// Generate all 240 E₈ roots
    fn generate_all_roots() -> Vec<Vector8> {
        let mut roots = Vec::with_capacity(E8_ROOT_COUNT);

        // Generate 112 integer roots: ±eᵢ ± eⱼ for i < j
        roots.extend(Self::generate_integer_roots());

        // Generate 128 half-integer roots: all coordinates ±1/2, even # of minus signs
        roots.extend(Self::generate_half_integer_roots());

        assert_eq!(roots.len(), E8_ROOT_COUNT, "Must generate exactly 240 roots");
        roots
    }

    /// Generate 112 integer-coordinate roots
    ///
    /// These are ±eᵢ ± eⱼ for all 0 ≤ i < j < 8 and all sign combinations.
    /// Total: C(8,2) × 4 = 28 × 4 = 112
    fn generate_integer_roots() -> Vec<Vector8> {
        let mut roots = Vec::with_capacity(E8_INTEGER_ROOT_COUNT);

        let zero = HalfInteger::from_integer(0);

        // For each pair (i, j) with i < j
        for i in 0..8 {
            for j in (i + 1)..8 {
                // For each combination of signs
                for &sign_i in &[1, -1] {
                    for &sign_j in &[1, -1] {
                        let mut coords = [zero; 8];
                        coords[i] = HalfInteger::from_integer(sign_i);
                        coords[j] = HalfInteger::from_integer(sign_j);
                        roots.push(Vector8::new(coords));
                    }
                }
            }
        }

        assert_eq!(roots.len(), E8_INTEGER_ROOT_COUNT);
        roots
    }

    /// Generate 128 half-integer-coordinate roots
    ///
    /// All coordinates are ±1/2, with an even number of minus signs.
    /// Total: 2⁸ / 2 = 256 / 2 = 128
    fn generate_half_integer_roots() -> Vec<Vector8> {
        let mut roots = Vec::with_capacity(E8_HALF_INTEGER_ROOT_COUNT);

        let half = HalfInteger::new(1); // 1/2

        // Iterate through all 256 sign patterns
        for pattern in 0..256_u16 {
            let mut coords = [half; 8];
            let mut num_negatives = 0;

            // Set signs based on bit pattern
            for (i, coord) in coords.iter_mut().enumerate() {
                if (pattern >> i) & 1 == 1 {
                    *coord = -half;
                    num_negatives += 1;
                }
            }

            // Only include if even number of minus signs
            if num_negatives % 2 == 0 {
                roots.push(Vector8::new(coords));
            }
        }

        assert_eq!(roots.len(), E8_HALF_INTEGER_ROOT_COUNT);
        roots
    }

    /// Create index mapping roots to their positions
    fn create_root_index(roots: &[Vector8]) -> HashMap<Vector8, usize> {
        roots.iter().enumerate().map(|(i, r)| (*r, i)).collect()
    }

    /// Compute negation table
    fn compute_negation_table(
        roots: &[Vector8],
        root_index: &HashMap<Vector8, usize>,
    ) -> Vec<usize> {
        let mut table = vec![0; roots.len()];

        for (i, root) in roots.iter().enumerate() {
            let neg_root = -(*root);
            if let Some(&neg_idx) = root_index.get(&neg_root) {
                table[i] = neg_idx;
            } else {
                panic!("Negation of root {i} not found in system");
            }
        }

        table
    }

    /// Verify all E₈ root system invariants
    fn verify_invariants(&self) {
        // Check counts
        assert_eq!(self.roots.len(), E8_ROOT_COUNT, "Must have exactly 240 roots");

        // Count integer vs half-integer roots
        let integer_count = self.roots.iter().filter(|r| Self::is_integer_root(r)).count();
        let half_int_count = self.roots.iter().filter(|r| Self::is_half_integer_root(r)).count();

        assert_eq!(integer_count, E8_INTEGER_ROOT_COUNT, "Must have 112 integer roots");
        assert_eq!(half_int_count, E8_HALF_INTEGER_ROOT_COUNT, "Must have 128 half-integer roots");

        // Check every root has norm² = 2
        for (i, root) in self.roots.iter().enumerate() {
            assert!(root.is_root(), "Root {i} must have norm² = 2");
        }

        // Check negation table is correct
        for (i, &neg_idx) in self.negation_table.iter().enumerate() {
            assert_ne!(i, neg_idx, "Root {i} cannot be its own negative");
            let expected_neg = -self.roots[i];
            assert_eq!(self.roots[neg_idx], expected_neg, "Negation table incorrect at {i}");
        }
    }

    /// Check if root has all integer coordinates
    fn is_integer_root(root: &Vector8) -> bool {
        root.coords().iter().all(|c| c.is_integer())
    }

    /// Check if root has all half-integer coordinates (all ±1/2)
    fn is_half_integer_root(root: &Vector8) -> bool {
        root.coords().iter().all(|c| !c.is_integer() && c.numerator().abs() == 1)
    }

    /// Get total number of roots
    #[must_use]
    pub const fn num_roots(&self) -> usize {
        E8_ROOT_COUNT
    }

    /// Get root by index
    ///
    /// # Panics
    ///
    /// Panics if index is out of bounds
    #[must_use]
    pub fn get_root(&self, index: usize) -> &Vector8 {
        &self.roots[index]
    }

    /// Get index of negation of a root
    ///
    /// # Panics
    ///
    /// Panics if index is out of bounds
    #[must_use]
    pub fn get_negation(&self, index: usize) -> usize {
        self.negation_table[index]
    }

    /// Get sign class representative (smaller of {r, -r})
    #[must_use]
    pub fn sign_class_representative(&self, index: usize) -> usize {
        index.min(self.negation_table[index])
    }

    /// Count number of distinct sign classes used by a set of root indices
    #[must_use]
    pub fn count_sign_classes(&self, indices: &[usize]) -> usize {
        use std::collections::HashSet;
        indices
            .iter()
            .map(|&i| self.sign_class_representative(i))
            .collect::<HashSet<_>>()
            .len()
    }

    /// Get all roots as a slice
    #[must_use]
    pub fn roots(&self) -> &[Vector8] {
        &self.roots
    }

    /// Compute inner product between two roots
    #[must_use]
    pub fn inner_product(&self, i: usize, j: usize) -> Rational {
        self.roots[i].inner_product(&self.roots[j])
    }

    /// Check if two roots are negatives of each other
    ///
    /// Returns `true` if root j is the negative of root i
    #[must_use]
    pub fn are_negatives(&self, i: usize, j: usize) -> bool {
        self.negation_table[i] == j
    }

    /// Find index of a given root vector
    ///
    /// Returns `None` if root is not in the system.
    #[must_use]
    pub fn find_root(&self, root: &Vector8) -> Option<usize> {
        self.root_index.get(root).copied()
    }
}

impl Default for E8RootSystem {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_e8_generation() {
        let e8 = E8RootSystem::new();
        assert_eq!(e8.num_roots(), 240);
    }

    #[test]
    fn test_root_counts() {
        let e8 = E8RootSystem::new();

        let integer_count = e8.roots().iter().filter(|r| E8RootSystem::is_integer_root(r)).count();
        let half_int_count =
            e8.roots().iter().filter(|r| E8RootSystem::is_half_integer_root(r)).count();

        assert_eq!(integer_count, 112);
        assert_eq!(half_int_count, 128);
    }

    #[test]
    fn test_all_roots_have_norm_2() {
        let e8 = E8RootSystem::new();

        for root in e8.roots() {
            assert!(root.is_root(), "All E₈ roots must have norm² = 2");
        }
    }

    #[test]
    fn test_negation_table() {
        let e8 = E8RootSystem::new();

        for i in 0..e8.num_roots() {
            let neg_idx = e8.get_negation(i);

            // Check negation is different
            assert_ne!(i, neg_idx);

            // Check double negation is identity
            assert_eq!(e8.get_negation(neg_idx), i);

            // Check actual negation
            let root = e8.get_root(i);
            let neg_root = e8.get_root(neg_idx);
            assert_eq!(*neg_root, -(*root));
        }
    }

    #[test]
    fn test_sign_classes() {
        let e8 = E8RootSystem::new();

        // Should have 120 sign classes (240 roots / 2)
        let all_indices: Vec<usize> = (0..240).collect();
        assert_eq!(e8.count_sign_classes(&all_indices), 120);
    }

    #[test]
    fn test_integer_root_example() {
        let e8 = E8RootSystem::new();

        // Find a root like (1, 1, 0, 0, 0, 0, 0, 0)
        let target = Vector8::new([
            HalfInteger::from_integer(1),
            HalfInteger::from_integer(1),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
        ]);

        assert!(e8.roots().contains(&target), "Should contain (1,1,0,0,0,0,0,0)");
        assert!(target.is_root());
    }

    #[test]
    fn test_half_integer_root_example() {
        let e8 = E8RootSystem::new();

        // All +1/2 coordinates
        let target = Vector8::new([HalfInteger::new(1); 8]);

        assert!(e8.roots().contains(&target), "Should contain (1/2, 1/2, ..., 1/2)");
        assert!(target.is_root());
    }

    #[test]
    fn test_inner_products() {
        let e8 = E8RootSystem::new();

        // Self inner product = 2
        for i in 0..e8.num_roots() {
            assert_eq!(e8.inner_product(i, i), Rational::new(2, 1));
        }

        // Inner product with negation = -2
        for i in 0..e8.num_roots() {
            let neg_i = e8.get_negation(i);
            assert_eq!(e8.inner_product(i, neg_i), Rational::new(-2, 1));
        }
    }
}
