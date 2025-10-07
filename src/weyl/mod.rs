//! Weyl Groups and Simple Reflections
//!
//! This module provides Weyl groups for exceptional Lie algebras, implementing
//! simple reflections from first principles using exact rational arithmetic.
//!
//! # Mathematical Foundation
//!
//! For a root system Φ with simple roots {α₁, ..., αₙ}, the Weyl group W is generated
//! by simple reflections. The reflection through the hyperplane perpendicular to α is:
//!
//! ```text
//! s_α(v) = v - 2⟨v,α⟩/⟨α,α⟩ α
//! ```
//!
//! where ⟨·,·⟩ denotes the standard inner product.
//!
//! ## Properties
//!
//! - Each reflection is an involution: `s_α² = 1`
//! - Reflections satisfy Coxeter relations: `(s_i s_j)^{m_ij} = 1`
//! - The order `m_ij` depends on the Cartan matrix entry `C_ij`
//!
//! ## Exceptional Weyl Group Orders
//!
//! | Group | Order | Structure |
//! |-------|-------|-----------|
//! | G₂ | 12 | D₆ (dihedral) |
//! | F₄ | 1,152 | - |
//! | E₆ | 51,840 | - |
//! | E₇ | 2,903,040 | - |
//! | E₈ | 696,729,600 | - |
//!
//! # Implementation Notes
//!
//! This implementation uses **exact rational arithmetic** throughout, matching the
//! certified Python implementation. All vector operations use `Rational` types,
//! ensuring mathematical correctness without floating-point errors.
//!
//! For large groups (E₇, E₈), full enumeration is computationally infeasible.
//! The module provides reflection operations and stores known group orders.
//!
//! # Examples
//!
//! ```
//! use atlas_embeddings::weyl::SimpleReflection;
//! use atlas_embeddings::arithmetic::{Vector8, HalfInteger};
//!
//! // Create a simple root vector
//! let alpha = Vector8::new([
//!     HalfInteger::from_integer(1),
//!     HalfInteger::from_integer(-1),
//!     HalfInteger::from_integer(0),
//!     HalfInteger::from_integer(0),
//!     HalfInteger::from_integer(0),
//!     HalfInteger::from_integer(0),
//!     HalfInteger::from_integer(0),
//!     HalfInteger::from_integer(0),
//! ]);
//!
//! // Create reflection and apply to a vector
//! let refl = SimpleReflection::from_root(&alpha);
//! let v = Vector8::new([HalfInteger::from_integer(1); 8]);
//! let reflected = refl.apply(&v);
//! ```

use crate::arithmetic::{Rational, RationalMatrix, RationalVector, Vector8};
use crate::cartan::CartanMatrix;
use std::collections::HashSet;

/// Simple reflection through hyperplane perpendicular to a root
///
/// Implements the Weyl group generator: `s_α(v) = v - 2⟨v,α⟩/⟨α,α⟩ α`
#[derive(Debug, Clone)]
pub struct SimpleReflection {
    /// The root vector defining this reflection
    root: Vector8,
    /// Cached value of ⟨α,α⟩ for efficiency
    root_norm_squared: Rational,
}

impl SimpleReflection {
    /// Create a simple reflection from a root vector
    ///
    /// # Arguments
    ///
    /// * `root` - The root vector (must be non-zero)
    ///
    /// # Panics
    ///
    /// Panics if root has norm² = 0
    #[must_use]
    pub fn from_root(root: &Vector8) -> Self {
        let root_norm_squared = root.norm_squared();
        assert!(*root_norm_squared.numer() != 0, "Cannot create reflection from zero root");

        Self { root: *root, root_norm_squared }
    }

    /// Apply this reflection to a vector
    ///
    /// Computes: `s_α(v) = v - 2⟨v,α⟩/⟨α,α⟩ α`
    ///
    /// Uses exact rational arithmetic throughout.
    #[must_use]
    pub fn apply(&self, v: &Vector8) -> Vector8 {
        // Compute ⟨v,α⟩
        let inner = v.inner_product(&self.root);

        // Compute 2⟨v,α⟩/⟨α,α⟩
        let coefficient = Rational::new(2, 1) * inner / self.root_norm_squared;

        // Compute coefficient * α
        let scaled_root = self.root.scale_rational(coefficient);

        // Return v - scaled_root
        v.sub(&scaled_root)
    }

    /// Get the root vector for this reflection
    #[must_use]
    pub const fn root(&self) -> &Vector8 {
        &self.root
    }

    /// Verify this is an involution: `s_α(s_α(v)) = v`
    ///
    /// Returns true if applying reflection twice returns the original vector.
    #[must_use]
    pub fn verify_involution(&self, v: &Vector8) -> bool {
        let reflected_once = self.apply(v);
        let reflected_twice = self.apply(&reflected_once);
        reflected_twice == *v
    }
}

/// Weyl group structure for a given rank
///
/// Stores the Cartan matrix and provides Weyl group operations.
/// Group orders are known mathematical values (not computed).
#[derive(Debug, Clone)]
pub struct WeylGroup<const N: usize> {
    /// The Cartan matrix defining the root system
    cartan: CartanMatrix<N>,
    /// Known Weyl group order (from mathematics)
    known_order: usize,
}

impl<const N: usize> WeylGroup<N> {
    /// Create a Weyl group from Cartan matrix and known order
    #[must_use]
    pub const fn new(cartan: CartanMatrix<N>, known_order: usize) -> Self {
        Self { cartan, known_order }
    }

    /// Get the rank
    #[must_use]
    pub const fn rank(&self) -> usize {
        N
    }

    /// Get the Cartan matrix
    #[must_use]
    pub const fn cartan_matrix(&self) -> &CartanMatrix<N> {
        &self.cartan
    }

    /// Get the known Weyl group order
    ///
    /// This is the mathematically known value, not computed by enumeration.
    #[must_use]
    pub const fn order(&self) -> usize {
        self.known_order
    }

    /// Get the Coxeter number `m_ij` for simple reflections `s_i` and `s_j`
    ///
    /// Determines the order of the product `s_i s_j`:
    /// - `m_ii = 1` (`s_i² = 1`)
    /// - `m_ij = 2` if `C_ij = 0` (orthogonal)
    /// - `m_ij = 3` if `C_ij C_ji = 1` (simply-laced)
    /// - `m_ij = 4` if `C_ij C_ji = 2` (double bond in F₄)
    /// - `m_ij = 6` if `C_ij C_ji = 3` (triple bond in G₂)
    #[must_use]
    pub const fn coxeter_number(&self, i: usize, j: usize) -> usize {
        if i == j {
            return 1; // s_i² = 1
        }

        let c_ij = self.cartan.get(i, j);
        let c_ji = self.cartan.get(j, i);

        if c_ij == 0 {
            return 2; // Orthogonal roots commute
        }

        // Order determined by product C_ij × C_ji
        let product = c_ij * c_ji;

        match product {
            1 => 3, // Simply-laced
            2 => 4, // Double bond
            3 => 6, // Triple bond
            _ => 2, // Default (shouldn't occur)
        }
    }

    /// Generate Weyl group elements via BFS (exact arithmetic)
    ///
    /// Uses breadth-first search starting from identity, composing with
    /// simple reflections at each step. All operations use exact rational
    /// arithmetic - no floating point.
    ///
    /// From certified Python implementation: `generate_weyl_group()` method
    ///
    /// # Parameters
    ///
    /// - `simple_roots`: Simple root vectors in N-dimensional space
    /// - `max_length`: Maximum word length to explore (stops early if full group found)
    ///
    /// # Returns
    ///
    /// Set of Weyl group elements as exact rational matrices (N×N)
    ///
    /// # Computational Limits
    ///
    /// - G₂: 12 elements (fast)
    /// - F₄: 1,152 elements (seconds)
    /// - E₆: 51,840 elements (minutes)
    /// - E₇: 2,903,040 elements (hours - not recommended)
    /// - E₈: 696,729,600 elements (infeasible)
    ///
    /// # Note
    ///
    /// The number of simple roots may be less than N (e.g., G₂ has 2 simple roots
    /// in 3D space). The matrices will be N×N regardless.
    ///
    /// # Panics
    ///
    /// Panics if `simple_roots` is empty.
    pub fn generate_elements(
        &self,
        simple_roots: &[RationalVector<N>],
        max_length: usize,
    ) -> HashSet<RationalMatrix<N>> {
        assert!(!simple_roots.is_empty(), "Must provide at least one simple root");

        // Generate reflection matrices for simple roots
        let reflections: Vec<RationalMatrix<N>> =
            simple_roots.iter().map(RationalMatrix::reflection).collect();

        // Start with identity
        let identity = RationalMatrix::identity();
        let mut elements = HashSet::new();
        elements.insert(identity.clone());
        let mut frontier = vec![identity];

        println!("Generating Weyl group elements (expected order: {})", self.known_order);

        // BFS: at each level, multiply all frontier elements by all generators
        for length in 1..=max_length {
            let mut new_frontier = Vec::new();
            let prev_count = elements.len();

            for elem in &frontier {
                for refl in &reflections {
                    // Compose: refl @ elem (exact matrix multiplication)
                    let new_elem = refl.multiply(elem);

                    // Check if new (exact equality via HashSet)
                    if elements.insert(new_elem.clone()) {
                        new_frontier.push(new_elem);
                    }
                }
            }

            frontier = new_frontier;

            println!("  Length {length}: {} elements total", elements.len());

            // Check if we've generated full group
            if elements.len() == self.known_order {
                println!("✓ Generated full group!");
                break;
            } else if frontier.is_empty() || elements.len() == prev_count {
                // No new elements found - group generation complete
                println!("⚠ Generation stopped (no new elements)");
                break;
            }
        }

        if elements.len() != self.known_order {
            println!(
                "⚠ Warning: Generated {} elements, expected {}",
                elements.len(),
                self.known_order
            );
        }

        elements
    }
}

// Specialized constructors for exceptional groups

impl WeylGroup<2> {
    /// Create Weyl group for G₂
    ///
    /// Order: 12 (isomorphic to dihedral group D₆)
    #[must_use]
    pub const fn g2() -> Self {
        Self::new(CartanMatrix::g2(), 12)
    }

    /// Generate G₂ simple roots (exact rational coordinates)
    ///
    /// Returns 2 simple roots in 3D space:
    /// - α₁ = [1, -1, 0] (short root)
    /// - α₂ = [-2, 1, 1] (long root)
    ///
    /// From certified Python implementation: `generate_simple_roots()`
    #[must_use]
    pub fn simple_roots_3d() -> Vec<RationalVector<3>> {
        use num_rational::Ratio;

        vec![
            // α₁: short simple root
            RationalVector::new([Ratio::new(1, 1), Ratio::new(-1, 1), Ratio::new(0, 1)]),
            // α₂: long simple root
            RationalVector::new([Ratio::new(-2, 1), Ratio::new(1, 1), Ratio::new(1, 1)]),
        ]
    }
}

impl WeylGroup<4> {
    /// Create Weyl group for F₄
    ///
    /// Order: 1,152
    #[must_use]
    pub const fn f4() -> Self {
        Self::new(CartanMatrix::f4(), 1152)
    }

    /// Generate F₄ simple roots (exact rational coordinates)
    ///
    /// Returns 4 simple roots in 4D space (standard F₄ root system):
    /// - α₁ = [0, 1, -1, 0]
    /// - α₂ = [0, 0, 1, -1]
    /// - α₃ = [0, 0, 0, 1]
    /// - α₄ = [1/2, -1/2, -1/2, -1/2]
    ///
    /// From certified Python implementation: `generate_simple_roots()`
    #[must_use]
    pub fn simple_roots_4d() -> Vec<RationalVector<4>> {
        use num_rational::Ratio;

        vec![
            // α₁
            RationalVector::new([
                Ratio::new(0, 1),
                Ratio::new(1, 1),
                Ratio::new(-1, 1),
                Ratio::new(0, 1),
            ]),
            // α₂
            RationalVector::new([
                Ratio::new(0, 1),
                Ratio::new(0, 1),
                Ratio::new(1, 1),
                Ratio::new(-1, 1),
            ]),
            // α₃
            RationalVector::new([
                Ratio::new(0, 1),
                Ratio::new(0, 1),
                Ratio::new(0, 1),
                Ratio::new(1, 1),
            ]),
            // α₄ (half-integer coordinates)
            RationalVector::new([
                Ratio::new(1, 2),
                Ratio::new(-1, 2),
                Ratio::new(-1, 2),
                Ratio::new(-1, 2),
            ]),
        ]
    }
}

impl WeylGroup<6> {
    /// Create Weyl group for E₆
    ///
    /// Order: 51,840
    #[must_use]
    pub const fn e6() -> Self {
        Self::new(CartanMatrix::e6(), 51840)
    }
}

impl WeylGroup<7> {
    /// Create Weyl group for E₇
    ///
    /// Order: 2,903,040
    #[must_use]
    pub const fn e7() -> Self {
        Self::new(CartanMatrix::e7(), 2_903_040)
    }
}

impl WeylGroup<8> {
    /// Create Weyl group for E₈
    ///
    /// Order: 696,729,600
    #[must_use]
    pub const fn e8() -> Self {
        Self::new(CartanMatrix::e8(), 696_729_600)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::HalfInteger;

    #[test]
    fn test_simple_reflection_involution() {
        // Create a simple root (1, -1, 0, 0, 0, 0, 0, 0)
        let alpha = Vector8::new([
            HalfInteger::from_integer(1),
            HalfInteger::from_integer(-1),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
        ]);

        let refl = SimpleReflection::from_root(&alpha);

        // Test on a vector
        let v = Vector8::new([HalfInteger::from_integer(1); 8]);

        assert!(refl.verify_involution(&v), "Reflection must be an involution");
    }

    #[test]
    fn test_reflection_perpendicular_to_root() {
        // Create root (1, 0, 0, 0, 0, 0, 0, 0)
        let alpha = Vector8::new([
            HalfInteger::from_integer(1),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
        ]);

        let refl = SimpleReflection::from_root(&alpha);

        // Reflect the root itself: s_α(α) = -α
        let reflected = refl.apply(&alpha);
        let neg_alpha = alpha.scale_rational(Rational::new(-1, 1));

        assert_eq!(reflected, neg_alpha, "s_α(α) must equal -α");
    }

    #[test]
    fn test_g2_weyl_order() {
        let weyl = WeylGroup::g2();
        assert_eq!(weyl.order(), 12, "G₂ Weyl group has order 12");
    }

    #[test]
    fn test_f4_weyl_order() {
        let weyl = WeylGroup::f4();
        assert_eq!(weyl.order(), 1152, "F₄ Weyl group has order 1,152");
    }

    #[test]
    fn test_e6_weyl_order() {
        let weyl = WeylGroup::e6();
        assert_eq!(weyl.order(), 51840, "E₆ Weyl group has order 51,840");
    }

    #[test]
    fn test_e7_weyl_order() {
        let weyl = WeylGroup::e7();
        assert_eq!(weyl.order(), 2_903_040, "E₇ Weyl group has order 2,903,040");
    }

    #[test]
    fn test_e8_weyl_order() {
        let weyl = WeylGroup::e8();
        assert_eq!(weyl.order(), 696_729_600, "E₈ Weyl group has order 696,729,600");
    }

    #[test]
    fn test_coxeter_numbers_g2() {
        let weyl = WeylGroup::g2();

        // Diagonal
        assert_eq!(weyl.coxeter_number(0, 0), 1, "m_00 = 1");
        assert_eq!(weyl.coxeter_number(1, 1), 1, "m_11 = 1");

        // Triple bond
        assert_eq!(weyl.coxeter_number(0, 1), 6, "G₂ triple bond: m_01 = 6");
        assert_eq!(weyl.coxeter_number(1, 0), 6, "G₂ triple bond: m_10 = 6");
    }

    #[test]
    fn test_coxeter_numbers_f4() {
        let weyl = WeylGroup::f4();

        // Check double bond (indices 1,2)
        let m_12 = weyl.coxeter_number(1, 2);
        assert_eq!(m_12, 4, "F₄ double bond: m_12 = 4");
    }

    #[test]
    fn test_coxeter_numbers_e6() {
        let weyl = WeylGroup::e6();

        // E₆ is simply-laced: all off-diagonal Coxeter numbers are 3
        for i in 0..6 {
            for j in 0..6 {
                if i != j && weyl.cartan_matrix().get(i, j) != 0 {
                    assert_eq!(
                        weyl.coxeter_number(i, j),
                        3,
                        "E₆ is simply-laced: m_{{{i}{j}}} = 3"
                    );
                }
            }
        }
    }

    // ========================================================================
    // Weyl Group Generation Tests
    // ========================================================================

    #[test]
    fn test_g2_weyl_generation() {
        use crate::arithmetic::RationalMatrix;

        // Generate G₂ simple roots in 3D space
        let simple_roots = WeylGroup::simple_roots_3d();

        // Create WeylGroup for 3D (not rank 2, but dimension 3)
        let weyl = WeylGroup::<3>::new(
            CartanMatrix::new([
                [2, -3, 0],
                [-1, 2, 0],
                [0, 0, 2], // Dummy row for 3D
            ]),
            12,
        );

        // Generate group with max_length = 10 (should be enough for order 12)
        let elements = weyl.generate_elements(&simple_roots, 10);

        // G₂ Weyl group has order 12
        assert_eq!(elements.len(), 12, "G₂ Weyl group must have 12 elements");

        // All elements must be distinct (exact equality)
        // This is verified by HashSet containing 12 elements

        // Check identity is present
        let identity = RationalMatrix::<3>::identity();
        assert!(elements.contains(&identity), "Group must contain identity");
    }

    #[test]
    fn test_g2_reflections_involution() {
        use crate::arithmetic::RationalMatrix;

        let simple_roots = WeylGroup::simple_roots_3d();

        // Create reflection matrices
        let s1 = RationalMatrix::reflection(&simple_roots[0]);
        let s2 = RationalMatrix::reflection(&simple_roots[1]);

        // Verify s_i² = I (reflections are involutions)
        let identity = RationalMatrix::<3>::identity();

        let s1_squared = s1.multiply(&s1);
        assert_eq!(s1_squared, identity, "s₁² must equal identity");

        let s2_squared = s2.multiply(&s2);
        assert_eq!(s2_squared, identity, "s₂² must equal identity");
    }

    #[test]
    fn test_f4_simple_roots() {
        let simple_roots = WeylGroup::simple_roots_4d();

        // F₄ has 4 simple roots
        assert_eq!(simple_roots.len(), 4);

        // Verify Cartan matrix from inner products
        let f4_cartan = CartanMatrix::f4();

        for i in 0..4 {
            for j in 0..4 {
                let alpha_i = &simple_roots[i];
                let alpha_j = &simple_roots[j];

                // Cartan entry: 2⟨αᵢ, αⱼ⟩/⟨αⱼ, αⱼ⟩
                let computed = Rational::new(2, 1) * alpha_i.dot(alpha_j) / alpha_j.norm_squared();
                let expected = Rational::new(f4_cartan.get(i, j).into(), 1);

                assert_eq!(
                    computed, expected,
                    "Cartan[{i}][{j}] mismatch: computed {computed}, expected {expected}"
                );
            }
        }
    }

    #[test]
    #[ignore = "This test is slow (F₄ has 1,152 elements) - run with --ignored"]
    fn test_f4_weyl_generation() {
        use crate::arithmetic::RationalMatrix;

        println!("\n=== F₄ Weyl Group Generation (1,152 elements) ===");

        let simple_roots = WeylGroup::simple_roots_4d();
        let weyl = WeylGroup::f4();

        // Generate group (max_length = 30 should be sufficient)
        let start = std::time::Instant::now();
        let elements = weyl.generate_elements(&simple_roots, 30);
        let duration = start.elapsed();

        println!("Generated {} elements in {:.2?}", elements.len(), duration);

        // F₄ Weyl group has order 1,152
        assert_eq!(elements.len(), 1152, "F₄ Weyl group must have 1,152 elements");

        // Check identity is present
        let identity = RationalMatrix::<4>::identity();
        assert!(elements.contains(&identity), "Group must contain identity");

        // Verify all generators are involutions
        for root in &simple_roots {
            let s = RationalMatrix::reflection(root);
            let s_squared = s.multiply(&s);
            assert_eq!(s_squared, identity, "Reflection must be involution");
        }
    }

    #[test]
    fn test_rational_matrix_exact_equality() {
        use crate::arithmetic::RationalMatrix;

        let a = RationalMatrix::<2>::identity();
        let b = RationalMatrix::<2>::identity();

        // Exact equality (not tolerance-based)
        assert_eq!(a, b);

        let c = RationalMatrix::new([
            [Rational::new(1, 1), Rational::new(1, 1_000_000)],
            [Rational::new(0, 1), Rational::new(1, 1)],
        ]);

        // Even tiny rational differences are detected
        assert_ne!(a, c);
    }
}
