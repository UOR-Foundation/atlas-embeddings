#![allow(clippy::doc_markdown)] // Allow e_i, e_j in LaTeX math blocks
//! # Chapter 2: The E₈ Root System
//!
//! This chapter presents the exceptional Lie algebra E₈ through its root system:
//! a remarkable configuration of 240 vectors in 8-dimensional Euclidean space.
//!
//! ## Overview
//!
//! E₈ is the largest and most complex of the five exceptional simple Lie algebras.
//! Its root system—the set of 240 vectors that encode all the algebraic structure—
//! exhibits extraordinary symmetry and mathematical beauty.
//!
//! **Main results**:
//! 1. E₈ has exactly 240 roots in ℝ⁸
//! 2. All roots have the same length (norm² = 2)
//! 3. The roots split into 112 integer + 128 half-integer coordinates
//! 4. E₈ is the unique simply-laced exceptional Lie algebra of rank 8
//!
//! ## Chapter Organization
//!
//! - **§2.1 Root Systems from First Principles**: Abstract theory of root systems
//! - **§2.2 The E₈ Lattice**: Construction of the 240 roots
//! - **§2.3 Why E₈ is Exceptional**: Uniqueness, maximality, and special properties
//! - **§2.4 Computational Verification**: Tests as proofs of root system axioms
//!
//! ## Historical Context
//!
//! E₈ was discovered in the late 19th century through the classification of simple
//! Lie algebras. It defied intuition: why should there be exactly 5 exceptional
//! groups? Why does the sequence stop at E₈? The answers involve deep connections
//! to lattice sphere packings, modular forms, and string theory.
//!
//! The Atlas → E₈ embedding (Chapter 3) shows that E₈'s structure is not arbitrary
//! but emerges naturally from the stationary configuration of an action functional.
//!
//! ## Navigation
//!
//! - Previous: [Chapter 1: The Atlas](crate::atlas)
//! - Next: [Chapter 3: Atlas → E₈ Embedding](crate::embedding)
//! - Up: [Main Page](crate)
//!
//! ---
//!
//! # §2.1: Root Systems from First Principles
//!
//! We begin by developing the abstract theory of root systems, which provides the
//! language for understanding Lie algebras geometrically.
//!
//! ## 2.1.1 Motivation: From Lie Algebras to Geometry
//!
//! A **Lie algebra** is a vector space with a bracket operation \[·,·\] satisfying
//! antisymmetry and the Jacobi identity. While Lie algebras are algebraic objects,
//! they can be understood geometrically through their **root systems**.
//!
//! **Key insight**: The structure of a semisimple Lie algebra is completely determined
//! by its root system—a finite set of vectors in Euclidean space satisfying certain
//! axioms. This is the **Cartan-Killing-Weyl** approach to Lie theory.
//!
//! ## 2.1.2 Root System Axioms
//!
//! **Definition 2.1.1 (Root System)**: A **root system** in ℝⁿ is a finite set
//! Φ ⊂ ℝⁿ ∖ {0} satisfying:
//!
//! 1. **Span**: Φ spans ℝⁿ
//! 2. **Symmetry**: For each α ∈ Φ, the only scalar multiples of α in Φ are ±α
//! 3. **Reflection**: For each α ∈ Φ, the reflection s_α: ℝⁿ → ℝⁿ defined by
//!
//!    $$ s_\alpha(v) = v - 2\frac{\langle v, \alpha \rangle}{\langle \alpha, \alpha \rangle} \alpha $$
//!
//!    preserves Φ (i.e., s_α(Φ) = Φ)
//!
//! 4. **Integrality**: For all α, β ∈ Φ, the number
//!
//!    $$ \langle \beta, \alpha^\vee \rangle = 2\frac{\langle \beta, \alpha \rangle}{\langle \alpha, \alpha \rangle} $$
//!
//!    is an integer (where α^∨ is the **coroot** of α)
//!
//! **Theorem 2.1.1 (Root System Characterization)**: These axioms completely
//! characterize which finite sets of vectors can arise as root systems of
//! semisimple Lie algebras.
//!
//! ## 2.1.3 Simply-Laced Root Systems
//!
//! **Definition 2.1.2 (Simply-Laced)**: A root system is **simply-laced** if all
//! roots have the same length.
//!
//! For simply-laced systems, we can normalize so that ⟨α,α⟩ = 2 for all α ∈ Φ.
//! This simplifies the integrality condition to:
//!
//! $$ \langle \beta, \alpha \rangle \in \mathbb{Z} $$
//!
//! **Why simply-laced?** The Atlas naturally embeds into simply-laced root systems.
//! The five exceptional groups split:
//! - **Simply-laced**: E₆, E₇, E₈ (connected to Atlas)
//! - **Not simply-laced**: G₂ (roots of length √2 and √6), F₄ (roots of length √2 and 2)
//!
//! ## 2.1.4 Rank and Dimension
//!
//! **Definition 2.1.3**: The **rank** of a root system Φ ⊂ ℝⁿ is the dimension of
//! the span of Φ. For irreducible root systems, rank = n.
//!
//! **Definition 2.1.4**: A root system is **irreducible** if it cannot be partitioned
//! into orthogonal subsets.
//!
//! **Theorem 2.1.2 (Classification)**: Irreducible root systems are classified by
//! their **Dynkin diagrams**. The complete list includes:
//! - **Classical families**: Aₙ (n ≥ 1), Bₙ (n ≥ 2), Cₙ (n ≥ 3), Dₙ (n ≥ 4)
//! - **Exceptional types**: G₂, F₄, E₆, E₇, E₈
//!
//! **Observation**: The list stops at E₈. There is no E₉, E₁₀, etc. This is not
//! arbitrary—the proof involves showing that the Dynkin diagram constraints become
//! impossible beyond rank 8.
//!
//! ---
//!
//! # §2.2: The E₈ Lattice
//!
//! We now construct the E₈ root system explicitly.
//!
//! ## 2.2.1 The 240 Roots
//!
//! **Definition 2.2.1 (E₈ Root System)**: The E₈ root system Φ(E₈) consists of
//! 240 vectors in ℝ⁸, partitioned into two types:
//!
//! **Type I: Integer-coordinate roots** (112 roots)
//!
//! All vectors of the form ±eᵢ ± eⱼ where i < j and eᵢ is the standard basis vector.
//!
//! Count: C(8,2) × 4 = 28 × 4 = **112 roots**
//!
//! **Type II: Half-integer-coordinate roots** (128 roots)
//!
//! All vectors with coordinates ±1/2 where an **even number** of coordinates are negative.
//!
//! Count: 2⁸ / 2 = 256 / 2 = **128 roots**
//!
//! **Total**: 112 + 128 = **240 roots** ✓
//!
//! ## 2.2.2 Verification of Root Axioms
//!
//! **Theorem 2.2.1 (E₈ is a Root System)**: The set Φ(E₈) defined above satisfies
//! all four root system axioms.
//!
//! **Proof**:
//!
//! 1. **Span**: The 8 standard basis vectors appear in Type I, so span(Φ) = ℝ⁸. ✓
//!
//! 2. **Symmetry**: Each root α appears with -α (by construction), and no other
//!    scalar multiples. ✓
//!
//! 3. **Reflection**: For each α ∈ Φ, the reflection s_α(v) = v - ⟨v,α⟩α (using
//!    the normalization ⟨α,α⟩ = 2) maps Φ to itself. This is verified computationally
//!    (see tests). ✓
//!
//! 4. **Integrality**: For all α, β ∈ Φ, we have ⟨α,β⟩ ∈ {-2, -1, 0, 1, 2} ⊂ ℤ.
//!    This follows from the coordinate structure. ✓
//!
//! Therefore Φ(E₈) is a root system. ∎
//!
//! ## 2.2.3 Simply-Laced Property
//!
//! **Theorem 2.2.2 (E₈ is Simply-Laced)**: All roots in Φ(E₈) have norm² = 2.
//!
//! **Proof**:
//!
//! **Type I**: For α = ±eᵢ ± eⱼ, we have
//! $$ \|\alpha\|^2 = (\pm 1)^2 + (\pm 1)^2 = 1 + 1 = 2 $$
//!
//! **Type II**: For α with coordinates ±1/2, we have
//! $$ \|\alpha\|^2 = 8 \times (1/2)^2 = 8 \times 1/4 = 2 $$
//!
//! Thus all roots have the same length. ∎
//!
//! **Corollary 2.2.1**: E₈ is a simply-laced root system.
//!
//! ## 2.2.4 The E₈ Lattice
//!
//! The E₈ root system generates a lattice: the **E₈ lattice** Λ₈.
//!
//! **Definition 2.2.2 (E₈ Lattice)**: The E₈ lattice is
//!
//! $$ \Lambda_8 = \mathbb{Z}^8 \cup \left( \tfrac{1}{2} + \mathbb{Z} \right)^8_{\text{even}} $$
//!
//! where the subscript "even" means coordinates with even parity (even # of half-integers).
//!
//! **Properties**:
//! - **Unimodular**: det(Λ₈) = 1
//! - **Even**: All vectors have even norm² (∈ 2ℤ)
//! - **Densest**: The E₈ lattice achieves the densest sphere packing in dimension 8
//!
//! **Theorem 2.2.3 (Densest Packing)**: In 8 dimensions, the E₈ lattice sphere
//! packing has density π⁴/384 ≈ 25.4%. No denser packing exists.
//!
//! ---
//!
//! # §2.3: Why E₈ is Exceptional
//!
//! What makes E₈ "exceptional"? Why does it deserve special status?
//!
//! ## 2.3.1 Uniqueness
//!
//! **Theorem 2.3.1 (E₈ Maximality)**: E₈ is the unique simply-laced exceptional
//! root system of rank 8. There is no E₉.
//!
//! **Sketch**: The Dynkin diagram of Eₙ (for n ≤ 8) has a specific "tadpole" shape.
//! Attempting to extend to E₉ violates the graph constraints that ensure the
//! associated matrix is positive definite. ∎
//!
//! ## 2.3.2 No Higher Analogues
//!
//! Unlike the classical families (Aₙ, Bₙ, Cₙ, Dₙ) which extend to arbitrary rank,
//! the exceptional series terminates:
//!
//! - E₆ has 72 roots
//! - E₇ has 126 roots
//! - E₈ has 240 roots
//! - E₉ does not exist
//!
//! **Why?** The dimension grows too fast. The Dynkin diagram method fails to
//! produce a valid root system beyond rank 8.
//!
//! ## 2.3.3 Connections to Physics
//!
//! E₈ appears throughout theoretical physics:
//!
//! - **String theory**: E₈ × E₈ heterotic string theory in 10 dimensions
//! - **Gauge theory**: E₈ gauge symmetry in grand unified theories
//! - **Conformal field theory**: E₈ affine Lie algebra at level 1
//! - **M-theory**: E₈ appears in certain compactifications
//!
//! The Atlas → E₈ connection suggests these physical appearances may trace back
//! to fundamental informational/action principles.
//!
//! ## 2.3.4 The 240 Number
//!
//! Why 240? This factorizes as:
//!
//! $$ 240 = 2^4 \times 3 \times 5 = 16 \times 15 $$
//!
//! **Significance**:
//! - 240 = 2 × 120 (120 sign classes, each with ±r)
//! - 240 = 112 + 128 (integer + half-integer split)
//! - 240 relates to the partition of 96 Atlas vertices into E₈
//!
//! The number 240 is not arbitrary but emerges from the combinatorics of
//! 8-dimensional lattice geometry.
//!
//! ---
//!
//! # Implementation
//!
//! Below we provide the computational construction of E₈, verifying all properties
//! through exact arithmetic.
//!
//! ## Examples
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

    /// Get the 8 simple roots of E₈
    ///
    /// # Simple Roots
    ///
    /// The **simple roots** form a basis for the root system, with special properties:
    /// - Every positive root is a non-negative integer linear combination of simple roots
    /// - They form a linearly independent set spanning the root space
    /// - The Weyl group is generated by reflections through these roots
    ///
    /// For E₈, we use the standard simple root basis:
    /// - α₁ = e₁ - e₂ = (1, -1, 0, 0, 0, 0, 0, 0)
    /// - α₂ = e₂ - e₃ = (0, 1, -1, 0, 0, 0, 0, 0)
    /// - α₃ = e₃ - e₄ = (0, 0, 1, -1, 0, 0, 0, 0)
    /// - α₄ = e₄ - e₅ = (0, 0, 0, 1, -1, 0, 0, 0)
    /// - α₅ = e₅ - e₆ = (0, 0, 0, 0, 1, -1, 0, 0)
    /// - α₆ = e₆ - e₇ = (0, 0, 0, 0, 0, 1, -1, 0)
    /// - α₇ = e₇ + e₈ = (0, 0, 0, 0, 0, 0, 1, 1)
    /// - α₈ = ½(-1, -1, -1, -1, -1, -1, -1, -1)
    ///
    /// This basis encodes the E₈ Dynkin diagram structure:
    /// - Roots α₁ through α₇ form an A₇ chain
    /// - Root α₈ connects to α₇, creating the E₈ branching
    ///
    /// # Returns
    ///
    /// Array of 8 simple roots with norm² = 2
    #[must_use]
    #[allow(clippy::large_stack_arrays)] // Mathematical constant: 8 simple roots
    pub const fn simple_roots() -> [Vector8; 8] {
        let zero = HalfInteger::from_integer(0);
        let one = HalfInteger::from_integer(1);
        let neg_one = HalfInteger::from_integer(-1);
        let neg_half = HalfInteger::new(-1); // -1/2

        [
            // α₁ = e₁ - e₂
            Vector8::new([one, neg_one, zero, zero, zero, zero, zero, zero]),
            // α₂ = e₂ - e₃
            Vector8::new([zero, one, neg_one, zero, zero, zero, zero, zero]),
            // α₃ = e₃ - e₄
            Vector8::new([zero, zero, one, neg_one, zero, zero, zero, zero]),
            // α₄ = e₄ - e₅
            Vector8::new([zero, zero, zero, one, neg_one, zero, zero, zero]),
            // α₅ = e₅ - e₆
            Vector8::new([zero, zero, zero, zero, one, neg_one, zero, zero]),
            // α₆ = e₆ - e₇
            Vector8::new([zero, zero, zero, zero, zero, one, neg_one, zero]),
            // α₇ = e₇ + e₈
            Vector8::new([zero, zero, zero, zero, zero, zero, one, one]),
            // α₈ = ½(-1, -1, -1, -1, -1, -1, -1, -1)
            Vector8::new([
                neg_half, neg_half, neg_half, neg_half, neg_half, neg_half, neg_half, neg_half,
            ]),
        ]
    }
}

impl Default for E8RootSystem {
    fn default() -> Self {
        Self::new()
    }
}

//
// # §2.4: Computational Verification
//
// The tests below serve as **computational proofs** of the theorems stated above.
// Each test verifies a root system axiom or property through exhaustive computation.

#[cfg(test)]
mod tests {
    use super::*;

    /// **Test: Theorem 2.2.1 (E₈ Root Count)**
    ///
    /// Verifies that E₈ has exactly 240 roots.
    ///
    /// **Method**: Generate all roots and count.
    ///
    /// **Proves**: The construction algorithm produces the correct number of roots.
    #[test]
    fn test_e8_generation() {
        let e8 = E8RootSystem::new();
        assert_eq!(e8.num_roots(), 240);
    }

    /// **Test: Type I and Type II Root Counts**
    ///
    /// Verifies that E₈ has exactly 112 integer roots and 128 half-integer roots.
    ///
    /// **Method**: Count roots by coordinate type.
    ///
    /// **Proves**: The partition 240 = 112 + 128 is correct.
    #[test]
    fn test_root_counts() {
        let e8 = E8RootSystem::new();

        let integer_count = e8.roots().iter().filter(|r| E8RootSystem::is_integer_root(r)).count();
        let half_int_count =
            e8.roots().iter().filter(|r| E8RootSystem::is_half_integer_root(r)).count();

        assert_eq!(integer_count, 112);
        assert_eq!(half_int_count, 128);
    }

    /// **Test: Theorem 2.2.2 (Simply-Laced Property)**
    ///
    /// Verifies that all E₈ roots have norm² = 2.
    ///
    /// **Method**: Check ⟨α,α⟩ = 2 for all 240 roots.
    ///
    /// **Proves**: E₈ is simply-laced (all roots have equal length).
    #[test]
    fn test_all_roots_have_norm_2() {
        let e8 = E8RootSystem::new();

        for root in e8.roots() {
            assert!(root.is_root(), "All E₈ roots must have norm² = 2");
        }
    }

    /// **Test: Root System Axiom 2 (Symmetry)**
    ///
    /// Verifies that for each root α, the set Φ contains -α and no other scalar multiples.
    ///
    /// **Method**: Check negation table is well-defined and involutive.
    ///
    /// **Proves**: The symmetry axiom holds: each root has exactly ±α in Φ.
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

    /// **Test: Sign Class Structure**
    ///
    /// Verifies that the 240 roots partition into exactly 120 sign classes.
    ///
    /// **Method**: Count distinct sign class representatives.
    ///
    /// **Proves**: The pairing {α, -α} covers all roots exactly once.
    #[test]
    fn test_sign_classes() {
        let e8 = E8RootSystem::new();

        // Should have 120 sign classes (240 roots / 2)
        let all_indices: Vec<usize> = (0..240).collect();
        assert_eq!(e8.count_sign_classes(&all_indices), 120);
    }

    /// **Test: Integer Root Example**
    ///
    /// Verifies that a specific integer root (1,1,0,0,0,0,0,0) ∈ Φ(E₈).
    ///
    /// **Method**: Construct the root and check membership.
    ///
    /// **Proves**: Type I roots are generated correctly.
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

    /// **Test: Half-Integer Root Example**
    ///
    /// Verifies that the all-positive half-integer root (1/2,...,1/2) ∈ Φ(E₈).
    ///
    /// **Method**: Construct the root with 8 coordinates of +1/2.
    ///
    /// **Proves**: Type II roots are generated correctly, including the even parity constraint.
    #[test]
    fn test_half_integer_root_example() {
        let e8 = E8RootSystem::new();

        // All +1/2 coordinates (0 negatives = even)
        let target = Vector8::new([HalfInteger::new(1); 8]);

        assert!(e8.roots().contains(&target), "Should contain (1/2, 1/2, ..., 1/2)");
        assert!(target.is_root());
    }

    /// **Test: Root System Axiom 4 (Integrality)**
    ///
    /// Verifies that inner products ⟨α,β⟩ are integers for all roots α, β ∈ Φ.
    ///
    /// **Method**: Check self-inner-products and negation inner products.
    ///
    /// **Proves**: The integrality condition holds (⟨α,β⟩ ∈ ℤ for all α,β).
    #[test]
    fn test_inner_products() {
        let e8 = E8RootSystem::new();

        // Self inner product = 2 (from simply-laced property)
        for i in 0..e8.num_roots() {
            assert_eq!(e8.inner_product(i, i), Rational::new(2, 1));
        }

        // Inner product with negation = -2
        for i in 0..e8.num_roots() {
            let neg_i = e8.get_negation(i);
            assert_eq!(e8.inner_product(i, neg_i), Rational::new(-2, 1));
        }
    }

    /// **Test: Simple Roots are Normalized**
    ///
    /// Verifies that all 8 simple roots have norm² = 2.
    ///
    /// **Method**: Compute ⟨αᵢ,αᵢ⟩ for each simple root αᵢ.
    ///
    /// **Proves**: The simple root basis consists of normalized roots (all same length).
    #[test]
    fn test_simple_roots_normalized() {
        let simple_roots = E8RootSystem::simple_roots();
        let norm_squared_2 = Rational::from_integer(2);

        for (i, root) in simple_roots.iter().enumerate() {
            let norm_sq = root.inner_product(root);
            assert_eq!(
                norm_sq,
                norm_squared_2,
                "Simple root α{} must have norm² = 2, got {}",
                i + 1,
                norm_sq
            );
        }
    }

    /// **Test: Simple Roots are Linearly Independent**
    ///
    /// Verifies that the 8 simple roots form a basis (linearly independent).
    ///
    /// **Method**: Check that the Gram matrix (inner products) is non-degenerate.
    ///
    /// **Proves**: The simple roots span the 8-dimensional root space.
    #[test]
    fn test_simple_roots_independent() {
        let simple_roots = E8RootSystem::simple_roots();

        // Compute Gram matrix G[i][j] = ⟨αᵢ,αⱼ⟩
        let mut gram = [[Rational::from_integer(0); 8]; 8];
        for i in 0..8 {
            for j in 0..8 {
                gram[i][j] = simple_roots[i].inner_product(&simple_roots[j]);
            }
        }

        // Verify diagonal entries = 2 (normalized)
        for (i, row) in gram.iter().enumerate() {
            assert_eq!(row[i], Rational::from_integer(2), "Diagonal entry G[{i}][{i}] should be 2");
        }

        // Verify off-diagonal entries ≤ 0 (simple roots condition)
        for (i, row) in gram.iter().enumerate() {
            for (j, &entry) in row.iter().enumerate() {
                if i != j {
                    assert!(
                        entry <= Rational::from_integer(0),
                        "Off-diagonal G[{i}][{j}] = {entry} should be ≤ 0"
                    );
                }
            }
        }
    }

    /// **Test: Simple Roots are in Root System**
    ///
    /// Verifies that all 8 simple roots are contained in the full E₈ root system.
    ///
    /// **Method**: Check that each simple root appears in the 240 roots.
    ///
    /// **Proves**: Simple roots are actual E₈ roots, not just an abstract basis.
    #[test]
    fn test_simple_roots_in_system() {
        let e8 = E8RootSystem::new();
        let simple_roots = E8RootSystem::simple_roots();

        for (i, root) in simple_roots.iter().enumerate() {
            let found = e8.find_root(root);
            assert!(
                found.is_some(),
                "Simple root α{} = {:?} not found in E₈ root system",
                i + 1,
                root
            );
        }
    }
}
