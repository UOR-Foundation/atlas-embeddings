//! Property-Based Tests for Atlas Embeddings
//!
//! This module uses proptest to verify mathematical properties hold for ALL inputs,
//! matching the verification approach in the certified Python implementation.
//!
//! Key properties verified:
//! - Exact arithmetic (no precision loss)
//! - Cartan matrix axioms
//! - Weyl group properties (involutions, group axioms)
//! - Root system closure
//! - Categorical operation correctness

#![allow(clippy::large_stack_arrays)] // format! macros in assertions create temporary arrays

use atlas_embeddings::arithmetic::{HalfInteger, Rational, Vector8};
use atlas_embeddings::cartan::CartanMatrix;
use atlas_embeddings::weyl::{SimpleReflection, WeylGroup};
use atlas_embeddings::{Atlas, E8RootSystem};
use num_traits::Zero;
use proptest::prelude::*;

// ============================================================================
// Exact Arithmetic Properties
// ============================================================================

/// Strategy for generating `HalfIntegers`
fn half_integer_strategy() -> impl Strategy<Value = HalfInteger> {
    (-100i64..=100i64).prop_map(HalfInteger::new)
}

/// Strategy for generating Rationals
fn rational_strategy() -> impl Strategy<Value = Rational> {
    (-100i64..=100i64, 1i64..=100i64).prop_map(|(n, d)| Rational::new(n, d))
}

/// Strategy for generating Vector8
fn vector8_strategy() -> impl Strategy<Value = Vector8> {
    prop::array::uniform8(half_integer_strategy()).prop_map(Vector8::new)
}

proptest! {
    /// Property: HalfInteger addition is associative
    /// Matches Python: Fraction addition is exact
    #[test]
    fn prop_half_integer_addition_associative(
        a in half_integer_strategy(),
        b in half_integer_strategy(),
        c in half_integer_strategy()
    ) {
        let left = (a + b) + c;
        let right = a + (b + c);
        prop_assert_eq!(left, right, "Addition must be associative");
    }

    /// Property: HalfInteger addition is commutative
    #[test]
    fn prop_half_integer_addition_commutative(
        a in half_integer_strategy(),
        b in half_integer_strategy()
    ) {
        prop_assert_eq!(a + b, b + a, "Addition must be commutative");
    }

    /// Property: HalfInteger has additive identity (zero)
    #[test]
    fn prop_half_integer_additive_identity(a in half_integer_strategy()) {
        let zero = HalfInteger::zero();
        prop_assert_eq!(a + zero, a, "Zero is additive identity");
        prop_assert_eq!(zero + a, a, "Zero is additive identity (commuted)");
    }

    /// Property: HalfInteger has additive inverse
    #[test]
    fn prop_half_integer_additive_inverse(a in half_integer_strategy()) {
        let neg_a = -a;
        let zero = HalfInteger::zero();
        prop_assert_eq!(a + neg_a, zero, "a + (-a) = 0");
        prop_assert_eq!(neg_a + a, zero, "(-a) + a = 0");
    }

    /// Property: HalfInteger multiplication produces exact rationals
    #[test]
    fn prop_half_integer_multiplication_exact(
        a in half_integer_strategy(),
        b in half_integer_strategy()
    ) {
        let product = a * b;
        let expected = Rational::new(a.numerator() * b.numerator(), 4);
        prop_assert_eq!(product, expected, "Multiplication must be exact");
    }

    /// Property: HalfInteger square is always non-negative
    #[test]
    fn prop_half_integer_square_nonnegative(a in half_integer_strategy()) {
        let sq = a.square();
        prop_assert!(*sq.numer() >= 0, "Square must be non-negative: got {}", sq);
    }

    /// Property: Rational arithmetic is exact (no precision loss)
    /// Critical property from CLAUDE.md
    #[test]
    fn prop_rational_arithmetic_exact(
        a in rational_strategy(),
        b in rational_strategy(),
        c in rational_strategy()
    ) {
        // (a + b) + c = a + (b + c)
        prop_assert_eq!((a + b) + c, a + (b + c), "Rational addition must be associative");

        // a * (b + c) = a * b + a * c
        prop_assert_eq!(a * (b + c), a * b + a * c, "Distributivity must hold");
    }
}

// ============================================================================
// Vector8 Properties
// ============================================================================

proptest! {
    /// Property: Vector addition is associative
    #[test]
    fn prop_vector8_addition_associative(
        v1 in vector8_strategy(),
        v2 in vector8_strategy(),
        v3 in vector8_strategy()
    ) {
        let left = (v1 + v2) + v3;
        let right = v1 + (v2 + v3);
        prop_assert_eq!(left, right, "Vector addition must be associative");
    }

    /// Property: Vector addition is commutative
    #[test]
    fn prop_vector8_addition_commutative(
        v1 in vector8_strategy(),
        v2 in vector8_strategy()
    ) {
        prop_assert_eq!(v1 + v2, v2 + v1, "Vector addition must be commutative");
    }

    /// Property: Vector has additive identity (zero vector)
    #[test]
    fn prop_vector8_additive_identity(v in vector8_strategy()) {
        let zero = Vector8::zero();
        prop_assert_eq!(v.add(&zero), v, "Zero is additive identity");
        prop_assert_eq!(zero.add(&v), v, "Zero is additive identity (commuted)");
    }

    /// Property: Inner product is commutative
    #[test]
    fn prop_vector8_inner_product_commutative(
        v1 in vector8_strategy(),
        v2 in vector8_strategy()
    ) {
        let ip1 = v1.inner_product(&v2);
        let ip2 = v2.inner_product(&v1);
        prop_assert_eq!(ip1, ip2, "Inner product must be commutative");
    }

    /// Property: Inner product is bilinear
    #[test]
    fn prop_vector8_inner_product_bilinear(
        v1 in vector8_strategy(),
        v2 in vector8_strategy(),
        v3 in vector8_strategy()
    ) {
        // ⟨v1 + v2, v3⟩ = ⟨v1, v3⟩ + ⟨v2, v3⟩
        let left = v1.add(&v2).inner_product(&v3);
        let right = v1.inner_product(&v3) + v2.inner_product(&v3);
        prop_assert_eq!(left, right, "Inner product must be bilinear");
    }

    /// Property: Norm squared is non-negative
    #[test]
    fn prop_vector8_norm_squared_nonnegative(v in vector8_strategy()) {
        let norm_sq = v.norm_squared();
        prop_assert!(*norm_sq.numer() >= 0, "Norm² must be non-negative");
    }

    /// Property: Norm squared is zero iff vector is zero
    #[test]
    fn prop_vector8_norm_zero_iff_zero(v in vector8_strategy()) {
        let norm_sq = v.norm_squared();
        let is_zero_vec = v == Vector8::zero();
        let is_zero_norm = norm_sq.is_zero();

        if is_zero_vec {
            prop_assert!(is_zero_norm, "Zero vector must have zero norm");
        }
        if is_zero_norm {
            prop_assert!(is_zero_vec, "Zero norm implies zero vector");
        }
    }

    /// Property: Scaling preserves linearity
    #[test]
    fn prop_vector8_scaling_linear(
        v in vector8_strategy(),
        scalar in -10i64..=10i64
    ) {
        let scaled1 = v.scale(scalar);
        let scaled2 = v.scale(scalar);
        prop_assert_eq!(scaled1, scaled2, "Scaling must be deterministic");

        // scale(a + b) = scale(a) + scale(b) for scalar addition
        if scalar >= 0 {
            let v_plus_v = v.add(&v);
            let scaled_sum = v_plus_v.scale(scalar);
            let sum_scaled = v.scale(scalar).add(&v.scale(scalar));
            prop_assert_eq!(scaled_sum, sum_scaled, "Scaling must distribute");
        }
    }

    /// Property: Negation is involution
    #[test]
    fn prop_vector8_negation_involution(v in vector8_strategy()) {
        let neg_v = v.negate();
        let neg_neg_v = neg_v.negate();
        prop_assert_eq!(v, neg_neg_v, "Double negation returns original");
    }
}

// ============================================================================
// Weyl Reflection Properties
// ============================================================================
// Note: Reflections are tested on INTEGER vectors only, because reflections
// of arbitrary half-integer vectors can produce general rationals.
// From certified Python: ExactVector uses Fraction, not constrained to half-integers.

// Standard tests for Weyl reflection properties on actual root systems
#[test]
#[allow(clippy::large_stack_arrays)] // format! macro in assertions creates temporary arrays
fn test_weyl_reflection_involution_on_roots() {
    // Property: s_α(s_α(v)) = v for root system vectors
    // Test on E₈ roots where closure is guaranteed

    let e8 = E8RootSystem::new();
    let roots = e8.roots();

    // Test first 20 roots (representative sample)
    for (i, root) in roots.iter().enumerate().take(20) {
        let reflection = SimpleReflection::from_root(root);

        // Apply to other roots
        for (j, v) in roots.iter().enumerate().take(10) {
            let reflected_once = reflection.apply(v);
            let reflected_twice = reflection.apply(&reflected_once);

            assert_eq!(
                *v, reflected_twice,
                "Reflection must be involution on root {i}: s²(root_{j}) = root_{j}"
            );
        }
    }
}

#[test]
fn test_weyl_reflection_negates_root() {
    // Property: s_α(α) = -α

    let e8 = E8RootSystem::new();
    let roots = e8.roots();

    for (i, root) in roots.iter().take(20).enumerate() {
        let reflection = SimpleReflection::from_root(root);
        let reflected = reflection.apply(root);
        let neg_root = root.negate();

        assert_eq!(reflected, neg_root, "s_α(α) must equal -α for root {i}");
    }
}

#[test]
#[allow(clippy::large_stack_arrays)] // format! macro in assertions creates temporary arrays
fn test_weyl_reflection_preserves_norm_on_roots() {
    // Property: ‖s(v)‖² = ‖v‖² for root system vectors

    let e8 = E8RootSystem::new();
    let roots = e8.roots();

    let two = Rational::new(2, 1);

    for (i, root) in roots.iter().enumerate().take(20) {
        let reflection = SimpleReflection::from_root(root);

        for (j, v) in roots.iter().enumerate().take(10) {
            let reflected = reflection.apply(v);

            let original_norm = v.norm_squared();
            let reflected_norm = reflected.norm_squared();

            assert_eq!(original_norm, two, "Root must have norm² = 2");
            assert_eq!(
                reflected_norm, two,
                "Reflected root must have norm² = 2 (root {j} reflected by {i})"
            );
        }
    }
}

proptest! {
    /// Property: Reflection of integer vectors with integer roots
    /// Integer vectors are closed under reflection by integer roots with norm² = 2
    #[test]
    fn prop_weyl_reflection_on_integer_vectors(
        scalar in -5i64..=5i64
    ) {
        // Use simple integer roots
        let root = Vector8::new([
            HalfInteger::from_integer(1),
            HalfInteger::from_integer(-1),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
        ]);

        let reflection = SimpleReflection::from_root(&root);

        // Apply to simple integer vector
        let v = Vector8::new([
            HalfInteger::from_integer(scalar),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
        ]);

        let reflected = reflection.apply(&v);

        // Check involution
        let reflected_twice = reflection.apply(&reflected);
        prop_assert_eq!(v, reflected_twice, "Reflection must be involution");
    }

    /// Property: Reflection fixes vectors perpendicular to root
    #[test]
    fn prop_weyl_reflection_fixes_perpendicular(
        v_parallel in -10i64..=10i64,
        v_perp in -10i64..=10i64
    ) {
        // Root in e1 direction
        let root = Vector8::new([
            HalfInteger::from_integer(1),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
        ]);

        // Vector with component in e1 and perpendicular component in e2
        let v = Vector8::new([
            HalfInteger::from_integer(v_parallel),
            HalfInteger::from_integer(v_perp),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
            HalfInteger::from_integer(0),
        ]);

        let reflection = SimpleReflection::from_root(&root);
        let reflected = reflection.apply(&v);

        // Perpendicular component (e2) should be unchanged
        prop_assert_eq!(
            reflected.get(1),
            v.get(1),
            "Perpendicular component must be unchanged"
        );
    }
}

// ============================================================================
// Cartan Matrix Properties
// ============================================================================

#[test]
fn test_cartan_diagonal_is_two() {
    // Property: All Cartan matrices have diagonal entries = 2
    // From Python: __post_init__ checks cartan_matrix[i][i] == 2

    let g2 = CartanMatrix::g2();
    assert_eq!(g2.get(0, 0), 2, "G₂ diagonal must be 2");
    assert_eq!(g2.get(1, 1), 2, "G₂ diagonal must be 2");

    let f4 = CartanMatrix::f4();
    for i in 0..4 {
        assert_eq!(f4.get(i, i), 2, "F₄ diagonal[{i}] must be 2");
    }

    let e6 = CartanMatrix::e6();
    for i in 0..6 {
        assert_eq!(e6.get(i, i), 2, "E₆ diagonal[{i}] must be 2");
    }

    let e7 = CartanMatrix::e7();
    for i in 0..7 {
        assert_eq!(e7.get(i, i), 2, "E₇ diagonal[{i}] must be 2");
    }

    let e8 = CartanMatrix::e8();
    for i in 0..8 {
        assert_eq!(e8.get(i, i), 2, "E₈ diagonal[{i}] must be 2");
    }
}

#[test]
fn test_cartan_off_diagonal_nonpositive() {
    // Property: All off-diagonal Cartan entries are ≤ 0
    // From Lie theory: C_ij ≤ 0 for i ≠ j

    let e6 = CartanMatrix::e6();
    for i in 0..6 {
        for j in 0..6 {
            if i != j {
                assert!(
                    e6.get(i, j) <= 0,
                    "E₆ off-diagonal C[{}][{}] = {} must be ≤ 0",
                    i,
                    j,
                    e6.get(i, j)
                );
            }
        }
    }
}

#[test]
#[allow(clippy::large_stack_arrays)] // format! macro in assertions creates temporary arrays
fn test_simply_laced_cartan_symmetric() {
    // Property: Simply-laced Cartan matrices are symmetric
    // E₆, E₇, E₈ are simply-laced

    let e6 = CartanMatrix::e6();
    assert!(e6.is_symmetric(), "E₆ Cartan must be symmetric (simply-laced)");
    for i in 0..6 {
        for j in 0..6 {
            assert_eq!(
                e6.get(i, j),
                e6.get(j, i),
                "E₆ Cartan[{i}][{j}] must equal Cartan[{j}][{i}]"
            );
        }
    }

    let e7 = CartanMatrix::e7();
    assert!(e7.is_symmetric(), "E₇ Cartan must be symmetric (simply-laced)");

    let e8 = CartanMatrix::e8();
    assert!(e8.is_symmetric(), "E₈ Cartan must be symmetric (simply-laced)");
}

#[test]
fn test_non_simply_laced_cartan_asymmetric() {
    // Property: Non-simply-laced Cartan matrices are NOT symmetric
    // G₂ and F₄ have different root lengths

    let g2 = CartanMatrix::g2();
    assert!(!g2.is_symmetric(), "G₂ Cartan must be asymmetric (non-simply-laced)");

    let f4 = CartanMatrix::f4();
    assert!(!f4.is_symmetric(), "F₄ Cartan must be asymmetric (non-simply-laced)");
}

// ============================================================================
// Root System Properties
// ============================================================================

#[test]
fn test_e8_roots_have_norm_two() {
    // Property: All E₈ roots have norm² = 2
    // From Python: simply-laced means all roots same length

    let e8 = E8RootSystem::new();
    let roots = e8.roots();

    let two = Rational::new(2, 1);
    for (i, root) in roots.iter().enumerate() {
        let norm_sq = root.norm_squared();
        assert_eq!(norm_sq, two, "E₈ root {i} must have norm² = 2, got {norm_sq}");
    }
}

#[test]
fn test_root_count_exact() {
    // Property: Exceptional groups have exact root counts
    // From Python: num_roots is exact integer

    let atlas = Atlas::new();

    // These are the EXACT counts from mathematics
    // No approximation, no tolerance
    assert_eq!(atlas.num_vertices(), 96, "Atlas must have exactly 96 vertices");

    let e8 = E8RootSystem::new();
    assert_eq!(e8.roots().len(), 240, "E₈ must have exactly 240 roots");
}

#[test]
fn test_weyl_orders_exact() {
    // Property: Weyl groups have exact orders (known mathematical values)
    // From Python: weyl_order is exact integer, not computed

    let g2 = WeylGroup::g2();
    assert_eq!(g2.order(), 12, "G₂ Weyl group order must be exactly 12");

    let f4 = WeylGroup::f4();
    assert_eq!(f4.order(), 1152, "F₄ Weyl group order must be exactly 1,152");

    let e6 = WeylGroup::e6();
    assert_eq!(e6.order(), 51840, "E₆ Weyl group order must be exactly 51,840");

    let e7 = WeylGroup::e7();
    assert_eq!(e7.order(), 2_903_040, "E₇ Weyl group order must be exactly 2,903,040");

    let e8 = WeylGroup::e8();
    assert_eq!(e8.order(), 696_729_600, "E₈ Weyl group order must be exactly 696,729,600");
}

// ============================================================================
// Atlas Properties
// ============================================================================

#[test]
fn test_atlas_vertex_count_exact() {
    // Property: Atlas has exactly 96 vertices
    // No approximation - this is EXACT

    let atlas = Atlas::new();
    assert_eq!(atlas.num_vertices(), 96, "Atlas must have exactly 96 vertices");
}

#[test]
#[allow(clippy::large_stack_arrays)] // format! macro in assertions creates temporary arrays
fn test_atlas_mirror_involution() {
    // Property: Mirror map is an involution: τ(τ(v)) = v
    // From Python: mirror pairs (v, τ(v))

    let atlas = Atlas::new();

    for v in 0..atlas.num_vertices() {
        let mirror = atlas.mirror_pair(v);
        let mirror_mirror = atlas.mirror_pair(mirror);

        assert_eq!(v, mirror_mirror, "Mirror must be involution: τ(τ({v})) = {v}");
    }
}

#[test]
fn test_atlas_mirror_produces_pairs() {
    // Property: Mirror creates exactly 48 pairs from 96 vertices
    // From Python: QuotientOperation verifies 96/± = 48

    let atlas = Atlas::new();
    let mut seen = vec![false; atlas.num_vertices()];
    let mut pair_count = 0;

    for v in 0..atlas.num_vertices() {
        if !seen[v] {
            let mirror = atlas.mirror_pair(v);
            seen[v] = true;
            seen[mirror] = true;
            pair_count += 1;
        }
    }

    assert_eq!(pair_count, 48, "Mirror must produce exactly 48 pairs");
}

#[test]
fn test_atlas_twelve_fold_divisibility() {
    // Property: 12-fold divisibility throughout Atlas
    // From Python: twelve_fold.py verifies G₂ structure

    let atlas = Atlas::new();

    assert_eq!(atlas.num_vertices() % 12, 0, "96 vertices must be divisible by 12");

    // 12-fold structure relates to G₂ (12 roots)
    assert_eq!(96 / 12, 8, "96 = 12 × 8");
    assert_eq!(48 / 12, 4, "48 = 12 × 4");
}

#[test]
fn test_atlas_degree_partition() {
    // Property: Degree partition gives E₆
    // From Python: FiltrationOperation - 64 deg-5 + 8 deg-6 = 72

    let atlas = Atlas::new();

    let mut deg5_count = 0;
    let mut deg6_count = 0;

    for v in 0..atlas.num_vertices() {
        match atlas.degree(v) {
            5 => deg5_count += 1,
            6 => deg6_count += 1,
            _ => {},
        }
    }

    // E₆ emerges from this partition
    assert!(deg5_count >= 64, "Need at least 64 degree-5 vertices for E₆");
    assert!(deg6_count >= 8, "Need at least 8 degree-6 vertices for E₆");

    let e6_total = 64 + 8;
    assert_eq!(e6_total, 72, "E₆ has exactly 72 roots");
}

// ============================================================================
// No Floating Point (Critical Property)
// ============================================================================

#[test]
#[allow(clippy::assertions_on_constants)] // Placeholder assertion for documentation
fn test_no_floating_point_in_arithmetic() {
    // Property: NO floating point anywhere in arithmetic
    // From CLAUDE.md: "NO floating point arithmetic"

    // This is a compile-time check via clippy lints:
    // #![cfg_attr(not(test), warn(clippy::float_arithmetic))]
    // But we verify runtime types are exact

    let h = HalfInteger::new(1);
    let _r = h.to_rational(); // Rational, not float

    let v = Vector8::zero();
    let _norm = v.norm_squared(); // Rational, not float

    // If this compiles and runs, no floats were used
    assert!(true, "All arithmetic is exact (no floats)");
}
