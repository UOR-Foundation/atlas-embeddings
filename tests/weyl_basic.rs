//! Basic Weyl Group Tests: Reflections and Root System Preservation
//!
//! This integration test verifies fundamental properties of Weyl reflections:
//! - Norm preservation (Weyl reflections are isometries)
//! - Root system permutation (Weyl group acts on roots)
//! - Group structure (composition is associative)

#![allow(clippy::large_stack_arrays)] // Testing with mathematical constants

use atlas_embeddings::{e8::E8RootSystem, weyl::WeylElement};

#[test]
fn test_weyl_preserves_norm() {
    let e8 = E8RootSystem::new();
    let simple_roots = E8RootSystem::simple_roots();

    // Test that simple reflections preserve norm² = 2
    for &root in e8.roots() {
        for i in 0..8 {
            let s_i = WeylElement::<8>::simple_reflection(i);
            let reflected = s_i.apply(&root, &simple_roots);

            let original_norm = root.inner_product(&root);
            let reflected_norm = reflected.inner_product(&reflected);

            assert_eq!(
                original_norm, reflected_norm,
                "Weyl reflection s_{i} must preserve norm: ||α||² = ||s_i(α)||²"
            );
        }
    }
}

#[test]
fn test_weyl_permutes_root_system() {
    let e8 = E8RootSystem::new();
    let simple_roots = E8RootSystem::simple_roots();

    // Test that simple reflections map roots to roots
    for &root in e8.roots() {
        for i in 0..8 {
            let s_i = WeylElement::<8>::simple_reflection(i);
            let reflected = s_i.apply(&root, &simple_roots);

            let found = e8.find_root(&reflected);
            assert!(found.is_some(), "Weyl reflection s_{i} must map root α to another root in Φ");
        }
    }
}

#[test]
fn test_weyl_composition_associative() {
    let simple_roots = E8RootSystem::simple_roots();

    // Test associativity: (s_i · s_j) · s_k = s_i · (s_j · s_k)
    let s0 = WeylElement::<8>::simple_reflection(0);
    let s1 = WeylElement::<8>::simple_reflection(1);
    let s2 = WeylElement::<8>::simple_reflection(2);

    let left = s0.compose(&s1).compose(&s2);
    let right = s0.compose(&s1.compose(&s2));

    // Test on a specific root
    let test_root = simple_roots[0];
    let left_result = left.apply(&test_root, &simple_roots);
    let right_result = right.apply(&test_root, &simple_roots);

    assert_eq!(
        left_result, right_result,
        "Weyl composition must be associative: (s₀·s₁)·s₂ = s₀·(s₁·s₂)"
    );
}

#[test]
fn test_weyl_reflection_formula() {
    let simple_roots = E8RootSystem::simple_roots();

    // Test the reflection formula: s_α(v) = v - ⟨v,α⟩·α
    // For a simple root α_i, s_i(α_i) = -α_i
    for i in 0..8 {
        let alpha_i = simple_roots[i];
        let s_i = WeylElement::<8>::simple_reflection(i);
        let reflected = s_i.apply(&alpha_i, &simple_roots);
        let expected = alpha_i.negate();

        assert_eq!(
            reflected, expected,
            "Reflection through α_i sends α_i to -α_i: s_i(α_i) = -α_i"
        );
    }
}

#[test]
fn test_weyl_identity_acts_trivially() {
    let simple_roots = E8RootSystem::simple_roots();
    let identity = WeylElement::<8>::identity();

    // Test that identity fixes all simple roots
    for &root in &simple_roots {
        let result = identity.apply(&root, &simple_roots);
        assert_eq!(result, root, "Identity element must fix all roots: id(α) = α");
    }
}

#[test]
fn test_weyl_involution() {
    let e8 = E8RootSystem::new();
    let simple_roots = E8RootSystem::simple_roots();

    // Test that s_i² = id for all simple reflections
    for i in 0..8 {
        let s_i = WeylElement::<8>::simple_reflection(i);
        let s_i_squared = s_i.compose(&s_i);

        // Test on all roots
        for &root in e8.roots() {
            let double_reflected = s_i_squared.apply(&root, &simple_roots);
            assert_eq!(double_reflected, root, "Simple reflection squared is identity: s_i² = id");
        }
    }
}

#[test]
fn test_weyl_inverse() {
    let simple_roots = E8RootSystem::simple_roots();

    // Test that w · w⁻¹ = id
    let s0 = WeylElement::<8>::simple_reflection(0);
    let s1 = WeylElement::<8>::simple_reflection(1);
    let s2 = WeylElement::<8>::simple_reflection(2);

    let w = s0.compose(&s1).compose(&s2);
    let w_inv = w.inverse();
    let composition = w.compose(&w_inv);

    // Test on all simple roots
    for &root in &simple_roots {
        let result = composition.apply(&root, &simple_roots);
        assert_eq!(result, root, "Composition with inverse is identity: w·w⁻¹(α) = α");
    }
}

#[test]
fn test_weyl_length() {
    // Test that length is correctly computed
    let s0 = WeylElement::<8>::simple_reflection(0);
    let s1 = WeylElement::<8>::simple_reflection(1);

    assert_eq!(s0.length(), 1, "Simple reflection has length 1");

    let w = s0.compose(&s1);
    assert_eq!(w.length(), 2, "s₀·s₁ has length 2");

    let w_squared = w.compose(&w);
    // After reduction: s₀·s₁·s₀·s₁ may reduce depending on Coxeter relations
    // But length should still be reasonable
    assert!(w_squared.length() <= 4, "Composition length is bounded");
}

#[test]
fn test_simple_roots_cartan_matrix() {
    let simple_roots = E8RootSystem::simple_roots();

    // Verify Cartan matrix entries: A[i][j] = 2⟨αᵢ,αⱼ⟩/⟨αⱼ,αⱼ⟩
    // For simply-laced E₈: A[i][j] = 2⟨αᵢ,αⱼ⟩/2 = ⟨αᵢ,αⱼ⟩
    for i in 0..8 {
        for j in 0..8 {
            let inner = simple_roots[i].inner_product(&simple_roots[j]);

            if i == j {
                // Diagonal: A[i][i] = 2
                assert_eq!(*inner.numer(), 2, "Cartan diagonal A[{i}][{i}] = 2");
            } else {
                // Off-diagonal: A[i][j] ∈ {0, -1} for simply-laced
                assert!(
                    *inner.numer() == 0 || *inner.numer() == -1,
                    "Cartan off-diagonal A[{i}][{j}] = {inner} must be 0 or -1"
                );
            }
            assert_eq!(*inner.denom(), 1);
        }
    }
}
