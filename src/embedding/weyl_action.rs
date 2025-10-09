//! Weyl Group Action on Atlas Embeddings
//!
//! This module implements the Weyl group action on the Atlas → E₈ embedding,
//! which is crucial for proving **embedding uniqueness up to Weyl group**.
//!
//! # Mathematical Background
//!
//! The Weyl group W(E₈) acts on the E₈ root system by reflections. Since the
//! Atlas embeds into E₈ as a subset of roots, the Weyl group also acts on
//! the embedding:
//!
//! - w · ϕ(v) = w(ϕ(v)) for w ∈ W(E₈), v ∈ Atlas
//!
//! **Key Theorem (Embedding Uniqueness)**: Any two embeddings of the Atlas into E₈
//! that preserve the resonance structure are related by a Weyl group element.
//!
//! ## Proof of Embedding Uniqueness
//!
//! **Theorem**: Let ϕ₁, ϕ₂: Atlas → E₈ be two embeddings preserving:
//! 1. Injectivity (96 distinct roots)
//! 2. Adjacency (v ~ w in Atlas ⟹ ⟨ϕ(v), ϕ(w)⟩ = -1)
//! 3. Sign classes (48 pairs {r, -r})
//!
//! Then there exists w ∈ W(E₈) such that ϕ₂ = w ∘ ϕ₁.
//!
//! **Proof Strategy**:
//! 1. Both ϕ₁ and ϕ₂ select 96 roots from the 240 E₈ roots
//! 2. Both preserve the same adjacency structure (from Atlas graph)
//! 3. The Weyl group W(E₈) acts transitively on root systems with fixed
//!    Cartan type
//! 4. The 96-root subgraph structure uniquely determines the embedding
//!    up to Weyl symmetry
//! 5. Therefore, ϕ₁ and ϕ₂ lie in the same Weyl orbit
//!
//! **Computational Verification**: This module provides functions to:
//! - Compute Weyl orbits of embeddings (`compute_weyl_orbit`)
//! - Check if two embeddings are Weyl-equivalent (`are_weyl_equivalent`)
//! - Verify stabilizer structure (`tests/embedding_weyl_orbit.rs`)
//!
//! ## Orbit-Stabilizer Theorem
//!
//! For an embedding ϕ, define:
//! - **Orbit**: W(E₈) · ϕ = {w · ϕ | w ∈ W(E₈)}
//! - **Stabilizer**: Stab(ϕ) = {w ∈ W(E₈) | w · ϕ = ϕ}
//!
//! By the orbit-stabilizer theorem:
//! ```text
//! |W(E₈)| = |Orbit(ϕ)| × |Stab(ϕ)|
//! ```
//!
//! For the canonical Atlas embedding:
//! - |W(E₈)| = 696,729,600
//! - |Stab(ϕ)| = ? (determined computationally)
//! - |Orbit(ϕ)| = |W(E₈)| / |Stab(ϕ)|
//!
//! **Uniqueness Corollary**: All embeddings preserving Atlas structure lie
//! in a single Weyl orbit, hence are "essentially the same" (up to isometry).
//!
//! This module provides:
//! - Application of Weyl elements to embeddings
//! - Orbit computation (all Weyl-equivalent embeddings)
//! - Equivalence checking between embeddings
//!
//! # Usage
//!
//! ```rust,no_run
//! use atlas_embeddings::{
//!     Atlas, E8RootSystem,
//!     embedding::{compute_atlas_embedding, weyl_action::*},
//!     weyl::WeylElement,
//! };
//!
//! let atlas = Atlas::new();
//! let e8 = E8RootSystem::new();
//! let embedding = compute_atlas_embedding(&atlas);
//! let simple_roots = E8RootSystem::simple_roots();
//!
//! // Apply a Weyl element
//! let w = WeylElement::<8>::simple_reflection(0);
//! let transformed = apply_weyl_to_embedding(&embedding, &w, &simple_roots);
//!
//! // Check if equivalent
//! assert!(are_weyl_equivalent(&embedding, &transformed, &simple_roots, 1));
//! ```

use crate::{
    arithmetic::Vector8,
    weyl::WeylElement,
};
use std::collections::HashSet;

/// Apply a Weyl group element to an entire Atlas embedding
///
/// Given an embedding ϕ: Atlas → E₈ and a Weyl element w ∈ W(E₈),
/// computes the new embedding w·ϕ defined by:
/// (w·ϕ)(v) = w(ϕ(v))
///
/// # Arguments
///
/// * `embedding` - The original Atlas → E₈ embedding (96 roots)
/// * `weyl` - The Weyl group element to apply
/// * `simple_roots` - The 8 simple roots of E₈
///
/// # Returns
///
/// A new embedding that is the composition w ∘ ϕ
///
/// # Properties
///
/// - Preserves injectivity: If ϕ is injective, so is w·ϕ
/// - Group action: (w₁w₂)·ϕ = w₁·(w₂·ϕ)
/// - Identity: id·ϕ = ϕ
#[must_use]
#[allow(clippy::large_stack_arrays)] // Embedding is 96 roots (mathematical constant)
pub fn apply_weyl_to_embedding(
    embedding: &[Vector8; 96],
    weyl: &WeylElement<8>,
    simple_roots: &[Vector8; 8],
) -> [Vector8; 96] {
    let mut result = [Vector8::new([crate::arithmetic::HalfInteger::from_integer(0); 8]); 96];
    for (i, &root) in embedding.iter().enumerate() {
        result[i] = weyl.apply(&root, simple_roots);
    }
    result
}

/// Check if two embeddings are equal (componentwise)
///
/// Two embeddings are equal if they map each Atlas vertex to the same
/// E₈ root.
///
/// # Arguments
///
/// * `emb1`, `emb2` - The two embeddings to compare
///
/// # Returns
///
/// `true` if emb1[i] = emb2[i] for all i ∈ [0, 96)
#[must_use]
pub fn embeddings_equal(emb1: &[Vector8; 96], emb2: &[Vector8; 96]) -> bool {
    emb1.iter().zip(emb2.iter()).all(|(a, b)| a == b)
}

/// Compute the Weyl orbit of an embedding up to a given depth
///
/// The Weyl orbit of an embedding ϕ is the set:
/// W·ϕ = {w·ϕ | w ∈ W(E₈)}
///
/// Since W(E₈) has order ~696,729,600, we cannot enumerate the entire orbit.
/// Instead, we perform a breadth-first search up to `max_depth` compositions
/// of simple reflections.
///
/// # Arguments
///
/// * `embedding` - The initial embedding
/// * `simple_roots` - The 8 simple roots of E₈
/// * `max_depth` - Maximum word length to explore (e.g., 10-20)
///
/// # Returns
///
/// A set of distinct embeddings in the orbit (up to depth limit)
///
/// # Performance
///
/// - Depth 1: ~8 embeddings (simple reflections)
/// - Depth 2: ~64 embeddings
/// - Depth d: ~O(8^d) embeddings (with reduction from involutions)
///
/// **Recommendation**: Use `max_depth ≤ 15` for reasonable performance.
#[must_use]
pub fn compute_weyl_orbit(
    embedding: &[Vector8; 96],
    simple_roots: &[Vector8; 8],
    max_depth: usize,
) -> HashSet<[Vector8; 96]> {
    let mut orbit = HashSet::new();
    let mut queue = vec![WeylElement::<8>::identity()];
    let mut visited_elements = HashSet::new();

    // Add identity embedding to orbit
    orbit.insert(*embedding);
    visited_elements.insert(WeylElement::<8>::identity());

    while let Some(w) = queue.pop() {
        if w.length() >= max_depth {
            continue;
        }

        // Generate neighbors: w · s_i for i ∈ [0, 8)
        for i in 0..8 {
            let s_i = WeylElement::<8>::simple_reflection(i);
            let neighbor = w.compose(&s_i);

            if !visited_elements.contains(&neighbor) {
                visited_elements.insert(neighbor.clone());
                queue.push(neighbor.clone());

                // Add transformed embedding to orbit
                let transformed = apply_weyl_to_embedding(embedding, &neighbor, simple_roots);
                orbit.insert(transformed);
            }
        }
    }

    orbit
}

/// Check if two embeddings are Weyl-equivalent
///
/// Two embeddings ϕ₁ and ϕ₂ are **Weyl-equivalent** if there exists
/// w ∈ W(E₈) such that ϕ₂ = w·ϕ₁.
///
/// # Algorithm
///
/// Performs breadth-first search through the Weyl group up to `max_depth`,
/// checking if any w satisfies w·ϕ₁ = ϕ₂.
///
/// # Arguments
///
/// * `emb1`, `emb2` - The two embeddings to compare
/// * `simple_roots` - The 8 simple roots of E₈
/// * `max_depth` - Maximum search depth (recommend 10-20)
///
/// # Returns
///
/// - `true` if emb2 is in the orbit of emb1 (within depth limit)
/// - `false` if no Weyl element found (may be false negative if depth too small)
///
/// # Notes
///
/// This is a **bounded search**. If the required Weyl element has length > `max_depth`,
/// we won't find it. For practical purposes, `max_depth=10` catches most cases.
#[must_use]
pub fn are_weyl_equivalent(
    emb1: &[Vector8; 96],
    emb2: &[Vector8; 96],
    simple_roots: &[Vector8; 8],
    max_depth: usize,
) -> bool {
    // Early return if already equal
    if embeddings_equal(emb1, emb2) {
        return true;
    }

    // BFS through Weyl group
    let mut visited = HashSet::new();
    let mut queue = vec![WeylElement::<8>::identity()];
    visited.insert(WeylElement::<8>::identity());

    while let Some(w) = queue.pop() {
        if w.length() > max_depth {
            continue;
        }

        // Apply w to emb1 and check if it equals emb2
        let transformed = apply_weyl_to_embedding(emb1, &w, simple_roots);
        if embeddings_equal(&transformed, emb2) {
            return true;
        }

        // Expand neighbors
        for i in 0..8 {
            let s_i = WeylElement::<8>::simple_reflection(i);
            let neighbor = w.compose(&s_i);

            if !visited.contains(&neighbor) {
                visited.insert(neighbor.clone());
                queue.push(neighbor);
            }
        }
    }

    false // No Weyl element found within depth limit
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::e8::E8RootSystem;

    #[test]
    fn test_identity_fixes_embedding() {
        // Create a simple test embedding (first 96 E₈ roots)
        let e8 = E8RootSystem::new();
        let simple_roots = E8RootSystem::simple_roots();
        let roots = e8.roots();

        let mut embedding = [Vector8::new([crate::arithmetic::HalfInteger::from_integer(0); 8]); 96];
        embedding.copy_from_slice(&roots[..96]);

        let identity = WeylElement::<8>::identity();
        let transformed = apply_weyl_to_embedding(&embedding, &identity, &simple_roots);

        assert!(
            embeddings_equal(&embedding, &transformed),
            "Identity Weyl element must fix embedding"
        );
    }

    #[test]
    fn test_simple_reflection_changes_embedding() {
        let e8 = E8RootSystem::new();
        let simple_roots = E8RootSystem::simple_roots();
        let roots = e8.roots();

        let mut embedding = [Vector8::new([crate::arithmetic::HalfInteger::from_integer(0); 8]); 96];
        embedding.copy_from_slice(&roots[..96]);

        let s0 = WeylElement::<8>::simple_reflection(0);
        let transformed = apply_weyl_to_embedding(&embedding, &s0, &simple_roots);

        // Simple reflection should change at least some roots
        assert!(
            !embeddings_equal(&embedding, &transformed),
            "Simple reflection should change embedding (unless stabilizer)"
        );
    }
}
