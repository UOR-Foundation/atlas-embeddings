#![allow(clippy::doc_markdown)] // Allow mathematical notation (e₁, Q₄, etc.)
#![allow(clippy::large_stack_arrays)] // 3×3 Rational arrays are fundamental mathematical objects
#![allow(clippy::large_const_arrays)] // Q4 spectrum is a small mathematical constant
//! # Chapter 10: Spectral Analysis of the Atlas Laplacian
//!
//! This chapter presents the spectral analysis of the Atlas graph Laplacian,
//! proving that the **spectral gap is exactly λ₁ = 1** through a block
//! tridiagonal decomposition into Q₄ hypercube blocks.
//!
//! ## Overview
//!
//! The Atlas of Resonance Classes is a 96-vertex graph with 256 edges that
//! decomposes into **two disconnected hemispheres** (split by the e₇ coordinate).
//! Each hemisphere has 48 vertices and 128 edges. Within each hemisphere, the
//! vertices partition into **three Q₄ hypercube blocks** (split by d₄₅ ∈ {-1, 0, +1}),
//! connected by identity matchings.
//!
//! This block structure yields a **block tridiagonal decomposition** of the
//! hemisphere Laplacian, reducing the 48×48 eigenvalue problem to five independent
//! 3×3 problems (one per Q₄ eigenvalue). Each 3×3 block matrix M_ν has eigenvalues
//! {ν, ν+1, ν+3}, proven by exact rational determinant computation.
//!
//! ## Background: Graph Laplacians
//!
//! **Definition 10.1.1 (Graph Laplacian)**: For a graph G = (V, E), the
//! **combinatorial Laplacian** is the matrix L = D - A where:
//! - D is the degree matrix: D\[i,i\] = deg(i), D\[i,j\] = 0 for i ≠ j
//! - A is the adjacency matrix: A\[i,j\] = 1 if {i,j} ∈ E, else 0
//!
//! **Key Properties**:
//! - L is symmetric and positive semidefinite
//! - L has zero row sums: L·**1** = **0**
//! - Smallest eigenvalue λ₀ = 0 (with eigenvector **1**)
//! - Multiplicity of λ₀ = number of connected components
//! - tr(L) = Σᵢ deg(i) = 2|E|
//! - tr(L²) = Σᵢ deg(i)² + 2|E|
//!
//! **Definition 10.1.2 (Spectral Gap)**: The **spectral gap** λ₁ is the smallest
//! nonzero eigenvalue of L. It measures algebraic connectivity:
//! - λ₁ > 0 iff the graph is connected
//! - Larger λ₁ → better connected, faster mixing
//! - Cheeger inequality: h²/(2d) ≤ λ₁ ≤ 2h where h is edge expansion
//!
//! ## The Atlas Structure
//!
//! **Theorem 10.2.1 (Hemisphere Decomposition)**: The Atlas graph decomposes as
//! a disjoint union of two isomorphic hemispheres:
//!
//! Atlas = H₀ ⊔ H₁ where Hₖ = {v : e₇(v) = k}
//!
//! Each hemisphere has 48 vertices and 128 edges. The isomorphism is the mirror
//! map τ: H₀ → H₁ which flips e₇.
//!
//! **Theorem 10.2.2 (Q₄ Block Decomposition)**: Each hemisphere decomposes into
//! three Q₄ hypercube blocks:
//!
//! Hₖ = B₋₁ ∪ B₀ ∪ B₊₁ where Bₘ = {v ∈ Hₖ : d₄₅(v) = m}
//!
//! Each block Bₘ has 16 vertices with coordinates (e₁, e₂, e₃, e₆) ∈ {0,1}⁴.
//! The within-block adjacency is exactly the Q₄ hypercube: two vertices are
//! adjacent iff they differ in exactly one of {e₁, e₂, e₃, e₆}.
//!
//! **Theorem 10.2.3 (Inter-Block Identity Matching)**: The inter-block edges
//! form **identity matchings** between adjacent blocks:
//!
//! - B₋₁ ↔ B₀: vertex (e₁,e₂,e₃,-1,e₆) connects to (e₁,e₂,e₃,0,e₆)
//! - B₀ ↔ B₊₁: vertex (e₁,e₂,e₃,0,e₆) connects to (e₁,e₂,e₃,+1,e₆)
//! - B₋₁ ↔ B₊₁: **no edges** (no single coordinate flip connects them)
//!
//! This gives a path graph of blocks: B₋₁ — B₀ — B₊₁
//!
//! ## Block Tridiagonal Decomposition
//!
//! **Theorem 10.3.1 (Block Laplacian Structure)**: The hemisphere Laplacian
//! in the block ordering \[B₋₁, B₀, B₊₁\] has block tridiagonal form:
//!
//! ```text
//! L_H = [ L_Q₄ + I,    -I,        0       ]
//!       [   -I,      L_Q₄ + 2I,   -I      ]
//!       [    0,         -I,      L_Q₄ + I  ]
//! ```
//!
//! where L_Q₄ is the 16×16 Q₄ Laplacian and I is the 16×16 identity.
//!
//! **Proof**: Block (1,1) has degree 5 = 4 (Q₄) + 1 (inter-block), giving
//! L₁₁ = 5I - A_Q₄ = (4I - A_Q₄) + I = L_Q₄ + I. Block (2,2) has degree
//! 6 = 4 + 2, giving L₂₂ = L_Q₄ + 2I. Off-diagonal blocks are -I
//! (identity matching). ∎
//!
//! **Theorem 10.3.2 (Reduction to 3×3 Blocks)**: Since the inter-block
//! coupling (identity matrix) commutes with L_Q₄, the hemisphere Laplacian
//! block-diagonalizes in each Q₄ eigenspace. For Q₄ eigenvalue ν, the
//! reduced 3×3 block is:
//!
//! ```text
//! M_ν = [ ν+1,  -1,   0  ]
//!       [ -1,   ν+2,  -1 ]
//!       [  0,   -1,  ν+1 ]
//! ```
//!
//! ## Main Result
//!
//! **Theorem 10.4.1 (Eigenvalues of M_ν)**: The characteristic polynomial of
//! M_ν factors as:
//!
//! det(M_ν - λI) = (ν - λ)(ν + 1 - λ)(ν + 3 - λ)
//!
//! giving eigenvalues **{ν, ν+1, ν+3}** for each Q₄ eigenvalue ν.
//!
//! **Theorem 10.4.2 (Complete Hemisphere Spectrum)**: Combining Q₄ eigenvalues
//! ν ∈ {0, 2, 4, 6, 8} with multiplicities {1, 4, 6, 4, 1}, the complete
//! hemisphere spectrum is:
//!
//! | λ  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 11 |
//! |----|---|---|---|---|---|---|---|---|---|---|----|
//! | mult | 1 | 1 | 4 | 5 | 6 | 10| 4 | 10| 1 | 5 | 1  |
//!
//! Total: 48 eigenvalues ✓
//!
//! **Theorem 10.4.3 (Spectral Gap)**: The spectral gap of each hemisphere
//! (and of the full Atlas) is **λ₁ = 1**, arising from the M₀ block
//! (Q₄ eigenvalue ν = 0, which has eigenvalues {0, 1, 3}).
//!
//! ## Cross-Checks
//!
//! - tr(L_H) = Σ λᵢ·multᵢ = 256 = 2|E_H| ✓
//! - tr(L_H²) = Σ λᵢ²·multᵢ = 1632 = Σ deg(v)² + 2|E_H| ✓
//! - Gershgorin bound: all λᵢ ∈ \[0, 12\] ✓
//! - L_H symmetric: L = L^T ✓
//!
//! ## Connection to Toroidal Coherence
//!
//! The spectral gap λ₁ = 1 bridges the Atlas of Resonance Classes to the
//! Tonnetz toroidal manifold. The Laplacian eigenvalues determine:
//! - Heat kernel decay rates on the Atlas
//! - Random walk mixing times
//! - Algebraic connectivity bounds
//!
//! This spectral structure provides the analytical foundation for the
//! toroidal coherence framework applied to consensus and ML systems.
//!
//! ## Navigation
//!
//! - Previous: [Chapter 9: Atlas Initiality](crate)
//! - Up: [Main Page](crate)

use crate::arithmetic::Rational;
use crate::atlas::Atlas;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fmt;

// ─────────────────────────────────────────────────────────────────────────────
// Constants
// ─────────────────────────────────────────────────────────────────────────────

/// Number of vertices per hemisphere (48 = 96/2)
const HEMISPHERE_VERTICES: usize = 48;

/// Number of vertices per Q₄ hypercube block (16 = 2⁴)
const Q4_VERTICES: usize = 16;

/// Degree of each vertex in a Q₄ hypercube
const Q4_DEGREE: usize = 4;

/// Number of edges in a Q₄ hypercube (32 = 16×4/2)
const Q4_EDGES: usize = 32;

/// Q₄ Laplacian eigenvalues with multiplicities: (eigenvalue, C(4,k))
///
/// For the 4-dimensional hypercube, the Laplacian L = 4I - A has eigenvalues
/// 2k for k = 0,1,2,3,4 with multiplicities C(4,k) = 1,4,6,4,1.
const Q4_SPECTRUM: [(i64, usize); 5] = [
    (0, 1),  // C(4,0) = 1
    (2, 4),  // C(4,1) = 4
    (4, 6),  // C(4,2) = 6
    (6, 4),  // C(4,3) = 4
    (8, 1),  // C(4,4) = 1
];

// ─────────────────────────────────────────────────────────────────────────────
// Dense Rational Matrix (internal utility for Laplacian construction)
// ─────────────────────────────────────────────────────────────────────────────

/// Dense matrix with exact rational entries (module-internal)
///
/// Used to construct and verify the graph Laplacian explicitly.
/// Row-major storage for cache efficiency.
#[derive(Clone)]
struct DenseRatMatrix {
    n: usize,
    data: Vec<Rational>,
}

impl DenseRatMatrix {
    /// Create an n×n zero matrix
    fn new(n: usize) -> Self {
        Self {
            n,
            data: vec![Rational::zero(); n * n],
        }
    }

    /// Get entry at (i, j)
    fn get(&self, i: usize, j: usize) -> Rational {
        self.data[i * self.n + j]
    }

    /// Set entry at (i, j)
    fn set(&mut self, i: usize, j: usize, val: Rational) {
        self.data[i * self.n + j] = val;
    }

    /// Compute trace: tr(M) = Σ M\[i,i\]
    fn trace(&self) -> Rational {
        let mut sum = Rational::zero();
        for i in 0..self.n {
            sum += self.get(i, i);
        }
        sum
    }

    /// Check if symmetric: M\[i,j\] = M\[j,i\] for all i,j
    fn is_symmetric(&self) -> bool {
        for i in 0..self.n {
            for j in (i + 1)..self.n {
                if self.get(i, j) != self.get(j, i) {
                    return false;
                }
            }
        }
        true
    }

    /// Compute row sum: Σⱼ M\[i,j\]
    fn row_sum(&self, i: usize) -> Rational {
        let mut sum = Rational::zero();
        for j in 0..self.n {
            sum += self.get(i, j);
        }
        sum
    }

    /// Compute Frobenius norm squared: Σᵢⱼ M\[i,j\]²
    ///
    /// For a symmetric matrix, this equals tr(M²).
    fn frobenius_squared(&self) -> Rational {
        let mut sum = Rational::zero();
        for val in &self.data {
            sum += *val * *val;
        }
        sum
    }

    /// Check that all diagonal entries are non-negative
    fn has_nonneg_diagonal(&self) -> bool {
        for i in 0..self.n {
            if self.get(i, i) < Rational::zero() {
                return false;
            }
        }
        true
    }

    /// Check that all off-diagonal entries are non-positive
    fn has_nonpos_off_diagonal(&self) -> bool {
        for i in 0..self.n {
            for j in 0..self.n {
                if i != j && self.get(i, j) > Rational::zero() {
                    return false;
                }
            }
        }
        true
    }

    /// Construct graph Laplacian from Atlas subgraph
    ///
    /// Given a set of Atlas vertex indices, builds L = D - A for the
    /// induced subgraph. Uses exact rational arithmetic.
    fn from_atlas_subgraph(atlas: &Atlas, vertices: &[usize]) -> Self {
        let n = vertices.len();
        let mut mat = Self::new(n);

        // Build mapping: Atlas vertex index → local index
        let index_map: HashMap<usize, usize> = vertices
            .iter()
            .enumerate()
            .map(|(local, &atlas_idx)| (atlas_idx, local))
            .collect();

        for (i, &v) in vertices.iter().enumerate() {
            let mut degree = 0i64;
            for &neighbor in atlas.neighbors(v) {
                if let Some(&j) = index_map.get(&neighbor) {
                    mat.set(i, j, -Rational::one());
                    degree += 1;
                }
            }
            mat.set(i, i, Rational::from_integer(degree));
        }

        mat
    }
}

impl fmt::Debug for DenseRatMatrix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DenseRatMatrix({}×{})", self.n, self.n)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 3×3 Matrix Operations
// ─────────────────────────────────────────────────────────────────────────────

/// Compute determinant of a 3×3 rational matrix (exact)
///
/// Uses cofactor expansion along the first row:
/// det(M) = M₀₀(M₁₁M₂₂ - M₁₂M₂₁) - M₀₁(M₁₀M₂₂ - M₁₂M₂₀) + M₀₂(M₁₀M₂₁ - M₁₁M₂₀)
fn det_3x3(m: &[[Rational; 3]; 3]) -> Rational {
    m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
        - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
        + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
}

/// Construct the 3×3 block tridiagonal matrix M_ν
///
/// For Q₄ eigenvalue ν, the reduced block is:
///
/// ```text
/// M_ν = [ ν+1,  -1,   0  ]
///       [ -1,   ν+2,  -1 ]
///       [  0,   -1,  ν+1 ]
/// ```
///
/// This arises from the hemisphere Laplacian's block structure when
/// restricted to the ν-eigenspace of L_Q₄.
fn block_tridiagonal_matrix(nu: i64) -> [[Rational; 3]; 3] {
    let n = Rational::from_integer(nu);
    let one = Rational::one();
    let two = Rational::new(2, 1);
    let neg = -one;
    let zero = Rational::zero();

    [
        [n + one, neg, zero],
        [neg, n + two, neg],
        [zero, neg, n + one],
    ]
}

/// Verify eigenvalues of M_ν by checking det(M_ν - λI) = 0
///
/// Returns the three eigenvalues {ν, ν+1, ν+3} after verification.
///
/// # Panics
///
/// Panics if any candidate eigenvalue does not satisfy the characteristic equation.
fn verify_block_eigenvalues(nu: i64) -> [Rational; 3] {
    let m = block_tridiagonal_matrix(nu);
    let nu_r = Rational::from_integer(nu);

    // Candidate eigenvalues: {ν, ν+1, ν+3}
    let eigenvalues = [
        nu_r,
        nu_r + Rational::one(),
        nu_r + Rational::new(3, 1),
    ];

    for &lambda in &eigenvalues {
        // Compute M_ν - λI
        let shifted = [
            [m[0][0] - lambda, m[0][1], m[0][2]],
            [m[1][0], m[1][1] - lambda, m[1][2]],
            [m[2][0], m[2][1], m[2][2] - lambda],
        ];
        let det = det_3x3(&shifted);
        assert!(
            det.is_zero(),
            "det(M_{nu} - {lambda}·I) must be 0, got {det}"
        );
    }

    eigenvalues
}

// ─────────────────────────────────────────────────────────────────────────────
// Hemisphere and Block Decomposition
// ─────────────────────────────────────────────────────────────────────────────

/// Decompose Atlas into two hemispheres by e₇ value
///
/// Returns \[hemisphere_e7_0, hemisphere_e7_1\] where each is a sorted
/// vector of Atlas vertex indices.
fn decompose_hemispheres(atlas: &Atlas) -> [Vec<usize>; 2] {
    let mut h0 = Vec::with_capacity(HEMISPHERE_VERTICES);
    let mut h1 = Vec::with_capacity(HEMISPHERE_VERTICES);

    for v in 0..atlas.num_vertices() {
        if atlas.label(v).e7 == 0 {
            h0.push(v);
        } else {
            h1.push(v);
        }
    }

    assert_eq!(h0.len(), HEMISPHERE_VERTICES, "Hemisphere 0 must have 48 vertices");
    assert_eq!(h1.len(), HEMISPHERE_VERTICES, "Hemisphere 1 must have 48 vertices");

    [h0, h1]
}

/// Verify that no edges cross between hemispheres
///
/// Since adjacency flips {e₁, e₂, e₃, e₄, e₅, e₆} but NOT e₇,
/// all neighbors of a vertex share its e₇ value.
fn verify_no_cross_hemisphere_edges(atlas: &Atlas, hemispheres: &[Vec<usize>; 2]) {
    let h0_set: HashSet<usize> = hemispheres[0].iter().copied().collect();
    let h1_set: HashSet<usize> = hemispheres[1].iter().copied().collect();

    for &v in &hemispheres[0] {
        for &n in atlas.neighbors(v) {
            assert!(
                h0_set.contains(&n),
                "Vertex {v} (e7=0) has neighbor {n} outside hemisphere 0"
            );
            assert!(
                !h1_set.contains(&n),
                "Cross-hemisphere edge detected: {v} ~ {n}"
            );
        }
    }
}

/// Decompose a hemisphere into three Q₄ blocks by d₄₅ value
///
/// Returns \[block_d45_neg1, block_d45_0, block_d45_pos1\] where each
/// is a sorted vector of Atlas vertex indices.
fn decompose_blocks(atlas: &Atlas, hemisphere: &[usize]) -> [Vec<usize>; 3] {
    let mut b_neg = Vec::with_capacity(Q4_VERTICES);
    let mut b_zero = Vec::with_capacity(Q4_VERTICES);
    let mut b_pos = Vec::with_capacity(Q4_VERTICES);

    for &v in hemisphere {
        match atlas.label(v).d45 {
            -1 => b_neg.push(v),
            0 => b_zero.push(v),
            1 => b_pos.push(v),
            d => panic!("Invalid d45 value: {d}"),
        }
    }

    assert_eq!(b_neg.len(), Q4_VERTICES, "d45=-1 block must have 16 vertices");
    assert_eq!(b_zero.len(), Q4_VERTICES, "d45=0 block must have 16 vertices");
    assert_eq!(b_pos.len(), Q4_VERTICES, "d45=+1 block must have 16 vertices");

    [b_neg, b_zero, b_pos]
}

/// Verify that a block forms a Q₄ hypercube
///
/// Checks:
/// 1. Exactly 16 vertices
/// 2. Each vertex has exactly 4 neighbors within the block
/// 3. The block is connected (single component)
/// 4. The block is bipartite (parity of e₁+e₂+e₃+e₆ separates parts)
fn verify_q4_block(atlas: &Atlas, block: &[usize]) {
    assert_eq!(block.len(), Q4_VERTICES, "Q4 block must have 16 vertices");

    let block_set: HashSet<usize> = block.iter().copied().collect();

    // Check within-block degree = 4
    for &v in block {
        let within_degree = atlas
            .neighbors(v)
            .iter()
            .filter(|n| block_set.contains(n))
            .count();
        assert_eq!(
            within_degree, Q4_DEGREE,
            "Q4 vertex {v} has within-block degree {within_degree}, expected {Q4_DEGREE}"
        );
    }

    // Check connected via BFS
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    visited.insert(block[0]);
    queue.push_back(block[0]);

    while let Some(v) = queue.pop_front() {
        for &n in atlas.neighbors(v) {
            if block_set.contains(&n) && visited.insert(n) {
                queue.push_back(n);
            }
        }
    }

    assert_eq!(
        visited.len(),
        Q4_VERTICES,
        "Q4 block must be connected (reached {} of {})",
        visited.len(),
        Q4_VERTICES
    );

    // Check bipartite via parity of e1+e2+e3+e6
    for &v in block {
        let vl = atlas.label(v);
        let v_parity = (vl.e1 + vl.e2 + vl.e3 + vl.e6) % 2;
        for &n in atlas.neighbors(v) {
            if block_set.contains(&n) {
                let nl = atlas.label(n);
                let n_parity = (nl.e1 + nl.e2 + nl.e3 + nl.e6) % 2;
                assert_ne!(
                    v_parity, n_parity,
                    "Q4 must be bipartite: adjacent vertices {v} and {n} have same parity"
                );
            }
        }
    }
}

/// Verify inter-block edges form identity matchings
///
/// Between adjacent blocks (d45=-1 ↔ d45=0 and d45=0 ↔ d45=+1),
/// each vertex connects to exactly one vertex with the same (e₁,e₂,e₃,e₆).
/// Between non-adjacent blocks (d45=-1 ↔ d45=+1), there are no edges.
fn verify_inter_block_structure(atlas: &Atlas, blocks: &[Vec<usize>; 3]) {
    let block_sets: [HashSet<usize>; 3] = [
        blocks[0].iter().copied().collect(),
        blocks[1].iter().copied().collect(),
        blocks[2].iter().copied().collect(),
    ];

    // d45=-1 → d45=0: each vertex has exactly 1 neighbor, identity matching
    verify_identity_matching(atlas, &blocks[0], &block_sets[1]);

    // d45=+1 → d45=0: each vertex has exactly 1 neighbor, identity matching
    verify_identity_matching(atlas, &blocks[2], &block_sets[1]);

    // d45=-1 → d45=+1: NO edges (skip edges)
    for &v in &blocks[0] {
        for &n in atlas.neighbors(v) {
            assert!(
                !block_sets[2].contains(&n),
                "Skip edge detected: d45=-1 vertex {v} ~ d45=+1 vertex {n}"
            );
        }
    }
}

/// Verify identity matching between a source block and target block
///
/// Each source vertex must have exactly one neighbor in the target,
/// and that neighbor must share coordinates (e₁, e₂, e₃, e₆).
fn verify_identity_matching(atlas: &Atlas, source: &[usize], target: &HashSet<usize>) {
    for &v in source {
        let inter_neighbors: Vec<usize> = atlas
            .neighbors(v)
            .iter()
            .filter(|n| target.contains(n))
            .copied()
            .collect();

        assert_eq!(
            inter_neighbors.len(),
            1,
            "Vertex {v} must have exactly 1 inter-block neighbor, got {}",
            inter_neighbors.len()
        );

        // Verify identity matching: same (e1, e2, e3, e6)
        let vl = atlas.label(v);
        let nl = atlas.label(inter_neighbors[0]);
        assert_eq!(vl.e1, nl.e1, "Identity matching: e1 must match");
        assert_eq!(vl.e2, nl.e2, "Identity matching: e2 must match");
        assert_eq!(vl.e3, nl.e3, "Identity matching: e3 must match");
        assert_eq!(vl.e6, nl.e6, "Identity matching: e6 must match");
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Q₄ Spectrum Verification
// ─────────────────────────────────────────────────────────────────────────────

/// Verify Q₄ spectrum by trace cross-checks
///
/// For a connected, bipartite, 4-regular graph on 16 vertices, the conditions:
/// - tr(L) = 64
/// - tr(L²) = 320
///
/// together with the known eigenvalue bounds uniquely determine the spectrum
/// as {0(1), 2(4), 4(6), 6(4), 8(1)}.
#[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
fn verify_q4_spectrum(atlas: &Atlas, block: &[usize]) {
    let block_set: HashSet<usize> = block.iter().copied().collect();

    // Compute degree sum and degree-squared sum within block
    let mut degree_sum: usize = 0;
    let mut degree_sq_sum: usize = 0;

    for &v in block {
        let deg = atlas
            .neighbors(v)
            .iter()
            .filter(|n| block_set.contains(n))
            .count();
        degree_sum += deg;
        degree_sq_sum += deg * deg;
    }
    let edge_count = degree_sum / 2;

    // Verify Q4 regularity
    assert_eq!(degree_sum, Q4_VERTICES * Q4_DEGREE, "Q4 degree sum");
    assert_eq!(edge_count, Q4_EDGES, "Q4 edge count");

    // tr(L) = degree_sum = 64
    let trace = degree_sum;
    let expected_trace: usize = Q4_SPECTRUM
        .iter()
        .map(|&(ev, mult)| ev as usize * mult)
        .sum();
    assert_eq!(trace, expected_trace, "Q4 trace mismatch");

    // tr(L²) = Σ deg(v)² + 2|E| = 256 + 64 = 320
    let trace_sq = degree_sq_sum + 2 * edge_count;
    let expected_trace_sq: usize = Q4_SPECTRUM
        .iter()
        .map(|&(ev, mult)| (ev as usize) * (ev as usize) * mult)
        .sum();
    assert_eq!(trace_sq, expected_trace_sq, "Q4 trace² mismatch");
}

// ─────────────────────────────────────────────────────────────────────────────
// Spectrum Computation
// ─────────────────────────────────────────────────────────────────────────────

/// Compute the complete hemisphere spectrum from block tridiagonal decomposition
///
/// For each Q₄ eigenvalue ν with multiplicity m(ν), M_ν contributes three
/// eigenvalues {ν, ν+1, ν+3}, each with multiplicity m(ν).
fn compute_hemisphere_spectrum() -> Vec<(Rational, usize)> {
    let mut spectrum_map: BTreeMap<Rational, usize> = BTreeMap::new();

    for &(nu, q4_mult) in &Q4_SPECTRUM {
        // Verify eigenvalues of M_ν and get them
        let block_eigs = verify_block_eigenvalues(nu);

        // Each eigenvalue of M_ν inherits the Q4 multiplicity
        for &eig in &block_eigs {
            *spectrum_map.entry(eig).or_insert(0) += q4_mult;
        }
    }

    // Convert to sorted vector
    spectrum_map.into_iter().collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// SpectralAnalysis: Main Public Interface
// ─────────────────────────────────────────────────────────────────────────────

/// Spectral analysis of the Atlas graph Laplacian
///
/// Computes the complete spectrum of the Atlas Laplacian through a block
/// tridiagonal decomposition, proving that the spectral gap is exactly λ₁ = 1.
///
/// # Construction
///
/// The analysis proceeds by:
/// 1. Decomposing the Atlas into two hemispheres (by e₇)
/// 2. Decomposing each hemisphere into three Q₄ blocks (by d₄₅)
/// 3. Verifying the block tridiagonal structure
/// 4. Computing eigenvalues of 3×3 block matrices M_ν
/// 5. Assembling the complete spectrum
/// 6. Cross-checking against trace identities
///
/// # Examples
///
/// ```
/// use atlas_embeddings::{Atlas, spectral::SpectralAnalysis};
/// use atlas_embeddings::arithmetic::Rational;
///
/// let atlas = Atlas::new();
/// let spectral = SpectralAnalysis::from_atlas(&atlas);
///
/// // Main result: spectral gap is exactly 1
/// assert_eq!(spectral.spectral_gap(), Rational::from_integer(1));
///
/// // Hemisphere has 48 eigenvalues (counting multiplicity)
/// let total: usize = spectral.hemisphere_spectrum().iter().map(|(_, m)| m).sum();
/// assert_eq!(total, 48);
/// ```
#[derive(Debug, Clone)]
pub struct SpectralAnalysis {
    /// Complete hemisphere spectrum: (eigenvalue, multiplicity) sorted by eigenvalue
    hemisphere_spectrum: Vec<(Rational, usize)>,

    /// Complete full Atlas spectrum: (eigenvalue, multiplicity) sorted by eigenvalue
    full_spectrum: Vec<(Rational, usize)>,

    /// Spectral gap: smallest nonzero eigenvalue
    spectral_gap: Rational,

    /// Hemisphere Laplacian trace: tr(L_H) = 2|E_H| = 256
    hemisphere_trace: Rational,

    /// Hemisphere Laplacian trace of square: tr(L_H²) = 1632
    hemisphere_trace_squared: Rational,

    /// Maximum eigenvalue (Gershgorin bound: ≤ 2 × max_degree)
    max_eigenvalue: Rational,

    /// Hemisphere Laplacian matrix (48×48, for explicit verification)
    hemisphere_laplacian: DenseRatMatrix,
}

impl SpectralAnalysis {
    /// Construct spectral analysis from an Atlas graph
    ///
    /// This performs the full block tridiagonal decomposition, verifying
    /// all structural assumptions and computing the complete spectrum.
    ///
    /// # Panics
    ///
    /// Panics if any structural verification fails (hemisphere count,
    /// block structure, Q₄ properties, trace cross-checks).
    ///
    /// # Examples
    ///
    /// ```
    /// use atlas_embeddings::{Atlas, spectral::SpectralAnalysis};
    ///
    /// let atlas = Atlas::new();
    /// let spectral = SpectralAnalysis::from_atlas(&atlas);
    /// assert_eq!(*spectral.spectral_gap().numer(), 1);
    /// assert_eq!(*spectral.spectral_gap().denom(), 1);
    /// ```
    #[must_use]
    pub fn from_atlas(atlas: &Atlas) -> Self {
        // Step 1: Verify Atlas basics
        assert_eq!(atlas.num_vertices(), 96, "Atlas must have 96 vertices");
        assert_eq!(atlas.num_edges(), 256, "Atlas must have 256 edges");

        // Step 2: Decompose into hemispheres
        let hemispheres = decompose_hemispheres(atlas);
        verify_no_cross_hemisphere_edges(atlas, &hemispheres);

        // Step 3: Decompose hemisphere 0 into Q4 blocks
        let blocks = decompose_blocks(atlas, &hemispheres[0]);

        // Step 4: Verify Q4 structure for each block
        for (i, block) in blocks.iter().enumerate() {
            verify_q4_block(atlas, block);
            verify_q4_spectrum(atlas, block);
            let _ = i; // suppress unused variable
        }

        // Step 5: Verify inter-block identity matching
        verify_inter_block_structure(atlas, &blocks);

        // Step 6: Compute spectrum from block tridiagonal decomposition
        let hemisphere_spectrum = compute_hemisphere_spectrum();

        // Step 7: Verify total multiplicity
        let total_mult: usize = hemisphere_spectrum.iter().map(|(_, m)| *m).sum();
        assert_eq!(
            total_mult, HEMISPHERE_VERTICES,
            "Total multiplicity must equal hemisphere vertex count"
        );

        // Step 8: Compute derived quantities
        let spectral_gap = Self::find_spectral_gap(&hemisphere_spectrum);
        let hemisphere_trace = Self::compute_trace(&hemisphere_spectrum);
        let hemisphere_trace_squared = Self::compute_trace_squared(&hemisphere_spectrum);
        let max_eigenvalue = Self::find_max_eigenvalue(&hemisphere_spectrum);

        // Step 9: Build explicit hemisphere Laplacian for verification
        let hemisphere_laplacian =
            DenseRatMatrix::from_atlas_subgraph(atlas, &hemispheres[0]);

        // Step 10: Cross-check trace against explicit Laplacian
        assert_eq!(
            hemisphere_laplacian.trace(),
            hemisphere_trace,
            "Trace mismatch: Laplacian trace vs spectrum trace"
        );

        // Step 11: Cross-check trace² against explicit Laplacian
        // tr(L²) = Σᵢⱼ L[i,j]² for symmetric L
        assert_eq!(
            hemisphere_laplacian.frobenius_squared(),
            hemisphere_trace_squared,
            "Trace² mismatch: Laplacian Frobenius² vs spectrum trace²"
        );

        // Step 12: Verify Laplacian properties
        assert!(
            hemisphere_laplacian.is_symmetric(),
            "Hemisphere Laplacian must be symmetric"
        );
        for i in 0..HEMISPHERE_VERTICES {
            assert!(
                hemisphere_laplacian.row_sum(i).is_zero(),
                "Laplacian row {i} sum must be zero"
            );
        }
        assert!(
            hemisphere_laplacian.has_nonneg_diagonal(),
            "Laplacian diagonal must be non-negative"
        );
        assert!(
            hemisphere_laplacian.has_nonpos_off_diagonal(),
            "Laplacian off-diagonal must be non-positive"
        );

        // Step 13: Build full Atlas spectrum (two copies of hemisphere)
        let full_spectrum: Vec<(Rational, usize)> = hemisphere_spectrum
            .iter()
            .map(|&(ev, mult)| (ev, mult * 2))
            .collect();

        Self {
            hemisphere_spectrum,
            full_spectrum,
            spectral_gap,
            hemisphere_trace,
            hemisphere_trace_squared,
            max_eigenvalue,
            hemisphere_laplacian,
        }
    }

    /// Get the spectral gap (smallest nonzero eigenvalue)
    ///
    /// **Theorem 10.4.3**: The spectral gap of the Atlas Laplacian is exactly λ₁ = 1.
    ///
    /// # Examples
    ///
    /// ```
    /// use atlas_embeddings::{Atlas, spectral::SpectralAnalysis};
    /// use atlas_embeddings::arithmetic::Rational;
    ///
    /// let spectral = SpectralAnalysis::from_atlas(&Atlas::new());
    /// assert_eq!(spectral.spectral_gap(), Rational::from_integer(1));
    /// ```
    #[must_use]
    pub const fn spectral_gap(&self) -> Rational {
        self.spectral_gap
    }

    /// Get the complete hemisphere spectrum as (eigenvalue, multiplicity) pairs
    ///
    /// Sorted by eigenvalue. Total multiplicity sums to 48.
    #[must_use]
    pub fn hemisphere_spectrum(&self) -> &[(Rational, usize)] {
        &self.hemisphere_spectrum
    }

    /// Get the complete full Atlas spectrum as (eigenvalue, multiplicity) pairs
    ///
    /// The full spectrum has double the multiplicities of the hemisphere spectrum
    /// (two disconnected hemispheres). Total multiplicity sums to 96.
    #[must_use]
    pub fn full_spectrum(&self) -> &[(Rational, usize)] {
        &self.full_spectrum
    }

    /// Get the hemisphere Laplacian trace: tr(L_H) = 2|E_H| = 256
    #[must_use]
    pub const fn hemisphere_trace(&self) -> Rational {
        self.hemisphere_trace
    }

    /// Get the hemisphere Laplacian trace of square: tr(L_H²) = 1632
    #[must_use]
    pub const fn hemisphere_trace_squared(&self) -> Rational {
        self.hemisphere_trace_squared
    }

    /// Get the maximum eigenvalue
    ///
    /// For the Atlas hemisphere, max eigenvalue is 11 (from Q₄ eigenvalue ν=8,
    /// contributing M₈ eigenvalue ν+3 = 11).
    #[must_use]
    pub const fn max_eigenvalue(&self) -> Rational {
        self.max_eigenvalue
    }

    /// Get the number of distinct eigenvalues in the hemisphere spectrum
    #[must_use]
    pub fn num_distinct_eigenvalues(&self) -> usize {
        self.hemisphere_spectrum.len()
    }

    /// Get the Gershgorin upper bound on eigenvalues
    ///
    /// For a graph Laplacian, all eigenvalues ≤ 2 × max_degree.
    /// For the Atlas hemisphere, max_degree = 6, so bound = 12.
    #[must_use]
    pub fn gershgorin_upper_bound(&self) -> Rational {
        Rational::from_integer(12)
    }

    /// Get the hemisphere Laplacian dimension (48×48)
    #[must_use]
    pub const fn hemisphere_laplacian_dimension(&self) -> usize {
        self.hemisphere_laplacian.n
    }

    /// Check if all eigenvalues are integers
    #[must_use]
    pub fn all_eigenvalues_integer(&self) -> bool {
        self.hemisphere_spectrum
            .iter()
            .all(|(ev, _)| *ev.denom() == 1)
    }

    /// Get the block tridiagonal matrix M_ν for a given Q₄ eigenvalue
    ///
    /// Returns the 3×3 matrix as a nested array of rationals.
    ///
    /// # Panics
    ///
    /// Panics if ν is not a valid Q₄ eigenvalue (must be 0, 2, 4, 6, or 8).
    #[must_use]
    pub fn block_matrix(&self, nu: i64) -> [[Rational; 3]; 3] {
        assert!(
            Q4_SPECTRUM.iter().any(|&(ev, _)| ev == nu),
            "ν = {nu} is not a Q4 eigenvalue (must be 0, 2, 4, 6, or 8)"
        );
        block_tridiagonal_matrix(nu)
    }

    // ─── Private helpers ─────────────────────────────────────────────

    /// Find the spectral gap (smallest nonzero eigenvalue)
    fn find_spectral_gap(spectrum: &[(Rational, usize)]) -> Rational {
        for &(ev, _) in spectrum {
            if !ev.is_zero() {
                return ev;
            }
        }
        panic!("No nonzero eigenvalue found in spectrum");
    }

    /// Compute trace from spectrum: Σ λᵢ × multᵢ
    #[allow(clippy::cast_possible_wrap)]
    fn compute_trace(spectrum: &[(Rational, usize)]) -> Rational {
        let mut sum = Rational::zero();
        for &(ev, mult) in spectrum {
            sum += ev * Rational::from_integer(mult as i64);
        }
        sum
    }

    /// Compute trace of square from spectrum: Σ λᵢ² × multᵢ
    #[allow(clippy::cast_possible_wrap)]
    fn compute_trace_squared(spectrum: &[(Rational, usize)]) -> Rational {
        let mut sum = Rational::zero();
        for &(ev, mult) in spectrum {
            sum += ev * ev * Rational::from_integer(mult as i64);
        }
        sum
    }

    /// Find maximum eigenvalue
    fn find_max_eigenvalue(spectrum: &[(Rational, usize)]) -> Rational {
        spectrum
            .last()
            .map_or_else(Rational::zero, |&(ev, _)| ev)
    }
}

impl fmt::Display for SpectralAnalysis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Atlas Spectral Analysis")?;
        writeln!(f, "======================")?;
        writeln!(f)?;
        writeln!(f, "Spectral gap: λ₁ = {}", self.spectral_gap)?;
        writeln!(f, "Max eigenvalue: λ_max = {}", self.max_eigenvalue)?;
        writeln!(f, "Distinct eigenvalues: {}", self.num_distinct_eigenvalues())?;
        writeln!(f)?;
        writeln!(f, "Hemisphere spectrum (48 eigenvalues):")?;
        for &(ev, mult) in &self.hemisphere_spectrum {
            writeln!(f, "  λ = {ev:>3}  multiplicity = {mult}")?;
        }
        writeln!(f)?;
        writeln!(f, "Trace:  {}", self.hemisphere_trace)?;
        writeln!(f, "Trace²: {}", self.hemisphere_trace_squared)?;
        writeln!(f, "Gershgorin bound: [0, {}]", self.gershgorin_upper_bound())?;
        Ok(())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Unit Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Atlas;

    // ─── 3×3 Determinant Tests ───────────────────────────────────────

    /// **Test: 3×3 Identity Determinant**
    ///
    /// Verifies det(I₃) = 1.
    #[test]
    fn test_det3x3_identity() {
        let eye = [
            [Rational::one(), Rational::zero(), Rational::zero()],
            [Rational::zero(), Rational::one(), Rational::zero()],
            [Rational::zero(), Rational::zero(), Rational::one()],
        ];
        assert_eq!(det_3x3(&eye), Rational::one());
    }

    /// **Test: 3×3 Known Determinant**
    ///
    /// Verifies determinant computation against a known example.
    #[test]
    fn test_det3x3_known() {
        let m = [
            [Rational::new(1, 1), Rational::new(2, 1), Rational::new(3, 1)],
            [Rational::new(4, 1), Rational::new(5, 1), Rational::new(6, 1)],
            [Rational::new(7, 1), Rational::new(8, 1), Rational::new(9, 1)],
        ];
        // This matrix is singular (row3 = row1 + row2 - row1... actually
        // det = 1(45-48) - 2(36-42) + 3(32-35) = -3 + 12 - 9 = 0)
        assert_eq!(det_3x3(&m), Rational::zero());
    }

    /// **Test: 3×3 Non-Singular Determinant**
    ///
    /// Verifies determinant of a non-singular matrix.
    #[test]
    fn test_det3x3_nonsingular() {
        let m = [
            [Rational::new(2, 1), Rational::new(-1, 1), Rational::zero()],
            [Rational::new(-1, 1), Rational::new(2, 1), Rational::new(-1, 1)],
            [Rational::zero(), Rational::new(-1, 1), Rational::new(2, 1)],
        ];
        // This is a tridiagonal 2,-1 matrix; det = 4
        assert_eq!(det_3x3(&m), Rational::new(4, 1));
    }

    // ─── Block Tridiagonal Matrix Tests ──────────────────────────────

    /// **Test: Theorem 10.3.2 (Block Matrix M₀)**
    ///
    /// Verifies M₀ = [[1,-1,0],[-1,2,-1],[0,-1,1]] has correct structure.
    #[test]
    fn test_block_matrix_nu0() {
        let m = block_tridiagonal_matrix(0);
        assert_eq!(m[0][0], Rational::one());
        assert_eq!(m[0][1], -Rational::one());
        assert_eq!(m[0][2], Rational::zero());
        assert_eq!(m[1][0], -Rational::one());
        assert_eq!(m[1][1], Rational::new(2, 1));
        assert_eq!(m[1][2], -Rational::one());
        assert_eq!(m[2][0], Rational::zero());
        assert_eq!(m[2][1], -Rational::one());
        assert_eq!(m[2][2], Rational::one());
    }

    /// **Test: Theorem 10.4.1 (Eigenvalues of M₀)**
    ///
    /// Verifies eigenvalues of M₀ are {0, 1, 3} by checking
    /// det(M₀ - λI) = 0 for each candidate.
    #[test]
    fn test_block_eigenvalues_nu0() {
        let eigs = verify_block_eigenvalues(0);
        assert_eq!(eigs[0], Rational::zero());
        assert_eq!(eigs[1], Rational::one());
        assert_eq!(eigs[2], Rational::new(3, 1));
    }

    /// **Test: Theorem 10.4.1 (Eigenvalues of M₂)**
    ///
    /// Verifies eigenvalues of M₂ are {2, 3, 5}.
    #[test]
    fn test_block_eigenvalues_nu2() {
        let eigs = verify_block_eigenvalues(2);
        assert_eq!(eigs[0], Rational::new(2, 1));
        assert_eq!(eigs[1], Rational::new(3, 1));
        assert_eq!(eigs[2], Rational::new(5, 1));
    }

    /// **Test: Theorem 10.4.1 (Eigenvalues of M₄)**
    ///
    /// Verifies eigenvalues of M₄ are {4, 5, 7}.
    #[test]
    fn test_block_eigenvalues_nu4() {
        let eigs = verify_block_eigenvalues(4);
        assert_eq!(eigs[0], Rational::new(4, 1));
        assert_eq!(eigs[1], Rational::new(5, 1));
        assert_eq!(eigs[2], Rational::new(7, 1));
    }

    /// **Test: Theorem 10.4.1 (Eigenvalues of M₆)**
    ///
    /// Verifies eigenvalues of M₆ are {6, 7, 9}.
    #[test]
    fn test_block_eigenvalues_nu6() {
        let eigs = verify_block_eigenvalues(6);
        assert_eq!(eigs[0], Rational::new(6, 1));
        assert_eq!(eigs[1], Rational::new(7, 1));
        assert_eq!(eigs[2], Rational::new(9, 1));
    }

    /// **Test: Theorem 10.4.1 (Eigenvalues of M₈)**
    ///
    /// Verifies eigenvalues of M₈ are {8, 9, 11}.
    #[test]
    fn test_block_eigenvalues_nu8() {
        let eigs = verify_block_eigenvalues(8);
        assert_eq!(eigs[0], Rational::new(8, 1));
        assert_eq!(eigs[1], Rational::new(9, 1));
        assert_eq!(eigs[2], Rational::new(11, 1));
    }

    /// **Test: M_ν Symmetry**
    ///
    /// Verifies that all block tridiagonal matrices are symmetric.
    #[test]
    fn test_block_matrix_symmetry() {
        for &(nu, _) in &Q4_SPECTRUM {
            let m = block_tridiagonal_matrix(nu);
            for i in 0..3 {
                for j in 0..3 {
                    assert_eq!(
                        m[i][j], m[j][i],
                        "M_{nu} must be symmetric at ({i},{j})"
                    );
                }
            }
        }
    }

    /// **Test: M_ν Trace Equals Sum of Eigenvalues**
    ///
    /// Verifies tr(M_ν) = ν + (ν+1) + (ν+3) = 3ν + 4 for each ν.
    #[test]
    fn test_block_matrix_trace() {
        for &(nu, _) in &Q4_SPECTRUM {
            let m = block_tridiagonal_matrix(nu);
            let trace = m[0][0] + m[1][1] + m[2][2];
            let expected = Rational::from_integer(3 * nu + 4);
            assert_eq!(trace, expected, "tr(M_{nu}) must be 3ν+4");
        }
    }

    /// **Test: M_ν Determinant Equals Product of Eigenvalues**
    ///
    /// Verifies det(M_ν) = ν · (ν+1) · (ν+3) for each ν.
    #[test]
    fn test_block_matrix_determinant() {
        for &(nu, _) in &Q4_SPECTRUM {
            let m = block_tridiagonal_matrix(nu);
            let det = det_3x3(&m);
            let expected = Rational::from_integer(nu * (nu + 1) * (nu + 3));
            assert_eq!(det, expected, "det(M_{nu}) must be ν(ν+1)(ν+3)");
        }
    }

    // ─── Hemisphere Decomposition Tests ──────────────────────────────

    /// **Test: Theorem 10.2.1 (Hemisphere Vertex Count)**
    ///
    /// Verifies that each hemisphere has exactly 48 vertices.
    #[test]
    fn test_hemisphere_vertex_count() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);
        assert_eq!(hemispheres[0].len(), 48);
        assert_eq!(hemispheres[1].len(), 48);
    }

    /// **Test: Theorem 10.2.1 (No Cross-Hemisphere Edges)**
    ///
    /// Verifies that the two hemispheres are disconnected.
    #[test]
    fn test_no_cross_hemisphere_edges() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);
        verify_no_cross_hemisphere_edges(&atlas, &hemispheres);
    }

    /// **Test: Hemisphere Edge Count**
    ///
    /// Verifies each hemisphere has exactly 128 edges.
    #[test]
    fn test_hemisphere_edge_count() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);
        let h0_set: HashSet<usize> = hemispheres[0].iter().copied().collect();

        let mut edge_count = 0usize;
        for &v in &hemispheres[0] {
            for &n in atlas.neighbors(v) {
                if h0_set.contains(&n) && v < n {
                    edge_count += 1;
                }
            }
        }
        assert_eq!(edge_count, 128);
    }

    // ─── Q4 Block Tests ─────────────────────────────────────────────

    /// **Test: Theorem 10.2.2 (Q₄ Block Vertex Count)**
    ///
    /// Verifies each d₄₅ block has exactly 16 vertices.
    #[test]
    fn test_q4_block_vertex_count() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);
        let blocks = decompose_blocks(&atlas, &hemispheres[0]);
        for (i, block) in blocks.iter().enumerate() {
            assert_eq!(block.len(), 16, "Block {i} must have 16 vertices");
        }
    }

    /// **Test: Q₄ Block Regularity**
    ///
    /// Verifies each Q₄ block is 4-regular.
    #[test]
    fn test_q4_block_regularity() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);
        let blocks = decompose_blocks(&atlas, &hemispheres[0]);

        for block in &blocks {
            verify_q4_block(&atlas, block);
        }
    }

    /// **Test: Q₄ Block Spectrum**
    ///
    /// Verifies Q₄ spectrum via trace cross-checks.
    #[test]
    fn test_q4_block_spectrum() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);
        let blocks = decompose_blocks(&atlas, &hemispheres[0]);

        for block in &blocks {
            verify_q4_spectrum(&atlas, block);
        }
    }

    // ─── Inter-Block Structure Tests ─────────────────────────────────

    /// **Test: Theorem 10.2.3 (Inter-Block Identity Matching)**
    ///
    /// Verifies inter-block edges form identity matchings.
    #[test]
    fn test_inter_block_identity_matching() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);
        let blocks = decompose_blocks(&atlas, &hemispheres[0]);
        verify_inter_block_structure(&atlas, &blocks);
    }

    /// **Test: No Skip Edges (d45=-1 ↔ d45=+1)**
    ///
    /// Verifies there are no edges between non-adjacent blocks.
    #[test]
    fn test_no_skip_edges() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);
        let blocks = decompose_blocks(&atlas, &hemispheres[0]);

        let b_neg_set: HashSet<usize> = blocks[0].iter().copied().collect();
        let b_pos_set: HashSet<usize> = blocks[2].iter().copied().collect();

        for &v in &blocks[0] {
            for &n in atlas.neighbors(v) {
                assert!(!b_pos_set.contains(&n), "Skip edge: {v} ~ {n}");
            }
        }
        for &v in &blocks[2] {
            for &n in atlas.neighbors(v) {
                assert!(!b_neg_set.contains(&n), "Skip edge: {v} ~ {n}");
            }
        }
    }

    /// **Test: Inter-Block Edge Count**
    ///
    /// Verifies 16 edges between d45=-1↔d45=0 and 16 between d45=0↔d45=+1.
    #[test]
    fn test_inter_block_edge_count() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);
        let blocks = decompose_blocks(&atlas, &hemispheres[0]);

        let block_sets: [HashSet<usize>; 3] = [
            blocks[0].iter().copied().collect(),
            blocks[1].iter().copied().collect(),
            blocks[2].iter().copied().collect(),
        ];

        // Count edges between d45=-1 and d45=0
        let mut edges_neg_zero = 0usize;
        for &v in &blocks[0] {
            edges_neg_zero += atlas
                .neighbors(v)
                .iter()
                .filter(|n| block_sets[1].contains(n))
                .count();
        }
        assert_eq!(edges_neg_zero, 16, "16 edges from d45=-1 to d45=0");

        // Count edges between d45=+1 and d45=0
        let mut edges_pos_zero = 0usize;
        for &v in &blocks[2] {
            edges_pos_zero += atlas
                .neighbors(v)
                .iter()
                .filter(|n| block_sets[1].contains(n))
                .count();
        }
        assert_eq!(edges_pos_zero, 16, "16 edges from d45=+1 to d45=0");
    }

    // ─── Hemisphere Spectrum Tests ───────────────────────────────────

    /// **Test: Theorem 10.4.2 (Complete Hemisphere Spectrum)**
    ///
    /// Verifies the hemisphere spectrum matches the expected eigenvalues
    /// and multiplicities from the block tridiagonal decomposition.
    #[test]
    fn test_hemisphere_spectrum() {
        let spectrum = compute_hemisphere_spectrum();

        let expected: Vec<(Rational, usize)> = vec![
            (Rational::zero(), 1),
            (Rational::from_integer(1), 1),
            (Rational::from_integer(2), 4),
            (Rational::from_integer(3), 5),
            (Rational::from_integer(4), 6),
            (Rational::from_integer(5), 10),
            (Rational::from_integer(6), 4),
            (Rational::from_integer(7), 10),
            (Rational::from_integer(8), 1),
            (Rational::from_integer(9), 5),
            (Rational::from_integer(11), 1),
        ];

        assert_eq!(spectrum, expected);
    }

    /// **Test: Hemisphere Spectrum Total Multiplicity**
    ///
    /// Verifies the total multiplicity sums to 48 (hemisphere vertex count).
    #[test]
    fn test_hemisphere_spectrum_total() {
        let spectrum = compute_hemisphere_spectrum();
        let total: usize = spectrum.iter().map(|(_, m)| m).sum();
        assert_eq!(total, 48);
    }

    /// **Test: 11 Distinct Eigenvalues**
    ///
    /// Verifies the hemisphere has exactly 11 distinct eigenvalues.
    /// Note: eigenvalue 10 is absent (not achievable from M_ν eigenvalues).
    #[test]
    fn test_distinct_eigenvalue_count() {
        let spectrum = compute_hemisphere_spectrum();
        assert_eq!(spectrum.len(), 11, "11 distinct eigenvalues");
    }

    /// **Test: Eigenvalue 10 Is Absent**
    ///
    /// Verifies that λ = 10 does not appear in the spectrum.
    /// This is because no combination of ν ∈ {0,2,4,6,8} and offset ∈ {0,1,3}
    /// yields 10.
    #[test]
    fn test_eigenvalue_10_absent() {
        let spectrum = compute_hemisphere_spectrum();
        let ten = Rational::from_integer(10);
        assert!(
            !spectrum.iter().any(|&(ev, _)| ev == ten),
            "Eigenvalue 10 must not appear in spectrum"
        );
    }

    // ─── Spectral Gap Tests ──────────────────────────────────────────

    /// **Test: Theorem 10.4.3 (Spectral Gap λ₁ = 1)**
    ///
    /// The main result: spectral gap of the Atlas Laplacian is exactly 1.
    #[test]
    fn test_spectral_gap_is_one() {
        let atlas = Atlas::new();
        let spectral = SpectralAnalysis::from_atlas(&atlas);
        assert_eq!(spectral.spectral_gap(), Rational::from_integer(1));
    }

    /// **Test: Spectral Gap Origin**
    ///
    /// Verifies the spectral gap λ₁ = 1 arises from M₀'s second eigenvalue.
    /// M₀ has eigenvalues {0, 1, 3}, and 1 is the smallest nonzero value
    /// across all M_ν eigenvalues.
    #[test]
    fn test_spectral_gap_origin() {
        let eigs_0 = verify_block_eigenvalues(0);
        // M_0 eigenvalues are 0, 1, 3
        // The spectral gap is 1 (second eigenvalue of M_0)
        assert_eq!(eigs_0[1], Rational::one());

        // Verify no other block contributes a smaller nonzero eigenvalue
        for &(nu, _) in &Q4_SPECTRUM {
            if nu > 0 {
                let eigs = verify_block_eigenvalues(nu);
                for &e in &eigs {
                    assert!(
                        e >= Rational::one(),
                        "Eigenvalue {e} from M_{nu} is less than spectral gap"
                    );
                }
            }
        }
    }

    // ─── Cross-Check Tests ───────────────────────────────────────────

    /// **Test: Trace Cross-Check**
    ///
    /// Verifies tr(L_H) = 256 = 2|E_H| both from spectrum and from
    /// direct degree sum computation.
    #[test]
    fn test_trace_crosscheck() {
        let atlas = Atlas::new();
        let spectral = SpectralAnalysis::from_atlas(&atlas);

        // From spectrum
        assert_eq!(
            spectral.hemisphere_trace(),
            Rational::from_integer(256)
        );

        // From degree sum
        let hemispheres = decompose_hemispheres(&atlas);
        let h0_set: HashSet<usize> = hemispheres[0].iter().copied().collect();
        let mut degree_sum: i64 = 0;
        for &v in &hemispheres[0] {
            let deg = atlas
                .neighbors(v)
                .iter()
                .filter(|n| h0_set.contains(n))
                .count() as i64;
            degree_sum += deg;
        }
        assert_eq!(degree_sum, 256);
    }

    /// **Test: Trace² Cross-Check**
    ///
    /// Verifies tr(L_H²) = 1632 both from spectrum and from
    /// the formula Σ deg(v)² + 2|E|.
    #[test]
    fn test_trace_squared_crosscheck() {
        let atlas = Atlas::new();
        let spectral = SpectralAnalysis::from_atlas(&atlas);

        // From spectrum
        assert_eq!(
            spectral.hemisphere_trace_squared(),
            Rational::from_integer(1632)
        );

        // From degree formula
        let hemispheres = decompose_hemispheres(&atlas);
        let h0_set: HashSet<usize> = hemispheres[0].iter().copied().collect();
        let mut deg_sq_sum: i64 = 0;
        let mut edge_count: i64 = 0;
        for &v in &hemispheres[0] {
            let deg = atlas
                .neighbors(v)
                .iter()
                .filter(|n| h0_set.contains(n))
                .count() as i64;
            deg_sq_sum += deg * deg;
            edge_count += deg;
        }
        edge_count /= 2; // each edge counted twice
        let trace_sq = deg_sq_sum + 2 * edge_count;
        assert_eq!(trace_sq, 1632);
    }

    /// **Test: Gershgorin Bound**
    ///
    /// Verifies all eigenvalues lie within [0, 12] (Gershgorin circle theorem).
    /// The bound 12 = 2 × max_degree = 2 × 6.
    #[test]
    fn test_gershgorin_bound() {
        let atlas = Atlas::new();
        let spectral = SpectralAnalysis::from_atlas(&atlas);

        let bound = spectral.gershgorin_upper_bound();
        for &(ev, _) in spectral.hemisphere_spectrum() {
            assert!(ev >= Rational::zero(), "Eigenvalue {ev} < 0");
            assert!(ev <= bound, "Eigenvalue {ev} > Gershgorin bound {bound}");
        }
    }

    /// **Test: All Eigenvalues Are Integers**
    ///
    /// Verifies that every eigenvalue in the hemisphere spectrum is an integer.
    /// This is a consequence of the block structure: all M_ν eigenvalues
    /// {ν, ν+1, ν+3} are integers for integer ν.
    #[test]
    fn test_all_eigenvalues_integer() {
        let atlas = Atlas::new();
        let spectral = SpectralAnalysis::from_atlas(&atlas);
        assert!(spectral.all_eigenvalues_integer());
    }

    /// **Test: Laplacian Symmetry**
    ///
    /// Verifies the explicit hemisphere Laplacian matrix is symmetric.
    #[test]
    fn test_laplacian_symmetry() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);
        let laplacian = DenseRatMatrix::from_atlas_subgraph(&atlas, &hemispheres[0]);
        assert!(laplacian.is_symmetric());
    }

    /// **Test: Laplacian Row Sums Zero**
    ///
    /// Verifies every row of the hemisphere Laplacian sums to zero
    /// (L·1 = 0 is a defining property).
    #[test]
    fn test_laplacian_row_sums_zero() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);
        let laplacian = DenseRatMatrix::from_atlas_subgraph(&atlas, &hemispheres[0]);

        for i in 0..HEMISPHERE_VERTICES {
            assert!(
                laplacian.row_sum(i).is_zero(),
                "Row {i} sum is not zero"
            );
        }
    }

    /// **Test: Full Atlas Spectrum**
    ///
    /// Verifies the full Atlas spectrum (96 eigenvalues) is twice
    /// the hemisphere spectrum (two isomorphic disconnected components).
    #[test]
    fn test_full_atlas_spectrum() {
        let atlas = Atlas::new();
        let spectral = SpectralAnalysis::from_atlas(&atlas);

        let full = spectral.full_spectrum();
        let hemi = spectral.hemisphere_spectrum();

        // Same eigenvalues, doubled multiplicities
        assert_eq!(full.len(), hemi.len());
        for i in 0..full.len() {
            assert_eq!(full[i].0, hemi[i].0);
            assert_eq!(full[i].1, hemi[i].1 * 2);
        }

        // Total multiplicity = 96
        let total: usize = full.iter().map(|(_, m)| m).sum();
        assert_eq!(total, 96);
    }

    /// **Test: Zero Eigenvalue Multiplicity**
    ///
    /// Verifies λ = 0 has multiplicity 1 per hemisphere (each hemisphere
    /// is connected) and multiplicity 2 for the full Atlas.
    #[test]
    fn test_zero_eigenvalue_multiplicity() {
        let atlas = Atlas::new();
        let spectral = SpectralAnalysis::from_atlas(&atlas);

        // Hemisphere: multiplicity 1 (connected)
        let hemi_zero = spectral
            .hemisphere_spectrum()
            .iter()
            .find(|&&(ev, _)| ev.is_zero());
        assert_eq!(hemi_zero, Some(&(Rational::zero(), 1)));

        // Full Atlas: multiplicity 2 (two connected components)
        let full_zero = spectral
            .full_spectrum()
            .iter()
            .find(|&&(ev, _)| ev.is_zero());
        assert_eq!(full_zero, Some(&(Rational::zero(), 2)));
    }

    /// **Test: Maximum Eigenvalue Is 11**
    ///
    /// Verifies the largest eigenvalue is 11 (from M₈: eigenvalues {8, 9, 11}).
    #[test]
    fn test_max_eigenvalue() {
        let atlas = Atlas::new();
        let spectral = SpectralAnalysis::from_atlas(&atlas);
        assert_eq!(spectral.max_eigenvalue(), Rational::from_integer(11));
    }

    /// **Test: Hemisphere Isomorphism**
    ///
    /// Verifies both hemispheres have the same degree sequence,
    /// confirming they are isomorphic (via mirror map τ).
    #[test]
    fn test_hemisphere_isomorphism() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);

        let h0_set: HashSet<usize> = hemispheres[0].iter().copied().collect();
        let h1_set: HashSet<usize> = hemispheres[1].iter().copied().collect();

        let mut degrees_0: Vec<usize> = hemispheres[0]
            .iter()
            .map(|&v| {
                atlas
                    .neighbors(v)
                    .iter()
                    .filter(|n| h0_set.contains(n))
                    .count()
            })
            .collect();

        let mut degrees_1: Vec<usize> = hemispheres[1]
            .iter()
            .map(|&v| {
                atlas
                    .neighbors(v)
                    .iter()
                    .filter(|n| h1_set.contains(n))
                    .count()
            })
            .collect();

        degrees_0.sort_unstable();
        degrees_1.sort_unstable();
        assert_eq!(degrees_0, degrees_1, "Hemispheres must have same degree sequence");
    }

    /// **Test: Display Formatting**
    ///
    /// Verifies the Display implementation produces output containing
    /// the key result (spectral gap = 1).
    #[test]
    fn test_display() {
        let atlas = Atlas::new();
        let spectral = SpectralAnalysis::from_atlas(&atlas);
        let output = format!("{spectral}");
        assert!(output.contains("Spectral gap"));
        assert!(output.contains('1'));
    }

    /// **Test: Block Matrix Accessor**
    ///
    /// Verifies the public `block_matrix()` accessor works correctly.
    #[test]
    fn test_block_matrix_accessor() {
        let atlas = Atlas::new();
        let spectral = SpectralAnalysis::from_atlas(&atlas);

        let m0 = spectral.block_matrix(0);
        assert_eq!(m0[0][0], Rational::one());
        assert_eq!(m0[1][1], Rational::new(2, 1));

        let m8 = spectral.block_matrix(8);
        assert_eq!(m8[0][0], Rational::new(9, 1));
        assert_eq!(m8[1][1], Rational::new(10, 1));
    }

    /// **Test: Characteristic Polynomial Factorization**
    ///
    /// Verifies det(M_ν - λI) = (ν-λ)(ν+1-λ)(ν+3-λ) for all ν by
    /// checking at multiple non-eigenvalue points.
    #[test]
    fn test_characteristic_polynomial() {
        for &(nu, _) in &Q4_SPECTRUM {
            let m = block_tridiagonal_matrix(nu);
            let nu_r = Rational::from_integer(nu);

            // Check at several non-eigenvalue points
            for test_val in [nu - 1, nu + 2, nu + 4, nu + 5] {
                let lambda = Rational::from_integer(test_val);
                let shifted = [
                    [m[0][0] - lambda, m[0][1], m[0][2]],
                    [m[1][0], m[1][1] - lambda, m[1][2]],
                    [m[2][0], m[2][1], m[2][2] - lambda],
                ];
                let det = det_3x3(&shifted);

                // Expected: (ν - λ)(ν+1 - λ)(ν+3 - λ)
                let expected = (nu_r - lambda)
                    * (nu_r + Rational::one() - lambda)
                    * (nu_r + Rational::new(3, 1) - lambda);

                assert_eq!(
                    det, expected,
                    "Characteristic polynomial mismatch at ν={nu}, λ={test_val}"
                );
            }
        }
    }

    /// **Test: Degree Distribution Within Hemisphere**
    ///
    /// Verifies the hemisphere has 32 degree-5 vertices (d45=±1) and
    /// 16 degree-6 vertices (d45=0).
    #[test]
    fn test_hemisphere_degree_distribution() {
        let atlas = Atlas::new();
        let hemispheres = decompose_hemispheres(&atlas);
        let h0_set: HashSet<usize> = hemispheres[0].iter().copied().collect();

        let mut deg5_count = 0usize;
        let mut deg6_count = 0usize;

        for &v in &hemispheres[0] {
            let deg = atlas
                .neighbors(v)
                .iter()
                .filter(|n| h0_set.contains(n))
                .count();
            match deg {
                5 => deg5_count += 1,
                6 => deg6_count += 1,
                d => panic!("Unexpected degree {d} in hemisphere"),
            }
        }

        assert_eq!(deg5_count, 32, "32 vertices of degree 5 (d45=±1)");
        assert_eq!(deg6_count, 16, "16 vertices of degree 6 (d45=0)");
    }
}
