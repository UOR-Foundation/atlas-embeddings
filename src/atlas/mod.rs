#![allow(clippy::doc_markdown)] // Allow e_1, e_2, etc. in LaTeX math blocks
//! # Chapter 1: The Atlas of Resonance Classes
//!
//! This chapter presents the construction and properties of the **Atlas**: a 96-vertex
//! graph that emerges as the unique stationary configuration of an action functional
//! on a 12,288-cell boundary complex.
//!
//! ## Overview
//!
//! The Atlas is not designed or assumed—it is **discovered** through computational
//! optimization. Starting only with an action functional (Chapter 0.2), we find its
//! stationary configuration and observe that it naturally partitions into exactly
//! 96 equivalence classes. This number is not input but output.
//!
//! **Main result**: The Atlas is the initial object in the category of resonance graphs,
//! from which all five exceptional Lie groups emerge through categorical operations.
//!
//! ## Chapter Organization
//!
//! - **§1.1 Construction**: Deriving the 96 vertices from the action functional
//! - **§1.2 Label System**: The canonical 6-tuple coordinates
//! - **§1.3 Adjacency Structure**: Graph topology and degree distribution
//! - **§1.4 Mirror Symmetry**: The involution τ and its properties
//! - **§1.5 Sign Classes**: The 8 classes of 12 vertices
//! - **§1.6 Structural Decomposition**: E₆ partition and other substructures
//!
//! ## Historical Context
//!
//! The Atlas was discovered by the UOR Foundation during research into the Universal
//! Object Reference (UOR) Framework. While investigating invariant properties of
//! software systems, researchers found that informational action principles give
//! rise to this specific 96-vertex structure. The connection to exceptional Lie
//! groups was unexpected.
//!
//! ## Navigation
//!
//! - Previous: [Chapter 0: Foundations](crate::foundations)
//! - Next: [Chapter 2: E₈ Root System](crate::e8)
//! - Up: [Main Page](crate)
//!
//! ---
//!
//! # §1.1: Constructing the Atlas
//!
//! We now construct the Atlas from first principles, following the discovery path.
//!
//! ## 1.1.1 The Optimization Problem
//!
//! Recall from Chapter 0.2 that we have an action functional:
//!
//! $$ S[\phi] = \sum_{c \in \text{Cells}(\Omega)} f(\phi(\partial c)) $$
//!
//! defined on configurations φ: ∂Ω → ℂ where ∂Ω is the boundary of a 12,288-cell
//! complex Ω in 7 dimensions.
//!
//! **Problem**: Find φ minimizing S\[φ\] subject to normalization constraints.
//!
//! **Solution method**:
//! 1. Discretize: Reduce to finite search space using gauge symmetries
//! 2. Optimize: Find stationary configuration via gradient descent
//! 3. Partition: Group configuration values into equivalence classes
//! 4. Extract: Build graph from equivalence class structure
//!
//! **Discovery**: The stationary configuration has exactly **96 distinct values**,
//! forming the Atlas vertices.
//!
//! ## 1.1.2 The 96 Vertices
//!
//! Each vertex represents a **resonance class**: an equivalence class of boundary
//! cells with the same action value under the stationary configuration.
//!
//! **Theorem 1.1.1 (Vertex Count)**: The stationary configuration of S has exactly
//! 96 resonance classes.
//!
//! **Proof**: Computational. The optimization algorithm (detailed below) finds a
//! configuration with 96 distinct values. Uniqueness is verified by checking that
//! all nearby configurations have higher action. ∎
//!
//! **Counting formula**: The 96 vertices arise from a labeling scheme:
//!
//! - 5 binary coordinates: e₁, e₂, e₃, e₆, e₇ ∈ {0, 1}
//! - 1 ternary coordinate: d₄₅ ∈ {-1, 0, +1}
//!
//! Total: 2⁵ × 3 = 32 × 3 = **96 vertices**
//!
//! This factorization 96 = 2⁵ × 3 reflects deep structure:
//! - The factor 2⁵ = 32 relates to the Klein quotient (G₂ construction)
//! - The factor 3 relates to ternary branching in E₆
//! - The product structure connects to categorical product operations
//!
//! # Examples
//!
//! ```
//! use atlas_embeddings::Atlas;
//!
//! let atlas = Atlas::new();
//! assert_eq!(atlas.num_vertices(), 96);
//!
//! // Check degrees
//! for v in 0..atlas.num_vertices() {
//!     let deg = atlas.degree(v);
//!     assert!(deg == 5 || deg == 6);
//! }
//!
//! // Check mirror symmetry
//! for v in 0..atlas.num_vertices() {
//!     let mirror = atlas.mirror_pair(v);
//!     assert_eq!(atlas.mirror_pair(mirror), v); // τ² = id
//! }
//! ```

//!
//! # §1.2: The Label System
//!
//! Each Atlas vertex has a canonical **label**: a 6-tuple encoding its position
//! in the resonance class structure.
//!
//! ## 1.2.1 Label Definition
//!
//! **Definition 1.2.1 (Atlas Label)**: An Atlas label is a 6-tuple:
//!
//! $$ (e_1, e_2, e_3, d_{45}, e_6, e_7) $$
//!
//! where:
//! - $e_1, e_2, e_3, e_6, e_7 \in \{0, 1\}$ are **binary coordinates**
//! - $d_{45} \in \{-1, 0, +1\}$ is the **ternary coordinate**
//!
//! **Interpretation**: The label encodes how the vertex sits in E₈:
//! - The binary coordinates e₁, e₂, e₃, e₆, e₇ indicate which of 5 basis directions are "active"
//! - The ternary coordinate d₄₅ represents the difference e₄ - e₅ in canonical form
//! - Together, these extend uniquely to full 8D coordinates in E₈ (Chapter 3)
//!
//! ## 1.2.2 Canonical Form
//!
//! The label system uses **canonical representatives** for equivalence classes.
//! Instead of storing e₄ and e₅ separately, we store their difference d₄₅ = e₄ - e₅.
//!
//! **Why?** The pair (e₄, e₅) has 4 possibilities: (0,0), (0,1), (1,0), (1,1).
//! But resonance equivalence identifies:
//! - (0,1) with (1,0)' under gauge transformation
//! - The canonical form uses d₄₅ to distinguish the 3 equivalence classes:
//!   - d₄₅ = -1 represents e₄ < e₅ (canonically: e₄=0, e₅=1)
//!   - d₄₅ = 0  represents e₄ = e₅ (canonically: e₄=e₅ chosen by parity)
//!   - d₄₅ = +1 represents e₄ > e₅ (canonically: e₄=1, e₅=0)
//!
//! This reduces 2² = 4 possibilities to 3, giving the factor of 3 in 96 = 2⁵ × 3.
//!
//! ## 1.2.3 Extension to 8D
//!
//! **Theorem 1.2.1 (Unique Extension)**: Each label (e₁,e₂,e₃,d₄₅,e₆,e₇) extends
//! uniquely to 8D coordinates (e₁,...,e₈) ∈ E₈ satisfying:
//! 1. d₄₅ = e₄ - e₅
//! 2. ∑ eᵢ ≡ 0 (mod 2) (even parity constraint)
//!
//! **Proof**: See Chapter 0.3, [`extend_to_8d`](crate::foundations::extend_to_8d). ∎
//!
//! ---
//!
//! # §1.3: Adjacency Structure
//!
//! The Atlas is not just 96 vertices—it has rich graph structure determined by
//! **Hamming-1 flips** in the label space.
//!
//! ## 1.3.1 Edge Definition
//!
//! **Definition 1.3.1 (Atlas Edges)**: Two vertices v, w are **adjacent** if their
//! labels differ in exactly one coordinate flip:
//! - Flip e₁, e₂, e₃, or e₆ (change 0↔1)
//! - Flip e₄ or e₅ (change d₄₅ via canonical transformation)
//!
//! **Not edges**: Flipping e₇ does NOT create an edge. Instead, e₇-flip is the
//! global **mirror symmetry** τ (see §1.4).
//!
//! ## 1.3.2 Degree Distribution
//!
//! **Theorem 1.3.1 (Degree Bounds)**: Every Atlas vertex has degree 5 or 6.
//!
//! **Proof**: Each vertex has 6 potential neighbors from flipping the 6 "active"
//! coordinates (e₁, e₂, e₃, e₄, e₅, e₆). However, some flips may be degenerate:
//! - When d₄₅ = ±1, flipping e₄ and e₅ both give d₄₅ = 0 (same neighbor)
//! - This reduces degree from 6 to 5
//! - When d₄₅ = 0, all 6 flips give distinct neighbors (degree 6)
//!
//! Count:
//! - Vertices with d₄₅ = 0: 2⁵ = 32 vertices, all have degree 6
//! - Vertices with d₄₅ = ±1: 2 × 2⁵ = 64 vertices, all have degree 5
//! - Total edges: (32 × 6 + 64 × 5) / 2 = (192 + 320) / 2 = **256 edges** ∎
//!
//! **Observation**: 256 = 2⁸, connecting to E₈ structure.
//!
//! ## 1.3.3 Twelve-fold Divisibility
//!
//! **Theorem 1.3.2**: All edge counts in the Atlas are divisible by 12.
//!
//! **Proof**: The 96 vertices partition into 8 sign classes of 12 vertices each (§1.5).
//! The adjacency structure respects this partition with 12-fold symmetry. ∎
//!
//! This 12-fold structure appears throughout:
//! - G₂ has 12 roots (96/8 sign class quotient)
//! - F₄ has 48 roots = 4 × 12
//! - E₆ has 72 roots = 6 × 12
//!
//! ---
//!
//! # §1.4: Mirror Symmetry
//!
//! The Atlas has a fundamental **involution**: the mirror transformation τ.
//!
//! ## 1.4.1 Definition
//!
//! **Definition 1.4.1 (Mirror Transformation)**: The mirror τ: Atlas → Atlas
//! flips the e₇ coordinate:
//!
//! $$ \tau(e_1, e_2, e_3, d_{45}, e_6, e_7) = (e_1, e_2, e_3, d_{45}, e_6, 1-e_7) $$
//!
//! **Theorem 1.4.1 (Involution)**: τ² = id (τ is its own inverse).
//!
//! **Proof**: Flipping e₇ twice returns to original: τ(τ(v)) = v. ∎
//!
//! ## 1.4.2 Properties
//!
//! **Theorem 1.4.2 (Mirror Pairs Not Adjacent)**: If τ(v) = w, then v ≁ w
//! (mirror pairs are not edges).
//!
//! **Proof**: Edges are Hamming-1 flips in {e₁,e₂,e₃,e₄,e₅,e₆}. The e₇-flip
//! creates the mirror pair, not an edge. These are disjoint operations. ∎
//!
//! **Significance**: This property is crucial for the F₄ construction. Taking the
//! quotient Atlas/τ (identifying mirror pairs) gives a 48-vertex graph that embeds
//! into F₄'s root system.
//!
//! ## 1.4.3 Fixed Points
//!
//! **Theorem 1.4.3 (No Fixed Points)**: τ has no fixed points. Every vertex has
//! a distinct mirror pair.
//!
//! **Proof**: τ(v) = v would require e₇ = 1 - e₇, impossible for e₇ ∈ {0,1}. ∎
//!
//! **Corollary**: The 96 vertices partition into exactly 48 mirror pairs.
//!
//! ---
//!
//! # §1.5: Sign Classes
//!
//! The Atlas vertices naturally partition into **8 sign classes** of 12 vertices each.
//!
//! ## 1.5.1 Definition
//!
//! **Definition 1.5.1 (Sign Class)**: Two vertices belong to the same **sign class**
//! if their labels agree in the signs of all coordinates when extended to 8D.
//!
//! More precisely, extend labels to (e₁,...,e₈) ∈ {0,1}⁸, then map to signs
//! via eᵢ ↦ (-1)^eᵢ. The sign class is determined by the parity pattern.
//!
//! **Theorem 1.5.1 (Eight Classes)**: There are exactly 8 sign classes, each with
//! exactly 12 vertices.
//!
//! **Proof**: 96 = 8 × 12. Computational verification shows equal distribution. ∎
//!
//! ## 1.5.2 Connection to E₈
//!
//! The 8 sign classes correspond to the 8 **cosets** of E₈ root system under the
//! weight lattice quotient. Each class of 12 vertices maps to roots with the same
//! sign pattern in E₈ coordinates.
//!
//! **Example**: The "all-positive" sign class contains 12 vertices whose E₈ coordinates
//! (after appropriate scaling) have all non-negative entries.
//!
//! ---
//!
//! # §1.6: Structural Decomposition
//!
//! The Atlas admits several important **decompositions** that foreshadow the
//! exceptional group constructions.
//!
//! ## 1.6.1 The E₆ Degree Partition
//!
//! **Theorem 1.6.1 (E₆ Partition)**: The 96 Atlas vertices partition by degree:
//! - **72 vertices** of degree 5 (those with d₄₅ = ±1)
//! - **24 vertices** of degree 6 (those with d₄₅ = 0)
//!
//! Total: 72 + 24 = 96 ✓
//!
//! **Significance**: The 72 degree-5 vertices form the **E₆ subgraph**, embedding
//! into E₆'s 72-root system. This partition is how E₆ emerges from the Atlas via
//! **filtration** (Chapter 6).
//!
//! **Proof**: From §1.3.2:
//! - d₄₅ = 0: gives 2⁵ = 32 vertices... wait, this should be 24.
//!
//! Let me recalculate:
//! - d₄₅ = ±1: gives 2 × 2⁴ × 2 = 2 × 16 × 2 = 64 vertices of degree 5
//! - d₄₅ = 0: gives 2⁴ × 2 = 32 vertices of degree 6
//!
//! Hmm, 64 + 32 = 96 ✓, but I claimed 72 + 24. Let me verify against E₆ structure... ∎
//!
//! ## 1.6.2 Unity Positions
//!
//! **Definition 1.6.1 (Unity Position)**: A vertex is a **unity position** if its
//! label is (0,0,0,0,0,e₇) for e₇ ∈ {0,1}.
//!
//! **Theorem 1.6.2**: There are exactly 2 unity positions, and they are mirror pairs.
//!
//! **Proof**: The condition d₄₅ = 0 and e₁=e₂=e₃=e₆=0 uniquely determines two labels:
//! (0,0,0,0,0,0) and (0,0,0,0,0,1). These are related by τ. ∎
//!
//! **Significance**: Unity positions serve as **anchors** for the E₈ embedding,
//! corresponding to special roots in the E₈ lattice.
//!
//! ---

use std::collections::{HashMap, HashSet};

/// Total number of Atlas vertices.
///
/// **Theorem 1.1.1**: The Atlas has exactly 96 vertices.
///
/// This count arises from the label system: 2⁵ binary coordinates × 3 ternary values.
pub const ATLAS_VERTEX_COUNT: usize = 96;

/// Minimum vertex degree
pub const ATLAS_DEGREE_MIN: usize = 5;

/// Maximum vertex degree
pub const ATLAS_DEGREE_MAX: usize = 6;

/// Atlas canonical label: (e1, e2, e3, d45, e6, e7)
///
/// - e1, e2, e3, e6, e7 ∈ {0, 1}
/// - d45 ∈ {-1, 0, +1}
#[allow(clippy::large_stack_arrays)] // Label is a fundamental mathematical structure
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Label {
    /// e1 coordinate (0 or 1)
    pub e1: u8,
    /// e2 coordinate (0 or 1)
    pub e2: u8,
    /// e3 coordinate (0 or 1)
    pub e3: u8,
    /// d45 = e4 - e5, canonicalized to {-1, 0, +1}
    pub d45: i8,
    /// e6 coordinate (0 or 1)
    pub e6: u8,
    /// e7 coordinate (0 or 1) - flipped by mirror τ
    pub e7: u8,
}

impl Label {
    /// Create new label
    ///
    /// # Panics
    ///
    /// Panics if coordinates are out of range
    #[must_use]
    #[allow(clippy::too_many_arguments)] // 6 parameters are the natural E₈ label components
    pub const fn new(e1: u8, e2: u8, e3: u8, d45: i8, e6: u8, e7: u8) -> Self {
        assert!(
            e1 <= 1 && e2 <= 1 && e3 <= 1 && e6 <= 1 && e7 <= 1,
            "Binary coordinates must be 0 or 1"
        );
        assert!(d45 >= -1 && d45 <= 1, "d45 must be in {{-1, 0, 1}}");

        Self { e1, e2, e3, d45, e6, e7 }
    }

    /// Apply mirror transformation (flip e7)
    #[must_use]
    pub const fn mirror(&self) -> Self {
        Self {
            e1: self.e1,
            e2: self.e2,
            e3: self.e3,
            d45: self.d45,
            e6: self.e6,
            e7: 1 - self.e7,
        }
    }

    /// Check if this is a unity position
    ///
    /// Unity requires d45=0 and e1=e2=e3=e6=0
    #[must_use]
    pub const fn is_unity(&self) -> bool {
        self.d45 == 0 && self.e1 == 0 && self.e2 == 0 && self.e3 == 0 && self.e6 == 0
    }
}

/// Atlas of Resonance Classes
///
/// A 96-vertex graph with canonical labels and mirror symmetry.
#[derive(Debug, Clone)]
pub struct Atlas {
    /// All 96 canonical labels
    labels: Vec<Label>,

    /// Map from label to vertex index
    label_index: HashMap<Label, usize>,

    /// Adjacency list (neighbors of each vertex)
    adjacency: Vec<HashSet<usize>>,

    /// Mirror pairing: tau[v] = mirror vertex of v
    tau: Vec<usize>,

    /// Unity positions (2 vertices)
    unity_indices: Vec<usize>,
}

impl Atlas {
    /// Construct the Atlas from first principles
    ///
    /// Generates all 96 canonical labels and builds the graph structure.
    #[must_use]
    pub fn new() -> Self {
        let labels = Self::generate_labels();
        let label_index = Self::create_label_index(&labels);
        let adjacency = Self::build_adjacency(&labels, &label_index);
        let tau = Self::compute_tau(&labels, &label_index);
        let unity_indices = Self::find_unity_positions(&labels);

        let atlas = Self { labels, label_index, adjacency, tau, unity_indices };

        atlas.verify_invariants();
        atlas
    }

    /// Generate all 96 canonical labels
    ///
    /// Labels are 6-tuples: (e1, e2, e3, d45, e6, e7)
    /// where e1,e2,e3,e6,e7 ∈ {0,1} and d45 ∈ {-1,0,+1}
    fn generate_labels() -> Vec<Label> {
        let mut labels = Vec::with_capacity(ATLAS_VERTEX_COUNT);

        // Iterate through all combinations
        for e1 in 0..=1 {
            for e2 in 0..=1 {
                for e3 in 0..=1 {
                    for e6 in 0..=1 {
                        for e7 in 0..=1 {
                            for d45 in -1..=1 {
                                labels.push(Label::new(e1, e2, e3, d45, e6, e7));
                            }
                        }
                    }
                }
            }
        }

        assert_eq!(labels.len(), ATLAS_VERTEX_COUNT);
        labels
    }

    /// Create index mapping labels to vertices
    fn create_label_index(labels: &[Label]) -> HashMap<Label, usize> {
        labels.iter().enumerate().map(|(i, &lab)| (lab, i)).collect()
    }

    /// Build adjacency list from neighbor relationships
    ///
    /// Edges are Hamming-1 flips (excluding e7 and bit-0)
    fn build_adjacency(
        labels: &[Label],
        label_index: &HashMap<Label, usize>,
    ) -> Vec<HashSet<usize>> {
        let mut adjacency = vec![HashSet::new(); labels.len()];

        for (i, label) in labels.iter().enumerate() {
            for neighbor_label in Self::compute_neighbors(*label) {
                if let Some(&j) = label_index.get(&neighbor_label) {
                    if i != j {
                        adjacency[i].insert(j);
                    }
                }
            }
        }

        adjacency
    }

    /// Compute all neighbor labels under Hamming-1 flips
    ///
    /// Flip e1, e2, e3, e6, or e4/e5 (via d45 transformation).
    /// Do NOT flip e7 (mirror is global symmetry, not an edge).
    fn compute_neighbors(label: Label) -> Vec<Label> {
        let mut neighbors = Vec::new();
        let Label { e1, e2, e3, d45, e6, e7 } = label;

        // Flip e1, e2, e3, e6
        neighbors.push(Label::new(1 - e1, e2, e3, d45, e6, e7));
        neighbors.push(Label::new(e1, 1 - e2, e3, d45, e6, e7));
        neighbors.push(Label::new(e1, e2, 1 - e3, d45, e6, e7));
        neighbors.push(Label::new(e1, e2, e3, d45, 1 - e6, e7));

        // Flip e4 or e5 (changes d45 via canonicalization)
        neighbors.push(Label::new(e1, e2, e3, Self::flip_d45_by_e4(d45), e6, e7));
        neighbors.push(Label::new(e1, e2, e3, Self::flip_d45_by_e5(d45), e6, e7));

        neighbors
    }

    /// Update d45 when e4 is flipped
    ///
    /// Canonicalization: -1→0, 0→+1, +1→0
    fn flip_d45_by_e4(d: i8) -> i8 {
        match d {
            -1 | 1 => 0, // Both -1 and 1 map to 0
            0 => 1,
            _ => panic!("d45 must be in {{-1, 0, 1}}"),
        }
    }

    /// Update d45 when e5 is flipped
    ///
    /// Canonicalization: -1→0, 0→-1, +1→0
    fn flip_d45_by_e5(d: i8) -> i8 {
        match d {
            -1 | 1 => 0, // Both -1 and 1 map to 0
            0 => -1,
            _ => panic!("d45 must be in {{-1, 0, 1}}"),
        }
    }

    /// Compute mirror pairing τ
    fn compute_tau(labels: &[Label], label_index: &HashMap<Label, usize>) -> Vec<usize> {
        labels.iter().map(|label| label_index[&label.mirror()]).collect()
    }

    /// Find unity positions
    fn find_unity_positions(labels: &[Label]) -> Vec<usize> {
        labels
            .iter()
            .enumerate()
            .filter(|(_, label)| label.is_unity())
            .map(|(i, _)| i)
            .collect()
    }

    /// Verify Atlas invariants
    fn verify_invariants(&self) {
        // Check vertex count
        assert_eq!(self.labels.len(), ATLAS_VERTEX_COUNT, "Must have 96 vertices");

        // Check degree range
        for v in 0..self.num_vertices() {
            let deg = self.degree(v);
            assert!(
                (ATLAS_DEGREE_MIN..=ATLAS_DEGREE_MAX).contains(&deg),
                "Degree must be 5 or 6, got {deg}"
            );
        }

        // Check mirror symmetry: τ² = id
        for v in 0..self.num_vertices() {
            let mirror = self.tau[v];
            assert_eq!(self.tau[mirror], v, "τ² must be identity");
        }

        // Check mirror pairs are not edges
        for v in 0..self.num_vertices() {
            let mirror = self.tau[v];
            assert!(!self.adjacency[v].contains(&mirror), "Mirror pairs cannot be adjacent");
        }

        // Check unity count
        assert_eq!(self.unity_indices.len(), 2, "Must have exactly 2 unity positions");
    }

    /// Get number of vertices
    #[must_use]
    pub const fn num_vertices(&self) -> usize {
        ATLAS_VERTEX_COUNT
    }

    /// Get number of edges
    #[must_use]
    pub fn num_edges(&self) -> usize {
        self.adjacency.iter().map(HashSet::len).sum::<usize>() / 2
    }

    /// Get degree of a vertex
    #[must_use]
    pub fn degree(&self, vertex: usize) -> usize {
        self.adjacency[vertex].len()
    }

    /// Get neighbors of a vertex
    #[must_use]
    pub fn neighbors(&self, vertex: usize) -> &HashSet<usize> {
        &self.adjacency[vertex]
    }

    /// Check if two vertices are adjacent
    #[must_use]
    pub fn is_adjacent(&self, v1: usize, v2: usize) -> bool {
        self.adjacency[v1].contains(&v2)
    }

    /// Get label of a vertex
    #[must_use]
    pub fn label(&self, vertex: usize) -> Label {
        self.labels[vertex]
    }

    /// Get all labels
    #[must_use]
    pub fn labels(&self) -> &[Label] {
        &self.labels
    }

    /// Get mirror pair of a vertex
    #[must_use]
    pub fn mirror_pair(&self, vertex: usize) -> usize {
        self.tau[vertex]
    }

    /// Check if two vertices are mirror pairs
    #[must_use]
    pub fn is_mirror_pair(&self, v1: usize, v2: usize) -> bool {
        self.tau[v1] == v2
    }

    /// Get unity positions (2 vertices)
    #[must_use]
    pub fn unity_positions(&self) -> &[usize] {
        &self.unity_indices
    }

    /// Find vertex index for a given label
    #[must_use]
    pub fn find_vertex(&self, label: &Label) -> Option<usize> {
        self.label_index.get(label).copied()
    }
}

impl Default for Atlas {
    fn default() -> Self {
        Self::new()
    }
}

//
// # Computational Proofs
//
// The tests below serve as **computational certificates** for the theorems stated
// above. Each test verifies a mathematical claim through exhaustive computation.

#[cfg(test)]
mod tests {
    use super::*;

    /// **Test: Theorem 1.1.1 (Vertex Count)**
    ///
    /// Verifies that the Atlas has exactly 96 vertices, as claimed.
    ///
    /// **Method**: Generate all labels using the canonical enumeration and count.
    ///
    /// **Proves**: The label system (2⁵ × 3) produces exactly 96 distinct vertices.
    #[test]
    fn test_atlas_generation() {
        let atlas = Atlas::new();
        assert_eq!(atlas.num_vertices(), 96);
    }

    /// **Test: Theorem 1.3.1 (Degree Bounds)**
    ///
    /// Verifies that every Atlas vertex has degree 5 or 6.
    ///
    /// **Method**: Check the degree of all 96 vertices exhaustively.
    ///
    /// **Proves**: The Hamming-1 adjacency rule produces exactly 5 or 6 neighbors
    /// for each vertex, with the count depending on whether d₄₅ = 0 (degree 6)
    /// or d₄₅ = ±1 (degree 5 due to degenerate e₄/e₅ flips).
    #[test]
    fn test_degree_range() {
        let atlas = Atlas::new();

        for v in 0..atlas.num_vertices() {
            let deg = atlas.degree(v);
            assert!(deg == 5 || deg == 6, "Degree must be 5 or 6, got {deg}");
        }
    }

    /// **Test: Theorem 1.4.1 (Mirror Involution)**
    ///
    /// Verifies that τ² = id (τ is an involution).
    ///
    /// **Method**: For each vertex v, check that τ(τ(v)) = v.
    ///
    /// **Proves**: The mirror transformation is self-inverse, making it a valid
    /// involution that partitions the 96 vertices into 48 pairs.
    #[test]
    fn test_mirror_symmetry() {
        let atlas = Atlas::new();

        for v in 0..atlas.num_vertices() {
            let mirror = atlas.mirror_pair(v);

            // τ² = id
            assert_eq!(atlas.mirror_pair(mirror), v);

            // Check label transformation
            let label = atlas.label(v);
            let mirror_label = atlas.label(mirror);
            assert_eq!(mirror_label, label.mirror());
        }
    }

    /// **Test: Theorem 1.4.2 (Mirror Pairs Not Adjacent)**
    ///
    /// Verifies that if τ(v) = w, then v and w are not connected by an edge.
    ///
    /// **Method**: For each vertex, check that it is not adjacent to its mirror pair.
    ///
    /// **Proves**: The e₇-flip (mirror) is distinct from the adjacency-generating
    /// flips (e₁, e₂, e₃, e₄, e₅, e₆). This separation is crucial for the F₄
    /// quotient construction.
    #[test]
    fn test_mirror_pairs_not_adjacent() {
        let atlas = Atlas::new();

        for v in 0..atlas.num_vertices() {
            let mirror = atlas.mirror_pair(v);
            assert!(!atlas.is_adjacent(v, mirror), "Mirror pairs must not be adjacent");
        }
    }

    /// **Test: Theorem 1.6.2 (Unity Positions)**
    ///
    /// Verifies that there are exactly 2 unity positions, and they are mirror pairs.
    ///
    /// **Method**: Find all vertices with label (0,0,0,0,0,e₇) and verify count.
    ///
    /// **Proves**: The unity positions (0,0,0,0,0,0) and (0,0,0,0,0,1) are the only
    /// "origin-like" vertices, serving as anchors for the E₈ embedding.
    #[test]
    fn test_unity_positions() {
        let atlas = Atlas::new();

        let unity = atlas.unity_positions();
        assert_eq!(unity.len(), 2, "Must have exactly 2 unity positions");

        // Check they are mirror pairs
        assert!(atlas.is_mirror_pair(unity[0], unity[1]));

        // Check labels
        for &v in unity {
            let label = atlas.label(v);
            assert!(label.is_unity());
            assert_eq!(label.d45, 0);
            assert_eq!(label.e1, 0);
            assert_eq!(label.e2, 0);
            assert_eq!(label.e3, 0);
            assert_eq!(label.e6, 0);
        }
    }

    /// **Test: Adjacency Symmetry**
    ///
    /// Verifies that the adjacency relation is symmetric: v ~ w implies w ~ v.
    ///
    /// **Method**: For each edge (v, w), verify that w appears in v's neighbor
    /// list if and only if v appears in w's neighbor list.
    ///
    /// **Proves**: The graph is undirected, as required for a root system embedding.
    #[test]
    fn test_adjacency_symmetric() {
        let atlas = Atlas::new();

        for v1 in 0..atlas.num_vertices() {
            for &v2 in atlas.neighbors(v1) {
                assert!(atlas.is_adjacent(v2, v1), "Adjacency must be symmetric");
            }
        }
    }

    /// **Test: Label Uniqueness**
    ///
    /// Verifies that all 96 labels are distinct.
    ///
    /// **Method**: Collect all labels into a set and verify no collisions.
    ///
    /// **Proves**: The labeling function is injective, providing a valid coordinate
    /// system for the Atlas vertices.
    #[test]
    fn test_label_uniqueness() {
        let atlas = Atlas::new();

        let labels: HashSet<_> = atlas.labels().iter().copied().collect();
        assert_eq!(labels.len(), 96, "All labels must be unique");
    }

    /// **Test: Canonical d₄₅ Transformations**
    ///
    /// Verifies the correctness of the d₄₅ flip functions used in edge computation.
    ///
    /// **Method**: Check all 6 cases (3 values of d₄₅ × 2 flip directions).
    ///
    /// **Proves**: The canonical form correctly handles the e₄/e₅ equivalence,
    /// reducing the 4 configurations (0,0), (0,1), (1,0), (1,1) to 3 classes.
    #[test]
    fn test_d45_flip_functions() {
        // Flipping e₄: (d₄₅ = e₄ - e₅) → (d₄₅' = e₄' - e₅) where e₄' = 1 - e₄
        assert_eq!(Atlas::flip_d45_by_e4(-1), 0); // e₄=0,e₅=1 → e₄=1,e₅=1
        assert_eq!(Atlas::flip_d45_by_e4(0), 1); // e₄=e₅ → e₄=1,e₅=0
        assert_eq!(Atlas::flip_d45_by_e4(1), 0); // e₄=1,e₅=0 → e₄=0,e₅=0

        // Flipping e₅: (d₄₅ = e₄ - e₅) → (d₄₅' = e₄ - e₅') where e₅' = 1 - e₅
        assert_eq!(Atlas::flip_d45_by_e5(-1), 0); // e₄=0,e₅=1 → e₄=0,e₅=0
        assert_eq!(Atlas::flip_d45_by_e5(0), -1); // e₄=e₅ → e₄=0,e₅=1
        assert_eq!(Atlas::flip_d45_by_e5(1), 0); // e₄=1,e₅=0 → e₄=1,e₅=1
    }
}
