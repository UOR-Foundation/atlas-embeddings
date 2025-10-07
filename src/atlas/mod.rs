//! Atlas of Resonance Classes
//!
//! The Atlas is a 96-vertex graph that emerges as the stationary configuration
//! of an action functional on a 12,288-cell boundary complex.
//!
//! # Structure
//!
//! The Atlas graph consists of:
//! - **96 vertices** with canonical labels
//! - **Degree 5-6** for each vertex
//! - **Mirror symmetry τ** (involution flipping e7 coordinate)
//! - **Unity positions** (2 special vertices)
//!
//! # Label System
//!
//! Each vertex has a 6-tuple label: `(e1, e2, e3, d45, e6, e7)` where:
//! - `e1, e2, e3, e6, e7` are binary (0 or 1)
//! - `d45` is ternary (-1, 0, or +1) representing the canonical e4-e5 difference
//!
//! Total: 2⁵ × 3 = 32 × 3 = 96 vertices
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

use std::collections::{HashMap, HashSet};

/// Total number of Atlas vertices
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
            -1 | 1 => 0,  // Both -1 and 1 map to 0
            0 => 1,
            _ => panic!("d45 must be in {{-1, 0, 1}}"),
        }
    }

    /// Update d45 when e5 is flipped
    ///
    /// Canonicalization: -1→0, 0→-1, +1→0
    fn flip_d45_by_e5(d: i8) -> i8 {
        match d {
            -1 | 1 => 0,  // Both -1 and 1 map to 0
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atlas_generation() {
        let atlas = Atlas::new();
        assert_eq!(atlas.num_vertices(), 96);
    }

    #[test]
    fn test_degree_range() {
        let atlas = Atlas::new();

        for v in 0..atlas.num_vertices() {
            let deg = atlas.degree(v);
            assert!(deg == 5 || deg == 6, "Degree must be 5 or 6, got {deg}");
        }
    }

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

    #[test]
    fn test_mirror_pairs_not_adjacent() {
        let atlas = Atlas::new();

        for v in 0..atlas.num_vertices() {
            let mirror = atlas.mirror_pair(v);
            assert!(!atlas.is_adjacent(v, mirror), "Mirror pairs must not be adjacent");
        }
    }

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

    #[test]
    fn test_adjacency_symmetric() {
        let atlas = Atlas::new();

        for v1 in 0..atlas.num_vertices() {
            for &v2 in atlas.neighbors(v1) {
                assert!(atlas.is_adjacent(v2, v1), "Adjacency must be symmetric");
            }
        }
    }

    #[test]
    fn test_label_uniqueness() {
        let atlas = Atlas::new();

        let labels: HashSet<_> = atlas.labels().iter().copied().collect();
        assert_eq!(labels.len(), 96, "All labels must be unique");
    }

    #[test]
    fn test_d45_flip_functions() {
        assert_eq!(Atlas::flip_d45_by_e4(-1), 0);
        assert_eq!(Atlas::flip_d45_by_e4(0), 1);
        assert_eq!(Atlas::flip_d45_by_e4(1), 0);

        assert_eq!(Atlas::flip_d45_by_e5(-1), 0);
        assert_eq!(Atlas::flip_d45_by_e5(0), -1);
        assert_eq!(Atlas::flip_d45_by_e5(1), 0);
    }
}
