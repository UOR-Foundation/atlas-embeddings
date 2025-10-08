//! # Chapter 0.1: Primitive Concepts
//!
//! We begin by defining the most basic mathematical objects needed for our construction.
//! No prior knowledge is assumed beyond elementary set theory and basic programming concepts.
//!
//! This chapter establishes:
//! - What is a graph?
//! - What is exact arithmetic?
//! - What is a group?
//! - What are vectors and inner products?
//!
//! Each concept is accompanied by minimal Rust implementations that serve as
//! executable definitions.

// # 0.1.1 Graphs

//! ## 0.1.1 Graphs
//!
//! A **graph** is one of the most fundamental structures in mathematics and computer science.
//!
//! ### Definition 0.1.1 (Graph)
//!
//! A graph G = (V, E) consists of:
//! - A finite set **V** of **vertices** (also called nodes)
//! - A set **E ⊆ V × V** of **edges** (pairs of vertices)
//!
//! We write `v ~ w` when (v,w) ∈ E, read "v is adjacent to w".
//!
//! ### Properties
//!
//! - **Undirected**: If v ~ w, then w ~ v (edges have no direction)
//! - **Simple**: No self-loops (v ≁ v) and no multiple edges
//! - **Finite**: Both V and E are finite sets
//!
//! ### Example 0.1.1: Triangle Graph
//!
//! The triangle graph has 3 vertices {A, B, C} with edges forming a cycle:
//!
//! ```text
//!     A
//!    / \
//!   B---C
//! ```
//!
//! In set notation: V = {A, B, C}, E = {(A,B), (B,C), (C,A)}.
//!
//! ### Computational Representation
//!
//! We represent graphs using **adjacency lists**: for each vertex, store its neighbors.

use std::collections::HashSet;

/// A simple undirected graph with vertices labeled by generic type V.
///
/// **Implementation note**: This is a minimal educational implementation.
/// The Atlas uses a more specialized representation in [`crate::atlas`].
///
/// # Examples
///
/// ```
/// use atlas_embeddings::foundations::primitives::SimpleGraph;
///
/// // Create triangle graph
/// let mut g = SimpleGraph::new();
/// g.add_edge(0, 1);
/// g.add_edge(1, 2);
/// g.add_edge(2, 0);
///
/// assert_eq!(g.vertex_count(), 3);
/// assert_eq!(g.edge_count(), 3);
/// assert!(g.is_adjacent(0, 1));
/// assert!(g.is_adjacent(1, 0)); // Undirected
/// ```
#[derive(Debug, Clone)]
pub struct SimpleGraph {
    /// Adjacency lists: for each vertex, store its neighbors
    adjacency: Vec<HashSet<usize>>,
}

impl SimpleGraph {
    /// Create an empty graph with no vertices.
    #[must_use]
    pub const fn new() -> Self {
        Self { adjacency: Vec::new() }
    }

    /// Add a vertex to the graph, returning its index.
    ///
    /// Vertices are numbered sequentially: 0, 1, 2, ...
    pub fn add_vertex(&mut self) -> usize {
        let idx = self.adjacency.len();
        self.adjacency.push(HashSet::new());
        idx
    }

    /// Add an undirected edge between vertices u and v.
    ///
    /// Automatically adds vertices if they don't exist yet.
    pub fn add_edge(&mut self, u: usize, v: usize) {
        // Ensure both vertices exist
        while self.adjacency.len() <= u.max(v) {
            self.add_vertex();
        }

        // Add edge in both directions (undirected)
        self.adjacency[u].insert(v);
        self.adjacency[v].insert(u);
    }

    /// Check if vertices u and v are adjacent.
    #[must_use]
    pub fn is_adjacent(&self, u: usize, v: usize) -> bool {
        if u >= self.adjacency.len() || v >= self.adjacency.len() {
            return false;
        }
        self.adjacency[u].contains(&v)
    }

    /// Get the degree of vertex v (number of neighbors).
    ///
    /// **Definition**: The **degree** of a vertex is the number of edges incident to it.
    #[must_use]
    pub fn degree(&self, v: usize) -> usize {
        if v >= self.adjacency.len() {
            return 0;
        }
        self.adjacency[v].len()
    }

    /// Get the number of vertices in the graph.
    #[must_use]
    pub fn vertex_count(&self) -> usize {
        self.adjacency.len()
    }

    /// Get the number of edges in the graph.
    ///
    /// Since the graph is undirected, we count each edge once.
    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.adjacency.iter().map(HashSet::len).sum::<usize>() / 2
    }

    /// Get the neighbors of vertex v.
    #[must_use]
    pub fn neighbors(&self, v: usize) -> Vec<usize> {
        if v >= self.adjacency.len() {
            return Vec::new();
        }
        self.adjacency[v].iter().copied().collect()
    }
}

impl Default for SimpleGraph {
    fn default() -> Self {
        Self::new()
    }
}

// # 0.1.2 Exact Arithmetic

// ## 0.1.2 Exact Arithmetic
//
// In this work, we use **exact arithmetic** exclusively. No floating-point
// calculations are permitted.
//
// ### Principle 0.1.2 (Exactness)
//
// All numerical computations use exact representations:
// - **Integers**: ℤ represented as `i64` (64-bit signed integers)
// - **Rationals**: ℚ represented as `Ratio<i64>` (pairs of integers p/q)
// - **Half-integers**: ½ℤ represented as `HalfInteger` (multiples of 1/2)
//
// **NO floating-point arithmetic** is used anywhere in this crate.
//
// ### Why Exactness?
//
// 1. **Mathematical correctness**: No rounding errors corrupt our results
// 2. **Reproducibility**: Same results on all platforms (no architecture-dependent floats)
// 3. **Verifiability**: Equality is decidable (can test if a = b exactly)
// 4. **Peer review**: Reviewers can verify exact values
//
// ### Example 0.1.2: Rational Arithmetic
//
// ```
// use num_rational::Ratio;
//
// // Exact: 1/3 + 1/6 = 1/2
// let a = Ratio::new(1, 3);
// let b = Ratio::new(1, 6);
// let c = a + b;
// assert_eq!(c, Ratio::new(1, 2));
//
// // Contrast with floating point:
// // 0.333... + 0.166... ≈ 0.5 (approximation)
// ```
//
// ### Mathematical Perspective
//
// Exact arithmetic aligns with mathematical practice: when a mathematician
// writes "√2", they mean the exact value, not a decimal approximation like 1.41421356.
// Similarly, our code manipulates exact values.
//
// ### Computer Science Perspective
//
// Exact arithmetic trades performance for correctness. Floating-point operations
// are faster but introduce errors. For mathematical research where correctness
// is paramount, this tradeoff favors exactness.
//
// ### Type Aliases
//
// For convenience, we re-export commonly used exact types:

pub use crate::arithmetic::{HalfInteger, Rational, Vector8};

// # 0.1.3 Groups

// ## 0.1.3 Groups
//
// A **group** is a fundamental algebraic structure encoding the concept of symmetry.
//
// ### Definition 0.1.3 (Group)
//
// A group (G, ·, e) consists of:
// - A set **G**
// - A binary operation **· : G × G → G** (multiplication)
// - An identity element **e ∈ G**
//
// satisfying:
//
// 1. **Associativity**: (a · b) · c = a · (b · c) for all a,b,c ∈ G
// 2. **Identity**: e · a = a · e = a for all a ∈ G
// 3. **Inverses**: For each a ∈ G, there exists a⁻¹ ∈ G with a · a⁻¹ = e
//
// ### Example 0.1.3 (Integers under Addition)
//
// The integers ℤ form a group under addition:
// - Set: G = ℤ = {..., -2, -1, 0, 1, 2, ...}
// - Operation: · is ordinary addition +
// - Identity: e = 0 (since 0 + a = a)
// - Inverses: a⁻¹ = -a (since a + (-a) = 0)
//
// ### Example 0.1.4 (Klein Four-Group)
//
// The Klein four-group V₄ has 4 elements {e, a, b, c} with multiplication:
//
// ```text
//   ·  | e  a  b  c
//  ----+------------
//   e  | e  a  b  c
//   a  | a  e  c  b
//   b  | b  c  e  a
//   c  | c  b  a  e
// ```
//
// Every element is its own inverse: a² = b² = c² = e.
//
// **Physical interpretation**: The Klein group describes the symmetries of a
// rectangle (rotations by 0°, 180° and reflections through both axes).
//
// This group will appear in our construction of G₂ in Chapter 4.

/// Klein four-group: V₄ = {e, a, b, c} with every element its own inverse.
///
/// Used in the product construction of G₂.
///
/// # Examples
///
/// ```
/// use atlas_embeddings::foundations::primitives::KleinElement;
///
/// let a = KleinElement::A;
/// let b = KleinElement::B;
///
/// // Group operation
/// let c = a.multiply(b);
/// assert_eq!(c, KleinElement::C);
///
/// // Every element is its own inverse
/// assert_eq!(a.multiply(a), KleinElement::Identity);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum KleinElement {
    /// Identity element e
    Identity,
    /// Element a
    A,
    /// Element b
    B,
    /// Element c = a·b
    C,
}

impl KleinElement {
    /// Group multiplication in V₄.
    #[must_use]
    pub const fn multiply(self, other: Self) -> Self {
        use KleinElement::{Identity, A, B, C};
        match (self, other) {
            (Identity, x) | (x, Identity) => x,
            (A, A) | (B, B) | (C, C) => Identity,
            (A, B) | (B, A) => C,
            (A, C) | (C, A) => B,
            (B, C) | (C, B) => A,
        }
    }

    /// Get the inverse element (every element is its own inverse).
    #[must_use]
    pub const fn inverse(self) -> Self {
        self
    }
}

// # 0.1.4 Vectors and Inner Products

// ## 0.1.4 Vectors and Inner Products
//
// Much of our work takes place in 8-dimensional Euclidean space ℝ⁸.
//
// ### Definition 0.1.4 (Vector Space)
//
// A **vector space** over ℝ is a set V with operations:
// - **Addition**: + : V × V → V
// - **Scalar multiplication**: · : ℝ × V → V
//
// satisfying standard axioms (associativity, distributivity, etc.).
//
// **For our purposes**: We work with V = ℝ⁸, vectors are 8-tuples of real numbers.
//
// ### Definition 0.1.5 (Inner Product)
//
// An **inner product** on a vector space V is a function ⟨·,·⟩ : V × V → ℝ
// satisfying:
//
// 1. **Symmetry**: ⟨u, v⟩ = ⟨v, u⟩
// 2. **Linearity**: ⟨au + bv, w⟩ = a⟨u,w⟩ + b⟨v,w⟩
// 3. **Positive-definite**: ⟨v, v⟩ ≥ 0, with equality iff v = 0
//
// ### The Standard Inner Product on ℝ⁸
//
// For vectors u = (u₁, ..., u₈) and v = (v₁, ..., v₈):
//
// $$ \langle u, v \rangle = u_1 v_1 + u_2 v_2 + \cdots + u_8 v_8 $$
//
// ### Definition 0.1.6 (Norm)
//
// The **norm** (or length) of a vector v is:
//
// $$ \|v\| = \sqrt{\langle v, v \rangle} $$
//
// We often work with **norm squared** to avoid square roots:
//
// $$ \|v\|^2 = \langle v, v \rangle = v_1^2 + \cdots + v_8^2 $$
//
// ### Example 0.1.5: Computing Norms
//
// ```
// use atlas_embeddings::arithmetic::Vector8;
// use num_rational::Ratio;
//
// // Integer vector (1,1,0,0,0,0,0,0)
// let v = Vector8::new([
//     Ratio::from_integer(1),
//     Ratio::from_integer(1),
//     Ratio::from_integer(0),
//     Ratio::from_integer(0),
//     Ratio::from_integer(0),
//     Ratio::from_integer(0),
//     Ratio::from_integer(0),
//     Ratio::from_integer(0),
// ]);
//
// // Norm squared: 1² + 1² = 2
// assert_eq!(v.norm_squared(), Ratio::from_integer(2));
// ```
//
// **Significance**: All E₈ roots have norm² = 2, making this the fundamental
// scale in our construction.

// ## 0.1.5 Summary
//
// We have established the primitive concepts needed for our construction:
//
// 1. **Graphs**: Vertices and edges, adjacency
// 2. **Exact arithmetic**: Rationals, no floating point
// 3. **Groups**: Algebraic structures encoding symmetry
// 4. **Vectors**: 8-dimensional space with inner products
//
// These are the building blocks. In the next section, we introduce the
// action functional that generates the Atlas.
//
// ---
//
// **Navigation**:
// - Next: [§0.2 Action Functionals](super::action)
// - Up: [Chapter 0: Foundations](super)

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_graph_triangle() {
        let mut g = SimpleGraph::new();
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(2, 0);

        assert_eq!(g.vertex_count(), 3);
        assert_eq!(g.edge_count(), 3);

        // Check all edges exist (both directions)
        assert!(g.is_adjacent(0, 1));
        assert!(g.is_adjacent(1, 0));
        assert!(g.is_adjacent(1, 2));
        assert!(g.is_adjacent(2, 1));
        assert!(g.is_adjacent(2, 0));
        assert!(g.is_adjacent(0, 2));

        // Check degrees
        assert_eq!(g.degree(0), 2);
        assert_eq!(g.degree(1), 2);
        assert_eq!(g.degree(2), 2);
    }

    #[test]
    fn test_simple_graph_no_self_loops() {
        let mut g = SimpleGraph::new();
        g.add_vertex();

        // Graph should not have self-loops
        assert!(!g.is_adjacent(0, 0));
    }

    #[test]
    fn test_klein_group_multiplication() {
        use KleinElement::{Identity, A, B, C};

        // Identity laws
        assert_eq!(Identity.multiply(A), A);
        assert_eq!(A.multiply(Identity), A);

        // Self-inverse property
        assert_eq!(A.multiply(A), Identity);
        assert_eq!(B.multiply(B), Identity);
        assert_eq!(C.multiply(C), Identity);

        // Products
        assert_eq!(A.multiply(B), C);
        assert_eq!(B.multiply(A), C);
        assert_eq!(A.multiply(C), B);
        assert_eq!(B.multiply(C), A);
    }

    #[test]
    fn test_klein_group_associativity() {
        use KleinElement::{A, B, C};

        // (a·b)·c = a·(b·c)
        let left = A.multiply(B).multiply(C);
        let right = A.multiply(B.multiply(C));
        assert_eq!(left, right);
    }
}
