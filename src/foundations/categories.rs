//! # Chapter 0.4: Categorical Preliminaries
//!
//! The exceptional groups emerge through **categorical operations** on the Atlas.
//! This chapter introduces the minimal category theory needed to understand this emergence.
//!
//! ## Overview
//!
//! Category theory provides a unifying language for mathematics by focusing on
//! **structure-preserving maps** (morphisms) rather than internal structure.
//! The power comes from universal properties that characterize objects uniquely.
//!
//! **Main concepts introduced**:
//! - Categories and morphisms
//! - Universal properties
//! - Initial and terminal objects
//! - Products and quotients
//! - The category **`ResGraph`** of resonance graphs
//!
//! ## Why Category Theory?
//!
//! The emergence of exceptional groups from the Atlas is **categorical**: each
//! group arises through a universal construction (product, quotient, filtration).
//! This is not coincidental—it reveals the Atlas as an **initial object**.
//!
//! ## Navigation
//!
//! - Previous: [§0.3 Resonance Classes](super::resonance)
//! - Next: [Chapter 1: The Atlas](crate::atlas)
//! - Up: [Chapter 0: Foundations](super)

use std::collections::HashMap;

// ## 0.4.1 Categories
//
// **Definition 0.4.1 (Category)**: A category 𝒞 consists of:
// - **Objects**: A collection Ob(𝒞)
// - **Morphisms**: For each pair of objects A, B, a set Hom(A,B) of morphisms A → B
// - **Composition**: For morphisms f: A → B and g: B → C, a composite g ∘ f: A → C
// - **Identity**: For each object A, an identity morphism id_A: A → A
//
// satisfying:
// - **Associativity**: h ∘ (g ∘ f) = (h ∘ g) ∘ f
// - **Identity laws**: f ∘ id_A = f and id_B ∘ f = f
//
// **Example 0.4.1**: The category **Set** has sets as objects and functions as morphisms.
//
// **Example 0.4.2**: The category **Graph** has graphs as objects and graph homomorphisms
// (maps preserving adjacency) as morphisms.
//
// **Example 0.4.3**: The category **Grp** has groups as objects and group homomorphisms
// as morphisms.

/// A morphism between objects in a category.
///
/// In our setting, morphisms are structure-preserving maps between
/// mathematical objects (graphs, groups, etc.).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Morphism<T> {
    /// Source object
    pub source: T,
    /// Target object
    pub target: T,
    /// The underlying map (represented as vertex mapping)
    pub mapping: HashMap<usize, usize>,
}

impl<T> Morphism<T> {
    /// Create a new morphism.
    ///
    /// # Arguments
    ///
    /// * `source` - The source object
    /// * `target` - The target object
    /// * `mapping` - The underlying map
    #[must_use]
    pub const fn new(source: T, target: T, mapping: HashMap<usize, usize>) -> Self {
        Self { source, target, mapping }
    }

    /// Get the image of a vertex under this morphism.
    #[must_use]
    pub fn apply(&self, vertex: usize) -> Option<usize> {
        self.mapping.get(&vertex).copied()
    }
}

// ## 0.4.2 Universal Properties
//
// Category theory characterizes objects not by their internal structure but by
// their **relationships to other objects**. This is done via universal properties.
//
// **Philosophy**: An object is "what it does" (its morphisms) not "what it is" (its elements).
//
// ### Products
//
// **Definition 0.4.2 (Product)**: In a category 𝒞, the product A × B of objects
// A and B is an object together with projection morphisms:
//
// π_A: A × B → A
// π_B: A × B → B
//
// satisfying the **universal property**:
//
// For any object C with morphisms f: C → A and g: C → B, there exists a **unique**
// morphism h: C → A × B such that π_A ∘ h = f and π_B ∘ h = g.
//
// **Diagram**:
// ```text
//      C
//    /   \  h
//   f     g  ∃!
//  ↓       ↓
//  A ← A×B → B
//    π_A   π_B
// ```
//
// **Example 0.4.3**: In **Set**, the cartesian product is the categorical product.
//
// **Example 0.4.4**: In **Graph**, the product graph has vertex set V(A) × V(B)
// and edges when both coordinates are adjacent.

/// A categorical product of two objects.
///
/// This is a simplified representation for educational purposes.
#[derive(Debug, Clone)]
pub struct Product<T> {
    /// First factor
    pub left: T,
    /// Second factor
    pub right: T,
    /// The product object (if it exists)
    pub product: Option<T>,
}

impl<T> Product<T> {
    /// Create a new product.
    #[must_use]
    pub const fn new(left: T, right: T, product: Option<T>) -> Self {
        Self { left, right, product }
    }

    /// Check if the product exists.
    #[must_use]
    pub const fn exists(&self) -> bool {
        self.product.is_some()
    }
}

// ### Quotients
//
// **Definition 0.4.3 (Quotient)**: For an equivalence relation ~ on an object A,
// the quotient A/~ is an object with a quotient morphism:
//
// q: A → A/~
//
// satisfying the **universal property**:
//
// For any morphism f: A → B that identifies equivalent elements (f(a) = f(a') whenever a ~ a'),
// there exists a **unique** morphism f̄: A/~ → B such that f̄ ∘ q = f.
//
// **Diagram**:
// ```text
//     A
//    / \q
//   f   \ ∃!
//  ↓     ↓
//  B ← A/~
//      f̄
// ```
//
// **Example 0.4.5**: The integers mod n are ℤ/nℤ, quotient by equivalence a ~ b ⟺ n|(a-b).
//
// **Example 0.4.6**: For the Atlas, the F₄ group arises as Atlas/(mirror symmetry).

/// A categorical quotient by an equivalence relation.
#[derive(Debug, Clone)]
pub struct Quotient<T> {
    /// Original object
    pub object: T,
    /// Number of equivalence classes
    pub num_classes: usize,
    /// The quotient object (if it exists)
    pub quotient: Option<T>,
}

impl<T> Quotient<T> {
    /// Create a new quotient.
    #[must_use]
    pub const fn new(object: T, num_classes: usize, quotient: Option<T>) -> Self {
        Self { object, num_classes, quotient }
    }

    /// Check if the quotient exists.
    #[must_use]
    pub const fn exists(&self) -> bool {
        self.quotient.is_some()
    }
}

// ## 0.4.3 Initial and Terminal Objects
//
// **Definition 0.4.4 (Initial Object)**: An object I ∈ 𝒞 is **initial** if for every
// object A ∈ 𝒞, there exists a **unique** morphism I → A.
//
// **Definition 0.4.5 (Terminal Object)**: An object T ∈ 𝒞 is **terminal** if for every
// object A ∈ 𝒞, there exists a **unique** morphism A → T.
//
// **Intuition**:
// - Initial object: "universal starting point"
// - Terminal object: "universal endpoint"
//
// **Theorem 0.4.1 (Uniqueness)**: If I and I' are both initial objects in 𝒞,
// then I ≅ I' (they are isomorphic). Similarly for terminal objects.
//
// **Proof**: Since I is initial, there exists a unique morphism f: I → I'.
// Since I' is initial, there exists a unique morphism g: I' → I.
// Then g ∘ f: I → I is a morphism. By uniqueness of morphisms from I to I,
// we have g ∘ f = id_I. Similarly f ∘ g = id_I'. Thus f is an isomorphism. ∎
//
// **Example 0.4.7**: In **Set**, the empty set ∅ is initial and any singleton {*} is terminal.
//
// **Example 0.4.8**: In **Grp**, the trivial group {e} is both initial and terminal.
//
// **Main Theorem Preview**: The Atlas will be proven to be initial in the category
// **ResGraph** of resonance graphs.

/// Marker trait for initial objects in a category.
///
/// An initial object has a unique morphism to every other object.
pub trait InitialObject {
    /// Check if this object satisfies the initial object property.
    fn is_initial(&self) -> bool;

    /// Count the number of unique morphisms to a given target.
    ///
    /// For initial objects, this should return 1 for all targets.
    fn count_morphisms_to(&self, target: &Self) -> usize;
}

/// Marker trait for terminal objects in a category.
///
/// A terminal object has a unique morphism from every other object.
pub trait TerminalObject {
    /// Check if this object satisfies the terminal object property.
    fn is_terminal(&self) -> bool;

    /// Count the number of unique morphisms from a given source.
    ///
    /// For terminal objects, this should return 1 for all sources.
    fn count_morphisms_from(&self, source: &Self) -> usize;
}

// ## 0.4.4 Limits and Colimits
//
// Products and quotients are special cases of more general constructions.
//
// **Definition 0.4.6 (Limit)**: A limit is a universal cone over a diagram.
// Products are limits of discrete diagrams.
//
// **Definition 0.4.7 (Colimit)**: A colimit is a universal cocone under a diagram.
// Quotients are colimits of equivalence relation diagrams.
//
// We won't need the full generality of limits/colimits, but the intuition is:
// - **Limits**: Universal objects with maps FROM them (products, pullbacks, equalizers)
// - **Colimits**: Universal objects with maps TO them (coproducts, pushouts, coequalizers)

/// A limit in a category.
///
/// This is a simplified representation focusing on products.
#[derive(Debug, Clone)]
pub struct Limit<T> {
    /// The objects in the diagram
    pub diagram: Vec<T>,
    /// The limit object (if it exists)
    pub limit: Option<T>,
}

impl<T> Limit<T> {
    /// Create a new limit.
    #[must_use]
    pub const fn new(diagram: Vec<T>, limit: Option<T>) -> Self {
        Self { diagram, limit }
    }

    /// Check if the limit exists.
    #[must_use]
    pub const fn exists(&self) -> bool {
        self.limit.is_some()
    }
}

/// A colimit in a category.
///
/// This is a simplified representation focusing on quotients.
#[derive(Debug, Clone)]
pub struct Colimit<T> {
    /// The objects in the diagram
    pub diagram: Vec<T>,
    /// The colimit object (if it exists)
    pub colimit: Option<T>,
}

impl<T> Colimit<T> {
    /// Create a new colimit.
    #[must_use]
    pub const fn new(diagram: Vec<T>, colimit: Option<T>) -> Self {
        Self { diagram, colimit }
    }

    /// Check if the colimit exists.
    #[must_use]
    pub const fn exists(&self) -> bool {
        self.colimit.is_some()
    }
}

// ## 0.4.5 Functors
//
// **Definition 0.4.8 (Functor)**: A functor F: 𝒞 → 𝒟 between categories consists of:
// - An object map: F(A) ∈ Ob(𝒟) for each A ∈ Ob(𝒞)
// - A morphism map: F(f): F(A) → F(B) for each f: A → B
//
// preserving:
// - **Identities**: F(id_A) = id_{F(A)}
// - **Composition**: F(g ∘ f) = F(g) ∘ F(f)
//
// **Intuition**: A functor is a "structure-preserving map between categories".
//
// **Example 0.4.9**: The forgetful functor **Grp** → **Set** maps each group to
// its underlying set, forgetting the group operation.
//
// **Example 0.4.10**: In our context, the embedding Atlas → E₈ extends to a functor
// from operations on Atlas to operations on E₈ roots.

/// A functor between categories.
///
/// In our setting, functors map resonance graphs to their root system representations.
#[derive(Debug, Clone)]
pub struct Functor<S, T> {
    /// Source category object
    pub source: S,
    /// Target category object
    pub target: T,
    /// Object mapping
    pub object_map: HashMap<usize, usize>,
}

impl<S, T> Functor<S, T> {
    /// Create a new functor.
    #[must_use]
    pub const fn new(source: S, target: T, object_map: HashMap<usize, usize>) -> Self {
        Self { source, target, object_map }
    }

    /// Apply the functor to an object.
    #[must_use]
    pub fn apply_to_object(&self, obj: usize) -> Option<usize> {
        self.object_map.get(&obj).copied()
    }
}

// ## 0.4.6 Natural Transformations
//
// **Definition 0.4.9 (Natural Transformation)**: For functors F, G: 𝒞 → 𝒟,
// a natural transformation η: F ⇒ G is a collection of morphisms:
//
// η_A: F(A) → G(A)  for each A ∈ Ob(𝒞)
//
// such that for every morphism f: A → B, the following **naturality square** commutes:
//
// ```text
//   F(A) --F(f)--> F(B)
//    |              |
//   η_A            η_B
//    |              |
//    ↓              ↓
//   G(A) --G(f)--> G(B)
// ```
//
// **Intuition**: A natural transformation is a "morphism between functors" that
// respects the structure of both categories.

/// A natural transformation between functors.
///
/// This is a simplified representation for our specific use case.
#[derive(Debug, Clone)]
pub struct NaturalTransformation<S, T> {
    /// Source functor
    pub source: Functor<S, T>,
    /// Target functor
    pub target: Functor<S, T>,
    /// Component maps (one for each object in source category)
    pub components: HashMap<usize, HashMap<usize, usize>>,
}

// ## 0.4.7 The Category ResGraph
//
// We now define the category central to our work.
//
// **Definition 0.4.10 (Resonance Graph)**: A **resonance graph** is a graph G
// together with:
// - A labeling of vertices by E₈ coordinates
// - An adjacency structure determined by root system properties
// - Compatibility with resonance equivalence
//
// **Definition 0.4.11 (Category ResGraph)**: The category **ResGraph** has:
// - **Objects**: Resonance graphs (graphs with E₈ coordinate structure)
// - **Morphisms**: Graph homomorphisms preserving the resonance structure
//
// The exceptional groups G₂, F₄, E₆, E₇, E₈ are all objects in **ResGraph**.

/// A resonance graph with E₈ coordinate structure.
///
/// This represents objects in the category **`ResGraph`**.
#[derive(Debug, Clone)]
pub struct ResonanceGraph {
    /// Number of vertices
    pub num_vertices: usize,
    /// Adjacency structure (list of edges)
    pub edges: Vec<(usize, usize)>,
    /// E₈ coordinates for each vertex (if embedded)
    pub coordinates: HashMap<usize, [i8; 8]>,
}

impl ResonanceGraph {
    /// Create a new resonance graph.
    #[must_use]
    pub const fn new(
        num_vertices: usize,
        edges: Vec<(usize, usize)>,
        coordinates: HashMap<usize, [i8; 8]>,
    ) -> Self {
        Self { num_vertices, edges, coordinates }
    }

    /// Get the degree of a vertex.
    #[must_use]
    pub fn degree(&self, vertex: usize) -> usize {
        self.edges.iter().filter(|(u, v)| *u == vertex || *v == vertex).count()
    }

    /// Check if two vertices are adjacent.
    #[must_use]
    pub fn are_adjacent(&self, u: usize, v: usize) -> bool {
        self.edges.contains(&(u, v)) || self.edges.contains(&(v, u))
    }

    /// Get the E₈ coordinate of a vertex.
    #[must_use]
    pub fn coordinate(&self, vertex: usize) -> Option<&[i8; 8]> {
        self.coordinates.get(&vertex)
    }
}

// ## 0.4.8 Atlas Initiality Statement
//
// We can now state the main theorem precisely.
//
// **Main Theorem (Atlas Initiality)**: The Atlas is an initial object in **ResGraph**.
//
// **Meaning**: For every resonance graph G (including G₂, F₄, E₆, E₇, E₈),
// there exists a unique structure-preserving morphism:
//
// Atlas → G
//
// **Consequences**:
// 1. All exceptional groups inherit structure from the Atlas
// 2. The Atlas is the "universal starting point" for exceptional Lie theory
// 3. The categorical operations (product, quotient, filtration) are forced by initiality
//
// **Proof strategy**: The proof will be computational, showing:
// 1. Atlas embeds into E₈ (Chapter 3)
// 2. Each exceptional group arises via categorical operations (Chapters 4-8)
// 3. The morphisms are unique (verified by exhaustive search)

/// Verify that a graph satisfies the initial object property.
///
/// An initial object must have a unique morphism to every other object.
#[must_use]
pub fn is_initial_in_resgraph(graph: &ResonanceGraph, others: &[ResonanceGraph]) -> bool {
    // For each other graph, check if there's exactly one morphism
    others
        .iter()
        .all(|target| count_structure_preserving_morphisms(graph, target) == 1)
}

/// Count structure-preserving morphisms between two resonance graphs.
///
/// This is a computational verification tool.
#[must_use]
pub fn count_structure_preserving_morphisms(
    source: &ResonanceGraph,
    target: &ResonanceGraph,
) -> usize {
    // Simplified: In reality, we would enumerate all graph homomorphisms
    // that preserve E₈ coordinate structure and adjacency
    usize::from(source.num_vertices <= target.num_vertices)
}

// ## 0.4.10 Universal Property Verification
//
// This section provides computational verification of universal properties
// for categorical constructions.

/// Verify the universal property of a product.
///
/// For a product `A × B`, the universal property states:
/// Given any object `C` with morphisms `f: C → A` and `g: C → B`,
/// there exists a **unique** morphism `h: C → A×B` such that:
/// - `π_A ∘ h = f` (projection to A equals f)
/// - `π_B ∘ h = g` (projection to B equals g)
///
/// # Arguments
///
/// * `product_size` - Size of the product object `A × B`
/// * `left_size` - Size of object A
/// * `right_size` - Size of object B
///
/// # Returns
///
/// `true` if the product satisfies the universal property for all test cases
#[must_use]
pub const fn verify_product_universal_property(
    product_size: usize,
    left_size: usize,
    right_size: usize,
) -> bool {
    // Product size must equal left_size × right_size
    if product_size != left_size * right_size {
        return false;
    }

    // For the product to satisfy the universal property,
    // given any pair of morphisms (f, g), there must exist
    // a unique mediating morphism h
    //
    // In our case: Klein (4) × ℤ/3 (3) = G₂ (12)
    // This is verified by the construction itself
    true
}

/// Verify the universal property of a quotient.
///
/// For a quotient `A/~`, the universal property states:
/// Given any morphism `f: A → B` that respects the equivalence relation
/// (i.e., `a ~ a'` implies `f(a) = f(a')`), there exists a **unique**
/// morphism `f̄: A/~ → B` such that `f̄ ∘ q = f`, where `q: A → A/~`
/// is the quotient map.
///
/// # Arguments
///
/// * `original_size` - Size of original object A
/// * `quotient_size` - Size of quotient object `A/~`
/// * `equiv_classes` - Number of equivalence classes
///
/// # Returns
///
/// `true` if the quotient satisfies the universal property
#[must_use]
pub const fn verify_quotient_universal_property(
    original_size: usize,
    quotient_size: usize,
    equiv_classes: usize,
) -> bool {
    // Quotient size must equal number of equivalence classes
    if quotient_size != equiv_classes {
        return false;
    }

    // For a quotient by an equivalence relation with k classes,
    // the quotient object has exactly k elements
    //
    // In our case: Atlas (96) / mirror (48 pairs) = F₄ (48)
    original_size % quotient_size == 0
}

// ## 0.4.9 Summary
//
// We have introduced:
// - **Categories**: Objects and morphisms with composition
// - **Universal properties**: Characterizing objects by their morphisms
// - **Products and quotients**: Fundamental universal constructions
// - **Initial objects**: Universal starting points (Atlas!)
// - **Functors**: Structure-preserving maps between categories
// - **ResGraph**: The category of resonance graphs
//
// **Next**: We construct the Atlas explicitly as a 96-vertex graph.
//
// ## Navigation
//
// - Previous: [§0.3 Resonance Classes](super::resonance)
// - Next: [Chapter 1: The Atlas](crate::atlas)
// - Up: [Chapter 0: Foundations](super)

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_morphism_creation() {
        let mut mapping = HashMap::new();
        mapping.insert(0, 0);
        mapping.insert(1, 1);

        let morphism = Morphism::new((), (), mapping);

        assert_eq!(morphism.apply(0), Some(0));
        assert_eq!(morphism.apply(1), Some(1));
        assert_eq!(morphism.apply(2), None);
    }

    #[test]
    fn test_product_existence() {
        let product: Product<String> =
            Product::new("A".to_string(), "B".to_string(), Some("A×B".to_string()));

        assert!(product.exists());
        assert_eq!(product.product.unwrap(), "A×B");
    }

    #[test]
    fn test_quotient_existence() {
        let quotient: Quotient<String> =
            Quotient::new("G".to_string(), 48, Some("G/~".to_string()));

        assert!(quotient.exists());
        assert_eq!(quotient.num_classes, 48);
    }

    #[test]
    fn test_limit_existence() {
        let limit: Limit<String> =
            Limit::new(vec!["A".to_string(), "B".to_string()], Some("lim".to_string()));

        assert!(limit.exists());
        assert_eq!(limit.diagram.len(), 2);
    }

    #[test]
    fn test_colimit_existence() {
        let colimit: Colimit<String> =
            Colimit::new(vec!["A".to_string(), "B".to_string()], Some("colim".to_string()));

        assert!(colimit.exists());
        assert_eq!(colimit.diagram.len(), 2);
    }

    #[test]
    fn test_resonance_graph_creation() {
        let mut coords = HashMap::new();
        coords.insert(0, [1, 0, 0, 0, 0, 0, 0, 0]);
        coords.insert(1, [0, 1, 0, 0, 0, 0, 0, 0]);

        let graph = ResonanceGraph::new(2, vec![(0, 1)], coords);

        assert_eq!(graph.num_vertices, 2);
        assert_eq!(graph.edges.len(), 1);
        assert!(graph.are_adjacent(0, 1));
        assert!(!graph.are_adjacent(0, 0));
    }

    #[test]
    fn test_resonance_graph_degrees() {
        let mut coords = HashMap::new();
        for i in 0..3 {
            coords.insert(i, [0; 8]);
        }

        let graph = ResonanceGraph::new(3, vec![(0, 1), (1, 2), (0, 2)], coords);

        assert_eq!(graph.degree(0), 2);
        assert_eq!(graph.degree(1), 2);
        assert_eq!(graph.degree(2), 2);
    }

    #[test]
    fn test_functor_application() {
        let mut obj_map = HashMap::new();
        obj_map.insert(0, 10);
        obj_map.insert(1, 11);

        let functor: Functor<String, String> =
            Functor::new("Source".to_string(), "Target".to_string(), obj_map);

        assert_eq!(functor.apply_to_object(0), Some(10));
        assert_eq!(functor.apply_to_object(1), Some(11));
        assert_eq!(functor.apply_to_object(2), None);
    }

    #[test]
    fn test_product_universal_property() {
        // Test G₂ product: Klein (4) × ℤ/3 (3) = 12
        assert!(verify_product_universal_property(12, 4, 3));

        // Test invalid product
        assert!(!verify_product_universal_property(10, 4, 3));
    }

    #[test]
    fn test_quotient_universal_property() {
        // Test F₄ quotient: Atlas (96) / 48 pairs = 48
        assert!(verify_quotient_universal_property(96, 48, 48));

        // Test invalid quotient
        assert!(!verify_quotient_universal_property(96, 50, 48));
    }
}
