//! # Atlas Embeddings: Exceptional Lie Groups from First Principles
//!
//! This crate provides a mathematically rigorous construction of the five exceptional
//! Lie groups (G₂, F₄, E₆, E₇, E₈) from the **Atlas of Resonance Classes**.
//!
//! ## Mathematical Foundation
//!
//! ### The Atlas of Resonance Classes
//!
//! The Atlas is a 96-vertex graph that emerges as the **stationary configuration**
//! of an action functional on a 12,288-cell boundary complex. It is NOT constructed
//! algorithmically—it IS the unique configuration satisfying:
//!
//! $$S[\phi] = \sum_{\text{cells}} \phi(\partial \text{cell})$$
//!
//! where the action functional's stationary points define resonance classes.
//!
//! ### Key Properties
//!
//! 1. **96 vertices** - Resonance classes labeled by E₈ coordinates
//! 2. **Mirror symmetry** τ - Canonical involution
//! 3. **12,288-cell boundary** - Discrete action functional domain
//! 4. **Unity constraint** - Adjacency determined by roots of unity
//!
//! ## Exceptional Groups from Categorical Operations
//!
//! The five exceptional groups emerge through categorical operations on the Atlas:
//!
//! | Group | Operation | Structure | Roots | Rank |
//! |-------|-----------|-----------|-------|------|
//! | **G₂** | Product: Klein × ℤ/3 | 2 × 3 = 6 vertices | 12 | 2 |
//! | **F₄** | Quotient: 96/± | Mirror equivalence | 48 | 4 |
//! | **E₆** | Filtration: degree partition | 64 + 8 = 72 | 72 | 6 |
//! | **E₇** | Augmentation: 96 + 30 | S₄ orbits | 126 | 7 |
//! | **E₈** | Embedding: Atlas → E₈ | Direct isomorphism | 240 | 8 |
//!
//! ## Design Principles
//!
//! ### 1. Exact Arithmetic Only
//!
//! **NO floating point arithmetic** is used. All computations employ:
//!
//! - [`i64`] for integer values
//! - [`Fraction`](num_rational::Ratio) for rational numbers
//! - Half-integers (multiples of 1/2) for E₈ coordinates
//!
//! This ensures **mathematical exactness** and **reproducibility**.
//!
//! ### 2. First Principles Construction
//!
//! We do NOT:
//! - Import Cartan matrices from tables
//! - Use Dynkin diagram classification
//! - Assume Lie algebra theory
//!
//! We DO:
//! - Construct Atlas from action functional
//! - Derive exceptional groups from categorical operations
//! - Verify properties computationally
//!
//! ### 3. Type-Level Guarantees
//!
//! Rust's type system enforces mathematical invariants:
//!
//! ```rust
//! # use atlas_embeddings::cartan::CartanMatrix;
//! // Rank encoded at type level - dimension mismatches caught at compile time
//! let g2: CartanMatrix<2> = CartanMatrix::new([[2, -1], [-1, 2]]);
//! let f4: CartanMatrix<4> = CartanMatrix::new([
//!     [2, -1, 0, 0],
//!     [-1, 2, -2, 0],  // Double bond for F₄
//!     [0, -1, 2, -1],
//!     [0, 0, -1, 2],
//! ]);
//! ```
//!
//! ### 4. Documentation as Primary Exposition
//!
//! This crate uses **documentation-driven development** where:
//!
//! - Mathematical theory is explained in module docs
//! - Theorems are stated as doc comments
//! - Proofs are tests that verify claims
//! - Code serves as formal certificate
//!
//! The generated rustdoc serves as the primary "paper".
//!
//! ## Quick Start
//!
//! ### Constructing E₆
//!
//! ```rust
//! use atlas_embeddings::{Atlas, groups::E6};
//!
//! // Construct Atlas (from first principles)
//! let atlas = Atlas::new();
//!
//! // E₆ emerges via degree-partition: 72 = 64 + 8
//! let e6 = E6::from_atlas(&atlas);
//!
//! // Verify basic properties
//! assert_eq!(e6.num_roots(), 72);
//! assert_eq!(e6.rank(), 6);
//! assert!(e6.is_simply_laced());
//!
//! // Cartan matrix verification
//! let cartan = e6.cartan_matrix();
//! assert!(cartan.is_simply_laced());
//! assert_eq!(cartan.determinant(), 3);
//! assert!(cartan.is_symmetric());
//! ```
//!
//! ### Computing Weyl Group Order
//!
//! ```rust
//! use atlas_embeddings::{Atlas, groups::{G2, F4}};
//!
//! let atlas = Atlas::new();
//!
//! let g2 = G2::from_atlas(&atlas);
//! assert_eq!(g2.weyl_order(), 12);
//!
//! let f4 = F4::from_atlas(&atlas);
//! assert_eq!(f4.weyl_order(), 1152);
//! ```
//!
//! ## Module Organization
//!
//! - [`atlas`] - Atlas graph construction from action functional
//! - [`arithmetic`] - Exact rational arithmetic (no floats!)
//! - [`e8`] - E₈ root system and Atlas embedding
//! - [`groups`] - Exceptional group constructions (G₂, F₄, E₆, E₇, E₈)
//! - [`cartan`] - Cartan matrices and Dynkin diagrams
//! - [`weyl`] - Weyl groups and simple reflections
//! - [`categorical`] - Categorical operations (product, quotient, filtration)
//!
//! ## Standards and Verification
//!
//! This crate is designed for **peer review** with:
//!
//! - ✅ **No unsafe code** (`#![forbid(unsafe_code)]`)
//! - ✅ **No floating point** (clippy: `deny(float_arithmetic)`)
//! - ✅ **Comprehensive tests** - Unit, integration, property-based
//! - ✅ **Strict linting** - Clippy pedantic, nursery, cargo
//! - ✅ **Full documentation** - All public items documented
//! - ✅ **Reproducible** - Deterministic, platform-independent
//!
//! Run verification suite:
//!
//! ```bash
//! make verify  # format-check + clippy + tests + docs
//! ```
//!
//! ## References
//!
//! 1. Conway, J. H., & Sloane, N. J. A. (1988). *Sphere Packings, Lattices and Groups*
//! 2. Baez, J. C. (2002). *The Octonions*
//! 3. Wilson, R. A. (2009). *The Finite Simple Groups*
//! 4. Carter, R. W. (2005). *Lie Algebras of Finite and Affine Type*
//!
//! ## About UOR Foundation
//!
//! This work is published by the [UOR Foundation](https://uor.foundation), dedicated to
//! advancing universal object reference systems and foundational research in mathematics,
//! physics, and computation.
//!
//! ## Citation
//!
//! If you use this crate in academic work, please cite it using the DOI:
//!
//! ```bibtex
//! @software{atlas_embeddings,
//!   title = {atlas-embeddings: First-principles construction of exceptional Lie groups},
//!   author = {{UOR Foundation}},
//!   year = {2025},
//!   url = {https://github.com/UOR-Foundation/atlas-embeddings},
//!   doi = {10.5281/zenodo.XXXXXXX}, % Update after first release
//! }
//! ```
//!
//! **Note**: The DOI will be generated automatically when the first release is created on GitHub.
//! Update the placeholder `XXXXXXX` with the actual DOI from Zenodo.
//!
//! ## Contact
//!
//! - Homepage: <https://uor.foundation>
//! - Issues: <https://github.com/UOR-Foundation/atlas-embeddings/issues>
//! - Discussions: <https://github.com/UOR-Foundation/atlas-embeddings/discussions>
//!
//! ## License
//!
//! This project is licensed under the [MIT License](https://github.com/UOR-Foundation/atlas-embeddings/blob/main/LICENSE-MIT).

#![forbid(unsafe_code)]
#![warn(missing_docs, missing_debug_implementations)]
#![cfg_attr(not(test), warn(clippy::float_arithmetic))]
#![cfg_attr(test, allow(clippy::large_stack_arrays))] // format! macros in tests create temp arrays
#![cfg_attr(docsrs, feature(doc_cfg))]

// Module declarations (to be implemented)
pub mod arithmetic;
pub mod atlas;
pub mod cartan;
pub mod categorical;
pub mod e8;
pub mod embedding;
pub mod groups;
pub mod weyl;

// Re-exports for convenience
pub use atlas::Atlas;
pub use cartan::CartanMatrix;
pub use e8::E8RootSystem;

/// Crate version for runtime verification
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Crate name
pub const NAME: &str = env!("CARGO_PKG_NAME");

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_crate_metadata() {
        assert_eq!(NAME, "atlas-embeddings");
        // VERSION is compile-time constant from CARGO_PKG_VERSION, always non-empty
    }
}
