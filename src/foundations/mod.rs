//! # Chapter 0: Foundations
//!
//! This chapter builds all mathematical prerequisites from first principles,
//! assuming no prior knowledge beyond elementary set theory.
//!
//! ## Purpose
//!
//! The Atlas of Resonance Classes and its embedding into E₈ is a deep mathematical
//! structure. To understand it rigorously, we must establish foundations carefully.
//!
//! This chapter provides:
//! - **Basic definitions**: Graphs, groups, vector spaces
//! - **Exact arithmetic**: Rational numbers, no floating point
//! - **Action principles**: Variational calculus and stationary configurations
//! - **Resonance classes**: The 96 equivalence classes forming Atlas vertices
//! - **Category theory**: The language for describing Atlas initiality (future section)
//!
//! ## Reading Guide
//!
//! **For mathematicians**: This chapter is elementary but establishes notation and
//! conventions. Skim §0.1-0.2, focus on §0.3 (resonance classes) and §0.4 (categories).
//!
//! **For physicists**: The action functional in §0.2 will be familiar. The 12,288-cell
//! complex may be new—it's a discrete analog of field theory configuration spaces.
//!
//! **For computer scientists**: Note the emphasis on exact arithmetic (§0.1.2) and
//! discrete optimization (§0.2.4). The code serves as executable definitions.
//!
//! ## Chapter Organization
//!
//! - **[§0.1 Primitive Concepts](primitives)**: Graphs, arithmetic, groups, vectors
//! - **[§0.2 Action Functionals](action)**: Variational calculus, the 12,288-cell complex
//! - **[§0.3 Resonance Classes](resonance)**: The 96 equivalence classes, label system
//! - **[§0.4 Categorical Preliminaries](categories)**: Categories, functors, initial objects
//!
//! ## Main Results
//!
//! This chapter establishes:
//!
//! 1. **Exact arithmetic framework** (§0.1.2): All computations use rationals, no floats
//! 2. **Action functional** (§0.2.3): Defined on 12,288-cell boundary complex
//! 3. **96 resonance classes** (§0.3.2): Stationary configuration partitions into exactly 96 classes
//! 4. **Label system** (§0.3.3): Each class labeled by 6-tuple (e₁,e₂,e₃,d₄₅,e₆,e₇)
//! 5. **8D extension** (§0.3.4): Labels extend uniquely to E₈ coordinates
//!
//! These results are **computational discoveries**, not assumptions. The number 96
//! emerges from optimization, not by design.
//!
//! ## Connection to Main Theorem
//!
//! The Atlas initiality theorem (proved in later chapters) states:
//!
//! > The Atlas is the initial object in the category of resonance graphs,
//! > from which all exceptional Lie groups emerge through categorical operations.
//!
//! This chapter provides:
//! - The **Atlas** itself (96 resonance classes from §0.3)
//! - The **categorical language** to state initiality (§0.4)
//! - The **first-principles approach** ensuring no circular reasoning
//!
//! ## Historical Context
//!
//! The Atlas emerged from research by the UOR Foundation into invariant properties
//! of software systems under the Universal Object Reference (UOR) framework. The
//! discovery that fundamental mathematical structures arise from informational
//! action principles was unexpected.
//!
//! This chapter reconstructs the discovery path: starting only with an action
//! functional, we derive the 96-vertex structure without assuming Lie theory.
//!
//! ---
//!
//! **Navigation**:
//! - Next: [§0.1 Primitive Concepts](primitives)
//! - Up: [Main Page](crate)

// Public submodules
pub mod action;
pub mod categories;
pub mod primitives;
pub mod resonance;

// Re-export key types for convenience
pub use action::{ActionFunctional, Complex12288, Configuration};
pub use categories::{Functor, Morphism, Product, Quotient, ResonanceGraph};
pub use primitives::{KleinElement, SimpleGraph};
pub use resonance::{extend_to_8d, generate_all_labels, AtlasLabel, ResonanceClass};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_foundations_module_structure() {
        // Verify we can create instances of key types
        let _ = SimpleGraph::new();
        let _ = KleinElement::Identity;
        let _ = Complex12288::new();
        let _ = AtlasLabel::new(0, 0, 0, 0, 0, 0);

        // Verify category theory types
        let _ = Product::new("A".to_string(), "B".to_string(), None);
        let _ = Quotient::new("G".to_string(), 48, None);
        let _ = ResonanceGraph::new(96, vec![], std::collections::HashMap::new());
    }

    #[test]
    fn test_96_labels_generation() {
        let labels = generate_all_labels();
        assert_eq!(labels.len(), 96);

        // All should be valid
        assert!(labels.iter().all(AtlasLabel::is_valid));
    }

    #[test]
    fn test_all_labels_extend_to_8d() {
        let labels = generate_all_labels();

        for label in &labels {
            let extended = extend_to_8d(label);

            // Verify extension has 8 coordinates
            assert_eq!(extended.len(), 8);

            // Verify first 3 match
            assert_eq!(extended[0], label.e1);
            assert_eq!(extended[1], label.e2);
            assert_eq!(extended[2], label.e3);

            // Verify d45 constraint: e4 - e5 = d45
            assert_eq!(extended[3] - extended[4], label.d45);

            // Verify last 2 match
            assert_eq!(extended[5], label.e6);
            assert_eq!(extended[6], label.e7);

            // Verify parity: sum is even
            let sum: i8 = extended.iter().sum();
            assert_eq!(sum % 2, 0);
        }
    }
}
