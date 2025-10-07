//! Cartan matrices and Dynkin diagrams

#![allow(missing_docs)]

/// Cartan matrix for a Lie algebra
///
/// The type parameter `N` encodes the rank at compile time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CartanMatrix<const N: usize> {
    entries: [[i8; N]; N],
}

impl<const N: usize> CartanMatrix<N> {
    /// Create a new Cartan matrix
    #[must_use]
    pub const fn new(entries: [[i8; N]; N]) -> Self {
        Self { entries }
    }
}
