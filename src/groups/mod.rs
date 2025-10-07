//! Exceptional groups module

#![allow(missing_docs)]

use crate::Atlas;

/// G₂ exceptional Lie group
#[derive(Debug, Clone)]
pub struct G2 {
    _phantom: (),
}

impl G2 {
    /// Construct G₂ from Atlas
    #[must_use]
    pub fn from_atlas(_atlas: &Atlas) -> Self {
        Self { _phantom: () }
    }

    /// Get Weyl group order
    #[must_use]
    pub const fn weyl_order(&self) -> usize {
        12
    }
}

/// F₄ exceptional Lie group
#[derive(Debug, Clone)]
pub struct F4 {
    _phantom: (),
}

impl F4 {
    /// Construct F₄ from Atlas
    #[must_use]
    pub fn from_atlas(_atlas: &Atlas) -> Self {
        Self { _phantom: () }
    }

    /// Get Weyl group order
    #[must_use]
    pub const fn weyl_order(&self) -> usize {
        1152
    }
}

/// E₆ exceptional Lie group
#[derive(Debug, Clone)]
pub struct E6 {
    _phantom: (),
}

impl E6 {
    /// Construct E₆ from Atlas
    #[must_use]
    pub fn from_atlas(_atlas: &Atlas) -> Self {
        Self { _phantom: () }
    }

    /// Get simple roots (placeholder)
    #[must_use]
    pub fn simple_roots(&self) -> Vec<usize> {
        vec![]
    }

    /// Get Cartan matrix (placeholder)
    #[must_use]
    pub fn cartan_matrix(&self) -> crate::CartanMatrix<6> {
        crate::CartanMatrix::new([[0; 6]; 6])
    }
}
