//! Integration tests for atlas-embeddings
//!
//! These tests verify the complete construction pipeline from Atlas
//! through all exceptional groups.

#![cfg(test)]
#![allow(clippy::large_stack_arrays)] // format! macros in assertions create temporary arrays

// Integration tests will be organized by module
mod atlas_construction;
mod categorical_operations;
mod e6_construction;
mod e7_construction;
mod e8_embedding;
mod f4_construction;
mod g2_construction;

/// Common test utilities
#[allow(dead_code)]
mod common {
    use std::fmt::Debug;

    /// Helper for verifying exact arithmetic invariants
    pub fn assert_exact_zero<T: num_traits::Zero + PartialEq + Debug>(value: &T) {
        assert_eq!(*value, T::zero(), "Value must be exactly zero");
    }
}
