//! Core 768-cycle quantum computing primitives
//!
//! This module provides the foundational types for deterministic quantum computing
//! in the 768-dimensional cycle space.
//!
//! ## Overview
//!
//! - **768-Cycle Model**: 768 = 3 × 256 (modalities × bytes) = 96 × 8 (classes × octaves)
//! - **Deterministic Quantum Computing**: 100% deterministic, no wave function collapse
//! - **Cycle-Based State**: Quantum state as position in 768-cycle
//!
//! ## Core Types
//!
//! - [`QuantumState`] - Single qubit state in 768-cycle space
//! - [`Measurement`] - Measurement operations and outcomes
//! - [`BornRule`] - Probability calculations in cycle space

pub mod born_rule;
pub mod measurement;
pub mod state;

pub use born_rule::{BornRuleValidation, SuperpositionState};
pub use measurement::{measure_detailed, measure_quantum_state, project_to_class, verify_determinism};
pub use state::QuantumState;

pub use born_rule::validate_born_rule_single_qubit;
