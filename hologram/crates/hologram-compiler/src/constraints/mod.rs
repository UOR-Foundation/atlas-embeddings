//! Constraint-based execution for multi-qubit entangled systems
//!
//! This module provides the constraint engine that enables O(1) operations
//! for complex multi-qubit systems, including nested loops like GEMM.
//!
//! ## Key Concepts
//!
//! - **Linear Constraints**: N-way entanglement as Σ c_i · p_i ≡ k (mod 768)
//! - **Constraint Propagation**: Topological sorting of dependency graphs
//! - **O(1) Complexity**: Per-iteration constant time (prevents exponential blowup)
//!
//! ## Applications
//!
//! - **GEMM (Matrix Multiplication)**: Loop indices → positions, dependencies → constraints
//! - **Convolution**: Sliding window as constraint propagation
//! - **General Nested Loops**: Any stateful accumulation pattern
//!
//! ## Core Types
//!
//! - [`MultiQubitConstraint`] - Linear constraint specification
//! - [`ConstraintGraph`] - Dependency graph with topological ordering
//! - [`NQubitState`] - Entangled state with constraint tracking
//! - [`EntanglementStructure`] - Multi-way entanglement representation

pub mod constraint;
pub mod entangled_state;
pub mod measurement;

pub use constraint::{ConstraintGraph, MultiQubitConstraint};
pub use entangled_state::{EntanglementStructure, NQubitState};
pub use measurement::{measure_qubit, measure_qubits};
