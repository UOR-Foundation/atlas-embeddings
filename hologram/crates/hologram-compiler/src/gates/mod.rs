//! Quantum gate operations in 768-cycle space
//!
//! This module provides gate operations for single-qubit, two-qubit, and multi-qubit systems.
//!
//! ## Gate Types
//!
//! - **Single-qubit gates**: H, X, Y, Z, T, S, phase rotations
//! - **Two-qubit gates**: CNOT, SWAP, CZ, controlled gates
//! - **Multi-qubit gates**: Toffoli, Fredkin, generalized controlled gates
//!
//! ## 768-Cycle Representation
//!
//! All gates are represented as transformations in the 768-dimensional cycle space,
//! providing a unified geometric framework for quantum operations.

pub mod n_qubit;
pub mod single_qubit;
pub mod two_qubit;

pub use n_qubit::{apply_fredkin, apply_toffoli};
pub use single_qubit::{
    apply_hadamard, apply_identity, apply_pauli_x, apply_pauli_y, apply_pauli_z, apply_s_gate, apply_t_gate,
};
pub use two_qubit::gates::{apply_cnot, apply_cz, apply_swap};
