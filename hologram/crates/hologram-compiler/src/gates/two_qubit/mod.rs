//! Two-Qubit Quantum Systems
//!
//! This module implements two-qubit quantum states with entanglement,
//! two-qubit gates, and Bell state creation/validation.

pub mod bell_states;
pub mod gates;
pub mod state;

// Re-export from state
pub use state::{CorrelationConstraint, TwoQubitState};

// Re-export from gates
pub use gates::{
    apply_cnot, apply_cz, apply_gate_sequence_two_qubit, apply_hadamard_to_qubit, apply_pauli_x_to_qubit,
    apply_pauli_z_to_qubit, apply_single_qubit_gate_to_qubit, apply_swap, GateApplication, TwoQubitGate,
    CNOT_ADVANCEMENT, COMPUTATIONAL_ONE_THRESHOLD, SWAP_ADVANCEMENT,
};

// Re-export from bell_states
pub use bell_states::{
    check_bell_correlation, create_bell_phi_minus, create_bell_phi_plus, create_bell_psi_minus, create_bell_psi_plus,
    is_computational_one_from_position, measure_two_qubit_state, BellState,
};
