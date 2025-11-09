//! Discovery Tests for 768-Cycle Quantum State Execution
//!
//! This module contains discovery tests that validate the hypothesis that quantum
//! gates execute as deterministic 768-cycle advancements.

// Experiment 5: Single-qubit discovery tests
pub mod determinism_validation;
pub mod gate_advancement_correctness;
pub mod gate_identities;
pub mod measurement_projection;
pub mod periodicity_test;

// Experiment 6: Multi-qubit discovery tests
#[cfg(feature = "quantum_state_768_multi_qubit")]
pub mod bell_state_validation;
#[cfg(feature = "quantum_state_768_multi_qubit")]
pub mod born_rule_validation;
#[cfg(feature = "quantum_state_768_multi_qubit")]
pub mod cnot_correctness;
#[cfg(feature = "quantum_state_768_multi_qubit")]
pub mod entanglement_correlation;
#[cfg(feature = "quantum_state_768_multi_qubit")]
pub mod swap_gate_correctness;

// Experiment 7: N-qubit discovery tests
#[cfg(feature = "quantum_state_768_n_qubit")]
pub mod ghz_state_validation;
#[cfg(feature = "quantum_state_768_n_qubit")]
pub mod n_qubit_constraint_satisfaction;
#[cfg(feature = "quantum_state_768_n_qubit")]
pub mod partial_measurement_tests;
#[cfg(feature = "quantum_state_768_n_qubit")]
pub mod toffoli_correctness;
#[cfg(feature = "quantum_state_768_n_qubit")]
pub mod w_state_validation;
