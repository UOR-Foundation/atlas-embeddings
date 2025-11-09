//! Two-Qubit Quantum Gates
//!
//! This module implements two-qubit gates as geometric operations in the 768-cycle model.
//! The key insight is that two-qubit gates can create entanglement by establishing
//! correlation constraints between qubit positions.
//!
//! ## Gate Mappings
//!
//! | Gate | Advancement | Type | Description |
//! |------|-------------|------|-------------|
//! | CNOT | 256/768 | Entangling | Control-NOT, creates entanglement |
//! | SWAP | 128/768 | Permutation | Exchange qubit positions |
//! | CZ | 384/768 | Phase | Control-Z, entangling phase gate |
//!
//! ## CNOT Gate
//!
//! The CNOT (Control-NOT) gate is the fundamental entangling gate:
//!
//! ```text
//! |00⟩ → |00⟩  (control=0: no change)
//! |01⟩ → |01⟩  (control=0: no change)
//! |10⟩ → |11⟩  (control=1: flip target)
//! |11⟩ → |10⟩  (control=1: flip target)
//! ```
//!
//! In the 768-cycle model:
//! - Control qubit position determines action
//! - If p_control ≥ 384 (computational |1⟩): apply X gate to target
//! - Creates correlation constraint: p_control + p_target ≡ k (mod 768)
//!
//! ## Bell State Creation
//!
//! ```
//! use hologram_compiler::{TwoQubitState, QuantumState};
//! use hologram_compiler::{apply_hadamard_to_qubit, apply_cnot};
//!
//! // Start with |00⟩
//! let mut state = TwoQubitState::new_product(
//!     QuantumState::new(0),
//!     QuantumState::new(0),
//! );
//!
//! // Apply H⊗I (Hadamard on first qubit)
//! state = apply_hadamard_to_qubit(state, 0);
//! // Now: (|0⟩+|1⟩) ⊗ |0⟩ / √2, qubit_0 at position 192
//!
//! // Apply CNOT(control=0, target=1)
//! state = apply_cnot(state, 0, 1);
//! // Result: |Φ⁺⟩ = (|00⟩+|11⟩) / √2, entangled!
//!
//! assert!(state.is_entangled());
//! ```

use hologram_tracing::perf_span;

use super::state::{CorrelationConstraint, TwoQubitState};
use crate::core::state::{QuantumState, CYCLE_SIZE};
use crate::gates::single_qubit::QuantumGate;

/// The threshold position that distinguishes |0⟩ from |1⟩ in computational basis
///
/// Positions [0, 384) → computational |0⟩
/// Positions [384, 768) → computational |1⟩
pub const COMPUTATIONAL_ONE_THRESHOLD: u16 = 384;

/// CNOT gate advancement (256/768 = 1/3 cycle)
pub const CNOT_ADVANCEMENT: u16 = 256;

/// SWAP gate advancement (128/768 = 1/6 cycle)
pub const SWAP_ADVANCEMENT: u16 = 128;

/// Two-qubit gate enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TwoQubitGate {
    /// Control-NOT gate (creates entanglement)
    CNOT,
    /// SWAP gate (exchange qubits)
    SWAP,
    /// Control-Z gate (entangling phase gate)
    CZ,
}

impl TwoQubitGate {
    /// Get the name of this gate
    pub fn name(&self) -> &'static str {
        match self {
            TwoQubitGate::CNOT => "CNOT",
            TwoQubitGate::SWAP => "SWAP",
            TwoQubitGate::CZ => "CZ",
        }
    }
}

/// Apply a single-qubit gate to a specific qubit in a two-qubit state
///
/// This preserves entanglement if present by updating both qubits to maintain
/// the correlation constraint.
///
/// # Arguments
///
/// * `state` - Two-qubit state
/// * `gate` - Single-qubit gate to apply
/// * `target` - Target qubit index (0 or 1)
///
/// # Example
///
/// ```
/// use hologram_compiler::{TwoQubitState, QuantumState, QuantumGate};
/// use hologram_compiler::apply_single_qubit_gate_to_qubit;
///
/// let state = TwoQubitState::new_product(
///     QuantumState::new(0),
///     QuantumState::new(0),
/// );
///
/// // Apply Hadamard to first qubit: H ⊗ I
/// let state = apply_single_qubit_gate_to_qubit(state, QuantumGate::Hadamard, 0);
/// assert_eq!(state.qubit_0().position(), 192);
/// assert_eq!(state.qubit_1().position(), 0);
/// ```
pub fn apply_single_qubit_gate_to_qubit(mut state: TwoQubitState, gate: QuantumGate, target: usize) -> TwoQubitState {
    let _span = perf_span!("apply_single_qubit_gate_to_qubit", gate = gate.name(), target = target);

    match target {
        0 => {
            let new_qubit_0 = gate.apply(state.qubit_0());
            state.set_qubit_0(new_qubit_0); // Automatically maintains correlation if entangled
        }
        1 => {
            let new_qubit_1 = gate.apply(state.qubit_1());
            state.set_qubit_1(new_qubit_1); // Automatically maintains correlation if entangled
        }
        _ => panic!("Invalid qubit index: {}. Must be 0 or 1", target),
    }

    state
}

/// Apply Hadamard gate to a specific qubit
///
/// # Example
///
/// ```
/// use hologram_compiler::{TwoQubitState, QuantumState};
/// use hologram_compiler::apply_hadamard_to_qubit;
///
/// let state = TwoQubitState::new_product(
///     QuantumState::new(0),
///     QuantumState::new(0),
/// );
///
/// let state = apply_hadamard_to_qubit(state, 0);
/// assert_eq!(state.qubit_0().position(), 192);  // H applied to qubit 0
/// assert_eq!(state.qubit_1().position(), 0);    // Qubit 1 unchanged
/// ```
pub fn apply_hadamard_to_qubit(state: TwoQubitState, target: usize) -> TwoQubitState {
    apply_single_qubit_gate_to_qubit(state, QuantumGate::Hadamard, target)
}

/// Apply Pauli-X gate to a specific qubit
pub fn apply_pauli_x_to_qubit(state: TwoQubitState, target: usize) -> TwoQubitState {
    apply_single_qubit_gate_to_qubit(state, QuantumGate::PauliX, target)
}

/// Apply Pauli-Z gate to a specific qubit
pub fn apply_pauli_z_to_qubit(state: TwoQubitState, target: usize) -> TwoQubitState {
    apply_single_qubit_gate_to_qubit(state, QuantumGate::PauliZ, target)
}

/// Check if a qubit is in computational |1⟩ state
///
/// In the 768-cycle model, computational basis states are determined by position:
/// - Positions [0, 384) → |0⟩
/// - Positions [384, 768) → |1⟩
fn is_computational_one(qubit: QuantumState) -> bool {
    qubit.position() >= COMPUTATIONAL_ONE_THRESHOLD
}

/// Apply CNOT gate (Control-NOT)
///
/// The fundamental two-qubit entangling gate. Flips the target qubit if and only if
/// the control qubit is in computational |1⟩ state (position ≥ 384).
///
/// # Truth Table
///
/// ```text
/// |00⟩ → |00⟩  (control=|0⟩: no change)
/// |01⟩ → |01⟩  (control=|0⟩: no change)
/// |10⟩ → |11⟩  (control=|1⟩: flip target)
/// |11⟩ → |10⟩  (control=|1⟩: flip target)
/// ```
///
/// # Arguments
///
/// * `state` - Two-qubit state
/// * `control` - Control qubit index (0 or 1)
/// * `target` - Target qubit index (0 or 1)
///
/// # Example
///
/// ```
/// use hologram_compiler::{TwoQubitState, QuantumState, apply_cnot};
///
/// // Test |10⟩ → |11⟩
/// let state = TwoQubitState::new_product(
///     QuantumState::new(384),  // |1⟩
///     QuantumState::new(0),    // |0⟩
/// );
///
/// let result = apply_cnot(state, 0, 1);
/// assert_eq!(result.qubit_0().position(), 384);  // Control unchanged
/// assert_eq!(result.qubit_1().position(), 384);  // Target flipped to |1⟩
/// assert!(result.is_entangled());  // Now entangled!
/// ```
pub fn apply_cnot(mut state: TwoQubitState, control: usize, target: usize) -> TwoQubitState {
    let _span = perf_span!("apply_cnot", control = control, target = target);

    assert!(control < 2 && target < 2, "Qubit indices must be 0 or 1");
    assert_ne!(control, target, "Control and target must be different qubits");

    // Break entanglement temporarily to apply gate operations cleanly
    // This ensures CNOT² = I works correctly
    if state.is_entangled() {
        state.break_entanglement();
    }

    let control_qubit = if control == 0 { state.qubit_0() } else { state.qubit_1() };
    let control_position = control_qubit.position();

    // CNOT behavior:
    // - If control is pure |0⟩ (position 0): no operation, no entanglement
    // - If control is |1⟩ (position >= 384): flip target, create entanglement
    // - If control is superposition (0 < position < 384): create entanglement without flipping

    if control_position == 0 {
        // Control is pure |0⟩: no operation, no entanglement
        state
    } else if is_computational_one(control_qubit) {
        // Control is |1⟩: flip target and create entanglement
        state = apply_pauli_x_to_qubit(state, target);

        // Create entanglement
        let sum = (state.qubit_0().position() + state.qubit_1().position()) % CYCLE_SIZE;
        let constraint = CorrelationConstraint::new(sum);
        state.create_entanglement(constraint);
        state
    } else {
        // Control is superposition: create entanglement without flipping
        // This handles Bell state creation where H puts qubit at position 192

        let sum = (state.qubit_0().position() + state.qubit_1().position()) % CYCLE_SIZE;
        let constraint = CorrelationConstraint::new(sum);
        state.create_entanglement(constraint);
        state
    }
}

/// Apply SWAP gate
///
/// Exchanges the positions of the two qubits. If the qubits are entangled,
/// the entanglement is preserved after the swap.
///
/// # Truth Table
///
/// ```text
/// |00⟩ → |00⟩  (no change)
/// |01⟩ → |10⟩  (swapped)
/// |10⟩ → |01⟩  (swapped)
/// |11⟩ → |11⟩  (no change)
/// ```
///
/// # Example
///
/// ```
/// use hologram_compiler::{TwoQubitState, QuantumState, apply_swap};
///
/// let state = TwoQubitState::new_product(
///     QuantumState::new(100),
///     QuantumState::new(200),
/// );
///
/// let result = apply_swap(state);
/// assert_eq!(result.qubit_0().position(), 200);  // Swapped
/// assert_eq!(result.qubit_1().position(), 100);  // Swapped
/// ```
pub fn apply_swap(state: TwoQubitState) -> TwoQubitState {
    let _span = perf_span!("apply_swap");

    let qubit_0 = state.qubit_0();
    let qubit_1 = state.qubit_1();
    let entangled = state.is_entangled();
    let correlation = state.correlation_constraint();

    // Swap positions
    if entangled {
        TwoQubitState::new_entangled(qubit_1, qubit_0, correlation.unwrap())
    } else {
        TwoQubitState::new_product(qubit_1, qubit_0)
    }
}

/// Apply Control-Z (CZ) gate
///
/// Applies a Z gate to the target if the control is in |1⟩ state.
/// Like CNOT, this is an entangling gate.
///
/// # Truth Table
///
/// ```text
/// |00⟩ → |00⟩  (no change)
/// |01⟩ → |01⟩  (no change)
/// |10⟩ → |10⟩  (no change)
/// |11⟩ → -|11⟩ (phase flip)
/// ```
///
/// Note: In the 768-cycle geometric model, the global phase is encoded in position,
/// so the phase flip manifests as a 384-advancement.
///
/// # Example
///
/// ```
/// use hologram_compiler::{TwoQubitState, QuantumState, apply_cz};
///
/// let state = TwoQubitState::new_product(
///     QuantumState::new(384),  // |1⟩
///     QuantumState::new(384),  // |1⟩
/// );
///
/// let result = apply_cz(state, 0, 1);
/// // Both qubits in |1⟩, so phase flip applied to target
/// assert!(result.is_entangled());
/// ```
pub fn apply_cz(mut state: TwoQubitState, control: usize, target: usize) -> TwoQubitState {
    let _span = perf_span!("apply_cz", control = control, target = target);

    assert!(control < 2 && target < 2, "Qubit indices must be 0 or 1");
    assert_ne!(control, target, "Control and target must be different qubits");

    let control_qubit = if control == 0 { state.qubit_0() } else { state.qubit_1() };

    // Check if control qubit is in |1⟩ state
    if is_computational_one(control_qubit) {
        // Apply Z gate to target (phase flip)
        state = apply_pauli_z_to_qubit(state, target);

        // Create entanglement if not already entangled
        if !state.is_entangled() {
            let sum = (state.qubit_0().position() + state.qubit_1().position()) % CYCLE_SIZE;
            let constraint = CorrelationConstraint::new(sum);
            state.create_entanglement(constraint);
        }
    }

    state
}

/// Apply a sequence of two-qubit gates
///
/// # Example
///
/// ```
/// use hologram_compiler::{TwoQubitState, QuantumState, QuantumGate};
/// use hologram_compiler::{GateApplication, apply_gate_sequence_two_qubit};
///
/// let state = TwoQubitState::new_product(
///     QuantumState::new(0),
///     QuantumState::new(0),
/// );
///
/// // Create Bell state: H ⊗ I, then CNOT
/// let gates = vec![
///     GateApplication::SingleQubit(0, QuantumGate::Hadamard),
///     GateApplication::CNOT(0, 1),
/// ];
///
/// let bell_state = apply_gate_sequence_two_qubit(state, &gates);
/// assert!(bell_state.is_entangled());
/// ```
#[derive(Debug, Clone, Copy)]
pub enum GateApplication {
    /// Apply single-qubit gate to target qubit
    SingleQubit(usize, QuantumGate),
    /// Apply CNOT with (control, target) indices
    CNOT(usize, usize),
    /// Apply SWAP
    SWAP,
    /// Apply CZ with (control, target) indices
    CZ(usize, usize),
}

pub fn apply_gate_sequence_two_qubit(mut state: TwoQubitState, gates: &[GateApplication]) -> TwoQubitState {
    let _span = perf_span!("apply_gate_sequence_two_qubit", num_gates = gates.len());

    for gate_app in gates {
        state = match gate_app {
            GateApplication::SingleQubit(target, gate) => apply_single_qubit_gate_to_qubit(state, *gate, *target),
            GateApplication::CNOT(control, target) => apply_cnot(state, *control, *target),
            GateApplication::SWAP => apply_swap(state),
            GateApplication::CZ(control, target) => apply_cz(state, *control, *target),
        };
    }

    state
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_computational_one() {
        assert!(!is_computational_one(QuantumState::new(0)));
        assert!(!is_computational_one(QuantumState::new(100)));
        assert!(!is_computational_one(QuantumState::new(383)));
        assert!(is_computational_one(QuantumState::new(384)));
        assert!(is_computational_one(QuantumState::new(500)));
        assert!(is_computational_one(QuantumState::new(767)));
    }

    #[test]
    fn test_apply_hadamard_to_qubit() {
        let state = TwoQubitState::new_product(QuantumState::new(0), QuantumState::new(0));

        let result = apply_hadamard_to_qubit(state, 0);
        assert_eq!(result.qubit_0().position(), 192); // H applied
        assert_eq!(result.qubit_1().position(), 0); // Unchanged
    }

    #[test]
    fn test_cnot_truth_table_00() {
        // |00⟩ → |00⟩
        let state = TwoQubitState::new_product(QuantumState::new(0), QuantumState::new(0));
        let result = apply_cnot(state, 0, 1);

        assert_eq!(result.qubit_0().position(), 0);
        assert_eq!(result.qubit_1().position(), 0);
        assert!(!result.is_entangled()); // Control is |0⟩, no entanglement
    }

    #[test]
    fn test_cnot_truth_table_01() {
        // |01⟩ → |01⟩
        let state = TwoQubitState::new_product(QuantumState::new(0), QuantumState::new(384));
        let result = apply_cnot(state, 0, 1);

        assert_eq!(result.qubit_0().position(), 0);
        assert_eq!(result.qubit_1().position(), 384);
        assert!(!result.is_entangled()); // Control is |0⟩, no entanglement
    }

    #[test]
    fn test_cnot_truth_table_10() {
        // |10⟩ → |11⟩
        let state = TwoQubitState::new_product(QuantumState::new(384), QuantumState::new(0));
        let result = apply_cnot(state, 0, 1);

        assert_eq!(result.qubit_0().position(), 384); // Control unchanged
        assert_eq!(result.qubit_1().position(), 384); // Target flipped: 0 + 384 = 384
        assert!(result.is_entangled()); // Control is |1⟩, creates entanglement
    }

    #[test]
    fn test_cnot_truth_table_11() {
        // |11⟩ → |10⟩
        let state = TwoQubitState::new_product(QuantumState::new(384), QuantumState::new(384));
        let result = apply_cnot(state, 0, 1);

        assert_eq!(result.qubit_0().position(), 384); // Control unchanged
                                                      // Target flipped: 384 + 384 = 768 ≡ 0 (mod 768)
        assert_eq!(result.qubit_1().position(), 0);
        assert!(result.is_entangled()); // Control is |1⟩, creates entanglement
    }

    #[test]
    fn test_swap_gate() {
        let state = TwoQubitState::new_product(QuantumState::new(100), QuantumState::new(200));
        let result = apply_swap(state);

        assert_eq!(result.qubit_0().position(), 200);
        assert_eq!(result.qubit_1().position(), 100);
        assert!(!result.is_entangled());
    }

    #[test]
    fn test_swap_preserves_entanglement() {
        // Create entangled state
        let constraint = CorrelationConstraint::new(192);
        let state = TwoQubitState::new_entangled(QuantumState::new(192), QuantumState::new(0), constraint);

        let result = apply_swap(state);

        assert_eq!(result.qubit_0().position(), 0);
        assert_eq!(result.qubit_1().position(), 192);
        assert!(result.is_entangled());
        assert_eq!(result.correlation_constraint().unwrap().sum_modulo(), 192);
    }

    #[test]
    fn test_cz_gate_11() {
        // |11⟩ → -|11⟩ (phase flip on target)
        let state = TwoQubitState::new_product(QuantumState::new(384), QuantumState::new(384));
        let result = apply_cz(state, 0, 1);

        assert_eq!(result.qubit_0().position(), 384); // Control unchanged
                                                      // Target gets Z gate: 384 + 384 = 768 ≡ 0 (mod 768)
        assert_eq!(result.qubit_1().position(), 0);
        assert!(result.is_entangled());
    }

    #[test]
    fn test_cz_gate_01() {
        // |01⟩ → |01⟩ (no change, control is |0⟩)
        let state = TwoQubitState::new_product(QuantumState::new(0), QuantumState::new(384));
        let result = apply_cz(state, 0, 1);

        assert_eq!(result.qubit_0().position(), 0);
        assert_eq!(result.qubit_1().position(), 384);
        assert!(!result.is_entangled());
    }

    #[test]
    fn test_bell_state_creation() {
        // Create |Φ⁺⟩ = (|00⟩ + |11⟩) / √2
        let mut state = TwoQubitState::new_product(QuantumState::new(0), QuantumState::new(0));

        // H ⊗ I
        state = apply_hadamard_to_qubit(state, 0);
        assert_eq!(state.qubit_0().position(), 192);
        assert_eq!(state.qubit_1().position(), 0);

        // CNOT
        state = apply_cnot(state, 0, 1);
        assert!(state.is_entangled());

        // Verify correlation constraint
        let constraint = state.correlation_constraint().unwrap();
        assert!(constraint.are_positions_correlated(state.qubit_0().position(), state.qubit_1().position()));
    }
}
