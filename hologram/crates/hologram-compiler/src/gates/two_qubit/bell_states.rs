//! Bell State Creation and Manipulation
//!
//! This module implements the four maximally entangled Bell states, which are
//! the foundation of quantum information theory and the key evidence for
//! quantum entanglement.
//!
//! ## The Four Bell States
//!
//! ```text
//! |Φ⁺⟩ = (|00⟩ + |11⟩) / √2   "Phi-plus"
//! |Φ⁻⟩ = (|00⟩ - |11⟩) / √2   "Phi-minus"
//! |Ψ⁺⟩ = (|01⟩ + |10⟩) / √2   "Psi-plus"
//! |Ψ⁻⟩ = (|01⟩ - |10⟩) / √2   "Psi-minus"
//! ```
//!
//! ## Creation Circuits
//!
//! Each Bell state is created from |00⟩ using a specific gate sequence:
//!
//! ```text
//! |Φ⁺⟩: H ⊗ I → CNOT
//! |Φ⁻⟩: H ⊗ I → CNOT → Z ⊗ I
//! |Ψ⁺⟩: H ⊗ I → CNOT → X ⊗ I
//! |Ψ⁻⟩: H ⊗ I → CNOT → X ⊗ I → Z ⊗ I
//! ```
//!
//! ## Measurement Correlations
//!
//! Bell states exhibit perfect correlation/anti-correlation when measured:
//!
//! ```text
//! |Φ⁺⟩: Both qubits always measure the same (00 or 11)
//! |Φ⁻⟩: Both qubits always measure the same (00 or 11)
//! |Ψ⁺⟩: Both qubits always measure different (01 or 10)
//! |Ψ⁻⟩: Both qubits always measure different (01 or 10)
//! ```
//!
//! ## 768-Cycle Interpretation
//!
//! In the geometric model, Bell states are NOT "both values simultaneously" -
//! they are specific correlated positions in the 768-cycle:
//!
//! - Entanglement = correlation constraint p_A + p_B ≡ k (mod 768)
//! - Measurement doesn't "collapse" - it reads the correlated positions
//! - 100% correlation is deterministic given positions, not probabilistic
//!
//! ## Example
//!
//! ```
//! use hologram_compiler::create_bell_phi_plus;
//! use hologram_compiler::{measure_quantum_state, measure_two_qubit_state};
//!
//! // Create maximally entangled state
//! let bell_state = create_bell_phi_plus();
//! assert!(bell_state.is_entangled());
//!
//! // Measure both qubits
//! let (class_0, class_1) = measure_two_qubit_state(&bell_state);
//!
//! // For |Φ⁺⟩, outcomes are always correlated
//! // (both |0⟩ or both |1⟩)
//! ```

use hologram_tracing::perf_span;

use super::gates::{apply_cnot, apply_hadamard_to_qubit, apply_pauli_x_to_qubit, apply_pauli_z_to_qubit};
use super::state::TwoQubitState;
use crate::core::state::QuantumState;

/// Bell state type enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BellState {
    /// |Φ⁺⟩ = (|00⟩ + |11⟩) / √2
    PhiPlus,
    /// |Φ⁻⟩ = (|00⟩ - |11⟩) / √2
    PhiMinus,
    /// |Ψ⁺⟩ = (|01⟩ + |10⟩) / √2
    PsiPlus,
    /// |Ψ⁻⟩ = (|01⟩ - |10⟩) / √2
    PsiMinus,
}

impl BellState {
    /// Get the name of this Bell state
    pub fn name(&self) -> &'static str {
        match self {
            BellState::PhiPlus => "Φ⁺",
            BellState::PhiMinus => "Φ⁻",
            BellState::PsiPlus => "Ψ⁺",
            BellState::PsiMinus => "Ψ⁻",
        }
    }

    /// Get the correlation type for this Bell state
    ///
    /// Returns true for same (|00⟩/|11⟩), false for different (|01⟩/|10⟩)
    pub fn has_same_correlation(&self) -> bool {
        matches!(self, BellState::PhiPlus | BellState::PhiMinus)
    }

    /// Create this Bell state from |00⟩
    pub fn create(&self) -> TwoQubitState {
        match self {
            BellState::PhiPlus => create_bell_phi_plus(),
            BellState::PhiMinus => create_bell_phi_minus(),
            BellState::PsiPlus => create_bell_psi_plus(),
            BellState::PsiMinus => create_bell_psi_minus(),
        }
    }
}

/// Create the |Φ⁺⟩ Bell state: (|00⟩ + |11⟩) / √2
///
/// This is the most commonly used maximally entangled state.
/// Created by applying Hadamard to first qubit, then CNOT.
///
/// # Circuit
///
/// ```text
/// |0⟩ ──H──●── |Φ⁺⟩
///          │
/// |0⟩ ─────⊕──
/// ```
///
/// # Example
///
/// ```
/// use hologram_compiler::create_bell_phi_plus;
///
/// let bell = create_bell_phi_plus();
/// assert!(bell.is_entangled());
/// assert_eq!(bell.qubit_0().position(), 192); // After H gate
/// ```
pub fn create_bell_phi_plus() -> TwoQubitState {
    let _span = perf_span!("create_bell_phi_plus");

    // Start with |00⟩
    let mut state = TwoQubitState::new_product(QuantumState::new(0), QuantumState::new(0));

    // Apply H ⊗ I (Hadamard on first qubit)
    state = apply_hadamard_to_qubit(state, 0);

    // Apply CNOT (control=0, target=1)
    state = apply_cnot(state, 0, 1);

    state
}

/// Create the |Φ⁻⟩ Bell state: (|00⟩ - |11⟩) / √2
///
/// Similar to |Φ⁺⟩ but with opposite phase between |00⟩ and |11⟩.
/// Created by applying H, CNOT, then Z to the first qubit.
///
/// # Circuit
///
/// ```text
/// |0⟩ ──H──●──Z── |Φ⁻⟩
///          │
/// |0⟩ ─────⊕─────
/// ```
///
/// # Example
///
/// ```
/// use hologram_compiler::create_bell_phi_minus;
///
/// let bell = create_bell_phi_minus();
/// assert!(bell.is_entangled());
/// ```
pub fn create_bell_phi_minus() -> TwoQubitState {
    let _span = perf_span!("create_bell_phi_minus");

    // Start with |Φ⁺⟩
    let mut state = create_bell_phi_plus();

    // Apply Z ⊗ I (Z gate on first qubit)
    state = apply_pauli_z_to_qubit(state, 0);

    state
}

/// Create the |Ψ⁺⟩ Bell state: (|01⟩ + |10⟩) / √2
///
/// This state has anti-correlated measurements: when one qubit is |0⟩,
/// the other is always |1⟩, and vice versa.
///
/// # Circuit
///
/// ```text
/// |0⟩ ──H────●── |Ψ⁺⟩
///            │
/// |0⟩ ──X────⊕──
/// ```
///
/// # Example
///
/// ```
/// use hologram_compiler::create_bell_psi_plus;
///
/// let bell = create_bell_psi_plus();
/// assert!(bell.is_entangled());
/// ```
pub fn create_bell_psi_plus() -> TwoQubitState {
    let _span = perf_span!("create_bell_psi_plus");

    // Start with |00⟩
    let mut state = TwoQubitState::new_product(QuantumState::new(0), QuantumState::new(0));

    // Apply X to second qubit: |01⟩
    state = apply_pauli_x_to_qubit(state, 1);

    // Apply H ⊗ I (Hadamard on first qubit)
    state = apply_hadamard_to_qubit(state, 0);

    // Apply CNOT (control=0, target=1)
    state = apply_cnot(state, 0, 1);

    state
}

/// Create the |Ψ⁻⟩ Bell state: (|01⟩ - |10⟩) / √2
///
/// Anti-correlated like |Ψ⁺⟩ but with opposite phase.
///
/// # Circuit
///
/// ```text
/// |0⟩ ──X──H──●──Z── |Ψ⁻⟩
///             │
/// |0⟩ ────────⊕─────
/// ```
///
/// # Example
///
/// ```
/// use hologram_compiler::create_bell_psi_minus;
///
/// let bell = create_bell_psi_minus();
/// assert!(bell.is_entangled());
/// ```
pub fn create_bell_psi_minus() -> TwoQubitState {
    let _span = perf_span!("create_bell_psi_minus");

    // Start with |Ψ⁺⟩
    let mut state = create_bell_psi_plus();

    // Apply Z ⊗ I (Z gate on first qubit)
    state = apply_pauli_z_to_qubit(state, 0);

    state
}

/// Measure both qubits of a two-qubit state
///
/// Returns a tuple of (class_0, class_1) representing the measurement outcomes.
/// For entangled states, measuring one qubit determines the other due to the
/// correlation constraint.
///
/// # Example
///
/// ```
/// use hologram_compiler::{create_bell_phi_plus, measure_two_qubit_state};
///
/// let bell = create_bell_phi_plus();
/// let (class_0, class_1) = measure_two_qubit_state(&bell);
///
/// // For |Φ⁺⟩, both outcomes should be correlated
/// // (both measure to similar classes due to position correlation)
/// ```
pub fn measure_two_qubit_state(state: &TwoQubitState) -> (u8, u8) {
    use crate::core::measurement::measure_quantum_state;

    let _span = perf_span!("measure_two_qubit_state", entangled = state.is_entangled());

    let class_0 = measure_quantum_state(state.qubit_0());
    let class_1 = measure_quantum_state(state.qubit_1());

    (class_0, class_1)
}

/// Check if two measurement outcomes satisfy the correlation for a Bell state
///
/// For Φ states (PhiPlus, PhiMinus): outcomes should be same
/// For Ψ states (PsiPlus, PsiMinus): outcomes should be different
///
/// Note: In the 768-cycle model, "same" means both qubits in similar computational
/// state regions ([0, 384) or [384, 768))
pub fn check_bell_correlation(bell_type: BellState, outcome_0: bool, outcome_1: bool) -> bool {
    match bell_type {
        BellState::PhiPlus | BellState::PhiMinus => {
            // Same correlation: both |0⟩ or both |1⟩
            outcome_0 == outcome_1
        }
        BellState::PsiPlus | BellState::PsiMinus => {
            // Different correlation: one |0⟩, one |1⟩
            outcome_0 != outcome_1
        }
    }
}

/// Determine computational basis from position
///
/// Returns true for |1⟩ (position >= 384), false for |0⟩ (position < 384)
pub fn is_computational_one_from_position(position: u16) -> bool {
    position >= 384
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_phi_plus_creation() {
        let state = create_bell_phi_plus();

        assert!(state.is_entangled());
        assert_eq!(state.qubit_0().position(), 192); // After H gate
    }

    #[test]
    fn test_phi_minus_creation() {
        let state = create_bell_phi_minus();

        assert!(state.is_entangled());
        // After H, CNOT, Z sequence
    }

    #[test]
    fn test_psi_plus_creation() {
        let state = create_bell_psi_plus();

        assert!(state.is_entangled());
    }

    #[test]
    fn test_psi_minus_creation() {
        let state = create_bell_psi_minus();

        assert!(state.is_entangled());
    }

    #[test]
    fn test_bell_state_enum() {
        assert_eq!(BellState::PhiPlus.name(), "Φ⁺");
        assert_eq!(BellState::PhiMinus.name(), "Φ⁻");
        assert_eq!(BellState::PsiPlus.name(), "Ψ⁺");
        assert_eq!(BellState::PsiMinus.name(), "Ψ⁻");
    }

    #[test]
    fn test_correlation_types() {
        assert!(BellState::PhiPlus.has_same_correlation());
        assert!(BellState::PhiMinus.has_same_correlation());
        assert!(!BellState::PsiPlus.has_same_correlation());
        assert!(!BellState::PsiMinus.has_same_correlation());
    }

    #[test]
    fn test_measure_two_qubit_state() {
        let state = create_bell_phi_plus();
        let (class_0, class_1) = measure_two_qubit_state(&state);

        // Both measurements should be valid classes
        assert!(class_0 < 96);
        assert!(class_1 < 96);
    }

    #[test]
    fn test_is_computational_one_from_position() {
        assert!(!is_computational_one_from_position(0));
        assert!(!is_computational_one_from_position(100));
        assert!(!is_computational_one_from_position(383));
        assert!(is_computational_one_from_position(384));
        assert!(is_computational_one_from_position(500));
        assert!(is_computational_one_from_position(767));
    }

    #[test]
    fn test_check_bell_correlation_phi() {
        // Φ states: same outcomes
        assert!(check_bell_correlation(BellState::PhiPlus, false, false));
        assert!(check_bell_correlation(BellState::PhiPlus, true, true));
        assert!(!check_bell_correlation(BellState::PhiPlus, false, true));
        assert!(!check_bell_correlation(BellState::PhiPlus, true, false));
    }

    #[test]
    fn test_check_bell_correlation_psi() {
        // Ψ states: different outcomes
        assert!(!check_bell_correlation(BellState::PsiPlus, false, false));
        assert!(!check_bell_correlation(BellState::PsiPlus, true, true));
        assert!(check_bell_correlation(BellState::PsiPlus, false, true));
        assert!(check_bell_correlation(BellState::PsiPlus, true, false));
    }

    #[test]
    fn test_all_bell_states_create() {
        for bell_type in [
            BellState::PhiPlus,
            BellState::PhiMinus,
            BellState::PsiPlus,
            BellState::PsiMinus,
        ] {
            let state = bell_type.create();
            assert!(state.is_entangled(), "Bell state {:?} should be entangled", bell_type);
        }
    }
}
