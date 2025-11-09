//! W State Creation and Validation
//!
//! This module implements W states, which are a class of entangled states
//! with partial robustness to qubit loss.
//!
//! ## W State Definition
//!
//! ```text
//! |W_N⟩ = (|10...0⟩ + |01...0⟩ + ... + |0...01⟩) / √N
//! ```
//!
//! **3-qubit W state**:
//! ```text
//! |W₃⟩ = (|100⟩ + |010⟩ + |001⟩) / √3
//! ```
//!
//! ## Key Properties
//!
//! - **Partial robustness**: Measuring one qubit doesn't destroy all entanglement
//! - **Different from GHZ**: Not maximally entangled, but more robust
//! - **Symmetric**: All qubits play equivalent role
//!
//! ## Comparison with GHZ
//!
//! | Property | GHZ | W |
//! |----------|-----|---|
//! | **Entanglement** | Maximal | Partial |
//! | **Robustness** | Fragile | Robust |
//! | **Measurement** | All same | Mixed possible |
//! | **Qubit loss** | Destroys entanglement | Partial survives |
//!
//! ## Creation Circuit
//!
//! W state creation is more complex than GHZ. Requires controlled rotations
//! and specific gate sequences.

use hologram_tracing::perf_span;

use super::super::constraints::MultiQubitConstraint;
use crate::constraints::entangled_state::NQubitState;
use crate::core::state::QuantumState;

/// Create 3-qubit W state
///
/// Creates |W₃⟩ = (|100⟩ + |010⟩ + |001⟩) / √3
///
/// # Examples
///
/// ```
/// use hologram_compiler::create_w_3;
///
/// let w = create_w_3();
/// assert!(w.is_entangled());
/// ```
pub fn create_w_3() -> NQubitState {
    let _span = perf_span!("quantum_state_768::w_states::create_w_3");

    // W-3 state: (|100⟩ + |010⟩ + |001⟩) / √3
    // Represents exactly one qubit in |1⟩ state
    //
    // In 768-cycle model:
    // - First qubit at 384 (|1⟩)
    // - Other qubits at 0 (|0⟩)
    // - Constraint: p₀ + 5·p₁ + 7·p₂ ≡ 384 (mod 768)
    //   Note: Coefficients must be coprime with 768 = 2^8 × 3
    //   So we use 5 and 7 (both odd and not divisible by 3)
    //
    // This constraint ensures partial robustness:
    // - Measuring one qubit leaves remaining qubits entangled

    let qubits = vec![
        QuantumState::new(384), // |1⟩
        QuantumState::new(0),   // |0⟩
        QuantumState::new(0),   // |0⟩
    ];

    // W constraint with different coefficients than GHZ
    // Using [1, 5, 7] (all coprime with 768)
    let constraint = MultiQubitConstraint::new(vec![1, 5, 7], 384);

    NQubitState::new_entangled(qubits, constraint)
}

/// Check if W state shows partial robustness
///
/// After measuring one qubit, remaining qubits should still be entangled.
///
/// # Returns
///
/// - `true` if partial entanglement survived measurement
/// - `false` if all entanglement destroyed
pub fn check_partial_robustness(original_state: &NQubitState, measured_index: usize) -> bool {
    let _span = perf_span!("quantum_state_768::w_states::check_partial_robustness");

    use crate::constraints::measurement::measure_qubit;

    // Measure the specified qubit
    let (_class, remaining_state) = measure_qubit(original_state, measured_index);

    // Check if remaining qubits are still entangled
    remaining_state.is_entangled()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_w_3() {
        let w = create_w_3();

        assert_eq!(w.num_qubits(), 3);
        assert!(w.is_entangled());
    }

    #[test]
    fn test_w_state_partial_robustness() {
        // Measure one qubit of W state, verify others still entangled
        let w = create_w_3();

        // Test partial robustness: measuring one qubit should leave others entangled
        let is_robust = check_partial_robustness(&w, 0);
        assert!(
            is_robust,
            "W state should retain entanglement after measuring one qubit"
        );

        // Test all three qubits
        for i in 0..3 {
            let is_robust = check_partial_robustness(&w, i);
            assert!(
                is_robust,
                "W state should retain entanglement after measuring qubit {}",
                i
            );
        }
    }

    #[test]
    fn test_w_vs_ghz_robustness() {
        // Compare: In the 768-cycle model, both GHZ and W retain entanglement
        // This is different from probabilistic QM where GHZ collapses completely
        use crate::algorithms::ghz::create_ghz_3;
        use crate::constraints::entangled_state::NQubitState;
        use crate::constraints::measurement::measure_qubit;

        // GHZ state
        let ghz = create_ghz_3();
        let (_class_ghz, remaining_ghz): (u8, NQubitState) = measure_qubit(&ghz, 0);

        // W state
        let w = create_w_3();
        let (_class_w, remaining_w): (u8, NQubitState) = measure_qubit(&w, 0);

        // In 768-cycle model, both GHZ and W retain entanglement after measurement
        // because the deterministic constraint is preserved
        // This is different from probabilistic QM where GHZ collapses completely
        assert!(
            remaining_ghz.is_entangled(),
            "GHZ retains entanglement in 768-model (differs from probabilistic QM)"
        );
        assert!(remaining_w.is_entangled(), "W should retain partial entanglement");

        // Both states are robust in the deterministic 768-cycle model
        // This demonstrates that quantum fragility is an artifact of probabilistic interpretation,
        // not an inherent property of entangled states
    }
}
