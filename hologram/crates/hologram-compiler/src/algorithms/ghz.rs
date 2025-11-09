//! GHZ State Creation and Validation
//!
//! This module implements Greenberger-Horne-Zeilinger (GHZ) states, which are
//! maximally entangled N-qubit states showing perfect N-way correlation.
//!
//! ## GHZ State Definition
//!
//! ```text
//! |GHZ_N⟩ = (|00...0⟩ + |11...1⟩) / √2
//! ```
//!
//! **Properties**:
//! - Maximally entangled (all qubits correlated)
//! - Measurement gives either all |0⟩ or all |1⟩ (never mixed)
//! - 50/50 probability distribution
//! - Fragile: measuring one qubit destroys all entanglement
//!
//! ## Examples
//!
//! **3-qubit GHZ**:
//! ```text
//! |GHZ₃⟩ = (|000⟩ + |111⟩) / √2
//! ```
//!
//! **4-qubit GHZ**:
//! ```text
//! |GHZ₄⟩ = (|0000⟩ + |1111⟩) / √2
//! ```
//!
//! ## Creation Circuit
//!
//! Standard circuit for N-qubit GHZ:
//! ```text
//! 1. Start with |00...0⟩
//! 2. Apply H to first qubit: creates |+⟩|00...0⟩
//! 3. Apply CNOT cascade: CNOT(0→1), CNOT(1→2), ..., CNOT(N-2→N-1)
//! ```
//!
//! In 768-cycle model:
//! ```text
//! 1. All qubits at p=0
//! 2. H on q0: p₀ = 192
//! 3. CNOT cascade creates constraint: p₀ + p₁ + ... + p_{N-1} ≡ 192 (mod 768)
//! ```

use hologram_tracing::perf_span;

use crate::constraints::constraint::MultiQubitConstraint;
use crate::constraints::entangled_state::NQubitState;
use crate::core::state::QuantumState;

/// Create 3-qubit GHZ state
///
/// Circuit: H ⊗ I ⊗ I → CNOT(0,1) → CNOT(1,2)
///
/// # Examples
///
/// ```
/// use hologram_compiler::create_ghz_3;
///
/// let ghz = create_ghz_3();
/// assert!(ghz.is_entangled());
/// assert_eq!(ghz.num_qubits(), 3);
/// ```
pub fn create_ghz_3() -> NQubitState {
    let _span = perf_span!("quantum_state_768::ghz_states::create_ghz_3");

    // Create 3 qubits: first at position 192 (after H gate), others at 0
    let qubits = vec![
        QuantumState::new(192), // H applied to |0⟩
        QuantumState::new(0),
        QuantumState::new(0),
    ];

    // GHZ constraint: p₀ + p₁ + p₂ ≡ 192 (mod 768)
    // This represents the entanglement created by CNOT cascade
    let constraint = MultiQubitConstraint::new(vec![1, 1, 1], 192);

    NQubitState::new_entangled(qubits, constraint)
}

/// Create 4-qubit GHZ state
///
/// Circuit: H ⊗ I^3 → CNOT(0,1) → CNOT(1,2) → CNOT(2,3)
pub fn create_ghz_4() -> NQubitState {
    let _span = perf_span!("quantum_state_768::ghz_states::create_ghz_4");

    // Create 4 qubits: first at position 192 (after H gate), others at 0
    let qubits = vec![
        QuantumState::new(192), // H applied to |0⟩
        QuantumState::new(0),
        QuantumState::new(0),
        QuantumState::new(0),
    ];

    // GHZ constraint: p₀ + p₁ + p₂ + p₃ ≡ 192 (mod 768)
    let constraint = MultiQubitConstraint::new(vec![1, 1, 1, 1], 192);

    NQubitState::new_entangled(qubits, constraint)
}

/// Create N-qubit GHZ state
///
/// Generic GHZ creation for arbitrary N.
///
/// # Arguments
///
/// * `n` - Number of qubits (must be >= 2)
///
/// # Panics
///
/// Panics if n < 2
pub fn create_ghz_n(n: usize) -> NQubitState {
    let _span = perf_span!("quantum_state_768::ghz_states::create_ghz_n", num_qubits = n);

    assert!(n >= 2, "GHZ state requires at least 2 qubits");

    // Create N qubits: first at position 192 (after H gate), others at 0
    let mut qubits = vec![QuantumState::new(192)]; // H applied to first qubit
    for _ in 1..n {
        qubits.push(QuantumState::new(0));
    }

    // GHZ constraint: p₀ + p₁ + ... + p_{N-1} ≡ 192 (mod 768)
    // All coefficients are 1
    let coefficients = vec![1; n];
    let constraint = MultiQubitConstraint::new(coefficients, 192);

    NQubitState::new_entangled(qubits, constraint)
}

/// Check if measurements show perfect N-way correlation
///
/// For GHZ states, all qubits should measure to same computational basis.
///
/// # Returns
///
/// - `true` if all measurements are same (all |0⟩ or all |1⟩)
/// - `false` if measurements are mixed
pub fn check_ghz_correlation(measurements: &[bool]) -> bool {
    let _span = perf_span!(
        "quantum_state_768::ghz_states::check_correlation",
        num_measurements = measurements.len()
    );

    if measurements.is_empty() {
        return true;
    }

    // Check if all measurements are the same (all true or all false)
    let first = measurements[0];
    measurements.iter().all(|&m| m == first)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_ghz_3() {
        let ghz = create_ghz_3();

        assert_eq!(ghz.num_qubits(), 3);
        assert!(ghz.is_entangled());

        // First qubit should be at 192 (after H gate)
        assert_eq!(ghz.qubit(0).position(), 192);
    }

    #[test]
    fn test_create_ghz_4() {
        let ghz = create_ghz_4();

        assert_eq!(ghz.num_qubits(), 4);
        assert!(ghz.is_entangled());
    }

    #[test]
    fn test_create_ghz_n() {
        for n in 2..=8 {
            let ghz = create_ghz_n(n);
            assert_eq!(ghz.num_qubits(), n);
            assert!(ghz.is_entangled());
        }
    }

    #[test]

    fn test_ghz_3_correlation() {
        // Measure GHZ-3, verify perfect correlation
        // In the 768-cycle deterministic model, measurement gives consistent results
        use crate::measure_qubits;

        let ghz = create_ghz_3();

        // Measure all three qubits
        let (classes, _remaining) = measure_qubits(&ghz, &[0, 1, 2]);

        // Convert classes to computational basis: class < 48 is |0⟩, class >= 48 is |1⟩
        let outcomes: Vec<bool> = classes.iter().map(|&c| c >= 48).collect();

        // Verify perfect correlation using check_ghz_correlation helper
        assert!(
            check_ghz_correlation(&outcomes),
            "GHZ-3 state must show perfect 3-way correlation"
        );

        // All qubits should measure to the same value
        let first = outcomes[0];
        let all_same = outcomes.iter().all(|&o| o == first);
        assert!(all_same, "All qubits in GHZ-3 must measure to same computational basis");
    }

    #[test]

    fn test_ghz_4_correlation() {
        // Measure GHZ-4, verify perfect correlation
        // In the 768-cycle deterministic model, measurement gives consistent results
        use crate::measure_qubits;

        let ghz = create_ghz_4();

        // Measure all four qubits
        let (classes, _remaining) = measure_qubits(&ghz, &[0, 1, 2, 3]);

        // Convert classes to computational basis: class < 48 is |0⟩, class >= 48 is |1⟩
        let outcomes: Vec<bool> = classes.iter().map(|&c| c >= 48).collect();

        // Verify perfect correlation using check_ghz_correlation helper
        assert!(
            check_ghz_correlation(&outcomes),
            "GHZ-4 state must show perfect 4-way correlation"
        );

        // All qubits should measure to the same value
        let first = outcomes[0];
        let all_same = outcomes.iter().all(|&o| o == first);
        assert!(all_same, "All qubits in GHZ-4 must measure to same computational basis");
    }

    #[test]
    fn test_check_correlation_same() {
        assert!(check_ghz_correlation(&[true, true, true]));
        assert!(check_ghz_correlation(&[false, false, false]));
    }

    #[test]
    fn test_check_correlation_mixed() {
        assert!(!check_ghz_correlation(&[true, false, true]));
        assert!(!check_ghz_correlation(&[true, true, false]));
    }
}
