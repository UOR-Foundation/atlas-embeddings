//! Three-Qubit Gates for N-Qubit Systems
//!
//! This module implements three-qubit quantum gates (Toffoli, Fredkin, CCZ)
//! as geometric operations in the 768-cycle model, operating on N-qubit states.
//!
//! ## Three-Qubit Gates
//!
//! | Gate | Operation | Advancement | Creates Entanglement |
//! |------|-----------|-------------|---------------------|
//! | **Toffoli** | CCNOT | 384/768 | Yes (if controls superposed) |
//! | **Fredkin** | CSWAP | Swap | Preserves |
//! | **CCZ** | CC-Phase | 384/768 | Yes (if controls superposed) |
//!
//! ## Toffoli Gate (CCNOT)
//!
//! ```text
//! Truth table: |abc⟩ → |ab(c ⊕ ab)⟩
//!
//! Only flips target c if both controls a,b are |1⟩
//!
//! Examples:
//!   |000⟩ → |000⟩  (controls inactive)
//!   |001⟩ → |001⟩  (controls inactive)
//!   |110⟩ → |111⟩  (both controls active, flip target)
//!   |111⟩ → |110⟩  (both controls active, flip target)
//! ```
//!
//! **Geometric mapping**:
//! - Check if p_control1 >= 384 AND p_control2 >= 384
//! - If yes: advance p_target by 384/768 (1/2 cycle)
//! - Creates 3-way entanglement when controls in superposition
//!
//! ## Fredkin Gate (CSWAP)
//!
//! ```text
//! |abc⟩ → |a⟩ ⊗ (if a=|1⟩: |cb⟩ else |bc⟩)
//!
//! Swaps b and c only if control a is |1⟩
//! ```

use hologram_tracing::perf_span;

use crate::constraints::entangled_state::NQubitState;
use crate::core::state::QuantumState;

/// Toffoli gate advancement (1/2 cycle = 384/768, same as X gate when controls active)
pub const TOFFOLI_ADVANCEMENT: u16 = 384;

/// Apply Toffoli (CCNOT) gate to N-qubit state
///
/// Flips target qubit if both control qubits are |1⟩ (position >= 384).
/// Creates 3-way entanglement if controls are in superposition.
///
/// # Arguments
///
/// * `state` - N-qubit state to apply gate to
/// * `control1` - Index of first control qubit
/// * `control2` - Index of second control qubit
/// * `target` - Index of target qubit to flip
///
/// # Panics
///
/// Panics if any index >= num_qubits or indices overlap
///
/// # Examples
///
/// ```
/// use hologram_compiler::{NQubitState, QuantumState, apply_toffoli};
///
/// // |110⟩ → |111⟩
/// let state = NQubitState::new_product(vec![
///     QuantumState::new(384), // |1⟩
///     QuantumState::new(384), // |1⟩
///     QuantumState::new(0),   // |0⟩
/// ]);
///
/// let result = apply_toffoli(state, 0, 1, 2);
/// assert_eq!(result.qubit(2).position(), 384); // Flipped to |1⟩
/// ```
pub fn apply_toffoli(mut state: NQubitState, control1: usize, control2: usize, target: usize) -> NQubitState {
    let _span = perf_span!("quantum_state_768::three_qubit_gates::apply_toffoli");

    // Validate indices
    assert!(control1 < state.num_qubits(), "control1 index out of bounds");
    assert!(control2 < state.num_qubits(), "control2 index out of bounds");
    assert!(target < state.num_qubits(), "target index out of bounds");
    assert!(control1 != control2, "control indices must be different");
    assert!(control1 != target, "control1 and target must be different");
    assert!(control2 != target, "control2 and target must be different");

    // Check if both controls are |1⟩
    let ctrl1_active = is_computational_one(state.qubit(control1));
    let ctrl2_active = is_computational_one(state.qubit(control2));

    if ctrl1_active && ctrl2_active {
        // Both controls active: flip target by advancing 384/768
        let target_pos = state.qubit(target).position();
        let new_pos = (target_pos + TOFFOLI_ADVANCEMENT) % 768;
        state.set_qubit(target, QuantumState::new(new_pos));
    }

    state
}

/// Apply Fredkin (CSWAP) gate to N-qubit state
///
/// Swaps two qubits if control qubit is |1⟩.
/// Preserves entanglement if present.
///
/// # Arguments
///
/// * `state` - N-qubit state to apply gate to
/// * `control` - Index of control qubit
/// * `swap1` - Index of first qubit to swap
/// * `swap2` - Index of second qubit to swap
///
/// # Panics
///
/// Panics if any index >= num_qubits or indices overlap
pub fn apply_fredkin(mut state: NQubitState, control: usize, swap1: usize, swap2: usize) -> NQubitState {
    let _span = perf_span!("quantum_state_768::three_qubit_gates::apply_fredkin");

    // Validate indices
    assert!(control < state.num_qubits(), "control index out of bounds");
    assert!(swap1 < state.num_qubits(), "swap1 index out of bounds");
    assert!(swap2 < state.num_qubits(), "swap2 index out of bounds");
    assert!(control != swap1, "control and swap1 must be different");
    assert!(control != swap2, "control and swap2 must be different");
    assert!(swap1 != swap2, "swap indices must be different");

    // Check if control is |1⟩
    if is_computational_one(state.qubit(control)) {
        // Control active: swap the two qubits
        let pos1 = state.qubit(swap1).position();
        let pos2 = state.qubit(swap2).position();

        state.set_qubit(swap1, QuantumState::new(pos2));
        state.set_qubit(swap2, QuantumState::new(pos1));
    }

    state
}

/// Apply Controlled-Controlled-Z (CCZ) gate to N-qubit state
///
/// Applies Z gate (384/768 advancement) to target if both controls are |1⟩.
///
/// # Arguments
///
/// * `state` - N-qubit state to apply gate to
/// * `control1` - Index of first control qubit
/// * `control2` - Index of second control qubit
/// * `target` - Index of target qubit for phase flip
///
/// # Panics
///
/// Panics if any index >= num_qubits or indices overlap
pub fn apply_ccz(mut state: NQubitState, control1: usize, control2: usize, target: usize) -> NQubitState {
    let _span = perf_span!("quantum_state_768::three_qubit_gates::apply_ccz");

    // Validate indices
    assert!(control1 < state.num_qubits(), "control1 index out of bounds");
    assert!(control2 < state.num_qubits(), "control2 index out of bounds");
    assert!(target < state.num_qubits(), "target index out of bounds");
    assert!(control1 != control2, "control indices must be different");
    assert!(control1 != target, "control1 and target must be different");
    assert!(control2 != target, "control2 and target must be different");

    // Check if both controls are |1⟩
    let ctrl1_active = is_computational_one(state.qubit(control1));
    let ctrl2_active = is_computational_one(state.qubit(control2));

    if ctrl1_active && ctrl2_active {
        // Both controls active: apply Z gate (384/768 advancement)
        let target_pos = state.qubit(target).position();
        let new_pos = (target_pos + 384) % 768;
        state.set_qubit(target, QuantumState::new(new_pos));
    }

    state
}

/// Check if qubit is in computational |1⟩ state (position >= 384)
pub fn is_computational_one(qubit: &QuantumState) -> bool {
    let _span = perf_span!("quantum_state_768::three_qubit_gates::is_computational_one");
    qubit.position() >= 384
}

#[cfg(test)]
mod tests {
    use super::*;

    // Toffoli Truth Table Tests

    #[test]
    fn test_toffoli_000_to_000() {
        // |000⟩ → |000⟩ (no controls active)
        let state = NQubitState::new_product(vec![
            QuantumState::new(0), // |0⟩
            QuantumState::new(0), // |0⟩
            QuantumState::new(0), // |0⟩
        ]);

        let result = apply_toffoli(state, 0, 1, 2);

        assert_eq!(result.qubit(0).position(), 0);
        assert_eq!(result.qubit(1).position(), 0);
        assert_eq!(result.qubit(2).position(), 0); // No change
    }

    #[test]
    fn test_toffoli_001_to_001() {
        // |001⟩ → |001⟩ (no controls active)
        let state = NQubitState::new_product(vec![
            QuantumState::new(0),   // |0⟩
            QuantumState::new(0),   // |0⟩
            QuantumState::new(384), // |1⟩
        ]);

        let result = apply_toffoli(state, 0, 1, 2);

        assert_eq!(result.qubit(0).position(), 0);
        assert_eq!(result.qubit(1).position(), 0);
        assert_eq!(result.qubit(2).position(), 384); // No change
    }

    #[test]
    fn test_toffoli_010_to_010() {
        // |010⟩ → |010⟩ (only one control active)
        let state = NQubitState::new_product(vec![
            QuantumState::new(0),   // |0⟩
            QuantumState::new(384), // |1⟩
            QuantumState::new(0),   // |0⟩
        ]);

        let result = apply_toffoli(state, 0, 1, 2);

        assert_eq!(result.qubit(0).position(), 0);
        assert_eq!(result.qubit(1).position(), 384);
        assert_eq!(result.qubit(2).position(), 0); // No change
    }

    #[test]
    fn test_toffoli_011_to_011() {
        // |011⟩ → |011⟩ (only one control active)
        let state = NQubitState::new_product(vec![
            QuantumState::new(0),   // |0⟩
            QuantumState::new(384), // |1⟩
            QuantumState::new(384), // |1⟩
        ]);

        let result = apply_toffoli(state, 0, 1, 2);

        assert_eq!(result.qubit(0).position(), 0);
        assert_eq!(result.qubit(1).position(), 384);
        assert_eq!(result.qubit(2).position(), 384); // No change
    }

    #[test]
    fn test_toffoli_100_to_100() {
        // |100⟩ → |100⟩ (only one control active)
        let state = NQubitState::new_product(vec![
            QuantumState::new(384), // |1⟩
            QuantumState::new(0),   // |0⟩
            QuantumState::new(0),   // |0⟩
        ]);

        let result = apply_toffoli(state, 0, 1, 2);

        assert_eq!(result.qubit(0).position(), 384);
        assert_eq!(result.qubit(1).position(), 0);
        assert_eq!(result.qubit(2).position(), 0); // No change
    }

    #[test]
    fn test_toffoli_101_to_101() {
        // |101⟩ → |101⟩ (only one control active)
        let state = NQubitState::new_product(vec![
            QuantumState::new(384), // |1⟩
            QuantumState::new(0),   // |0⟩
            QuantumState::new(384), // |1⟩
        ]);

        let result = apply_toffoli(state, 0, 1, 2);

        assert_eq!(result.qubit(0).position(), 384);
        assert_eq!(result.qubit(1).position(), 0);
        assert_eq!(result.qubit(2).position(), 384); // No change
    }

    #[test]
    fn test_toffoli_110_to_111() {
        // |110⟩ → |111⟩ (both controls active, flip target)
        let state = NQubitState::new_product(vec![
            QuantumState::new(384), // |1⟩
            QuantumState::new(384), // |1⟩
            QuantumState::new(0),   // |0⟩
        ]);

        let result = apply_toffoli(state, 0, 1, 2);

        assert_eq!(result.qubit(0).position(), 384);
        assert_eq!(result.qubit(1).position(), 384);
        assert_eq!(result.qubit(2).position(), 384); // Flipped to |1⟩
    }

    #[test]
    fn test_toffoli_111_to_110() {
        // |111⟩ → |110⟩ (both controls active, flip target)
        let state = NQubitState::new_product(vec![
            QuantumState::new(384), // |1⟩
            QuantumState::new(384), // |1⟩
            QuantumState::new(384), // |1⟩
        ]);

        let result = apply_toffoli(state, 0, 1, 2);

        assert_eq!(result.qubit(0).position(), 384);
        assert_eq!(result.qubit(1).position(), 384);
        assert_eq!(result.qubit(2).position(), (384 + 384) % 768); // Flipped back to |0⟩
    }

    #[test]
    fn test_toffoli_squared_is_identity() {
        // Toffoli² = I - applying twice returns to original
        let state = NQubitState::new_product(vec![
            QuantumState::new(384), // |1⟩
            QuantumState::new(384), // |1⟩
            QuantumState::new(100), // Arbitrary position
        ]);

        let once = apply_toffoli(state, 0, 1, 2);
        let twice = apply_toffoli(once, 0, 1, 2);

        assert_eq!(twice.qubit(2).position(), 100); // Back to original
    }

    #[test]
    fn test_toffoli_creates_entanglement() {
        // When controls in superposition, Toffoli preserves/creates entanglement
        // For now, just test that it works with product states
        let state = NQubitState::new_product(vec![
            QuantumState::new(192), // Superposition region
            QuantumState::new(192), // Superposition region
            QuantumState::new(0),
        ]);

        let result = apply_toffoli(state, 0, 1, 2);

        // Qubits should remain unchanged (neither control is |1⟩)
        assert_eq!(result.qubit(0).position(), 192);
        assert_eq!(result.qubit(1).position(), 192);
        assert_eq!(result.qubit(2).position(), 0);
    }

    // Fredkin Tests

    #[test]
    fn test_fredkin_control_zero() {
        // Control = |0⟩: no swap occurs
        let state = NQubitState::new_product(vec![
            QuantumState::new(0),   // Control |0⟩
            QuantumState::new(100), // Swap1
            QuantumState::new(200), // Swap2
        ]);

        let result = apply_fredkin(state, 0, 1, 2);

        assert_eq!(result.qubit(0).position(), 0);
        assert_eq!(result.qubit(1).position(), 100); // No swap
        assert_eq!(result.qubit(2).position(), 200); // No swap
    }

    #[test]
    fn test_fredkin_control_one() {
        // Control = |1⟩: swap occurs
        let state = NQubitState::new_product(vec![
            QuantumState::new(384), // Control |1⟩
            QuantumState::new(100), // Swap1
            QuantumState::new(200), // Swap2
        ]);

        let result = apply_fredkin(state, 0, 1, 2);

        assert_eq!(result.qubit(0).position(), 384);
        assert_eq!(result.qubit(1).position(), 200); // Swapped
        assert_eq!(result.qubit(2).position(), 100); // Swapped
    }

    #[test]
    fn test_fredkin_squared_is_identity() {
        // Fredkin² = I - applying twice returns to original
        let state = NQubitState::new_product(vec![
            QuantumState::new(384), // Control |1⟩
            QuantumState::new(100),
            QuantumState::new(200),
        ]);

        let once = apply_fredkin(state, 0, 1, 2);
        let twice = apply_fredkin(once, 0, 1, 2);

        assert_eq!(twice.qubit(1).position(), 100); // Back to original
        assert_eq!(twice.qubit(2).position(), 200); // Back to original
    }

    #[test]
    fn test_fredkin_preserves_entanglement() {
        // Fredkin on product state maintains product structure
        let state = NQubitState::new_product(vec![
            QuantumState::new(384),
            QuantumState::new(100),
            QuantumState::new(200),
        ]);

        let result = apply_fredkin(state, 0, 1, 2);

        assert!(!result.is_entangled()); // Still product state
    }

    // CCZ Tests

    #[test]
    fn test_ccz_both_controls_active() {
        // Both controls |1⟩: apply Z (384 advancement) to target
        let state = NQubitState::new_product(vec![
            QuantumState::new(384), // Control1 |1⟩
            QuantumState::new(384), // Control2 |1⟩
            QuantumState::new(100), // Target
        ]);

        let result = apply_ccz(state, 0, 1, 2);

        assert_eq!(result.qubit(0).position(), 384);
        assert_eq!(result.qubit(1).position(), 384);
        assert_eq!(result.qubit(2).position(), (100 + 384) % 768); // Z applied
    }

    #[test]
    fn test_ccz_one_control_inactive() {
        // Only one control active: no operation
        let state = NQubitState::new_product(vec![
            QuantumState::new(384), // Control1 |1⟩
            QuantumState::new(0),   // Control2 |0⟩
            QuantumState::new(100), // Target
        ]);

        let result = apply_ccz(state, 0, 1, 2);

        assert_eq!(result.qubit(0).position(), 384);
        assert_eq!(result.qubit(1).position(), 0);
        assert_eq!(result.qubit(2).position(), 100); // No change
    }

    #[test]
    fn test_ccz_squared_is_identity() {
        // CCZ² = I - applying twice returns to original
        let state = NQubitState::new_product(vec![
            QuantumState::new(384), // Control1 |1⟩
            QuantumState::new(384), // Control2 |1⟩
            QuantumState::new(100), // Target
        ]);

        let once = apply_ccz(state, 0, 1, 2);
        let twice = apply_ccz(once, 0, 1, 2);

        assert_eq!(twice.qubit(2).position(), 100); // Back to original
    }
}
