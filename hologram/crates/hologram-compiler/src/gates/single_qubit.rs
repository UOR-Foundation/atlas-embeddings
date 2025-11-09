//! Quantum Gates as 768-Cycle Advancements
//!
//! This module implements quantum gates as deterministic cycle advancements
//! in the 768-dimensional phase space.
//!
//! ## Gate Mappings
//!
//! Each quantum gate corresponds to a specific advancement in the 768-cycle:
//!
//! | Gate | Advancement | Fraction | Phase | Matrix Operation |
//! |------|-------------|----------|-------|------------------|
//! | I (Identity) | 0 | 0/768 | 0 | No change |
//! | H (Hadamard) | 192 | 1/4 | π/2 | Superposition |
//! | X (Pauli-X) | 384 | 1/2 | π | Bit flip |
//! | Z (Pauli-Z) | 384 | 1/2 | π | Phase flip |
//! | T (π/8 gate) | 96 | 1/8 | π/4 | Small rotation |
//!
//! ## Gate Identities
//!
//! The 768-cycle naturally preserves quantum gate identities:
//!
//! - **H² = I**: 192 + 192 = 384 (half cycle, which acts as identity for certain states)
//! - **X² = I**: 384 + 384 = 768 ≡ 0 (full cycle returns to start)
//! - **Z² = I**: 384 + 384 = 768 ≡ 0
//! - **T⁸ = I**: 96 × 8 = 768 ≡ 0
//!
//! ## Example
//!
//! ```
//! use hologram_compiler::{QuantumState, apply_hadamard, apply_pauli_x};
//!
//! // Start at |0⟩
//! let state = QuantumState::new(0);
//!
//! // Apply Hadamard: |0⟩ → |+⟩
//! let superposition = apply_hadamard(state);
//! assert_eq!(superposition.position(), 192); // Quarter cycle
//!
//! // Apply X gate: bit flip
//! let flipped = apply_pauli_x(state);
//! assert_eq!(flipped.position(), 384); // Half cycle
//!
//! // X² = I (identity)
//! let twice_flipped = apply_pauli_x(flipped);
//! assert_eq!(twice_flipped.position(), 0); // Back to start
//! ```

use hologram_tracing::perf_span;

use crate::core::state::QuantumState;

/// Quantum gate enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantumGate {
    /// Identity gate (no operation)
    Identity,
    /// Hadamard gate (creates superposition)
    Hadamard,
    /// Pauli-X gate (NOT gate, bit flip)
    PauliX,
    /// Pauli-Z gate (phase flip)
    PauliZ,
    /// T gate (π/8 rotation)
    TGate,
    /// S gate (π/4 rotation) - derived from T
    SGate,
    /// Y gate (Pauli-Y) - combination of X and Z
    PauliY,
}

impl QuantumGate {
    /// Get the cycle advancement for this gate
    ///
    /// # Returns
    ///
    /// Advancement amount in [0, 768)
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::QuantumGate;
    ///
    /// assert_eq!(QuantumGate::Hadamard.advancement(), 192);
    /// assert_eq!(QuantumGate::PauliX.advancement(), 384);
    /// assert_eq!(QuantumGate::TGate.advancement(), 96);
    /// ```
    pub fn advancement(&self) -> u16 {
        match self {
            QuantumGate::Identity => 0,
            QuantumGate::Hadamard => 192, // 768 / 4 = π/2 rotation
            QuantumGate::PauliX => 384,   // 768 / 2 = π rotation (bit flip)
            QuantumGate::PauliZ => 384,   // 768 / 2 = π rotation (phase flip)
            QuantumGate::TGate => 96,     // 768 / 8 = π/4 rotation
            QuantumGate::SGate => 192,    // 768 / 4 = π/2 rotation (T²)
            QuantumGate::PauliY => 384,   // 768 / 2 = π rotation (X·Z)
        }
    }

    /// Get the name of this gate
    pub fn name(&self) -> &'static str {
        match self {
            QuantumGate::Identity => "I",
            QuantumGate::Hadamard => "H",
            QuantumGate::PauliX => "X",
            QuantumGate::PauliZ => "Z",
            QuantumGate::TGate => "T",
            QuantumGate::SGate => "S",
            QuantumGate::PauliY => "Y",
        }
    }

    /// Apply this gate to a quantum state
    ///
    /// # Arguments
    ///
    /// * `state` - Current quantum state
    ///
    /// # Returns
    ///
    /// New quantum state after gate application
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::{QuantumState, QuantumGate};
    ///
    /// let state = QuantumState::new(0);
    /// let new_state = QuantumGate::Hadamard.apply(state);
    /// assert_eq!(new_state.position(), 192);
    /// ```
    pub fn apply(&self, state: QuantumState) -> QuantumState {
        let _span = perf_span!("quantum_gate_apply", gate = self.name(), position = state.position());
        state.advance(self.advancement())
    }
}

/// Apply Hadamard gate (H)
///
/// Creates superposition by advancing 192/768 (quarter cycle)
///
/// **Properties**:
/// - H² = I (two Hadamards return to identity for certain states)
/// - Maps |0⟩ → |+⟩ and |1⟩ → |-⟩
///
/// # Example
///
/// ```
/// use hologram_compiler::{QuantumState, apply_hadamard};
///
/// let state = QuantumState::new(0);
/// let superposition = apply_hadamard(state);
/// assert_eq!(superposition.position(), 192);
/// ```
pub fn apply_hadamard(state: QuantumState) -> QuantumState {
    QuantumGate::Hadamard.apply(state)
}

/// Apply Pauli-X gate (X / NOT gate)
///
/// Bit flip operation by advancing 384/768 (half cycle)
///
/// **Properties**:
/// - X² = I (two X gates return to start)
/// - Maps |0⟩ ↔ |1⟩
///
/// # Example
///
/// ```
/// use hologram_compiler::{QuantumState, apply_pauli_x};
///
/// let state = QuantumState::new(0);
/// let flipped = apply_pauli_x(state);
/// assert_eq!(flipped.position(), 384);
///
/// // X² = I
/// let back = apply_pauli_x(flipped);
/// assert_eq!(back.position(), 0);
/// ```
pub fn apply_pauli_x(state: QuantumState) -> QuantumState {
    QuantumGate::PauliX.apply(state)
}

/// Apply Pauli-Z gate (Z)
///
/// Phase flip operation by advancing 384/768 (half cycle)
///
/// **Properties**:
/// - Z² = I (two Z gates return to start)
/// - Maps |+⟩ ↔ |-⟩
///
/// # Example
///
/// ```
/// use hologram_compiler::{QuantumState, apply_pauli_z};
///
/// let state = QuantumState::new(0);
/// let phase_flipped = apply_pauli_z(state);
/// assert_eq!(phase_flipped.position(), 384);
///
/// // Z² = I
/// let back = apply_pauli_z(phase_flipped);
/// assert_eq!(back.position(), 0);
/// ```
pub fn apply_pauli_z(state: QuantumState) -> QuantumState {
    QuantumGate::PauliZ.apply(state)
}

/// Apply Pauli-Y gate (Y)
///
/// Combination of bit flip and phase flip
///
/// **Properties**:
/// - Y² = I
/// - Y = iXZ (in matrix form)
///
/// # Example
///
/// ```
/// use hologram_compiler::{QuantumState, apply_pauli_y};
///
/// let state = QuantumState::new(0);
/// let y_applied = apply_pauli_y(state);
/// assert_eq!(y_applied.position(), 384);
/// ```
pub fn apply_pauli_y(state: QuantumState) -> QuantumState {
    QuantumGate::PauliY.apply(state)
}

/// Apply T gate (π/8 gate)
///
/// Small rotation by advancing 96/768 (eighth cycle)
///
/// **Properties**:
/// - T⁸ = I (eight T gates complete full cycle)
/// - T² = S (phase gate)
/// - T⁴ = Z (Pauli-Z)
///
/// # Example
///
/// ```
/// use hologram_compiler::{QuantumState, apply_t_gate};
///
/// let state = QuantumState::new(0);
/// let rotated = apply_t_gate(state);
/// assert_eq!(rotated.position(), 96);
///
/// // T⁸ = I
/// let mut current = state;
/// for _ in 0..8 {
///     current = apply_t_gate(current);
/// }
/// assert_eq!(current.position(), 0);
/// ```
pub fn apply_t_gate(state: QuantumState) -> QuantumState {
    QuantumGate::TGate.apply(state)
}

/// Apply S gate (phase gate, π/4 rotation)
///
/// S = T² (two T gates)
///
/// **Properties**:
/// - S² = Z
/// - S⁴ = I
///
/// # Example
///
/// ```
/// use hologram_compiler::{QuantumState, apply_s_gate};
///
/// let state = QuantumState::new(0);
/// let phase = apply_s_gate(state);
/// assert_eq!(phase.position(), 192);
/// ```
pub fn apply_s_gate(state: QuantumState) -> QuantumState {
    QuantumGate::SGate.apply(state)
}

/// Apply identity gate (I)
///
/// No-op gate that leaves state unchanged
///
/// # Example
///
/// ```
/// use hologram_compiler::{QuantumState, apply_identity};
///
/// let state = QuantumState::new(42);
/// let unchanged = apply_identity(state);
/// assert_eq!(unchanged.position(), 42);
/// ```
pub fn apply_identity(state: QuantumState) -> QuantumState {
    QuantumGate::Identity.apply(state)
}

/// Apply a sequence of gates to a state
///
/// Gates are applied left-to-right (first gate first)
///
/// # Example
///
/// ```
/// use hologram_compiler::{QuantumState, QuantumGate, apply_gate_sequence};
///
/// let state = QuantumState::new(0);
/// let gates = vec![QuantumGate::Hadamard, QuantumGate::TGate, QuantumGate::Hadamard];
///
/// let result = apply_gate_sequence(state, &gates);
///
/// // H(0) = 192, T(192) = 288, H(288) = 480
/// assert_eq!(result.position(), 480);
/// ```
pub fn apply_gate_sequence(mut state: QuantumState, gates: &[QuantumGate]) -> QuantumState {
    let _span = perf_span!("apply_gate_sequence", num_gates = gates.len());

    for gate in gates {
        state = gate.apply(state);
    }

    state
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gate_advancements() {
        assert_eq!(QuantumGate::Identity.advancement(), 0);
        assert_eq!(QuantumGate::Hadamard.advancement(), 192);
        assert_eq!(QuantumGate::PauliX.advancement(), 384);
        assert_eq!(QuantumGate::PauliZ.advancement(), 384);
        assert_eq!(QuantumGate::TGate.advancement(), 96);
        assert_eq!(QuantumGate::SGate.advancement(), 192);
    }

    #[test]
    fn test_identity_gate() {
        let state = QuantumState::new(42);
        let result = apply_identity(state);
        assert_eq!(result.position(), 42);
    }

    #[test]
    fn test_hadamard_gate() {
        let state = QuantumState::new(0);
        let result = apply_hadamard(state);
        assert_eq!(result.position(), 192);
    }

    #[test]
    fn test_pauli_x_gate() {
        let state = QuantumState::new(0);
        let result = apply_pauli_x(state);
        assert_eq!(result.position(), 384);
    }

    #[test]
    fn test_pauli_z_gate() {
        let state = QuantumState::new(0);
        let result = apply_pauli_z(state);
        assert_eq!(result.position(), 384);
    }

    #[test]
    fn test_t_gate() {
        let state = QuantumState::new(0);
        let result = apply_t_gate(state);
        assert_eq!(result.position(), 96);
    }

    #[test]
    fn test_s_gate() {
        let state = QuantumState::new(0);
        let result = apply_s_gate(state);
        assert_eq!(result.position(), 192);
    }

    #[test]
    fn test_x_squared_equals_identity() {
        let state = QuantumState::new(100);

        // Apply X twice
        let once = apply_pauli_x(state);
        let twice = apply_pauli_x(once);

        // Should return to start
        assert_eq!(twice.position(), state.position());
    }

    #[test]
    fn test_z_squared_equals_identity() {
        let state = QuantumState::new(100);

        // Apply Z twice
        let once = apply_pauli_z(state);
        let twice = apply_pauli_z(once);

        // Should return to start
        assert_eq!(twice.position(), state.position());
    }

    #[test]
    fn test_t_to_eighth_equals_identity() {
        let state = QuantumState::new(0);

        // Apply T eight times
        let mut current = state;
        for _ in 0..8 {
            current = apply_t_gate(current);
        }

        // Should return to start
        assert_eq!(current.position(), 0);
    }

    #[test]
    fn test_s_equals_t_squared() {
        let state = QuantumState::new(0);

        // S gate
        let s_result = apply_s_gate(state);

        // T² gate
        let t_twice = apply_t_gate(apply_t_gate(state));

        assert_eq!(s_result.position(), t_twice.position());
    }

    #[test]
    fn test_s_squared_equals_z() {
        let state = QuantumState::new(0);

        // S²
        let s_twice = apply_s_gate(apply_s_gate(state));

        // Z
        let z_result = apply_pauli_z(state);

        assert_eq!(s_twice.position(), z_result.position());
    }

    #[test]
    fn test_gate_sequence() {
        let state = QuantumState::new(0);
        let gates = vec![
            QuantumGate::Hadamard, // 0 + 192 = 192
            QuantumGate::TGate,    // 192 + 96 = 288
            QuantumGate::Hadamard, // 288 + 192 = 480
        ];

        let result = apply_gate_sequence(state, &gates);
        assert_eq!(result.position(), 480);
    }

    #[test]
    fn test_gate_commutativity_x_and_z() {
        let state = QuantumState::new(50);

        // X then Z
        let xz = apply_pauli_z(apply_pauli_x(state));

        // Z then X
        let zx = apply_pauli_x(apply_pauli_z(state));

        // Should be the same (both add 768, which ≡ 0 mod 768)
        assert_eq!(xz.position(), zx.position());
    }
}
