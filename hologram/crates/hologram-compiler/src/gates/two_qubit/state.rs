//! Two-Qubit State Representation with Entanglement Tracking
//!
//! This module extends the single-qubit 768-cycle model to two-qubit systems,
//! implementing entanglement as deterministic geometric correlation between
//! cycle positions.
//!
//! ## Core Concept
//!
//! In the 768-cycle geometric model, entanglement is NOT "spooky action at a
//! distance" - it's a deterministic constraint between cycle positions:
//!
//! ```text
//! Entangled state: p_A + p_B ≡ k (mod 768)
//!
//! where:
//!   p_A = position of qubit A in [0, 768)
//!   p_B = position of qubit B in [0, 768)
//!   k = correlation constant
//! ```
//!
//! When you measure qubit A at position p_A, qubit B's position is immediately
//! known: p_B = (k - p_A) mod 768. This is geometric correlation, not collapse.
//!
//! ## Bell State Example
//!
//! ```text
//! |Φ⁺⟩ = (|00⟩ + |11⟩) / √2
//!
//! Created by:
//!   1. Start at |00⟩: (p_A=0, p_B=0)
//!   2. Apply H⊗I: (p_A=192, p_B=0)  [Hadamard on A]
//!   3. Apply CNOT: Creates constraint p_A + p_B ≡ 192 (mod 768)
//!
//! Now entangled! Measuring A determines B via correlation.
//! ```
//!
//! ## Two-Qubit State Space
//!
//! Two independent qubits: 768 × 768 = 589,824 possible states
//! But entangled states live on 1D manifold: only 768 correlated positions
//!
//! This constraint-based representation is sparse and scalable.

use hologram_tracing::perf_span;

use crate::core::state::{QuantumState, CYCLE_SIZE};

/// Correlation constraint for entangled qubits
///
/// Represents the relationship p_A + p_B ≡ sum_modulo (mod 768) for entangled pairs.
/// This is a geometric constraint in the 768-cycle space, not a probabilistic phenomenon.
///
/// # Example
///
/// ```
/// use hologram_compiler::CorrelationConstraint;
///
/// // Bell state |Φ⁺⟩ constraint
/// let constraint = CorrelationConstraint::new(192);
///
/// // If qubit A at position 100, qubit B must be at:
/// let p_b = constraint.compute_correlated_position(100);
/// assert_eq!(p_b, 92);  // (192 - 100) mod 768 = 92
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CorrelationConstraint {
    /// The sum p_A + p_B mod 768
    sum_modulo: u16,
}

impl CorrelationConstraint {
    /// Create a new correlation constraint
    ///
    /// # Arguments
    ///
    /// * `sum_modulo` - The value that p_A + p_B must equal (mod 768)
    ///
    /// # Panics
    ///
    /// Panics if sum_modulo >= 768
    pub fn new(sum_modulo: u16) -> Self {
        assert!(
            sum_modulo < CYCLE_SIZE,
            "sum_modulo {} must be < {}",
            sum_modulo,
            CYCLE_SIZE
        );
        Self { sum_modulo }
    }

    /// Get the sum modulo value
    pub fn sum_modulo(&self) -> u16 {
        self.sum_modulo
    }

    /// Compute the correlated position of the second qubit given the first
    ///
    /// Given p_A, returns p_B such that p_A + p_B ≡ sum_modulo (mod 768)
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::CorrelationConstraint;
    ///
    /// let constraint = CorrelationConstraint::new(384);
    /// assert_eq!(constraint.compute_correlated_position(100), 284);  // 384 - 100 = 284
    /// assert_eq!(constraint.compute_correlated_position(400), 752);  // (384 - 400 + 768) mod 768 = 752
    /// ```
    pub fn compute_correlated_position(&self, position_a: u16) -> u16 {
        if position_a <= self.sum_modulo {
            self.sum_modulo - position_a
        } else {
            CYCLE_SIZE - position_a + self.sum_modulo
        }
    }

    /// Check if two positions satisfy this correlation constraint
    pub fn are_positions_correlated(&self, position_a: u16, position_b: u16) -> bool {
        (position_a + position_b) % CYCLE_SIZE == self.sum_modulo
    }
}

/// Two-qubit quantum state representation
///
/// Represents a two-qubit system in the 768-cycle geometric model.
/// Supports both product states (independent qubits) and entangled states
/// (correlated positions).
///
/// # Product States
///
/// Two independent qubits, each at its own position in [0, 768):
///
/// ```
/// use hologram_compiler::{TwoQubitState, QuantumState};
///
/// let q0 = QuantumState::new(100);
/// let q1 = QuantumState::new(200);
/// let state = TwoQubitState::new_product(q0, q1);
///
/// assert!(!state.is_entangled());
/// assert_eq!(state.qubit_0().position(), 100);
/// assert_eq!(state.qubit_1().position(), 200);
/// ```
///
/// # Entangled States
///
/// Two qubits with correlated positions via a constraint:
///
/// ```
/// use hologram_compiler::{TwoQubitState, QuantumState, CorrelationConstraint};
///
/// let q0 = QuantumState::new(192);
/// let q1 = QuantumState::new(0);
/// let constraint = CorrelationConstraint::new(192);
/// let state = TwoQubitState::new_entangled(q0, q1, constraint);
///
/// assert!(state.is_entangled());
/// assert_eq!(state.correlation_constraint().unwrap().sum_modulo(), 192);
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct TwoQubitState {
    /// First qubit state
    qubit_0: QuantumState,
    /// Second qubit state
    qubit_1: QuantumState,
    /// Whether the qubits are entangled
    entangled: bool,
    /// Correlation constraint if entangled
    correlation: Option<CorrelationConstraint>,
}

impl TwoQubitState {
    /// Create a product state (two independent qubits)
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::{TwoQubitState, QuantumState};
    ///
    /// let state = TwoQubitState::new_product(
    ///     QuantumState::new(0),   // |0⟩
    ///     QuantumState::new(0),   // |0⟩
    /// );
    ///
    /// assert!(!state.is_entangled());
    /// ```
    pub fn new_product(qubit_0: QuantumState, qubit_1: QuantumState) -> Self {
        Self {
            qubit_0,
            qubit_1,
            entangled: false,
            correlation: None,
        }
    }

    /// Create an entangled state with a correlation constraint
    ///
    /// # Arguments
    ///
    /// * `qubit_0` - First qubit state
    /// * `qubit_1` - Second qubit state
    /// * `constraint` - Correlation constraint
    ///
    /// # Panics
    ///
    /// Panics if the positions don't satisfy the constraint
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::{TwoQubitState, QuantumState, CorrelationConstraint};
    ///
    /// let constraint = CorrelationConstraint::new(192);
    /// let state = TwoQubitState::new_entangled(
    ///     QuantumState::new(192),
    ///     QuantumState::new(0),
    ///     constraint,
    /// );
    ///
    /// assert!(state.is_entangled());
    /// ```
    pub fn new_entangled(qubit_0: QuantumState, qubit_1: QuantumState, constraint: CorrelationConstraint) -> Self {
        // Verify positions satisfy constraint
        assert!(
            constraint.are_positions_correlated(qubit_0.position(), qubit_1.position()),
            "Positions {} and {} don't satisfy correlation constraint (sum should be {} mod 768)",
            qubit_0.position(),
            qubit_1.position(),
            constraint.sum_modulo()
        );

        Self {
            qubit_0,
            qubit_1,
            entangled: true,
            correlation: Some(constraint),
        }
    }

    /// Get the first qubit state
    pub fn qubit_0(&self) -> QuantumState {
        self.qubit_0
    }

    /// Get the second qubit state
    pub fn qubit_1(&self) -> QuantumState {
        self.qubit_1
    }

    /// Check if the qubits are entangled
    pub fn is_entangled(&self) -> bool {
        self.entangled
    }

    /// Get the correlation constraint if entangled
    pub fn correlation_constraint(&self) -> Option<CorrelationConstraint> {
        self.correlation
    }

    /// Set qubit 0 to a new state
    ///
    /// If entangled, this will update qubit 1 to maintain the correlation constraint.
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::{TwoQubitState, QuantumState, CorrelationConstraint};
    ///
    /// let constraint = CorrelationConstraint::new(192);
    /// let mut state = TwoQubitState::new_entangled(
    ///     QuantumState::new(192),
    ///     QuantumState::new(0),
    ///     constraint,
    /// );
    ///
    /// // Change qubit 0 - qubit 1 will automatically adjust
    /// state.set_qubit_0(QuantumState::new(100));
    /// assert_eq!(state.qubit_0().position(), 100);
    /// assert_eq!(state.qubit_1().position(), 92);  // Maintains p_0 + p_1 = 192
    /// ```
    pub fn set_qubit_0(&mut self, new_state: QuantumState) {
        let _span = perf_span!("set_qubit_0", entangled = self.entangled);

        self.qubit_0 = new_state;

        if let Some(constraint) = self.correlation {
            // Update qubit 1 to maintain correlation
            let new_position_1 = constraint.compute_correlated_position(new_state.position());
            self.qubit_1 = QuantumState::new(new_position_1);
        }
    }

    /// Set qubit 1 to a new state
    ///
    /// If entangled, this will update qubit 0 to maintain the correlation constraint.
    pub fn set_qubit_1(&mut self, new_state: QuantumState) {
        let _span = perf_span!("set_qubit_1", entangled = self.entangled);

        self.qubit_1 = new_state;

        if let Some(constraint) = self.correlation {
            // Update qubit 0 to maintain correlation
            let new_position_0 = constraint.compute_correlated_position(new_state.position());
            self.qubit_0 = QuantumState::new(new_position_0);
        }
    }

    /// Create entanglement by establishing a correlation constraint
    ///
    /// This is used by two-qubit gates like CNOT to create entanglement.
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::{TwoQubitState, QuantumState, CorrelationConstraint};
    ///
    /// let mut state = TwoQubitState::new_product(
    ///     QuantumState::new(192),
    ///     QuantumState::new(384),
    /// );
    ///
    /// assert!(!state.is_entangled());
    ///
    /// // Create entanglement with constraint p_0 + p_1 = 576 (mod 768)
    /// let constraint = CorrelationConstraint::new((192 + 384) % 768);
    /// state.create_entanglement(constraint);
    ///
    /// assert!(state.is_entangled());
    /// ```
    pub fn create_entanglement(&mut self, constraint: CorrelationConstraint) {
        let _span = perf_span!("create_entanglement");

        // Verify current positions satisfy the constraint
        assert!(
            constraint.are_positions_correlated(self.qubit_0.position(), self.qubit_1.position()),
            "Cannot create entanglement: current positions don't satisfy constraint"
        );

        self.entangled = true;
        self.correlation = Some(constraint);
    }

    /// Break entanglement (for measurement or decoherence)
    ///
    /// After measurement, qubits are no longer entangled - each has a definite
    /// position that is now independent.
    pub fn break_entanglement(&mut self) {
        self.entangled = false;
        self.correlation = None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_correlation_constraint_creation() {
        let constraint = CorrelationConstraint::new(192);
        assert_eq!(constraint.sum_modulo(), 192);
    }

    #[test]
    #[should_panic(expected = "sum_modulo 768 must be < 768")]
    fn test_correlation_constraint_invalid() {
        CorrelationConstraint::new(768);
    }

    #[test]
    fn test_compute_correlated_position() {
        let constraint = CorrelationConstraint::new(192);

        // p_A + p_B = 192
        assert_eq!(constraint.compute_correlated_position(0), 192);
        assert_eq!(constraint.compute_correlated_position(192), 0);
        assert_eq!(constraint.compute_correlated_position(100), 92);

        // Wrap around case: p_A = 400, p_B = ? such that 400 + p_B ≡ 192 (mod 768)
        // p_B = 192 - 400 + 768 = 560? No: (192 + 768 - 400) mod 768
        // Actually: if 400 + p_B = 192 + 768, then p_B = 560
        assert_eq!(constraint.compute_correlated_position(400), 560);
    }

    #[test]
    fn test_are_positions_correlated() {
        let constraint = CorrelationConstraint::new(192);

        assert!(constraint.are_positions_correlated(0, 192));
        assert!(constraint.are_positions_correlated(192, 0));
        assert!(constraint.are_positions_correlated(100, 92));
        assert!(constraint.are_positions_correlated(400, 560));

        assert!(!constraint.are_positions_correlated(0, 0));
        assert!(!constraint.are_positions_correlated(100, 100));
    }

    #[test]
    fn test_product_state_creation() {
        let state = TwoQubitState::new_product(QuantumState::new(100), QuantumState::new(200));

        assert_eq!(state.qubit_0().position(), 100);
        assert_eq!(state.qubit_1().position(), 200);
        assert!(!state.is_entangled());
        assert!(state.correlation_constraint().is_none());
    }

    #[test]
    fn test_entangled_state_creation() {
        let constraint = CorrelationConstraint::new(192);
        let state = TwoQubitState::new_entangled(QuantumState::new(192), QuantumState::new(0), constraint);

        assert_eq!(state.qubit_0().position(), 192);
        assert_eq!(state.qubit_1().position(), 0);
        assert!(state.is_entangled());
        assert_eq!(state.correlation_constraint().unwrap().sum_modulo(), 192);
    }

    #[test]
    #[should_panic(expected = "don't satisfy correlation constraint")]
    fn test_entangled_state_invalid_positions() {
        let constraint = CorrelationConstraint::new(192);
        // These positions don't satisfy p_0 + p_1 = 192
        TwoQubitState::new_entangled(QuantumState::new(100), QuantumState::new(100), constraint);
    }

    #[test]
    fn test_set_qubit_0_product_state() {
        let mut state = TwoQubitState::new_product(QuantumState::new(100), QuantumState::new(200));

        state.set_qubit_0(QuantumState::new(150));
        assert_eq!(state.qubit_0().position(), 150);
        assert_eq!(state.qubit_1().position(), 200); // Unchanged
    }

    #[test]
    fn test_set_qubit_0_entangled_state() {
        let constraint = CorrelationConstraint::new(192);
        let mut state = TwoQubitState::new_entangled(QuantumState::new(192), QuantumState::new(0), constraint);

        // Change qubit 0 - qubit 1 should automatically adjust
        state.set_qubit_0(QuantumState::new(100));
        assert_eq!(state.qubit_0().position(), 100);
        assert_eq!(state.qubit_1().position(), 92); // Maintains correlation
        assert!(constraint.are_positions_correlated(100, 92));
    }

    #[test]
    fn test_set_qubit_1_entangled_state() {
        let constraint = CorrelationConstraint::new(192);
        let mut state = TwoQubitState::new_entangled(QuantumState::new(192), QuantumState::new(0), constraint);

        // Change qubit 1 - qubit 0 should automatically adjust
        state.set_qubit_1(QuantumState::new(100));
        assert_eq!(state.qubit_1().position(), 100);
        assert_eq!(state.qubit_0().position(), 92); // Maintains correlation
        assert!(constraint.are_positions_correlated(92, 100));
    }

    #[test]
    fn test_create_entanglement() {
        let mut state = TwoQubitState::new_product(QuantumState::new(192), QuantumState::new(384));

        assert!(!state.is_entangled());

        let sum = (192 + 384) % CYCLE_SIZE; // 576
        let constraint = CorrelationConstraint::new(sum);
        state.create_entanglement(constraint);

        assert!(state.is_entangled());
        assert_eq!(state.correlation_constraint().unwrap().sum_modulo(), 576);
    }

    #[test]
    #[should_panic(expected = "current positions don't satisfy constraint")]
    fn test_create_entanglement_invalid() {
        let mut state = TwoQubitState::new_product(QuantumState::new(100), QuantumState::new(200));

        // Try to create entanglement with wrong constraint
        let constraint = CorrelationConstraint::new(192); // But 100 + 200 = 300, not 192
        state.create_entanglement(constraint);
    }

    #[test]
    fn test_break_entanglement() {
        let constraint = CorrelationConstraint::new(192);
        let mut state = TwoQubitState::new_entangled(QuantumState::new(192), QuantumState::new(0), constraint);

        assert!(state.is_entangled());

        state.break_entanglement();

        assert!(!state.is_entangled());
        assert!(state.correlation_constraint().is_none());
        // Positions remain but are now independent
        assert_eq!(state.qubit_0().position(), 192);
        assert_eq!(state.qubit_1().position(), 0);
    }
}
