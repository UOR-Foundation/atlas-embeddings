//! N-Qubit State Representation with Multi-Way Entanglement
//!
//! This module generalizes the two-qubit 768-cycle model to arbitrary N qubits,
//! implementing multi-way entanglement as deterministic geometric constraints
//! between cycle positions.
//!
//! ## Core Concept
//!
//! In the 768-cycle geometric model, N-qubit entanglement is a system of
//! deterministic constraints between cycle positions:
//!
//! ```text
//! Multi-way constraint: Σ c_i · p_i ≡ k (mod 768)
//!
//! where:
//!   p_i = position of qubit i in [0, 768)
//!   c_i = coefficient for qubit i (typically +1 or -1)
//!   k = correlation constant
//! ```
//!
//! ## GHZ State Example (3 qubits)
//!
//! ```text
//! |GHZ⟩ = (|000⟩ + |111⟩) / √2
//!
//! Created by:
//!   1. Start at |000⟩: (p_0=0, p_1=0, p_2=0)
//!   2. Apply H⊗I⊗I: (p_0=192, p_1=0, p_2=0)
//!   3. Apply CNOT(0→1): p_0 + p_1 ≡ 192 (mod 768)
//!   4. Apply CNOT(1→2): p_1 + p_2 ≡ (some k)
//!
//! Result: All three qubits constrained, perfect 3-way correlation
//! ```
//!
//! ## N-Qubit State Space Scaling
//!
//! | N Qubits | Product States | Full Entangled | Reduction |
//! |----------|---------------|----------------|-----------|
//! | 2        | 768²          | 768            | 768×      |
//! | 3        | 768³          | 768²           | 768×      |
//! | 4        | 768⁴          | 768³           | 768×      |
//! | N        | 768^N         | 768^(N-1)      | 768×      |
//!
//! ## Entanglement Structures
//!
//! - **Product**: No entanglement, N independent qubits
//! - **Partial**: Some qubits entangled in groups
//! - **Full**: All qubits correlated via single constraint

use hologram_tracing::perf_span;

use crate::core::state::QuantumState;

/// N-Qubit quantum state with optional entanglement tracking
///
/// Represents a system of N qubits, where each qubit occupies a position
/// in the 768-cycle. Supports both product states (independent qubits) and
/// entangled states (constrained correlations).
///
/// # Examples
///
/// ```
/// use hologram_compiler::{NQubitState, QuantumState};
///
/// // Create 3-qubit product state |000⟩
/// let state = NQubitState::new_product(vec![
///     QuantumState::new(0),
///     QuantumState::new(0),
///     QuantumState::new(0),
/// ]);
///
/// assert_eq!(state.num_qubits(), 3);
/// assert!(!state.is_entangled());
/// ```
#[derive(Debug, Clone)]
pub struct NQubitState {
    /// Individual qubit positions in 768-cycle
    qubits: Vec<QuantumState>,

    /// Entanglement structure tracking
    entanglement: EntanglementStructure,
}

/// Entanglement structure for N-qubit systems
///
/// Tracks how qubits are correlated:
/// - Product: No correlations
/// - Partial: Some qubits form entangled groups
/// - Full: All qubits correlated via single constraint
#[derive(Debug, Clone)]
pub enum EntanglementStructure {
    /// No entanglement - all qubits independent
    Product,

    /// Partial entanglement - some qubits in correlated groups
    Partial {
        /// Groups of entangled qubits
        groups: Vec<EntanglementGroup>,
    },

    /// Full entanglement - all qubits correlated
    Full {
        /// Single constraint covering all qubits
        constraint: super::constraint::MultiQubitConstraint,
    },
}

/// Group of entangled qubits with their correlation constraint
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct EntanglementGroup {
    /// Indices of qubits in this entangled group
    qubit_indices: Vec<usize>,

    /// Correlation constraint for this group
    constraint: super::constraint::MultiQubitConstraint,
}

impl NQubitState {
    /// Create N-qubit product state (no entanglement)
    ///
    /// # Arguments
    ///
    /// * `qubits` - Vector of individual qubit states
    ///
    /// # Examples
    ///
    /// ```
    /// # use hologram_compiler::{NQubitState, QuantumState};
    /// // Create 4-qubit state |0000⟩
    /// let state = NQubitState::new_product(vec![QuantumState::new(0); 4]);
    /// assert_eq!(state.num_qubits(), 4);
    /// ```
    pub fn new_product(qubits: Vec<QuantumState>) -> Self {
        let _span = perf_span!("quantum_state_768::n_qubit_state::new_product");

        Self {
            qubits,
            entanglement: EntanglementStructure::Product,
        }
    }

    /// Create N-qubit fully entangled state
    ///
    /// All qubits correlated via single multi-way constraint.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hologram_compiler::{NQubitState, QuantumState, MultiQubitConstraint};
    /// let qubits = vec![QuantumState::new(192), QuantumState::new(0), QuantumState::new(0)];
    /// let constraint = MultiQubitConstraint::new(vec![1, 1, 1], 192);
    /// let state = NQubitState::new_entangled(qubits, constraint);
    /// assert!(state.is_entangled());
    /// ```
    pub fn new_entangled(qubits: Vec<QuantumState>, constraint: super::constraint::MultiQubitConstraint) -> Self {
        let _span = perf_span!("quantum_state_768::n_qubit_state::new_entangled");

        assert_eq!(
            qubits.len(),
            constraint.num_qubits(),
            "Number of qubits must match constraint"
        );

        Self {
            qubits,
            entanglement: EntanglementStructure::Full { constraint },
        }
    }

    /// Create N-qubit state with partial entanglement (multiple independent groups)
    ///
    /// # Arguments
    ///
    /// * `qubits` - Vector of quantum states for each qubit
    /// * `groups` - Vector of entanglement groups
    pub fn new_partial(qubits: Vec<QuantumState>, groups: Vec<EntanglementGroup>) -> Self {
        let _span = perf_span!("quantum_state_768::n_qubit_state::new_partial");

        Self {
            qubits,
            entanglement: EntanglementStructure::Partial { groups },
        }
    }

    /// Get number of qubits in this state
    pub fn num_qubits(&self) -> usize {
        let _span = perf_span!("quantum_state_768::n_qubit_state::num_qubits");
        self.qubits.len()
    }

    /// Check if state has any entanglement
    pub fn is_entangled(&self) -> bool {
        let _span = perf_span!("quantum_state_768::n_qubit_state::is_entangled");
        !matches!(self.entanglement, EntanglementStructure::Product)
    }

    /// Get reference to qubit at index
    ///
    /// # Panics
    ///
    /// Panics if index >= num_qubits
    pub fn qubit(&self, index: usize) -> &QuantumState {
        let _span = perf_span!("quantum_state_768::n_qubit_state::qubit");
        &self.qubits[index]
    }

    /// Set qubit position at index (with constraint propagation if entangled)
    ///
    /// If the state is entangled, setting one qubit's position will automatically
    /// update other qubits to satisfy correlation constraints.
    ///
    /// # Panics
    ///
    /// Panics if index >= num_qubits or constraints cannot be satisfied
    pub fn set_qubit(&mut self, index: usize, state: QuantumState) {
        let _span = perf_span!("quantum_state_768::n_qubit_state::set_qubit");

        assert!(index < self.qubits.len(), "Index out of bounds");

        // Set the qubit
        self.qubits[index] = state;

        // If entangled, propagate constraints
        match &self.entanglement {
            EntanglementStructure::Product => {
                // No propagation needed for product state
            }
            EntanglementStructure::Full { constraint } => {
                // Build constraint graph and propagate
                let constraints = vec![constraint.clone()];
                let graph = super::constraint::ConstraintGraph::from_constraints(self.qubits.len(), &constraints);

                // Get current positions
                let mut positions: Vec<u16> = self.qubits.iter().map(|q| q.position()).collect();

                // Propagate from changed qubit
                graph
                    .propagate_constraints(index, &mut positions, &constraints)
                    .expect("Failed to propagate constraints");

                // Update all qubits with new positions
                for (i, pos) in positions.iter().enumerate() {
                    if i != index {
                        self.qubits[i] = QuantumState::new(*pos);
                    }
                }
            }
            EntanglementStructure::Partial { groups } => {
                // Find which group(s) contain the changed qubit
                for group in groups.iter() {
                    if group.qubit_indices.contains(&index) {
                        // This group contains the changed qubit - propagate within group

                        // Build constraint for this group
                        let constraints = vec![group.constraint.clone()];
                        let graph = super::constraint::ConstraintGraph::from_constraints(
                            group.qubit_indices.len(),
                            &constraints,
                        );

                        // Get current positions for qubits in this group
                        let mut group_positions: Vec<u16> =
                            group.qubit_indices.iter().map(|&i| self.qubits[i].position()).collect();

                        // Find local index of changed qubit within group
                        let local_index = group
                            .qubit_indices
                            .iter()
                            .position(|&i| i == index)
                            .expect("Changed qubit must be in group");

                        // Propagate constraints within this group
                        graph
                            .propagate_constraints(local_index, &mut group_positions, &constraints)
                            .expect("Failed to propagate constraints");

                        // Update qubits in this group with new positions
                        for (local_i, &global_i) in group.qubit_indices.iter().enumerate() {
                            if global_i != index {
                                self.qubits[global_i] = QuantumState::new(group_positions[local_i]);
                            }
                        }

                        // Note: A qubit can only be in one group, so we can break here
                        break;
                    }
                }
                // If qubit not in any group, no propagation needed (it's independent)
            }
        }
    }

    /// Create entanglement between qubits
    ///
    /// Converts product or partially entangled state to have additional
    /// entanglement constraints.
    pub fn create_entanglement(
        &mut self,
        qubit_indices: Vec<usize>,
        constraint: super::constraint::MultiQubitConstraint,
    ) {
        let _span = perf_span!("quantum_state_768::n_qubit_state::create_entanglement");

        assert_eq!(
            qubit_indices.len(),
            constraint.num_qubits(),
            "Qubit indices must match constraint size"
        );

        // If the indices cover all qubits, convert to full entanglement
        if qubit_indices.len() == self.qubits.len() {
            self.entanglement = EntanglementStructure::Full { constraint };
        } else {
            // Otherwise, add to partial entanglement groups
            let group = EntanglementGroup {
                qubit_indices,
                constraint,
            };

            match &mut self.entanglement {
                EntanglementStructure::Product => {
                    self.entanglement = EntanglementStructure::Partial { groups: vec![group] };
                }
                EntanglementStructure::Partial { groups } => {
                    groups.push(group);
                }
                EntanglementStructure::Full { .. } => {
                    // Already fully entangled, cannot add more constraints
                    panic!("Cannot add partial entanglement to fully entangled state");
                }
            }
        }
    }

    /// Break entanglement, converting to product state
    pub fn break_entanglement(&mut self) {
        let _span = perf_span!("quantum_state_768::n_qubit_state::break_entanglement");
        self.entanglement = EntanglementStructure::Product;
    }

    /// Get reference to entanglement structure
    pub fn entanglement_structure(&self) -> &EntanglementStructure {
        let _span = perf_span!("quantum_state_768::n_qubit_state::entanglement_structure");
        &self.entanglement
    }

    /// Get all qubit positions as slice
    pub fn positions(&self) -> Vec<u16> {
        let _span = perf_span!("quantum_state_768::n_qubit_state::positions");
        self.qubits.iter().map(|q| q.position()).collect()
    }
}

impl EntanglementGroup {
    /// Create new entanglement group
    pub fn new(qubit_indices: Vec<usize>, constraint: super::constraint::MultiQubitConstraint) -> Self {
        let _span = perf_span!("quantum_state_768::n_qubit_state::entanglement_group::new");
        Self {
            qubit_indices,
            constraint,
        }
    }

    /// Get qubit indices in this group
    pub fn qubit_indices(&self) -> &[usize] {
        &self.qubit_indices
    }

    /// Get constraint for this group
    pub fn constraint(&self) -> &super::constraint::MultiQubitConstraint {
        &self.constraint
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::MultiQubitConstraint;

    #[test]
    fn test_create_product_state() {
        let qubits = vec![QuantumState::new(0), QuantumState::new(100), QuantumState::new(200)];

        let state = NQubitState::new_product(qubits);

        assert_eq!(state.num_qubits(), 3);
        assert!(!state.is_entangled());
        assert_eq!(state.qubit(0).position(), 0);
        assert_eq!(state.qubit(1).position(), 100);
        assert_eq!(state.qubit(2).position(), 200);
    }

    #[test]
    fn test_num_qubits() {
        let state = NQubitState::new_product(vec![QuantumState::new(0); 5]);
        assert_eq!(state.num_qubits(), 5);
    }

    #[test]
    fn test_qubit_access() {
        let state = NQubitState::new_product(vec![QuantumState::new(192), QuantumState::new(384)]);

        assert_eq!(state.qubit(0).position(), 192);
        assert_eq!(state.qubit(1).position(), 384);
    }

    #[test]
    #[should_panic]
    fn test_qubit_access_out_of_bounds() {
        let state = NQubitState::new_product(vec![QuantumState::new(0); 3]);
        let _ = state.qubit(3); // Should panic
    }

    #[test]
    fn test_create_entangled_state() {
        // Create 3-qubit entangled state with constraint p_0 + p_1 + p_2 = 192
        let qubits = vec![QuantumState::new(100), QuantumState::new(50), QuantumState::new(42)];
        let constraint = MultiQubitConstraint::new(vec![1, 1, 1], 192);

        let state = NQubitState::new_entangled(qubits, constraint);

        assert_eq!(state.num_qubits(), 3);
        assert!(state.is_entangled());

        // Verify constraint is satisfied
        let positions = state.positions();
        assert_eq!(positions[0] as i32 + positions[1] as i32 + positions[2] as i32, 192);
    }

    #[test]
    fn test_set_qubit_product_state() {
        // Test setting qubit in product state (no propagation)
        let mut state = NQubitState::new_product(vec![QuantumState::new(0), QuantumState::new(100)]);

        state.set_qubit(0, QuantumState::new(200));

        assert_eq!(state.qubit(0).position(), 200);
        assert_eq!(state.qubit(1).position(), 100); // Should not change
    }

    #[test]
    fn test_set_qubit_entangled_state() {
        // Test that setting one qubit propagates to others
        // Create entangled state: p_0 + p_1 = 192
        let qubits = vec![QuantumState::new(100), QuantumState::new(92)];
        let constraint = MultiQubitConstraint::new(vec![1, 1], 192);

        let mut state = NQubitState::new_entangled(qubits, constraint);

        // Set p_0 = 50, should automatically set p_1 = 142
        state.set_qubit(0, QuantumState::new(50));

        assert_eq!(state.qubit(0).position(), 50);
        assert_eq!(state.qubit(1).position(), 142); // Propagated
    }

    #[test]
    fn test_create_entanglement() {
        // Convert product state to entangled
        let mut state = NQubitState::new_product(vec![QuantumState::new(100), QuantumState::new(92)]);

        assert!(!state.is_entangled());

        // Add entanglement constraint
        let constraint = MultiQubitConstraint::new(vec![1, 1], 192);
        state.create_entanglement(vec![0, 1], constraint);

        assert!(state.is_entangled());
    }

    #[test]
    fn test_break_entanglement() {
        // Convert entangled state back to product
        let qubits = vec![QuantumState::new(100), QuantumState::new(92)];
        let constraint = MultiQubitConstraint::new(vec![1, 1], 192);

        let mut state = NQubitState::new_entangled(qubits, constraint);

        assert!(state.is_entangled());

        state.break_entanglement();

        assert!(!state.is_entangled());
    }

    #[test]
    fn test_positions() {
        let state = NQubitState::new_product(vec![
            QuantumState::new(0),
            QuantumState::new(192),
            QuantumState::new(384),
        ]);

        let positions = state.positions();
        assert_eq!(positions, vec![0, 192, 384]);
    }

    #[test]
    fn test_partial_entanglement_create() {
        // Create 4-qubit state with two independent entangled pairs
        // Group 1: qubits 0,1 with constraint p_0 + p_1 = 192
        // Group 2: qubits 2,3 with constraint p_2 + p_3 = 384

        let qubits = vec![
            QuantumState::new(100),
            QuantumState::new(92),
            QuantumState::new(200),
            QuantumState::new(184),
        ];

        let constraint1 = MultiQubitConstraint::new(vec![1, 1], 192);
        let constraint2 = MultiQubitConstraint::new(vec![1, 1], 384);

        let group1 = EntanglementGroup::new(vec![0, 1], constraint1);
        let group2 = EntanglementGroup::new(vec![2, 3], constraint2);

        let state = NQubitState::new_partial(qubits, vec![group1, group2]);

        assert_eq!(state.num_qubits(), 4);
        assert!(state.is_entangled());
    }

    #[test]
    fn test_set_qubit_partial_entanglement_group1() {
        // Test that setting qubit in group 1 only affects group 1
        let qubits = vec![
            QuantumState::new(100),
            QuantumState::new(92),
            QuantumState::new(200),
            QuantumState::new(184),
        ];

        let constraint1 = MultiQubitConstraint::new(vec![1, 1], 192);
        let constraint2 = MultiQubitConstraint::new(vec![1, 1], 384);

        let group1 = EntanglementGroup::new(vec![0, 1], constraint1);
        let group2 = EntanglementGroup::new(vec![2, 3], constraint2);

        let mut state = NQubitState::new_partial(qubits, vec![group1, group2]);

        // Set qubit 0 = 50, should propagate to qubit 1 (= 142), but not affect qubits 2,3
        state.set_qubit(0, QuantumState::new(50));

        assert_eq!(state.qubit(0).position(), 50);
        assert_eq!(state.qubit(1).position(), 142); // Propagated within group 1
        assert_eq!(state.qubit(2).position(), 200); // Unchanged (different group)
        assert_eq!(state.qubit(3).position(), 184); // Unchanged (different group)
    }

    #[test]
    fn test_set_qubit_partial_entanglement_group2() {
        // Test that setting qubit in group 2 only affects group 2
        let qubits = vec![
            QuantumState::new(100),
            QuantumState::new(92),
            QuantumState::new(200),
            QuantumState::new(184),
        ];

        let constraint1 = MultiQubitConstraint::new(vec![1, 1], 192);
        let constraint2 = MultiQubitConstraint::new(vec![1, 1], 384);

        let group1 = EntanglementGroup::new(vec![0, 1], constraint1);
        let group2 = EntanglementGroup::new(vec![2, 3], constraint2);

        let mut state = NQubitState::new_partial(qubits, vec![group1, group2]);

        // Set qubit 2 = 300, should propagate to qubit 3 (= 84), but not affect qubits 0,1
        state.set_qubit(2, QuantumState::new(300));

        assert_eq!(state.qubit(0).position(), 100); // Unchanged (different group)
        assert_eq!(state.qubit(1).position(), 92); // Unchanged (different group)
        assert_eq!(state.qubit(2).position(), 300);
        assert_eq!(state.qubit(3).position(), 84); // Propagated within group 2
    }

    #[test]
    fn test_set_qubit_partial_entanglement_independent_qubit() {
        // Test that setting an independent qubit (not in any group) doesn't affect others
        let qubits = vec![
            QuantumState::new(100),
            QuantumState::new(92),
            QuantumState::new(200), // Independent
        ];

        let constraint = MultiQubitConstraint::new(vec![1, 1], 192);
        let group = EntanglementGroup::new(vec![0, 1], constraint);

        let mut state = NQubitState::new_partial(qubits, vec![group]);

        // Set independent qubit 2, should not affect qubits 0,1
        state.set_qubit(2, QuantumState::new(500));

        assert_eq!(state.qubit(0).position(), 100); // Unchanged
        assert_eq!(state.qubit(1).position(), 92); // Unchanged
        assert_eq!(state.qubit(2).position(), 500);
    }
}
