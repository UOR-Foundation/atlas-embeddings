//! Partial Measurement for N-Qubit States
//!
//! This module implements measurement of a subset of qubits in an N-qubit state,
//! with automatic constraint propagation to the remaining unmeasured qubits.
//!
//! ## Core Concept
//!
//! In the 768-cycle model, measurement is **deterministic** - it reads the
//! pre-existing cycle position. When measuring a subset of qubits:
//!
//! 1. Measure selected qubits (read their positions → classes)
//! 2. Update constraints to reflect measured values
//! 3. Propagate constraints to remaining qubits
//! 4. Return new state with fewer qubits and updated constraints
//!
//! ## Example: Measuring 2 of 4 Qubits
//!
//! ```text
//! Initial: 4-qubit GHZ state
//!   Constraint: p₀ + p₁ + p₂ + p₃ ≡ 192 (mod 768)
//!
//! Measure q₀ and q₁:
//!   q₀ → position 192 → class c₀
//!   q₁ → position 0 → class c₁
//!
//! Updated constraint for remaining qubits:
//!   p₂ + p₃ ≡ (192 - 192 - 0) mod 768 = 0 (mod 768)
//!
//! Result: 2-qubit entangled state with new constraint
//! ```
//!
//! ## Determinism
//!
//! Unlike standard QM where measurement is probabilistic, partial measurement
//! in 768-cycle model is fully deterministic:
//! - Same positions → same measurement outcomes
//! - Same outcomes → same constraint propagation
//! - No randomness, just geometric projection

use hologram_tracing::perf_span;

use crate::constraints::entangled_state::NQubitState;

/// Measure a single qubit in N-qubit state
///
/// Returns measurement outcome and updated state with N-1 qubits.
///
/// # Arguments
///
/// * `state` - N-qubit state to measure
/// * `qubit_index` - Index of qubit to measure
///
/// # Returns
///
/// Tuple of (measurement_class, remaining_state)
///
/// # Examples
///
/// ```
/// use hologram_compiler::{create_ghz_3, measure_qubit};
///
/// let ghz = create_ghz_3();
/// let (class, remaining) = measure_qubit(&ghz, 0);
///
/// assert_eq!(remaining.num_qubits(), 2);
/// assert!(remaining.is_entangled()); // Remaining qubits still entangled
/// ```
pub fn measure_qubit(state: &NQubitState, qubit_index: usize) -> (u8, NQubitState) {
    let _span = perf_span!("quantum_state_768::partial_measurement::measure_qubit");

    assert!(qubit_index < state.num_qubits(), "Qubit index out of bounds");

    // Measure the qubit: read its position and convert to class
    let measured_position = state.qubit(qubit_index).position();
    let measured_class = (measured_position / 8) as u8;

    // Remove the measured qubit and update constraints
    let remaining_state = propagate_measurement_constraints(state, &[qubit_index], &[measured_position]);

    (measured_class, remaining_state)
}

/// Measure multiple qubits in N-qubit state
///
/// Returns measurement outcomes and updated state with N-M qubits.
///
/// # Arguments
///
/// * `state` - N-qubit state to measure
/// * `qubit_indices` - Indices of qubits to measure
///
/// # Returns
///
/// Tuple of (measurement_classes, remaining_state)
pub fn measure_qubits(state: &NQubitState, qubit_indices: &[usize]) -> (Vec<u8>, NQubitState) {
    let _span = perf_span!("quantum_state_768::partial_measurement::measure_qubits");

    assert!(!qubit_indices.is_empty(), "Must measure at least one qubit");
    assert!(
        qubit_indices.iter().all(|&i| i < state.num_qubits()),
        "Qubit index out of bounds"
    );

    // Measure all specified qubits
    let mut measured_classes = Vec::new();
    let mut measured_positions = Vec::new();

    for &index in qubit_indices {
        let position = state.qubit(index).position();
        let class = (position / 8) as u8;
        measured_classes.push(class);
        measured_positions.push(position);
    }

    // Remove measured qubits and update constraints
    let remaining_state = propagate_measurement_constraints(state, qubit_indices, &measured_positions);

    (measured_classes, remaining_state)
}

/// Update constraints after partial measurement
///
/// Given measurement outcomes for some qubits, update constraints for remaining qubits.
fn propagate_measurement_constraints(
    original_state: &NQubitState,
    measured_indices: &[usize],
    measured_positions: &[u16],
) -> NQubitState {
    let _span = perf_span!("quantum_state_768::partial_measurement::propagate_constraints");

    use crate::constraints::constraint::MultiQubitConstraint;
    use crate::constraints::entangled_state::EntanglementStructure;

    assert_eq!(measured_indices.len(), measured_positions.len());

    // Build list of remaining qubits (not measured)
    let mut remaining_qubits = Vec::new();
    for i in 0..original_state.num_qubits() {
        if !measured_indices.contains(&i) {
            remaining_qubits.push(*original_state.qubit(i));
        }
    }

    // If no qubits remain, return empty product state
    if remaining_qubits.is_empty() {
        return NQubitState::new_product(vec![]);
    }

    // If only one qubit remains, it cannot be entangled
    if remaining_qubits.len() == 1 {
        return NQubitState::new_product(remaining_qubits);
    }

    // Update entanglement structure based on measurement
    match original_state.entanglement_structure() {
        EntanglementStructure::Product => {
            // Product state remains product after measurement
            NQubitState::new_product(remaining_qubits)
        }
        EntanglementStructure::Full { constraint } => {
            // Update constraint to account for measured qubits
            // Original: c₀·p₀ + c₁·p₁ + ... + cₙ·pₙ ≡ sum (mod 768)
            // After measuring some qubits:
            // - Remove measured coefficients
            // - Adjust sum: new_sum = (sum - Σ(cᵢ·pᵢ for measured i)) mod 768

            let mut new_coefficients = Vec::new();
            let mut contribution_from_measured: i32 = 0;

            for i in 0..original_state.num_qubits() {
                if let Some(measured_idx) = measured_indices.iter().position(|&mi| mi == i) {
                    // This qubit was measured - accumulate its contribution
                    let coeff = constraint.coefficients()[i] as i32;
                    let pos = measured_positions[measured_idx] as i32;
                    contribution_from_measured += coeff * pos;
                } else {
                    // This qubit remains - keep its coefficient
                    new_coefficients.push(constraint.coefficients()[i]);
                }
            }

            // Compute new sum_modulo: (original_sum - measured_contribution) mod 768
            let original_sum = constraint.sum_modulo() as i32;
            let new_sum = (original_sum - contribution_from_measured).rem_euclid(768);

            // Create new constraint for remaining qubits
            let new_constraint = MultiQubitConstraint::new(new_coefficients, new_sum as u16);

            NQubitState::new_entangled(remaining_qubits, new_constraint)
        }
        EntanglementStructure::Partial { groups } => {
            // Handle partial entanglement measurement
            // For each group, update constraints based on which qubits were measured

            let mut remaining_groups = Vec::new();

            for group in groups.iter() {
                // Build mapping from old indices to new indices for this group
                let mut group_measured_indices = Vec::new();
                let mut group_measured_positions = Vec::new();
                let mut group_remaining_indices_old = Vec::new();
                let mut group_remaining_indices_new = Vec::new();

                for &old_group_idx in group.qubit_indices().iter() {
                    if let Some(measured_pos_idx) = measured_indices.iter().position(|&mi| mi == old_group_idx) {
                        // This qubit in the group was measured
                        group_measured_indices
                            .push(group.qubit_indices().iter().position(|&i| i == old_group_idx).unwrap());
                        group_measured_positions.push(measured_positions[measured_pos_idx]);
                    } else {
                        // This qubit in the group remains
                        let old_idx_in_group = group.qubit_indices().iter().position(|&i| i == old_group_idx).unwrap();
                        let new_global_idx = remaining_qubits
                            .iter()
                            .position(|q| {
                                // Find this qubit in remaining_qubits by matching position
                                q.position() == original_state.qubit(old_group_idx).position()
                            })
                            .unwrap();
                        group_remaining_indices_old.push(old_idx_in_group);
                        group_remaining_indices_new.push(new_global_idx);
                    }
                }

                // If all qubits in this group were measured, skip the group
                if group_remaining_indices_new.is_empty() {
                    continue;
                }

                // If only one qubit remains in this group, it's no longer entangled (skip group)
                if group_remaining_indices_new.len() == 1 {
                    continue;
                }

                // Update constraint for remaining qubits in this group
                let mut new_coefficients = Vec::new();
                let mut contribution_from_measured: i32 = 0;

                for (i, &coeff) in group.constraint().coefficients().iter().enumerate() {
                    if group_measured_indices.contains(&i) {
                        // This qubit was measured - accumulate contribution
                        let measured_idx = group_measured_indices.iter().position(|&mi| mi == i).unwrap();
                        let pos = group_measured_positions[measured_idx] as i32;
                        contribution_from_measured += (coeff as i32) * pos;
                    } else {
                        // This qubit remains - keep its coefficient
                        new_coefficients.push(coeff);
                    }
                }

                // Compute new sum_modulo
                let original_sum = group.constraint().sum_modulo() as i32;
                let new_sum = (original_sum - contribution_from_measured).rem_euclid(768);

                // Create updated group
                let new_constraint = MultiQubitConstraint::new(new_coefficients, new_sum as u16);
                let new_group =
                    super::entangled_state::EntanglementGroup::new(group_remaining_indices_new, new_constraint);
                remaining_groups.push(new_group);
            }

            // Return state with updated partial entanglement
            if remaining_groups.is_empty() {
                // No groups remain - return product state
                NQubitState::new_product(remaining_qubits)
            } else if remaining_groups.len() == 1 && remaining_groups[0].qubit_indices().len() == remaining_qubits.len()
            {
                // Only one group and it contains all qubits - convert to full entanglement
                NQubitState::new_entangled(remaining_qubits, remaining_groups[0].constraint().clone())
            } else {
                // Multiple groups or partial coverage - keep partial entanglement
                NQubitState::new_partial(remaining_qubits, remaining_groups)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_measure_single_qubit_product_state() {
        use crate::core::state::QuantumState;

        let state = NQubitState::new_product(vec![
            QuantumState::new(0),
            QuantumState::new(192),
            QuantumState::new(384),
        ]);

        let (class, remaining) = measure_qubit(&state, 1);

        assert_eq!(remaining.num_qubits(), 2);
        assert!(!remaining.is_entangled(), "Product state remains product");
        assert_eq!(class, 192 / 8); // Class should be 24
    }

    #[test]
    fn test_measure_single_qubit_ghz() {
        use crate::algorithms::ghz::create_ghz_3;

        let ghz = create_ghz_3();
        let (_class, remaining) = measure_qubit(&ghz, 0);

        assert_eq!(remaining.num_qubits(), 2);
        // After measuring one qubit of GHZ, remaining qubits should be entangled
        assert!(remaining.is_entangled(), "Remaining qubits should be constrained");
    }

    #[test]
    fn test_measure_two_of_four_qubits() {
        use crate::algorithms::ghz::create_ghz_4;

        let ghz = create_ghz_4();
        let (_classes, remaining) = measure_qubits(&ghz, &[0, 1]);

        assert_eq!(remaining.num_qubits(), 2);
        assert!(remaining.is_entangled(), "Remaining 2 qubits should be constrained");
    }

    #[test]
    fn test_measurement_determinism() {
        use crate::algorithms::ghz::create_ghz_3;

        let ghz = create_ghz_3();

        // Measure same state twice
        let (class1, remaining1) = measure_qubit(&ghz, 0);
        let (class2, remaining2) = measure_qubit(&ghz, 0);

        assert_eq!(class1, class2, "Same state → same outcome");
        assert_eq!(
            remaining1.qubit(0).position(),
            remaining2.qubit(0).position(),
            "Same propagation"
        );
    }

    #[test]
    fn test_measure_all_qubits() {
        use crate::algorithms::ghz::create_ghz_4;

        let ghz = create_ghz_4();
        let (_classes, remaining) = measure_qubits(&ghz, &[0, 1, 2]);

        assert_eq!(remaining.num_qubits(), 1);
        assert!(!remaining.is_entangled(), "Single qubit cannot be entangled");
    }

    #[test]
    fn test_measure_partial_entanglement_one_group() {
        use super::super::entangled_state::EntanglementGroup;
        use super::super::MultiQubitConstraint;
        use crate::core::state::QuantumState;

        // Create 4-qubit state with one entangled pair (0,1) and two independent qubits
        // Group: qubits 0,1 with constraint p_0 + p_1 = 192

        let qubits = vec![
            QuantumState::new(100),
            QuantumState::new(92),
            QuantumState::new(200),
            QuantumState::new(300),
        ];

        let constraint = MultiQubitConstraint::new(vec![1, 1], 192);
        let group = EntanglementGroup::new(vec![0, 1], constraint);

        let state = NQubitState::new_partial(qubits, vec![group]);

        // Measure qubit 0 from the entangled pair
        let (_class, remaining) = measure_qubit(&state, 0);

        // Should have 3 qubits remaining
        assert_eq!(remaining.num_qubits(), 3);

        // Qubit 1 (originally entangled with qubit 0) is now independent
        // because after measuring one qubit of a pair, only one remains
        assert!(!remaining.is_entangled());
    }

    #[test]
    fn test_measure_partial_entanglement_two_groups() {
        use super::super::entangled_state::EntanglementGroup;
        use super::super::MultiQubitConstraint;
        use crate::core::state::QuantumState;

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

        // Measure qubit 0 from group 1
        let (_class, remaining) = measure_qubit(&state, 0);

        // Should have 3 qubits remaining
        assert_eq!(remaining.num_qubits(), 3);

        // Group 2 should still be entangled (qubits 2,3 are now indices 1,2)
        assert!(remaining.is_entangled());
    }

    #[test]
    fn test_measure_partial_entanglement_three_qubit_group() {
        use super::super::entangled_state::EntanglementGroup;
        use super::super::MultiQubitConstraint;
        use crate::core::state::QuantumState;

        // Create 3-qubit entangled group
        // p_0 + p_1 + p_2 = 192

        let qubits = vec![QuantumState::new(100), QuantumState::new(50), QuantumState::new(42)];

        let constraint = MultiQubitConstraint::new(vec![1, 1, 1], 192);
        let group = EntanglementGroup::new(vec![0, 1, 2], constraint);

        let state = NQubitState::new_partial(qubits, vec![group]);

        // Measure qubit 0
        let (_class, remaining) = measure_qubit(&state, 0);

        // Should have 2 qubits remaining, still entangled
        assert_eq!(remaining.num_qubits(), 2);
        assert!(remaining.is_entangled());
    }

    #[test]
    fn test_measure_multiple_qubits_partial_entanglement() {
        use super::super::entangled_state::EntanglementGroup;
        use super::super::MultiQubitConstraint;
        use crate::core::state::QuantumState;

        // Create 6-qubit state with two groups of 3
        // Group 1: qubits 0,1,2 with p_0 + p_1 + p_2 = 192
        // Group 2: qubits 3,4,5 with p_3 + p_4 + p_5 = 384

        let qubits = vec![
            QuantumState::new(100),
            QuantumState::new(50),
            QuantumState::new(42),
            QuantumState::new(200),
            QuantumState::new(100),
            QuantumState::new(84),
        ];

        let constraint1 = MultiQubitConstraint::new(vec![1, 1, 1], 192);
        let constraint2 = MultiQubitConstraint::new(vec![1, 1, 1], 384);

        let group1 = EntanglementGroup::new(vec![0, 1, 2], constraint1);
        let group2 = EntanglementGroup::new(vec![3, 4, 5], constraint2);

        let state = NQubitState::new_partial(qubits, vec![group1, group2]);

        // Measure qubits 0 and 3 (one from each group)
        let (_classes, remaining) = measure_qubits(&state, &[0, 3]);

        // Should have 4 qubits remaining
        assert_eq!(remaining.num_qubits(), 4);

        // Both groups should still have 2 qubits each, still entangled
        assert!(remaining.is_entangled());
    }
}
