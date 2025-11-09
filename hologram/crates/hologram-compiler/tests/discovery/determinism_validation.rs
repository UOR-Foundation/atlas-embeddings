//! Determinism Validation Discovery Test
//!
//! This discovery test validates the core hypothesis: **Same cycle position → same measurement outcome**
//!
//! ## Hypothesis
//!
//! Quantum measurement is deterministic given the cycle position. Unlike Copenhagen
//! interpretation which treats measurement as fundamentally probabilistic "collapse",
//! the 768-cycle model predicts 100% reproducibility when measuring the same state.
//!
//! ## Methodology
//!
//! 1. Create quantum states at various positions in the 768-cycle
//! 2. Measure each state multiple times
//! 3. Verify that all measurements yield identical results
//! 4. Test across different positions and modalities
//!
//! ## Expected Result
//!
//! **100% deterministic**: Same position always yields same class

use hologram_tracing::perf_span;

use hologram_compiler::{measure_quantum_state, Modality, QuantumState};

/// Test determinism for a single quantum state
pub fn test_single_state_determinism(position: u16, num_measurements: usize) -> Result<(), String> {
    let _span = perf_span!(
        "test_single_state_determinism",
        position = position,
        measurements = num_measurements
    );

    let state = QuantumState::new(position);
    let first_measurement = measure_quantum_state(state);

    for i in 1..num_measurements {
        let measurement = measure_quantum_state(state);
        if measurement != first_measurement {
            return Err(format!(
                "Non-deterministic measurement at position {}! First: {}, Measurement {}: {}",
                position, first_measurement, i, measurement
            ));
        }
    }

    Ok(())
}

/// Test determinism across multiple positions
pub fn test_determinism_across_positions() -> Result<(), String> {
    let _span = perf_span!("test_determinism_across_positions");

    // Test positions matching the research document validation
    let test_positions = vec![0, 100, 200, 300, 400, 500, 600, 700];

    for position in test_positions {
        test_single_state_determinism(position, 100)?;
    }

    Ok(())
}

/// Test determinism across all modalities
pub fn test_determinism_across_modalities() -> Result<(), String> {
    let _span = perf_span!("test_determinism_across_modalities");

    let test_bytes = vec![0x00, 0x2A, 0x7F, 0xFF];

    for byte in test_bytes {
        // Test each modality
        let neutral = QuantumState::from_byte_modality(byte, Modality::Neutral);
        let produce = QuantumState::from_byte_modality(byte, Modality::Produce);
        let consume = QuantumState::from_byte_modality(byte, Modality::Consume);

        test_single_state_determinism(neutral.position(), 100)?;
        test_single_state_determinism(produce.position(), 100)?;
        test_single_state_determinism(consume.position(), 100)?;
    }

    Ok(())
}

/// Test determinism with high sample count (statistical validation)
pub fn test_determinism_statistical() -> Result<(), String> {
    let _span = perf_span!("test_determinism_statistical");

    // Pick 20 random-ish positions and test with 1000 measurements each
    let positions = (0..20).map(|i| (i * 38) % 768).collect::<Vec<_>>();

    for position in positions {
        test_single_state_determinism(position, 1000)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_position_0_determinism() {
        // Position 0 should always measure to same class
        let result = test_single_state_determinism(0, 1000);
        assert!(result.is_ok(), "Position 0 measurement not deterministic: {:?}", result);
    }

    #[test]
    fn test_position_100_determinism() {
        let result = test_single_state_determinism(100, 1000);
        assert!(
            result.is_ok(),
            "Position 100 measurement not deterministic: {:?}",
            result
        );
    }

    #[test]
    fn test_position_767_determinism() {
        // Test boundary position
        let result = test_single_state_determinism(767, 1000);
        assert!(
            result.is_ok(),
            "Position 767 measurement not deterministic: {:?}",
            result
        );
    }

    #[test]
    fn test_all_test_positions_deterministic() {
        let result = test_determinism_across_positions();
        assert!(result.is_ok(), "Some positions not deterministic: {:?}", result);
    }

    #[test]
    fn test_all_modalities_deterministic() {
        let result = test_determinism_across_modalities();
        assert!(result.is_ok(), "Some modalities not deterministic: {:?}", result);
    }

    #[test]
    fn test_statistical_determinism() {
        let result = test_determinism_statistical();
        assert!(result.is_ok(), "Statistical validation failed: {:?}", result);
    }

    #[test]
    fn test_expected_classes_from_research() {
        // From research document, these positions gave specific classes
        // Position 0: class c0
        let state_0 = QuantumState::new(0);
        let class_0 = measure_quantum_state(state_0);
        assert_eq!(class_0, 0, "Position 0 should measure to class 0");

        // Verify determinism for these specific cases
        for _ in 0..100 {
            assert_eq!(measure_quantum_state(state_0), class_0);
        }
    }

    #[test]
    fn test_comprehensive_determinism() {
        // Test every 10th position across the full cycle
        for position in (0..768).step_by(10) {
            let result = test_single_state_determinism(position, 100);
            assert!(result.is_ok(), "Position {} not deterministic: {:?}", position, result);
        }
    }
}
