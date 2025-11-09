//! Measurement Projection Discovery Test
//!
//! Validates that measurement correctly projects from 768 states to 96 canonical classes.

use hologram_tracing::perf_span;

use hologram_compiler::{measure_quantum_state, project_to_class, QuantumState, CLASS_COUNT};

/// Test that all measurements produce valid class indices
pub fn test_all_measurements_valid() -> Result<(), String> {
    let _span = perf_span!("test_all_measurements_valid");

    for position in 0..768 {
        let state = QuantumState::new(position);
        let class = measure_quantum_state(state);

        if class >= CLASS_COUNT {
            return Err(format!("Position {} measured to invalid class {}", position, class));
        }
    }

    Ok(())
}

/// Test that all 96 classes are reachable
pub fn test_all_classes_reachable() -> Result<(), String> {
    let _span = perf_span!("test_all_classes_reachable");

    let mut classes_seen = vec![false; CLASS_COUNT as usize];

    for position in 0..768 {
        let state = QuantumState::new(position);
        let class = measure_quantum_state(state);
        classes_seen[class as usize] = true;
    }

    let num_seen = classes_seen.iter().filter(|&&x| x).count();

    if num_seen != CLASS_COUNT as usize {
        return Err(format!("Only {} of {} classes reachable", num_seen, CLASS_COUNT));
    }

    Ok(())
}

/// Test projection from bytes
pub fn test_byte_projection() -> Result<(), String> {
    let _span = perf_span!("test_byte_projection");

    for byte in 0..=255 {
        let class = project_to_class(byte);
        if class >= CLASS_COUNT {
            return Err(format!("Byte {} projects to invalid class {}", byte, class));
        }
    }

    Ok(())
}

pub fn test_all_projection() -> Result<(), String> {
    test_all_measurements_valid()?;
    test_all_classes_reachable()?;
    test_byte_projection()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_measurements_valid() {
        assert!(test_all_measurements_valid().is_ok());
    }

    #[test]
    fn test_classes_reachable() {
        assert!(test_all_classes_reachable().is_ok());
    }

    #[test]
    fn test_bytes_project() {
        assert!(test_byte_projection().is_ok());
    }

    #[test]
    fn test_all() {
        assert!(test_all_projection().is_ok());
    }
}
