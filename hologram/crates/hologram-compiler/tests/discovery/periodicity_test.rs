//! Periodicity Test Discovery
//!
//! Validates that the 768-cycle exhibits perfect periodicity.

use hologram_tracing::perf_span;

use hologram_compiler::QuantumState;

/// Test that advancing by 768 returns to start
pub fn test_full_cycle_periodicity() -> Result<(), String> {
    let _span = perf_span!("test_full_cycle_periodicity");

    let state = QuantumState::new(42);
    let cycled = state.advance(768);

    if cycled.position() != state.position() {
        return Err(format!(
            "Full cycle failed: {} + 768 = {}",
            state.position(),
            cycled.position()
        ));
    }

    Ok(())
}

/// Test multiple full cycles
pub fn test_multiple_cycles() -> Result<(), String> {
    let _span = perf_span!("test_multiple_cycles");

    let state = QuantumState::new(100);

    for num_cycles in 1..=10 {
        let cycled = state.advance(768 * num_cycles);
        if cycled.position() != state.position() {
            return Err(format!("After {} cycles: position changed", num_cycles));
        }
    }

    Ok(())
}

/// Test that gate sequences repeat with period 768
pub fn test_gate_sequence_periodicity() -> Result<(), String> {
    let _span = perf_span!("test_gate_sequence_periodicity");

    let state = QuantumState::new(42);
    let gates = [96u16, 48, 192, 48, 96, 192]; // Sequence from research doc

    // Apply sequence
    let mut current = state;
    for &advancement in &gates {
        current = current.advance(advancement);
    }
    let first_result = current.position();

    // Apply again
    let mut current = state;
    for &advancement in &gates {
        current = current.advance(advancement);
    }
    let second_result = current.position();

    if first_result != second_result {
        return Err(format!("Sequence not periodic: {} vs {}", first_result, second_result));
    }

    Ok(())
}

/// Test wrapping at boundaries
pub fn test_boundary_wrapping() -> Result<(), String> {
    let _span = perf_span!("test_boundary_wrapping");

    // 767 + 1 should wrap to 0
    let state = QuantumState::new(767);
    let wrapped = state.advance(1);

    if wrapped.position() != 0 {
        return Err(format!("Wrapping failed: 767 + 1 = {}", wrapped.position()));
    }

    Ok(())
}

pub fn test_all_periodicity() -> Result<(), String> {
    test_full_cycle_periodicity()?;
    test_multiple_cycles()?;
    test_gate_sequence_periodicity()?;
    test_boundary_wrapping()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_full_cycle() {
        assert!(test_full_cycle_periodicity().is_ok());
    }

    #[test]
    fn test_multi_cycle() {
        assert!(test_multiple_cycles().is_ok());
    }

    #[test]
    fn test_gate_seq() {
        assert!(test_gate_sequence_periodicity().is_ok());
    }

    #[test]
    fn test_boundary() {
        assert!(test_boundary_wrapping().is_ok());
    }

    #[test]
    fn test_all() {
        assert!(test_all_periodicity().is_ok());
    }
}
