//! Gate Advancement Correctness Discovery Test
//!
//! Validates that quantum gates produce the correct cycle advancements as
//! specified in the 768-cycle research.

use hologram_tracing::perf_span;

use hologram_compiler::{apply_hadamard, apply_pauli_x, apply_pauli_z, apply_t_gate, QuantumState};

/// Test that H gate advances by 192 (quarter cycle)
pub fn test_hadamard_advancement() -> Result<(), String> {
    let _span = perf_span!("test_hadamard_advancement");

    let state = QuantumState::new(0);
    let result = apply_hadamard(state);

    if result.position() != 192 {
        return Err(format!("H gate: expected 192, got {}", result.position()));
    }

    Ok(())
}

/// Test that X gate advances by 384 (half cycle)
pub fn test_pauli_x_advancement() -> Result<(), String> {
    let _span = perf_span!("test_pauli_x_advancement");

    let state = QuantumState::new(0);
    let result = apply_pauli_x(state);

    if result.position() != 384 {
        return Err(format!("X gate: expected 384, got {}", result.position()));
    }

    Ok(())
}

/// Test that Z gate advances by 384 (half cycle)
pub fn test_pauli_z_advancement() -> Result<(), String> {
    let _span = perf_span!("test_pauli_z_advancement");

    let state = QuantumState::new(0);
    let result = apply_pauli_z(state);

    if result.position() != 384 {
        return Err(format!("Z gate: expected 384, got {}", result.position()));
    }

    Ok(())
}

/// Test that T gate advances by 96 (eighth cycle)
pub fn test_t_gate_advancement() -> Result<(), String> {
    let _span = perf_span!("test_t_gate_advancement");

    let state = QuantumState::new(0);
    let result = apply_t_gate(state);

    if result.position() != 96 {
        return Err(format!("T gate: expected 96, got {}", result.position()));
    }

    Ok(())
}

/// Test all gate advancements
pub fn test_all_gate_advancements() -> Result<(), String> {
    test_hadamard_advancement()?;
    test_pauli_x_advancement()?;
    test_pauli_z_advancement()?;
    test_t_gate_advancement()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use hologram_compiler::QuantumGate;

    #[test]
    fn test_h_advances_192() {
        assert!(test_hadamard_advancement().is_ok());
    }

    #[test]
    fn test_x_advances_384() {
        assert!(test_pauli_x_advancement().is_ok());
    }

    #[test]
    fn test_z_advances_384() {
        assert!(test_pauli_z_advancement().is_ok());
    }

    #[test]
    fn test_t_advances_96() {
        assert!(test_t_gate_advancement().is_ok());
    }

    #[test]
    fn test_all_gates() {
        assert!(test_all_gate_advancements().is_ok());
    }

    #[test]
    fn test_gate_enum_advancements() {
        assert_eq!(QuantumGate::Hadamard.advancement(), 192);
        assert_eq!(QuantumGate::PauliX.advancement(), 384);
        assert_eq!(QuantumGate::PauliZ.advancement(), 384);
        assert_eq!(QuantumGate::TGate.advancement(), 96);
        assert_eq!(QuantumGate::Identity.advancement(), 0);
    }
}
