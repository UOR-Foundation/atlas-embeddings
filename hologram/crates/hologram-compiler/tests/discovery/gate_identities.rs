//! Gate Identities Discovery Test
//!
//! Validates that quantum gate identities (H²=I, X²=I, etc.) hold in the 768-cycle model.

use hologram_tracing::perf_span;

use hologram_compiler::{
    apply_hadamard, apply_pauli_x, apply_pauli_z, apply_s_gate, apply_t_gate, QuantumState,
};

/// Test X² = I (two X gates return to start)
pub fn test_x_squared_equals_identity() -> Result<(), String> {
    let _span = perf_span!("test_x_squared_equals_identity");

    let state = QuantumState::new(100);
    let once = apply_pauli_x(state);
    let twice = apply_pauli_x(once);

    if twice.position() != state.position() {
        return Err(format!(
            "X² ≠ I: start={}, after X²={}",
            state.position(),
            twice.position()
        ));
    }

    Ok(())
}

/// Test Z² = I
pub fn test_z_squared_equals_identity() -> Result<(), String> {
    let _span = perf_span!("test_z_squared_equals_identity");

    let state = QuantumState::new(100);
    let once = apply_pauli_z(state);
    let twice = apply_pauli_z(once);

    if twice.position() != state.position() {
        return Err(format!(
            "Z² ≠ I: start={}, after Z²={}",
            state.position(),
            twice.position()
        ));
    }

    Ok(())
}

/// Test T⁸ = I (eight T gates return to start)
pub fn test_t_to_eighth_equals_identity() -> Result<(), String> {
    let _span = perf_span!("test_t_to_eighth_equals_identity");

    let state = QuantumState::new(0);
    let mut current = state;

    for _ in 0..8 {
        current = apply_t_gate(current);
    }

    if current.position() != state.position() {
        return Err(format!(
            "T⁸ ≠ I: start={}, after T⁸={}",
            state.position(),
            current.position()
        ));
    }

    Ok(())
}

/// Test S² = Z (two S gates equal one Z gate)
pub fn test_s_squared_equals_z() -> Result<(), String> {
    let _span = perf_span!("test_s_squared_equals_z");

    let state = QuantumState::new(0);
    let s_twice = apply_s_gate(apply_s_gate(state));
    let z_once = apply_pauli_z(state);

    if s_twice.position() != z_once.position() {
        return Err(format!("S² ≠ Z: S²={}, Z={}", s_twice.position(), z_once.position()));
    }

    Ok(())
}

/// Test S = T² (S gate equals two T gates)
pub fn test_s_equals_t_squared() -> Result<(), String> {
    let _span = perf_span!("test_s_equals_t_squared");

    let state = QuantumState::new(0);
    let s_once = apply_s_gate(state);
    let t_twice = apply_t_gate(apply_t_gate(state));

    if s_once.position() != t_twice.position() {
        return Err(format!("S ≠ T²: S={}, T²={}", s_once.position(), t_twice.position()));
    }

    Ok(())
}

/// Test H² behavior (note: H² = -I in standard QM, which maps to 384 in 768-cycle)
pub fn test_h_squared() -> Result<(), String> {
    let _span = perf_span!("test_h_squared");

    let state = QuantumState::new(0);
    let once = apply_hadamard(state);
    let twice = apply_hadamard(once);

    // H² = 192 + 192 = 384 (half cycle)
    if twice.position() != 384 {
        return Err(format!("H² expected 384, got {}", twice.position()));
    }

    Ok(())
}

pub fn test_all_gate_identities() -> Result<(), String> {
    test_x_squared_equals_identity()?;
    test_z_squared_equals_identity()?;
    test_t_to_eighth_equals_identity()?;
    test_s_squared_equals_z()?;
    test_s_equals_t_squared()?;
    test_h_squared()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_x_squared() {
        assert!(test_x_squared_equals_identity().is_ok());
    }

    #[test]
    fn test_z_squared() {
        assert!(test_z_squared_equals_identity().is_ok());
    }

    #[test]
    fn test_t_eighth() {
        assert!(test_t_to_eighth_equals_identity().is_ok());
    }

    #[test]
    fn test_s_squared() {
        assert!(test_s_squared_equals_z().is_ok());
    }

    #[test]
    fn test_s_t_squared() {
        assert!(test_s_equals_t_squared().is_ok());
    }

    #[test]
    fn test_h_sq() {
        assert!(test_h_squared().is_ok());
    }

    #[test]
    fn test_all() {
        assert!(test_all_gate_identities().is_ok());
    }
}
