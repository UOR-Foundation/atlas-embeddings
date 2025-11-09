//! CNOT Gate Correctness Validation
//!
//! This discovery test validates that the CNOT gate implementation correctly
//! implements the control-NOT truth table and creates entanglement when appropriate.
//!
//! ## CNOT Truth Table
//!
//! ```text
//! Input   → Output
//! |00⟩    → |00⟩     (control=0: no change, no entanglement)
//! |01⟩    → |01⟩     (control=0: no change, no entanglement)
//! |10⟩    → |11⟩     (control=1: flip target, creates entanglement)
//! |11⟩    → |10⟩     (control=1: flip target, creates entanglement)
//! ```
//!
//! ## Success Criteria
//!
//! 1. ✅ All truth table entries produce correct output states
//! 2. ✅ Entanglement created when control qubit is |1⟩
//! 3. ✅ No entanglement when control qubit is |0⟩
//! 4. ✅ Correlation constraint correctly established
//! 5. ✅ Cycle positions match expected advancements

#[cfg(test)]
use hologram_compiler::{apply_cnot, QuantumState, TwoQubitState};

#[test]
fn test_cnot_00_to_00() {
    println!("\n=== CNOT Truth Table: |00⟩ → |00⟩ ===");

    // Create |00⟩ state
    let state = TwoQubitState::new_product(QuantumState::new(0), QuantumState::new(0));

    println!(
        "Input:  qubit_0 = {}, qubit_1 = {}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    // Apply CNOT with control=0, target=1
    let result = apply_cnot(state, 0, 1);

    println!(
        "Output: qubit_0 = {}, qubit_1 = {}",
        result.qubit_0().position(),
        result.qubit_1().position()
    );
    println!("Entangled: {}", result.is_entangled());

    // Verify output is still |00⟩
    assert_eq!(result.qubit_0().position(), 0, "Control qubit should be unchanged");
    assert_eq!(result.qubit_1().position(), 0, "Target qubit should be unchanged");

    // Verify no entanglement (control is |0⟩)
    assert!(!result.is_entangled(), "Should not be entangled when control is |0⟩");

    println!("✅ CNOT |00⟩ → |00⟩ PASSED");
}

#[test]
fn test_cnot_01_to_01() {
    println!("\n=== CNOT Truth Table: |01⟩ → |01⟩ ===");

    // Create |01⟩ state (qubit_0=|0⟩, qubit_1=|1⟩)
    let state = TwoQubitState::new_product(QuantumState::new(0), QuantumState::new(384));

    println!(
        "Input:  qubit_0 = {}, qubit_1 = {}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    // Apply CNOT with control=0, target=1
    let result = apply_cnot(state, 0, 1);

    println!(
        "Output: qubit_0 = {}, qubit_1 = {}",
        result.qubit_0().position(),
        result.qubit_1().position()
    );
    println!("Entangled: {}", result.is_entangled());

    // Verify output is still |01⟩
    assert_eq!(result.qubit_0().position(), 0, "Control qubit should be unchanged");
    assert_eq!(result.qubit_1().position(), 384, "Target qubit should be unchanged");

    // Verify no entanglement (control is |0⟩)
    assert!(!result.is_entangled(), "Should not be entangled when control is |0⟩");

    println!("✅ CNOT |01⟩ → |01⟩ PASSED");
}

#[test]
fn test_cnot_10_to_11() {
    println!("\n=== CNOT Truth Table: |10⟩ → |11⟩ ===");

    // Create |10⟩ state (qubit_0=|1⟩, qubit_1=|0⟩)
    let state = TwoQubitState::new_product(QuantumState::new(384), QuantumState::new(0));

    println!(
        "Input:  qubit_0 = {}, qubit_1 = {}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    // Apply CNOT with control=0, target=1
    let result = apply_cnot(state, 0, 1);

    println!(
        "Output: qubit_0 = {}, qubit_1 = {}",
        result.qubit_0().position(),
        result.qubit_1().position()
    );
    println!("Entangled: {}", result.is_entangled());

    // Verify control unchanged
    assert_eq!(result.qubit_0().position(), 384, "Control qubit should be unchanged");

    // Verify target flipped: 0 + 384 (X gate) = 384
    assert_eq!(
        result.qubit_1().position(),
        384,
        "Target qubit should be flipped to |1⟩"
    );

    // Verify entanglement created (control is |1⟩)
    assert!(result.is_entangled(), "Should be entangled when control is |1⟩");

    // Verify correlation constraint
    let constraint = result
        .correlation_constraint()
        .expect("Should have correlation constraint");
    let sum = (result.qubit_0().position() + result.qubit_1().position()) % 768;
    assert_eq!(
        constraint.sum_modulo(),
        sum,
        "Correlation constraint should match qubit positions"
    );

    println!("✅ CNOT |10⟩ → |11⟩ PASSED");
}

#[test]
fn test_cnot_11_to_10() {
    println!("\n=== CNOT Truth Table: |11⟩ → |10⟩ ===");

    // Create |11⟩ state (qubit_0=|1⟩, qubit_1=|1⟩)
    let state = TwoQubitState::new_product(QuantumState::new(384), QuantumState::new(384));

    println!(
        "Input:  qubit_0 = {}, qubit_1 = {}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    // Apply CNOT with control=0, target=1
    let result = apply_cnot(state, 0, 1);

    println!(
        "Output: qubit_0 = {}, qubit_1 = {}",
        result.qubit_0().position(),
        result.qubit_1().position()
    );
    println!("Entangled: {}", result.is_entangled());

    // Verify control unchanged
    assert_eq!(result.qubit_0().position(), 384, "Control qubit should be unchanged");

    // Verify target flipped: 384 + 384 (X gate) = 768 ≡ 0 (mod 768)
    assert_eq!(result.qubit_1().position(), 0, "Target qubit should be flipped to |0⟩");

    // Verify entanglement created (control is |1⟩)
    assert!(result.is_entangled(), "Should be entangled when control is |1⟩");

    // Verify correlation constraint
    let constraint = result
        .correlation_constraint()
        .expect("Should have correlation constraint");
    let sum = (result.qubit_0().position() + result.qubit_1().position()) % 768;
    assert_eq!(
        constraint.sum_modulo(),
        sum,
        "Correlation constraint should match qubit positions"
    );

    println!("✅ CNOT |11⟩ → |10⟩ PASSED");
}

#[test]
fn test_cnot_with_arbitrary_positions() {
    println!("\n=== CNOT with Arbitrary Cycle Positions ===");

    // Test with positions that aren't exactly 0 or 384
    // but are in the |0⟩ and |1⟩ computational basis regions

    // Position 100 is in [0, 384) → computational |0⟩
    // Position 500 is in [384, 768) → computational |1⟩

    let state = TwoQubitState::new_product(QuantumState::new(500), QuantumState::new(100));

    println!(
        "Input:  qubit_0 = {} (|1⟩), qubit_1 = {} (|0⟩)",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    let result = apply_cnot(state, 0, 1);

    println!(
        "Output: qubit_0 = {}, qubit_1 = {}",
        result.qubit_0().position(),
        result.qubit_1().position()
    );

    // Control unchanged
    assert_eq!(result.qubit_0().position(), 500);

    // Target flipped: 100 + 384 = 484
    assert_eq!(result.qubit_1().position(), 484);

    // Should be entangled
    assert!(result.is_entangled());

    println!("✅ CNOT with arbitrary positions PASSED");
}

#[test]
fn test_cnot_control_target_swapped() {
    println!("\n=== CNOT with Swapped Control and Target ===");

    // Test CNOT with control=1, target=0 (reversed order)
    let state = TwoQubitState::new_product(QuantumState::new(0), QuantumState::new(384));

    println!(
        "Input:  qubit_0 = {}, qubit_1 = {}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );
    println!("Applying CNOT(control=1, target=0)");

    // Control=qubit_1, target=qubit_0
    let result = apply_cnot(state, 1, 0);

    println!(
        "Output: qubit_0 = {}, qubit_1 = {}",
        result.qubit_0().position(),
        result.qubit_1().position()
    );

    // qubit_1 is control (|1⟩), so qubit_0 should be flipped
    // 0 + 384 = 384
    assert_eq!(result.qubit_0().position(), 384, "Target (qubit_0) should be flipped");
    assert_eq!(result.qubit_1().position(), 384, "Control (qubit_1) unchanged");
    assert!(result.is_entangled());

    println!("✅ CNOT with swapped control/target PASSED");
}

#[test]
fn test_cnot_double_application_returns_to_original() {
    println!("\n=== Double CNOT Application ===");

    // CNOT is self-inverse: CNOT² = I
    let state = TwoQubitState::new_product(QuantumState::new(384), QuantumState::new(0));

    println!(
        "Original: qubit_0 = {}, qubit_1 = {}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    // First CNOT: |10⟩ → |11⟩
    let once = apply_cnot(state.clone(), 0, 1);
    println!(
        "After 1x: qubit_0 = {}, qubit_1 = {}",
        once.qubit_0().position(),
        once.qubit_1().position()
    );

    // Second CNOT: |11⟩ → |10⟩
    let twice = apply_cnot(once, 0, 1);
    println!(
        "After 2x: qubit_0 = {}, qubit_1 = {}",
        twice.qubit_0().position(),
        twice.qubit_1().position()
    );

    // Should return to original state
    assert_eq!(twice.qubit_0().position(), state.qubit_0().position());
    assert_eq!(twice.qubit_1().position(), state.qubit_1().position());

    println!("✅ Double CNOT returns to original PASSED");
}

#[test]
fn test_cnot_entanglement_correlation_constraint() {
    println!("\n=== CNOT Entanglement Correlation Constraint ===");

    // When CNOT creates entanglement, verify the correlation constraint is correct
    let state = TwoQubitState::new_product(QuantumState::new(500), QuantumState::new(200));

    let result = apply_cnot(state, 0, 1);

    if result.is_entangled() {
        let constraint = result.correlation_constraint().expect("Should have constraint");

        // Verify positions satisfy constraint
        assert!(
            constraint.are_positions_correlated(result.qubit_0().position(), result.qubit_1().position()),
            "Positions should satisfy correlation constraint"
        );

        // Verify sum modulo matches
        let expected_sum = (result.qubit_0().position() + result.qubit_1().position()) % 768;
        assert_eq!(constraint.sum_modulo(), expected_sum);

        println!(
            "Correlation constraint: p_0 + p_1 ≡ {} (mod 768)",
            constraint.sum_modulo()
        );
        println!("✅ Correlation constraint validated");
    }

    println!("✅ CNOT entanglement correlation PASSED");
}
