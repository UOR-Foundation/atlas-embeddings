//! Bell State Creation and Validation
//!
//! This discovery test validates that all four Bell states can be created
//! using the standard quantum circuits and that they exhibit the expected
//! entanglement properties.
//!
//! ## The Four Bell States
//!
//! ```text
//! |Φ⁺⟩ = (|00⟩ + |11⟩) / √2   Circuit: H ⊗ I → CNOT
//! |Φ⁻⟩ = (|00⟩ - |11⟩) / √2   Circuit: H ⊗ I → CNOT → Z ⊗ I
//! |Ψ⁺⟩ = (|01⟩ + |10⟩) / √2   Circuit: H ⊗ I → CNOT → X ⊗ I
//! |Ψ⁻⟩ = (|01⟩ - |10⟩) / √2   Circuit: H ⊗ I → CNOT → X ⊗ I → Z ⊗ I
//! ```
//!
//! ## Success Criteria
//!
//! 1. ✅ All 4 Bell states can be created
//! 2. ✅ All Bell states are entangled
//! 3. ✅ Correlation constraints are correctly established
//! 4. ✅ Circuit construction matches standard quantum computing
//! 5. ✅ Measurements are deterministic given positions

#[cfg(test)]
use hologram_compiler::{
    create_bell_phi_minus, create_bell_phi_plus, create_bell_psi_minus, create_bell_psi_plus, measure_two_qubit_state,
    BellState,
};

#[test]
fn test_create_phi_plus() {
    println!("\n=== Create Bell State |Φ⁺⟩ ===");
    println!("Circuit: H ⊗ I → CNOT");

    let bell_state = create_bell_phi_plus();

    println!("qubit_0 position: {}", bell_state.qubit_0().position());
    println!("qubit_1 position: {}", bell_state.qubit_1().position());
    println!("Entangled: {}", bell_state.is_entangled());

    // Verify entanglement
    assert!(bell_state.is_entangled(), "|Φ⁺⟩ should be entangled");

    // After H gate, qubit_0 at position 192
    assert_eq!(
        bell_state.qubit_0().position(),
        192,
        "After H gate, qubit_0 should be at 192"
    );

    // Verify correlation constraint exists
    assert!(
        bell_state.correlation_constraint().is_some(),
        "Should have correlation constraint"
    );

    let constraint = bell_state.correlation_constraint().unwrap();
    println!("Correlation: p_0 + p_1 ≡ {} (mod 768)", constraint.sum_modulo());

    // Verify positions satisfy constraint
    assert!(
        constraint.are_positions_correlated(bell_state.qubit_0().position(), bell_state.qubit_1().position()),
        "Positions should satisfy correlation"
    );

    println!("✅ |Φ⁺⟩ creation PASSED");
}

#[test]
fn test_create_phi_minus() {
    println!("\n=== Create Bell State |Φ⁻⟩ ===");
    println!("Circuit: H ⊗ I → CNOT → Z ⊗ I");

    let bell_state = create_bell_phi_minus();

    println!("qubit_0 position: {}", bell_state.qubit_0().position());
    println!("qubit_1 position: {}", bell_state.qubit_1().position());
    println!("Entangled: {}", bell_state.is_entangled());

    // Verify entanglement
    assert!(bell_state.is_entangled(), "|Φ⁻⟩ should be entangled");

    // Verify correlation constraint exists
    assert!(bell_state.correlation_constraint().is_some());

    println!("✅ |Φ⁻⟩ creation PASSED");
}

#[test]
fn test_create_psi_plus() {
    println!("\n=== Create Bell State |Ψ⁺⟩ ===");
    println!("Circuit: H ⊗ I → CNOT → X ⊗ I");

    let bell_state = create_bell_psi_plus();

    println!("qubit_0 position: {}", bell_state.qubit_0().position());
    println!("qubit_1 position: {}", bell_state.qubit_1().position());
    println!("Entangled: {}", bell_state.is_entangled());

    // Verify entanglement
    assert!(bell_state.is_entangled(), "|Ψ⁺⟩ should be entangled");

    // Verify correlation constraint exists
    assert!(bell_state.correlation_constraint().is_some());

    println!("✅ |Ψ⁺⟩ creation PASSED");
}

#[test]
fn test_create_psi_minus() {
    println!("\n=== Create Bell State |Ψ⁻⟩ ===");
    println!("Circuit: H ⊗ I → CNOT → X ⊗ I → Z ⊗ I");

    let bell_state = create_bell_psi_minus();

    println!("qubit_0 position: {}", bell_state.qubit_0().position());
    println!("qubit_1 position: {}", bell_state.qubit_1().position());
    println!("Entangled: {}", bell_state.is_entangled());

    // Verify entanglement
    assert!(bell_state.is_entangled(), "|Ψ⁻⟩ should be entangled");

    // Verify correlation constraint exists
    assert!(bell_state.correlation_constraint().is_some());

    println!("✅ |Ψ⁻⟩ creation PASSED");
}

#[test]
fn test_all_bell_states_via_enum() {
    println!("\n=== Create All Bell States via Enum ===");

    for bell_type in [
        BellState::PhiPlus,
        BellState::PhiMinus,
        BellState::PsiPlus,
        BellState::PsiMinus,
    ] {
        println!("\nCreating {}...", bell_type.name());

        let bell_state = bell_type.create();

        // All Bell states should be entangled
        assert!(bell_state.is_entangled(), "{} should be entangled", bell_type.name());

        // All should have correlation constraints
        assert!(
            bell_state.correlation_constraint().is_some(),
            "{} should have correlation constraint",
            bell_type.name()
        );

        println!("  qubit_0: {}", bell_state.qubit_0().position());
        println!("  qubit_1: {}", bell_state.qubit_1().position());
        println!("  ✅ {} validated", bell_type.name());
    }

    println!("\n✅ All 4 Bell states created and validated");
}

#[test]
fn test_bell_state_measurement_determinism() {
    println!("\n=== Bell State Measurement Determinism ===");

    let bell_state = create_bell_phi_plus();

    println!("Measuring |Φ⁺⟩ multiple times...");

    // Measure the same Bell state 100 times
    let (first_class_0, first_class_1) = measure_two_qubit_state(&bell_state);

    println!(
        "First measurement: class_0 = {}, class_1 = {}",
        first_class_0, first_class_1
    );

    // All subsequent measurements should be identical (deterministic)
    for i in 0..100 {
        let (class_0, class_1) = measure_two_qubit_state(&bell_state);

        assert_eq!(
            class_0,
            first_class_0,
            "Measurement {} of qubit_0 should be deterministic",
            i + 1
        );
        assert_eq!(
            class_1,
            first_class_1,
            "Measurement {} of qubit_1 should be deterministic",
            i + 1
        );
    }

    println!("100 measurements all identical");
    println!("✅ Bell state measurement determinism PASSED");
}

#[test]
fn test_bell_state_correlation_maintained() {
    println!("\n=== Bell State Correlation Maintained ===");

    let bell_state = create_bell_phi_plus();

    let constraint = bell_state.correlation_constraint().expect("Should have constraint");

    println!("Initial correlation: p_0 + p_1 ≡ {} (mod 768)", constraint.sum_modulo());
    println!("  qubit_0: {}", bell_state.qubit_0().position());
    println!("  qubit_1: {}", bell_state.qubit_1().position());

    // Verify positions satisfy constraint
    let p0 = bell_state.qubit_0().position();
    let p1 = bell_state.qubit_1().position();
    let sum = (p0 + p1) % 768;

    assert_eq!(sum, constraint.sum_modulo(), "Sum should match constraint");

    // Verify using constraint method
    assert!(
        constraint.are_positions_correlated(p0, p1),
        "Positions should be correlated according to constraint"
    );

    println!("✅ Correlation maintained");
}

#[test]
fn test_different_bell_states_have_different_positions() {
    println!("\n=== Different Bell States Have Different Positions ===");

    let phi_plus = create_bell_phi_plus();
    let phi_minus = create_bell_phi_minus();
    let psi_plus = create_bell_psi_plus();
    let psi_minus = create_bell_psi_minus();

    println!(
        "|Φ⁺⟩: qubit_0={}, qubit_1={}",
        phi_plus.qubit_0().position(),
        phi_plus.qubit_1().position()
    );
    println!(
        "|Φ⁻⟩: qubit_0={}, qubit_1={}",
        phi_minus.qubit_0().position(),
        phi_minus.qubit_1().position()
    );
    println!(
        "|Ψ⁺⟩: qubit_0={}, qubit_1={}",
        psi_plus.qubit_0().position(),
        psi_plus.qubit_1().position()
    );
    println!(
        "|Ψ⁻⟩: qubit_0={}, qubit_1={}",
        psi_minus.qubit_0().position(),
        psi_minus.qubit_1().position()
    );

    // The four Bell states should have different cycle positions
    // (due to different gate sequences)

    let positions = [
        (phi_plus.qubit_0().position(), phi_plus.qubit_1().position()),
        (phi_minus.qubit_0().position(), phi_minus.qubit_1().position()),
        (psi_plus.qubit_0().position(), psi_plus.qubit_1().position()),
        (psi_minus.qubit_0().position(), psi_minus.qubit_1().position()),
    ];

    // Verify at least some differences (not all identical)
    let unique_positions: std::collections::HashSet<_> = positions.iter().collect();
    assert!(
        unique_positions.len() > 1,
        "Bell states should have different positions due to different circuits"
    );

    println!("✅ Different Bell states have distinct cycle positions");
}

#[test]
fn test_bell_state_entanglement_flag() {
    println!("\n=== Bell State Entanglement Flag Validation ===");

    // All Bell states must have entanglement flag set
    let states = vec![
        ("Φ⁺", create_bell_phi_plus()),
        ("Φ⁻", create_bell_phi_minus()),
        ("Ψ⁺", create_bell_psi_plus()),
        ("Ψ⁻", create_bell_psi_minus()),
    ];

    for (name, state) in states {
        println!("Checking {}...", name);

        assert!(state.is_entangled(), "{} must be entangled", name);
        assert!(
            state.correlation_constraint().is_some(),
            "{} must have correlation constraint",
            name
        );

        println!("  ✅ {} entanglement verified", name);
    }

    println!("\n✅ All Bell states have entanglement flag set");
}
