//! Discovery Tests: Partial Measurement
//!
//! Validates partial measurement and constraint propagation.
//!
//! ## Success Criteria
//!
//! 1. ✅ Measuring subset of qubits leaves remaining qubits in valid state
//! 2. ✅ Constraints propagate correctly after measurement
//! 3. ✅ Determinism: same state → same measurement → same propagation
//! 4. ✅ Measurement of product state gives product state
//! 5. ✅ Measurement of entangled state updates constraints

#[cfg(test)]
use hologram_compiler::{create_ghz_3, create_ghz_4, measure_qubit, measure_qubits, NQubitState, QuantumState};

#[test]
fn test_measure_single_qubit_product_state() {
    println!("\n=== Measure Single Qubit from Product State ===");

    let state = NQubitState::new_product(vec![
        QuantumState::new(0),
        QuantumState::new(192),
        QuantumState::new(384),
    ]);

    let (class, remaining) = measure_qubit(&state, 1);

    assert_eq!(remaining.num_qubits(), 2);
    assert!(!remaining.is_entangled(), "Product state remains product");

    println!("  Measured class: {}", class);
    println!("✅ Measuring product state gives product state");
}

#[test]
fn test_measure_one_of_three_ghz() {
    println!("\n=== Measure 1 of 3 Qubits in GHZ State ===");

    let ghz = create_ghz_3();
    let (class, remaining) = measure_qubit(&ghz, 0);

    assert_eq!(remaining.num_qubits(), 2);
    assert!(remaining.is_entangled(), "Remaining qubits should be entangled");

    println!("  Measured class: {}", class);
    println!("  Remaining qubits: 2 (entangled)");
    println!("✅ Partial measurement of GHZ preserves constraint");
}

#[test]
fn test_measure_two_of_four_ghz() {
    println!("\n=== Measure 2 of 4 Qubits in GHZ State ===");

    let ghz = create_ghz_4();
    let (classes, remaining) = measure_qubits(&ghz, &[0, 1]);

    assert_eq!(remaining.num_qubits(), 2);
    assert!(remaining.is_entangled(), "Remaining 2 qubits should be constrained");

    println!("  Measured classes: {:?}", classes);
    println!("  Remaining qubits: 2 (entangled)");
    println!("✅ Measuring 2 of 4 qubits works correctly");
}

#[test]
fn test_measurement_determinism() {
    println!("\n=== Measurement Determinism ===");

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

    println!("  Measurement 1: class {}", class1);
    println!("  Measurement 2: class {}", class2);
    println!("✅ Measurement is deterministic");
}

#[test]
fn test_constraint_propagation_correctness() {
    println!("\n=== Constraint Propagation Correctness ===");

    // Create GHZ-3 with known constraint
    let ghz = create_ghz_3();

    // Get original position of qubit 0
    let p0 = ghz.qubit(0).position();

    // Measure qubit 0, verify constraint on remaining qubits
    let (_class0, remaining) = measure_qubit(&ghz, 0);

    // Remaining qubits should satisfy updated constraint
    // Original: p0 + p1 + p2 = 192 (mod 768)
    // After measuring p0: p1 + p2 = (192 - p0) mod 768

    let p1 = remaining.qubit(0).position();
    let p2 = remaining.qubit(1).position();

    let expected_sum = (192_i32 - p0 as i32).rem_euclid(768);
    let actual_sum = ((p1 as i32 + p2 as i32) % 768) as i32;

    assert_eq!(
        actual_sum, expected_sum,
        "Constraint not satisfied after measurement: p1={}, p2={}, sum={}, expected={}",
        p1, p2, actual_sum, expected_sum
    );

    println!("  Original constraint: p0 + p1 + p2 = 192 (mod 768)");
    println!("  Measured p0: {}", p0);
    println!("  Updated constraint: p1 + p2 = {} (mod 768)", expected_sum);
    println!("  Actual: {} + {} = {} ✓", p1, p2, actual_sum);

    println!("✅ Constraints propagated correctly");
}

#[test]
fn test_measure_all_but_one() {
    println!("\n=== Measure All But One Qubit ===");

    let ghz = create_ghz_4();
    let (classes, remaining) = measure_qubits(&ghz, &[0, 1, 2]);

    assert_eq!(remaining.num_qubits(), 1);
    assert!(!remaining.is_entangled(), "Single qubit cannot be entangled");

    println!("  Measured 3 qubits, 1 remaining");
    println!("✅ Measuring N-1 qubits leaves single qubit");
}
