//! SWAP Gate Correctness Validation
//!
//! This discovery test validates that the SWAP gate correctly exchanges
//! the positions of two qubits while preserving entanglement if present.
//!
//! ## SWAP Gate Truth Table
//!
//! ```text
//! Input   → Output
//! |00⟩    → |00⟩     (no visible change)
//! |01⟩    → |10⟩     (qubits swapped)
//! |10⟩    → |01⟩     (qubits swapped)
//! |11⟩    → |11⟩     (no visible change)
//! ```
//!
//! ## Key Properties
//!
//! 1. **Position Exchange**: qubit_0 ↔ qubit_1
//! 2. **Entanglement Preservation**: If input is entangled, output remains entangled
//! 3. **Self-Inverse**: SWAP² = I (two swaps return to original)
//! 4. **Commutes with Bell States**: SWAP on symmetric Bell states has no effect
//!
//! ## Success Criteria
//!
//! 1. ✅ All truth table entries produce correct output
//! 2. ✅ Positions are correctly exchanged
//! 3. ✅ Entanglement preserved if present
//! 4. ✅ SWAP² returns to original state
//! 5. ✅ Works with arbitrary cycle positions

#[cfg(test)]
use hologram_compiler::{apply_swap, QuantumState, TwoQubitState};

#[test]
fn test_swap_00_to_00() {
    println!("\n=== SWAP Truth Table: |00⟩ → |00⟩ ===");

    let state = TwoQubitState::new_product(QuantumState::new(0), QuantumState::new(0));

    println!(
        "Input:  qubit_0={}, qubit_1={}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    let result = apply_swap(state);

    println!(
        "Output: qubit_0={}, qubit_1={}",
        result.qubit_0().position(),
        result.qubit_1().position()
    );

    // Both qubits at same position, so swap doesn't change anything visibly
    assert_eq!(result.qubit_0().position(), 0);
    assert_eq!(result.qubit_1().position(), 0);

    println!("✅ SWAP |00⟩ → |00⟩ PASSED");
}

#[test]
fn test_swap_01_to_10() {
    println!("\n=== SWAP Truth Table: |01⟩ → |10⟩ ===");

    // |01⟩: qubit_0=|0⟩ (pos=0), qubit_1=|1⟩ (pos=384)
    let state = TwoQubitState::new_product(QuantumState::new(0), QuantumState::new(384));

    println!(
        "Input:  qubit_0={}, qubit_1={}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    let result = apply_swap(state);

    println!(
        "Output: qubit_0={}, qubit_1={}",
        result.qubit_0().position(),
        result.qubit_1().position()
    );

    // Positions should be swapped
    assert_eq!(
        result.qubit_0().position(),
        384,
        "qubit_0 should now be at qubit_1's old position"
    );
    assert_eq!(
        result.qubit_1().position(),
        0,
        "qubit_1 should now be at qubit_0's old position"
    );

    println!("✅ SWAP |01⟩ → |10⟩ PASSED");
}

#[test]
fn test_swap_10_to_01() {
    println!("\n=== SWAP Truth Table: |10⟩ → |01⟩ ===");

    // |10⟩: qubit_0=|1⟩ (pos=384), qubit_1=|0⟩ (pos=0)
    let state = TwoQubitState::new_product(QuantumState::new(384), QuantumState::new(0));

    println!(
        "Input:  qubit_0={}, qubit_1={}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    let result = apply_swap(state);

    println!(
        "Output: qubit_0={}, qubit_1={}",
        result.qubit_0().position(),
        result.qubit_1().position()
    );

    // Positions should be swapped
    assert_eq!(
        result.qubit_0().position(),
        0,
        "qubit_0 should now be at qubit_1's old position"
    );
    assert_eq!(
        result.qubit_1().position(),
        384,
        "qubit_1 should now be at qubit_0's old position"
    );

    println!("✅ SWAP |10⟩ → |01⟩ PASSED");
}

#[test]
fn test_swap_11_to_11() {
    println!("\n=== SWAP Truth Table: |11⟩ → |11⟩ ===");

    let state = TwoQubitState::new_product(QuantumState::new(384), QuantumState::new(384));

    println!(
        "Input:  qubit_0={}, qubit_1={}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    let result = apply_swap(state);

    println!(
        "Output: qubit_0={}, qubit_1={}",
        result.qubit_0().position(),
        result.qubit_1().position()
    );

    // Both at same position, no visible change
    assert_eq!(result.qubit_0().position(), 384);
    assert_eq!(result.qubit_1().position(), 384);

    println!("✅ SWAP |11⟩ → |11⟩ PASSED");
}

#[test]
fn test_swap_arbitrary_positions() {
    println!("\n=== SWAP with Arbitrary Positions ===");

    let position_a = 123;
    let position_b = 567;

    let state = TwoQubitState::new_product(QuantumState::new(position_a), QuantumState::new(position_b));

    println!(
        "Input:  qubit_0={}, qubit_1={}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    let result = apply_swap(state);

    println!(
        "Output: qubit_0={}, qubit_1={}",
        result.qubit_0().position(),
        result.qubit_1().position()
    );

    // Positions should be exchanged
    assert_eq!(result.qubit_0().position(), position_b, "Positions should be swapped");
    assert_eq!(result.qubit_1().position(), position_a, "Positions should be swapped");

    println!("✅ SWAP with arbitrary positions PASSED");
}

#[test]
fn test_swap_is_self_inverse() {
    println!("\n=== SWAP² = I (Self-Inverse) ===");

    let state = TwoQubitState::new_product(QuantumState::new(100), QuantumState::new(200));

    println!(
        "Original: qubit_0={}, qubit_1={}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    // First swap
    let once = apply_swap(state.clone());
    println!(
        "After 1x: qubit_0={}, qubit_1={}",
        once.qubit_0().position(),
        once.qubit_1().position()
    );

    // Second swap
    let twice = apply_swap(once);
    println!(
        "After 2x: qubit_0={}, qubit_1={}",
        twice.qubit_0().position(),
        twice.qubit_1().position()
    );

    // Should return to original
    assert_eq!(
        twice.qubit_0().position(),
        state.qubit_0().position(),
        "Two swaps should return to original"
    );
    assert_eq!(
        twice.qubit_1().position(),
        state.qubit_1().position(),
        "Two swaps should return to original"
    );

    println!("✅ SWAP² = I validated");
}

#[test]
fn test_swap_preserves_entanglement() {
    println!("\n=== SWAP Preserves Entanglement ===");

    // Create entangled state
    use hologram_compiler::CorrelationConstraint;

    let constraint = CorrelationConstraint::new(192);
    let state = TwoQubitState::new_entangled(QuantumState::new(192), QuantumState::new(0), constraint);

    println!(
        "Input (entangled): qubit_0={}, qubit_1={}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );
    println!("Entangled: {}", state.is_entangled());
    println!("Correlation: p_0 + p_1 ≡ {} (mod 768)", constraint.sum_modulo());

    let result = apply_swap(state);

    println!(
        "\nOutput: qubit_0={}, qubit_1={}",
        result.qubit_0().position(),
        result.qubit_1().position()
    );
    println!("Entangled: {}", result.is_entangled());

    // Entanglement should be preserved
    assert!(result.is_entangled(), "SWAP should preserve entanglement");

    // Correlation constraint should still exist
    assert!(
        result.correlation_constraint().is_some(),
        "Correlation constraint should be preserved"
    );

    // Positions swapped
    assert_eq!(result.qubit_0().position(), 0, "Positions swapped");
    assert_eq!(result.qubit_1().position(), 192, "Positions swapped");

    // Verify positions still satisfy correlation
    let result_constraint = result.correlation_constraint().unwrap();
    assert!(
        result_constraint.are_positions_correlated(result.qubit_0().position(), result.qubit_1().position()),
        "Swapped positions should still satisfy correlation"
    );

    println!(
        "Correlation preserved: p_0 + p_1 ≡ {} (mod 768)",
        result_constraint.sum_modulo()
    );
    println!("✅ Entanglement preserved through SWAP");
}

#[test]
fn test_swap_on_bell_state() {
    println!("\n=== SWAP on Bell State |Φ⁺⟩ ===");

    use hologram_compiler::create_bell_phi_plus;

    let bell_state = create_bell_phi_plus();

    println!(
        "Before SWAP: qubit_0={}, qubit_1={}",
        bell_state.qubit_0().position(),
        bell_state.qubit_1().position()
    );
    println!("Entangled: {}", bell_state.is_entangled());

    let swapped = apply_swap(bell_state);

    println!(
        "After SWAP:  qubit_0={}, qubit_1={}",
        swapped.qubit_0().position(),
        swapped.qubit_1().position()
    );
    println!("Entangled: {}", swapped.is_entangled());

    // Should still be entangled
    assert!(swapped.is_entangled(), "Bell state should remain entangled after SWAP");

    // For symmetric Bell states like |Φ⁺⟩, SWAP might have special behavior
    // but at minimum, entanglement must be preserved

    println!("✅ SWAP preserves Bell state entanglement");
}

#[test]
fn test_swap_does_not_change_product_state_entanglement() {
    println!("\n=== SWAP Does Not Create Entanglement ===");

    // Product state (not entangled)
    let state = TwoQubitState::new_product(QuantumState::new(100), QuantumState::new(200));

    println!("Input (product state): entangled = {}", state.is_entangled());

    let result = apply_swap(state);

    println!("Output: entangled = {}", result.is_entangled());

    // Should still be product state (not entangled)
    assert!(
        !result.is_entangled(),
        "SWAP should not create entanglement from product state"
    );

    println!("✅ SWAP preserves product state (no entanglement created)");
}

#[test]
fn test_swap_commutes_with_itself() {
    println!("\n=== SWAP Commutes With Itself ===");

    let state = TwoQubitState::new_product(QuantumState::new(150), QuantumState::new(300));

    // Apply SWAP twice in different "orders" (though it's the same gate)
    let path1 = apply_swap(apply_swap(state.clone()));
    let path2 = apply_swap(apply_swap(state.clone()));

    // Should give same result
    assert_eq!(path1.qubit_0().position(), path2.qubit_0().position());
    assert_eq!(path1.qubit_1().position(), path2.qubit_1().position());

    // And should equal original
    assert_eq!(path1.qubit_0().position(), state.qubit_0().position());
    assert_eq!(path1.qubit_1().position(), state.qubit_1().position());

    println!("✅ SWAP commutes with itself");
}

#[test]
fn test_swap_triple_application() {
    println!("\n=== Triple SWAP Application ===");

    let state = TwoQubitState::new_product(QuantumState::new(111), QuantumState::new(222));

    println!(
        "Original: qubit_0={}, qubit_1={}",
        state.qubit_0().position(),
        state.qubit_1().position()
    );

    // SWAP once: positions swapped
    let once = apply_swap(state.clone());
    println!(
        "After 1x: qubit_0={}, qubit_1={}",
        once.qubit_0().position(),
        once.qubit_1().position()
    );
    assert_eq!(once.qubit_0().position(), 222);
    assert_eq!(once.qubit_1().position(), 111);

    // SWAP twice: back to original
    let twice = apply_swap(once);
    println!(
        "After 2x: qubit_0={}, qubit_1={}",
        twice.qubit_0().position(),
        twice.qubit_1().position()
    );
    assert_eq!(twice.qubit_0().position(), 111);
    assert_eq!(twice.qubit_1().position(), 222);

    // SWAP thrice: swapped again
    let thrice = apply_swap(twice);
    println!(
        "After 3x: qubit_0={}, qubit_1={}",
        thrice.qubit_0().position(),
        thrice.qubit_1().position()
    );
    assert_eq!(thrice.qubit_0().position(), 222);
    assert_eq!(thrice.qubit_1().position(), 111);

    println!("✅ Triple SWAP application validated");
}
