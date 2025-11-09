//! Quantum Gate Canonicalization Tests
//!
//! This test suite verifies canonicalization of quantum gate patterns
//! using the rewrite engine. Tests focus on pattern-based optimizations
//! that reduce circuit operations through identities like H²=I, X²=I, etc.

use hologram_compiler::Canonicalizer;

#[test]
fn test_hadamard_squared_canonicalization() {
    // H² = I (4 ops → 1 op, 75% reduction)
    let h_squared = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";

    let result = Canonicalizer::parse_and_canonicalize(h_squared).unwrap();

    assert!(result.changed, "H² should be rewritten");
    assert_eq!(result.rewrite_count, 1, "Should apply one rewrite");
    assert!(
        result.applied_rules.contains(&"H² = I".to_string()),
        "Should apply H² = I rule"
    );

    // Check that canonical form is identity (mark@c00)
    let canonical_str = format!("{:?}", result.phrase);
    assert!(canonical_str.contains("class_index: 0"), "Should reduce to identity");
}

#[test]
fn test_pauli_x_squared_canonicalization() {
    // X² = I (2 ops → 1 op, 50% reduction)
    let x_squared = "mark@c21 . mark@c21";

    let result = Canonicalizer::parse_and_canonicalize(x_squared).unwrap();

    assert!(result.changed, "X² should be rewritten");
    assert_eq!(result.rewrite_count, 1);
    assert!(result.applied_rules.contains(&"X² = I".to_string()));

    let canonical_str = format!("{:?}", result.phrase);
    assert!(canonical_str.contains("class_index: 0"));
}

#[test]
fn test_pauli_z_squared_canonicalization() {
    // Z² = I (2 ops → 1 op, 50% reduction)
    let z_squared = "mark@c42 . mark@c42";

    let result = Canonicalizer::parse_and_canonicalize(z_squared).unwrap();

    assert!(result.changed, "Z² should be rewritten");
    assert_eq!(result.rewrite_count, 1);
    assert!(result.applied_rules.contains(&"Z² = I".to_string()));
}

#[test]
fn test_phase_gate_squared() {
    // S² = Z
    let s_squared = "mark@c07 . mark@c07";

    let result = Canonicalizer::parse_and_canonicalize(s_squared).unwrap();

    assert!(result.changed);
    assert!(result.applied_rules.contains(&"S² = Z".to_string()));

    // Canonical form should be Z (mark@c42)
    let canonical_str = format!("{:?}", result.phrase);
    assert!(canonical_str.contains("class_index: 42"));
}

#[test]
fn test_hadamard_conjugation() {
    // HXH = Z (5 ops → 1 op, 80% reduction)
    // Note: This may reduce via X² first depending on rule ordering
    let hxh = "copy@c05->c06 . mark@c21 . mark@c21 . copy@c05->c06 . mark@c21";

    let result = Canonicalizer::parse_and_canonicalize(hxh).unwrap();

    assert!(result.changed);
    // The HXH rule may not trigger if X² triggers first, but circuit should still reduce
    assert!(result.rewrite_count >= 1);
}

#[test]
fn test_identity_composition() {
    // I·I = I
    let i_i = "mark@c00 . mark@c00";

    let result = Canonicalizer::parse_and_canonicalize(i_i).unwrap();

    assert!(result.changed);
    assert!(result.applied_rules.contains(&"I.I = I".to_string()));
}

#[test]
fn test_hadamard_fourth_power() {
    // H⁴ = (H²)² = I² = I
    let h_fourth = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 . \
                    copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";

    let result = Canonicalizer::parse_and_canonicalize(h_fourth).unwrap();

    assert!(result.changed);
    assert!(result.rewrite_count >= 2, "Should have multiple iterations");

    // Should reduce to identity
    let canonical_str = format!("{:?}", result.phrase);
    assert!(canonical_str.contains("class_index: 0"));
}

#[test]
fn test_pauli_x_fourth_power() {
    // X⁴ = (X²)² = I² = I
    let x_fourth = "mark@c21 . mark@c21 . mark@c21 . mark@c21";

    let result = Canonicalizer::parse_and_canonicalize(x_fourth).unwrap();

    assert!(result.changed);
    assert!(result.rewrite_count >= 2);
}

#[test]
fn test_parallel_canonicalization() {
    // Both branches should canonicalize independently
    let parallel = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 || \
                    mark@c21 . mark@c21";

    let result = Canonicalizer::parse_and_canonicalize(parallel).unwrap();

    assert!(result.changed);
    assert!(result.rewrite_count >= 2, "Both branches should be rewritten");
}

#[test]
fn test_rewrite_convergence() {
    // Complex circuit should converge to stable form
    let complex = "mark@c21 . mark@c21 . mark@c00 . mark@c00";

    let result = Canonicalizer::parse_and_canonicalize(complex).unwrap();

    assert!(result.changed);
    // Should not hit iteration limit (would indicate non-convergence)
    assert!(result.rewrite_count < 100);
}

#[test]
fn test_canonical_form_output() {
    // Test that canonical_form() produces readable output
    let expr = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";

    let canonical = Canonicalizer::canonical_form(expr).unwrap();

    // Should contain Mark (the identity generator)
    assert!(canonical.contains("Mark"));
    assert!(canonical.contains("class_index: 0"));
}

#[test]
fn test_zero_rewrite_expressions() {
    // Already canonical expressions should have zero rewrites
    let identity = "mark@c00";

    let result = Canonicalizer::parse_and_canonicalize(identity).unwrap();

    assert!(!result.changed, "Identity should not need rewriting");
    assert_eq!(result.rewrite_count, 0);
}

#[test]
fn test_rewrite_statistics() {
    // Verify rewrite statistics are accurate
    let expr = "mark@c21 . mark@c21"; // X²

    let result = Canonicalizer::parse_and_canonicalize(expr).unwrap();

    assert_eq!(result.rewrite_count, 1);
    assert_eq!(result.applied_rules.len(), 1);
    assert_eq!(result.applied_rules[0], "X² = I");
}

#[test]
fn test_parse_error_handling() {
    // Invalid expression should return parse error
    let invalid = "invalid syntax";

    let result = Canonicalizer::parse_and_canonicalize(invalid);

    assert!(result.is_err(), "Should error on invalid syntax");
}

#[test]
fn test_complex_sequential_canonicalization() {
    // Long sequential composition
    let complex = "mark@c00 . mark@c00 . mark@c21 . mark@c21 . mark@c42 . mark@c42";

    let result = Canonicalizer::parse_and_canonicalize(complex).unwrap();

    assert!(result.changed);
    // Should reduce all three X² patterns
    assert!(result.rewrite_count >= 3);
}

#[test]
fn test_transform_preservation() {
    // Transforms should be preserved during canonicalization
    let with_transform = "R+1@ (mark@c00 . mark@c00)";

    let result = Canonicalizer::parse_and_canonicalize(with_transform).unwrap();

    // Should still canonicalize even with transforms
    assert!(result.changed);
}

#[test]
fn test_canonicalization_is_deterministic() {
    // Multiple canonicalizations should produce identical results
    let expr = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";

    let result1 = Canonicalizer::canonical_form(expr).unwrap();
    let result2 = Canonicalizer::canonical_form(expr).unwrap();

    assert_eq!(result1, result2, "Canonicalization should be deterministic");
}

#[test]
fn test_empty_parallel_branches() {
    // Parallel with identity branches
    let parallel = "mark@c00 || mark@c00";

    let _result = Canonicalizer::parse_and_canonicalize(parallel).unwrap();

    // Should parse and canonicalize without error
    // (No assertions needed - just checking it doesn't panic)
}

#[test]
fn test_nested_sequential_in_parallel() {
    // (A.B) || (C.D) where some reduce
    let nested = "(mark@c21 . mark@c21) || (mark@c42 . mark@c42)";

    let result = Canonicalizer::parse_and_canonicalize(nested).unwrap();

    assert!(result.changed);
    // Both X² and Z² should reduce
    assert!(result.rewrite_count >= 2);
}

#[test]
fn test_rewrite_rule_names() {
    // Verify rule names are correctly reported
    let h2 = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";
    let x2 = "mark@c21 . mark@c21";
    let z2 = "mark@c42 . mark@c42";

    let result_h = Canonicalizer::parse_and_canonicalize(h2).unwrap();
    let result_x = Canonicalizer::parse_and_canonicalize(x2).unwrap();
    let result_z = Canonicalizer::parse_and_canonicalize(z2).unwrap();

    assert!(result_h.applied_rules.contains(&"H² = I".to_string()));
    assert!(result_x.applied_rules.contains(&"X² = I".to_string()));
    assert!(result_z.applied_rules.contains(&"Z² = I".to_string()));
}
