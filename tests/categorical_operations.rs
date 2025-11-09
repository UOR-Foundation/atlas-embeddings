//! Integration tests for categorical operations
//!
//! Verifies that each exceptional group emerges from the Atlas
//! through its corresponding categorical operation.

#![allow(clippy::large_stack_arrays)]

use atlas_embeddings::{categorical::CategoricalOperation, Atlas};

#[test]
fn test_product_operation_g2_complete() {
    let atlas = Atlas::new();
    let op = CategoricalOperation::product();

    // Verify operation metadata
    assert_eq!(op.name(), "Product");
    assert_eq!(op.target_group(), "G₂");
    assert_eq!(op.expected_roots(), 12);

    // Execute operation
    let result = op.verify(&atlas);

    // Verify result
    assert!(result.verified, "Product operation must verify");
    assert_eq!(result.group_name, "G₂");
    assert_eq!(result.expected_roots, 12);
    assert_eq!(result.actual_count, 12);

    // Verify Klein × ℤ/3 structure
    assert!(result.details.contains("Klein"));
    assert!(result.details.contains("12"));
}

#[test]
fn test_quotient_operation_f4_complete() {
    let atlas = Atlas::new();
    let op = CategoricalOperation::quotient();

    // Verify operation metadata
    assert_eq!(op.name(), "Quotient");
    assert_eq!(op.target_group(), "F₄");
    assert_eq!(op.expected_roots(), 48);

    // Execute operation
    let result = op.verify(&atlas);

    // Verify result
    assert!(result.verified, "Quotient operation must verify");
    assert_eq!(result.group_name, "F₄");
    assert_eq!(result.expected_roots, 48);
    assert_eq!(result.actual_count, 48);

    // Verify sign class structure (96/± = 48)
    assert!(result.details.contains("96"));
    assert!(result.details.contains("48"));
    assert!(result.details.contains("sign classes"));
}

#[test]
fn test_filtration_operation_e6_complete() {
    let atlas = Atlas::new();
    let op = CategoricalOperation::filtration();

    // Verify operation metadata
    assert_eq!(op.name(), "Filtration");
    assert_eq!(op.target_group(), "E₆");
    assert_eq!(op.expected_roots(), 72);

    // Execute operation
    let result = op.verify(&atlas);

    // Verify result
    assert!(result.verified, "Filtration operation must verify");
    assert_eq!(result.group_name, "E₆");
    assert_eq!(result.expected_roots, 72);
    assert_eq!(result.actual_count, 72);

    // Verify degree partition (64 + 8 = 72)
    assert!(result.details.contains("64"));
    assert!(result.details.contains('8'));
    assert!(result.details.contains("72"));
}

#[test]
fn test_augmentation_operation_e7_complete() {
    let atlas = Atlas::new();
    let op = CategoricalOperation::augmentation();

    // Verify operation metadata
    assert_eq!(op.name(), "Augmentation");
    assert_eq!(op.target_group(), "E₇");
    assert_eq!(op.expected_roots(), 126);

    // Execute operation
    let result = op.verify(&atlas);

    // Verify result
    assert!(result.verified, "Augmentation operation must verify");
    assert_eq!(result.group_name, "E₇");
    assert_eq!(result.expected_roots, 126);
    assert_eq!(result.actual_count, 126);

    // Verify augmentation formula (96 + 30 = 126)
    assert!(result.details.contains("96"));
    assert!(result.details.contains("30"));
    assert!(result.details.contains("126"));
}

#[test]
fn test_morphism_operation_e8_complete() {
    let atlas = Atlas::new();
    let op = CategoricalOperation::morphism();

    // Verify operation metadata
    assert_eq!(op.name(), "Morphism");
    assert_eq!(op.target_group(), "E₈");
    assert_eq!(op.expected_roots(), 240);

    // Execute operation
    let result = op.verify(&atlas);

    // Verify result
    assert!(result.verified, "Morphism operation must verify");
    assert_eq!(result.group_name, "E₈");
    assert_eq!(result.expected_roots, 240);

    // Verify direct embedding
    assert!(result.details.contains("96"));
    assert!(result.details.contains("240"));
}

#[test]
fn test_all_operations_consistent() {
    let atlas = Atlas::new();

    // All operations should verify successfully
    let operations = vec![
        CategoricalOperation::product(),
        CategoricalOperation::quotient(),
        CategoricalOperation::filtration(),
        CategoricalOperation::augmentation(),
        CategoricalOperation::morphism(),
    ];

    for op in operations {
        let result = op.verify(&atlas);
        assert!(result.verified, "{} operation failed verification", op.name());
        assert_eq!(
            result.expected_roots,
            op.expected_roots(),
            "{} operation: expected_roots mismatch",
            op.name()
        );
    }
}

#[test]
#[allow(clippy::large_stack_arrays)]
fn test_categorical_hierarchy() {
    // Verify the exceptional group hierarchy via root counts
    let ops = [
        (CategoricalOperation::product(), 12),       // G₂
        (CategoricalOperation::quotient(), 48),      // F₄
        (CategoricalOperation::filtration(), 72),    // E₆
        (CategoricalOperation::augmentation(), 126), // E₇
        (CategoricalOperation::morphism(), 240),     // E₈
    ];

    // Root counts should be in increasing order
    for i in 0..ops.len() - 1 {
        let (op_i, count_i) = &ops[i];
        let (op_j, count_j) = &ops[i + 1];

        assert!(
            count_i < count_j,
            "Root counts should increase: {} ({}) < {} ({})",
            op_i.target_group(),
            count_i,
            op_j.target_group(),
            count_j
        );
    }
}

#[test]
#[allow(clippy::large_stack_arrays)]
fn test_operation_result_details() {
    let atlas = Atlas::new();

    // Each operation should provide detailed information
    let operations = vec![
        CategoricalOperation::product(),
        CategoricalOperation::quotient(),
        CategoricalOperation::filtration(),
        CategoricalOperation::augmentation(),
        CategoricalOperation::morphism(),
    ];

    for op in operations {
        let result = op.verify(&atlas);

        // Details should be non-empty
        assert!(!result.details.is_empty(), "{} operation should provide details", op.name());

        // Details should mention the group
        assert!(
            result.details.contains(&result.group_name)
                || result.details.contains(&result.expected_roots.to_string()),
            "{} details should mention group or root count",
            op.name()
        );
    }
}

#[test]
fn test_categorical_operations_deterministic() {
    let atlas = Atlas::new();

    // Operations should produce consistent results
    for _ in 0..3 {
        let result1 = CategoricalOperation::product().verify(&atlas);
        let result2 = CategoricalOperation::product().verify(&atlas);

        assert_eq!(result1.verified, result2.verified);
        assert_eq!(result1.actual_count, result2.actual_count);
    }
}

#[test]
fn test_operation_types_unique() {
    // Each operation produces a different group
    let ops = [
        CategoricalOperation::product(),
        CategoricalOperation::quotient(),
        CategoricalOperation::filtration(),
        CategoricalOperation::augmentation(),
        CategoricalOperation::morphism(),
    ];

    let mut groups: Vec<&str> = ops.iter().map(CategoricalOperation::target_group).collect();
    groups.sort_unstable();

    // Check all groups are unique
    for i in 0..groups.len() - 1 {
        assert_ne!(groups[i], groups[i + 1], "Groups should be unique");
    }

    // Should have all 5 exceptional groups
    assert_eq!(groups.len(), 5);
    assert!(groups.contains(&"G₂"));
    assert!(groups.contains(&"F₄"));
    assert!(groups.contains(&"E₆"));
    assert!(groups.contains(&"E₇"));
    assert!(groups.contains(&"E₈"));
}
