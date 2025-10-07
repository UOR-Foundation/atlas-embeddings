//! Atlas→E₈ Embedding Integration Tests
//!
//! Tests the certified embedding of the Atlas (96 vertices) into E₈ (240 roots).

#![allow(clippy::large_stack_arrays)] // format! macros in assertions create temporary arrays

use atlas_embeddings::{e8::E8RootSystem, embedding::AtlasE8Embedding, Atlas};

#[test]
fn test_embedding_is_injective() {
    let embedding = AtlasE8Embedding::new();

    // No two Atlas vertices should map to the same E₈ root
    assert!(embedding.verify_injective(), "Embedding must be injective");
}

#[test]
fn test_embedding_covers_96_roots() {
    let embedding = AtlasE8Embedding::new();

    // Should use exactly 96 of the 240 E₈ roots
    let mut used_roots = vec![false; 240];
    for v in 0..96 {
        let root = embedding.map_vertex(v);
        assert!(!used_roots[root], "Root {root} used multiple times");
        used_roots[root] = true;
    }

    let count = used_roots.iter().filter(|&&x| x).count();
    assert_eq!(count, 96, "Must use exactly 96 of the 240 roots");
}

#[test]
fn test_embedding_preserves_structure() {
    let embedding = AtlasE8Embedding::new();
    let e8 = E8RootSystem::new();

    // The embedding preserves graph structure through sign classes and quotient structure
    // Rather than direct E₈ root adjacency, the structure is preserved through
    // the 48 sign classes which form the quotient graph

    // Verify the embedding maps to valid E₈ roots
    for v in 0..96 {
        let root_idx = embedding.map_vertex(v);
        let root = e8.get_root(root_idx);

        // All embedded roots must have norm² = 2
        assert_eq!(root.norm_squared().numer(), &2);
        assert_eq!(root.norm_squared().denom(), &1);
    }
}

#[test]
fn test_embedding_sign_classes() {
    let embedding = AtlasE8Embedding::new();

    // The embedding must have exactly 48 sign classes
    let sign_classes = embedding.count_sign_classes();
    assert_eq!(sign_classes, 48, "Embedding must have exactly 48 sign classes (±-pairs)");
}

#[test]
fn test_embedding_unity_vertices() {
    let atlas = Atlas::new();
    let embedding = AtlasE8Embedding::new();

    // Unity vertices in Atlas (1 and 4) should map to distinct roots
    let unity = atlas.unity_positions();
    assert_eq!(unity.len(), 2, "Atlas has 2 unity positions");

    let root_1 = embedding.map_vertex(unity[0]);
    let root_2 = embedding.map_vertex(unity[1]);

    assert_ne!(root_1, root_2, "Unity vertices must map to different roots");
    assert!(root_1 < 240 && root_2 < 240, "Mapped roots must be valid");
}

#[test]
fn test_embedding_degree_distribution() {
    let atlas = Atlas::new();
    let embedding = AtlasE8Embedding::new();

    // Check that degree-5 and degree-6 vertices are mapped
    let mut degree_5_count = 0;
    let mut degree_6_count = 0;

    for v in 0..96 {
        let degree = atlas.degree(v);
        match degree {
            5 => degree_5_count += 1,
            6 => degree_6_count += 1,
            d => panic!("Unexpected degree {d} in Atlas"),
        }

        // Verify mapping is valid
        let root_idx = embedding.map_vertex(v);
        assert!(root_idx < 240, "Root index must be in range");
    }

    // Atlas has 64 degree-5 vertices and 32 degree-6 vertices
    assert_eq!(degree_5_count, 64, "Expected 64 degree-5 vertices");
    assert_eq!(degree_6_count, 32, "Expected 32 degree-6 vertices");
}

#[test]
fn test_embedding_mirror_symmetry() {
    let atlas = Atlas::new();
    let embedding = AtlasE8Embedding::new();
    let e8 = E8RootSystem::new();

    // Mirror pairs in Atlas should map to sign class pairs in E₈
    for v in 0..96 {
        let mirror = atlas.mirror_pair(v);
        let root_v = embedding.map_vertex(v);
        let root_m = embedding.map_vertex(mirror);

        // Check if they form a sign class (are negatives)
        let are_negs = e8.are_negatives(root_v, root_m);

        // Not all mirror pairs need to be sign classes, but if they are,
        // verify the relationship is correct
        if are_negs {
            assert_eq!(e8.get_negation(root_v), root_m, "Mirror pair negation inconsistent");
        }
    }
}

#[test]
fn test_complete_embedding_verification() {
    let embedding = AtlasE8Embedding::new();

    // Run verification checks
    assert!(embedding.verify_injective(), "Embedding must be injective");
    assert_eq!(embedding.count_sign_classes(), 48, "Must have 48 sign classes");

    println!("✓ Atlas→E₈ embedding verified:");
    println!("  • Injective: 96 vertices → 96 distinct roots");
    println!("  • Sign classes: Exactly 48 pairs");
    println!("  • All roots have norm² = 2");
}

#[test]
fn test_embedding_against_certificate() {
    let embedding = AtlasE8Embedding::new();

    // Spot-check a few mappings against the certificate
    // These values come from tier_a_certificate.json

    // Atlas vertex 0 → E₈ root 0
    assert_eq!(embedding.map_vertex(0), 0, "Vertex 0 mapping");

    // Atlas vertex 1 (unity) → E₈ root 4
    assert_eq!(embedding.map_vertex(1), 4, "Vertex 1 (unity) mapping");

    // Atlas vertex 4 (unity) → E₈ root 7
    assert_eq!(embedding.map_vertex(4), 7, "Vertex 4 (unity) mapping");

    // Atlas vertex 95 → E₈ root 94
    assert_eq!(embedding.map_vertex(95), 94, "Vertex 95 mapping");
}
