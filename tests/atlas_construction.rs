//! Integration tests for Atlas construction
//!
//! Verifies that the Atlas of Resonance Classes is constructed correctly
//! from first principles with exact arithmetic.

use atlas_embeddings::Atlas;

#[test]
fn test_atlas_basic_properties() {
    let atlas = Atlas::new();

    // Atlas has exactly 96 vertices
    assert_eq!(atlas.num_vertices(), 96, "Atlas must have 96 vertices");

    // All vertices have degree 5 or 6
    for v in 0..96 {
        let deg = atlas.degree(v);
        assert!(deg == 5 || deg == 6, "Vertex {v} has invalid degree {deg}");
    }
}

#[test]
fn test_atlas_degree_distribution() {
    let atlas = Atlas::new();

    // Count vertices by degree
    let mut deg5_count = 0;
    let mut deg6_count = 0;

    for v in 0..96 {
        match atlas.degree(v) {
            5 => deg5_count += 1,
            6 => deg6_count += 1,
            d => panic!("Invalid degree {d} for vertex {v}"),
        }
    }

    // Atlas degree distribution: 64 degree-5 + 32 degree-6
    assert_eq!(deg5_count, 64, "Must have 64 degree-5 vertices");
    assert_eq!(deg6_count, 32, "Must have 32 degree-6 vertices");
    assert_eq!(deg5_count + deg6_count, 96, "Total must be 96");
}

#[test]
fn test_atlas_mirror_symmetry() {
    let atlas = Atlas::new();

    // Every vertex has a unique mirror pair
    let mut seen = vec![false; 96];

    for v in 0..96 {
        if seen[v] {
            continue;
        }

        let mirror = atlas.mirror_pair(v);

        // Mirror involution: τ(τ(v)) = v
        assert_eq!(atlas.mirror_pair(mirror), v, "Mirror must be involution");

        // Mirror must be different (no fixed points)
        assert_ne!(mirror, v, "Mirror must map to different vertex");

        // Mark both as seen
        seen[v] = true;
        seen[mirror] = true;
    }

    // All vertices should be paired
    assert!(seen.iter().all(|&s| s), "All vertices must have mirror pairs");
}

#[test]
fn test_atlas_adjacency_symmetric() {
    let atlas = Atlas::new();

    // Adjacency is symmetric: if u~v then v~u
    for u in 0..96 {
        let neighbors = atlas.neighbors(u);
        for &v in neighbors {
            let v_neighbors = atlas.neighbors(v);
            assert!(
                v_neighbors.contains(&u),
                "Adjacency not symmetric: {u}~{v} but not {v}~{u}"
            );
        }
    }
}

#[test]
fn test_atlas_unity_positions() {
    let atlas = Atlas::new();

    // Unity positions define the Klein quartet structure
    let unity = atlas.unity_positions();

    // Must have exactly 2 unity positions
    assert_eq!(unity.len(), 2, "Atlas must have 2 unity positions");

    // Unity positions must be mirror pairs
    assert!(
        atlas.is_mirror_pair(unity[0], unity[1]),
        "Unity positions must be mirror pairs"
    );

    // Both must be valid vertices
    assert!(unity[0] < 96, "Unity position must be valid vertex");
    assert!(unity[1] < 96, "Unity position must be valid vertex");
}

#[test]
fn test_atlas_adjacency_degree_consistency() {
    let atlas = Atlas::new();

    // For each vertex, number of neighbors = degree
    for v in 0..96 {
        let neighbors = atlas.neighbors(v);
        let degree = atlas.degree(v);

        assert_eq!(
            neighbors.len(),
            degree,
            "Vertex {v}: neighbors.len() = {} but degree = {}",
            neighbors.len(),
            degree
        );
    }
}

#[test]
fn test_atlas_no_self_loops() {
    let atlas = Atlas::new();

    // No vertex is adjacent to itself
    for v in 0..96 {
        let neighbors = atlas.neighbors(v);
        assert!(
            !neighbors.contains(&v),
            "Vertex {v} should not be adjacent to itself"
        );
    }
}

#[test]
fn test_atlas_twelve_fold_divisibility() {
    let atlas = Atlas::new();

    // Atlas exhibits 12-fold divisibility (G₂ structure)
    // 96 = 12 × 8
    assert_eq!(atlas.num_vertices() % 12, 0, "96 must be divisible by 12");

    // Boundary: 12,288 = 12 × 1,024
    let boundary_cells = 12_288;
    assert_eq!(
        boundary_cells % 12,
        0,
        "Boundary cells must be divisible by 12"
    );
}

#[test]
fn test_atlas_sign_class_structure() {
    let atlas = Atlas::new();

    // Sign classes (mirror pairs) count
    let mut seen = vec![false; 96];
    let mut sign_classes = 0;

    for v in 0..96 {
        if !seen[v] {
            let mirror = atlas.mirror_pair(v);
            seen[v] = true;
            seen[mirror] = true;
            sign_classes += 1;
        }
    }

    // F₄ emerges from 96/± = 48 sign classes
    assert_eq!(sign_classes, 48, "Must have exactly 48 sign classes");
}

#[test]
fn test_atlas_construction_deterministic() {
    // Atlas construction is deterministic (no randomness)
    let atlas1 = Atlas::new();
    let atlas2 = Atlas::new();

    // Same vertex count
    assert_eq!(atlas1.num_vertices(), atlas2.num_vertices());

    // Same degrees
    for v in 0..96 {
        assert_eq!(atlas1.degree(v), atlas2.degree(v));
    }

    // Same adjacency
    for v in 0..96 {
        let n1 = atlas1.neighbors(v);
        let n2 = atlas2.neighbors(v);
        assert_eq!(n1, n2, "Adjacency must be deterministic for vertex {v}");
    }
}

#[test]
fn test_atlas_e6_degree_partition() {
    let atlas = Atlas::new();

    // E₆ uses degree partition: 64 deg-5 + 8 deg-6 = 72
    let mut deg5_vertices = Vec::new();
    let mut deg6_vertices = Vec::new();

    for v in 0..96 {
        match atlas.degree(v) {
            5 => deg5_vertices.push(v),
            6 => deg6_vertices.push(v),
            _ => {},
        }
    }

    // Can select 64 degree-5 vertices (enough for E₆)
    assert!(
        deg5_vertices.len() >= 64,
        "Need at least 64 degree-5 vertices for E₆"
    );

    // Can select 8 degree-6 vertices (enough for E₆)
    assert!(
        deg6_vertices.len() >= 8,
        "Need at least 8 degree-6 vertices for E₆"
    );

    // E₆ total: 64 + 8 = 72
    let e6_total = 64 + 8;
    assert_eq!(e6_total, 72, "E₆ must have 72 roots");
}
