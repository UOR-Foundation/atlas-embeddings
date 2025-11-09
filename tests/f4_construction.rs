//! F₄ Construction Integration Tests

use atlas_embeddings::{groups::F4, Atlas};
use std::collections::HashSet;

#[test]
fn test_f4_basic_properties() {
    let atlas = Atlas::new();
    let f4 = F4::from_atlas(&atlas);

    // Basic counts
    assert_eq!(f4.num_roots(), 48, "F₄ must have 48 roots");
    assert_eq!(f4.rank(), 4, "F₄ must have rank 4");
    assert_eq!(f4.weyl_order(), 1152, "F₄ Weyl group order is 1,152");

    // Not simply-laced (has double bond)
    assert!(!f4.is_simply_laced(), "F₄ is not simply-laced");
}

#[test]
fn test_f4_cartan_matrix() {
    let atlas = Atlas::new();
    let f4 = F4::from_atlas(&atlas);
    let cartan = f4.cartan_matrix();

    // Verify structure
    assert_eq!(cartan.rank(), 4);
    assert!(cartan.is_valid());
    assert!(!cartan.is_simply_laced(), "F₄ has double bond");
    assert!(!cartan.is_symmetric(), "F₄ Cartan matrix is asymmetric");

    // Verify diagonal
    for i in 0..4 {
        assert_eq!(cartan.get(i, i), 2);
    }

    // Verify double bond at (1,2)
    assert_eq!(cartan.get(1, 2), -2, "Double bond: entry (1,2) = -2");
    assert_eq!(cartan.get(2, 1), -1);

    // Determinant
    assert_eq!(cartan.determinant(), 1, "F₄ Cartan determinant is 1");

    // Connected
    assert!(cartan.is_connected());
}

#[test]
fn test_f4_sign_classes() {
    let atlas = Atlas::new();
    let f4 = F4::from_atlas(&atlas);

    let sign_classes = f4.sign_classes();
    assert_eq!(sign_classes.len(), 48, "Must have 48 sign class representatives");

    // Verify no duplicates
    let unique: HashSet<_> = sign_classes.iter().copied().collect();
    assert_eq!(unique.len(), 48, "All sign classes must be unique");

    // Verify all are valid Atlas vertices
    for &v in sign_classes {
        assert!(v < atlas.num_vertices());
    }
}

#[test]
fn test_f4_quotient_construction() {
    let atlas = Atlas::new();
    let f4 = F4::from_atlas(&atlas);

    // F₄ is the quotient of Atlas by mirror symmetry
    // 96 vertices / 2 (mirror pairs) = 48 sign classes
    assert_eq!(atlas.num_vertices(), 96);
    assert_eq!(f4.num_roots(), 48);
    assert_eq!(atlas.num_vertices() / 2, f4.num_roots());
}

#[test]
fn test_f4_degree_distribution() {
    let atlas = Atlas::new();
    let f4 = F4::from_atlas(&atlas);
    let sign_classes = f4.sign_classes();

    // Analyze degree distribution in Atlas
    let mut degree_5_count = 0;
    let mut degree_6_count = 0;

    for &v in sign_classes {
        match atlas.degree(v) {
            5 => degree_5_count += 1,
            6 => degree_6_count += 1,
            d => panic!("Unexpected degree {d} in Atlas"),
        }
    }

    // NOTE: This tests μ-class degrees (graph structure), NOT root norms
    // μ-class degrees: 32 degree-5, 16 degree-6 (2:1 ratio in Atlas graph)
    // Actual root norms: 24 short, 24 long (1:1 ratio by norm²)
    // See: working/exceptional_groups/f4/certificate_generator.py comments
    assert_eq!(degree_5_count, 32, "Expected 32 degree-5 vertices (μ-classes)");
    assert_eq!(degree_6_count, 16, "Expected 16 degree-6 vertices (μ-classes)");
}

#[test]
fn test_f4_contains_g2() {
    let atlas = Atlas::new();
    let g2 = atlas_embeddings::groups::G2::from_atlas(&atlas);
    let f4 = F4::from_atlas(&atlas);

    // G₂ ⊂ F₄ via Weyl order divisibility
    assert_eq!(f4.weyl_order() % g2.weyl_order(), 0, "Weyl(F₄) divisible by Weyl(G₂)");
    assert_eq!(f4.weyl_order() / g2.weyl_order(), 96, "Weyl index [F₄:G₂] = 96");

    // Root count ratio
    assert_eq!(f4.num_roots() / g2.num_roots(), 4, "F₄ has 4× roots of G₂");
}
