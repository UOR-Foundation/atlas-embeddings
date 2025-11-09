//! G₂ Construction Integration Tests

use atlas_embeddings::{groups::G2, Atlas};

#[test]
fn test_g2_basic_properties() {
    let atlas = Atlas::new();
    let g2 = G2::from_atlas(&atlas);

    // Basic counts
    assert_eq!(g2.num_roots(), 12, "G₂ must have 12 roots");
    assert_eq!(g2.rank(), 2, "G₂ must have rank 2");
    assert_eq!(g2.weyl_order(), 12, "G₂ Weyl group order is 12");

    // Not simply-laced (has triple bond)
    assert!(!g2.is_simply_laced(), "G₂ is not simply-laced");
}

#[test]
fn test_g2_cartan_matrix() {
    let atlas = Atlas::new();
    let g2 = G2::from_atlas(&atlas);
    let cartan = g2.cartan_matrix();

    // Verify structure
    assert_eq!(cartan.rank(), 2);
    assert!(cartan.is_valid());
    assert!(!cartan.is_simply_laced(), "G₂ has triple bond");
    assert!(!cartan.is_symmetric(), "G₂ Cartan matrix is asymmetric");

    // Verify specific entries (triple bond)
    assert_eq!(cartan.get(0, 0), 2);
    assert_eq!(cartan.get(1, 1), 2);
    assert_eq!(cartan.get(0, 1), -3, "Triple bond: entry (0,1) = -3");
    assert_eq!(cartan.get(1, 0), -1);

    // Determinant
    assert_eq!(cartan.determinant(), 1, "G₂ Cartan determinant is 1");

    // Connected
    assert!(cartan.is_connected());
}

#[test]
fn test_g2_klein_quartet() {
    let atlas = Atlas::new();
    let g2 = G2::from_atlas(&atlas);

    let klein = g2.klein_quartet();
    assert_eq!(klein.len(), 4, "Klein quartet has 4 vertices");
}

#[test]
fn test_g2_unity_positions() {
    let atlas = Atlas::new();
    let g2 = G2::from_atlas(&atlas);

    let unity = g2.unity_positions();
    assert_eq!(unity.len(), 2, "Must have 2 unity positions in canonical slice");

    // Verify unity positions are mirror pairs
    assert!(atlas.is_mirror_pair(unity[0], unity[1]));
}

#[test]
fn test_g2_twelve_fold_divisibility() {
    let atlas = Atlas::new();
    let g2 = G2::from_atlas(&atlas);

    // Everything divisible by 12
    assert_eq!(atlas.num_vertices() % 12, 0, "96 = 12 × 8");
    assert_eq!(g2.num_roots(), 12);
    assert_eq!(g2.weyl_order(), 12);
}
