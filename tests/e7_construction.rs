//! E₇ Construction Integration Tests

use atlas_embeddings::{groups::E7, Atlas};

#[test]
fn test_e7_basic_properties() {
    let atlas = Atlas::new();
    let e7 = E7::from_atlas(&atlas);

    // Basic counts
    assert_eq!(e7.num_roots(), 126, "E₇ must have 126 roots");
    assert_eq!(e7.rank(), 7, "E₇ must have rank 7");
    assert_eq!(e7.weyl_order(), 2_903_040, "E₇ Weyl group order is 2,903,040");

    // Simply-laced
    assert!(e7.is_simply_laced(), "E₇ is simply-laced");
}

#[test]
fn test_e7_cartan_matrix() {
    let atlas = Atlas::new();
    let e7 = E7::from_atlas(&atlas);
    let cartan = e7.cartan_matrix();

    // Verify structure
    assert_eq!(cartan.rank(), 7);
    assert!(cartan.is_valid());
    assert!(cartan.is_simply_laced(), "E₇ is simply-laced");
    assert!(cartan.is_symmetric(), "E₇ Cartan matrix is symmetric");

    // Verify diagonal
    for i in 0..7 {
        assert_eq!(cartan.get(i, i), 2);
    }

    // Determinant
    assert_eq!(cartan.determinant(), 2, "E₇ Cartan determinant is 2");

    // Connected
    assert!(cartan.is_connected());
}

#[test]
fn test_e7_augmentation_construction() {
    let atlas = Atlas::new();
    let e7 = E7::from_atlas(&atlas);

    // E₇ constructed via augmentation: 126 = 96 (Atlas) + 30 (S₄ orbits)
    assert_eq!(atlas.num_vertices(), 96, "Atlas has 96 vertices");
    assert_eq!(e7.num_roots(), 126, "E₇ has 126 roots");
    assert_eq!(e7.num_roots() - atlas.num_vertices(), 30, "30 S₄ orbit representatives");
}

#[test]
fn test_e7_simply_laced_properties() {
    let atlas = Atlas::new();
    let e7 = E7::from_atlas(&atlas);

    // Simply-laced means all roots have same length
    assert!(e7.is_simply_laced());

    // Cartan matrix has only {0, -1} off-diagonal
    let cartan = e7.cartan_matrix();
    for i in 0..7 {
        for j in 0..7 {
            if i != j {
                let entry = cartan.get(i, j);
                assert!(entry == 0 || entry == -1, "Simply-laced: off-diagonal ∈ {{0, -1}}");
            }
        }
    }
}

#[test]
fn test_e7_contains_e6() {
    let atlas = Atlas::new();
    let e6 = atlas_embeddings::groups::E6::from_atlas(&atlas);
    let e7 = E7::from_atlas(&atlas);

    // E₆ ⊂ E₇ via Weyl order divisibility
    assert_eq!(e7.weyl_order() % e6.weyl_order(), 0, "Weyl(E₇) divisible by Weyl(E₆)");
    assert_eq!(e7.weyl_order() / e6.weyl_order(), 56, "Weyl index [E₇:E₆] = 56");
}

#[test]
fn test_e7_root_ratio() {
    let atlas = Atlas::new();
    let e6 = atlas_embeddings::groups::E6::from_atlas(&atlas);
    let e7 = E7::from_atlas(&atlas);

    // Root count relationship
    assert_eq!(e7.num_roots(), 126);
    assert_eq!(e6.num_roots(), 72);
    assert_eq!(e7.num_roots() - e6.num_roots(), 54, "E₇ has 54 more roots than E₆");
}
