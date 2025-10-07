//! E₈ Embedding Integration Tests

use atlas_embeddings::{groups::E8Group, Atlas};

#[test]
fn test_e8_basic_properties() {
    let e8 = E8Group::new();

    // Basic counts
    assert_eq!(e8.num_roots(), 240, "E₈ must have 240 roots");
    assert_eq!(e8.rank(), 8, "E₈ must have rank 8");
    assert_eq!(e8.weyl_order(), 696_729_600, "E₈ Weyl group order is 696,729,600");

    // Simply-laced
    assert!(e8.is_simply_laced(), "E₈ is simply-laced");
}

#[test]
fn test_e8_cartan_matrix() {
    let e8 = E8Group::new();
    let cartan = e8.cartan_matrix();

    // Verify structure
    assert_eq!(cartan.rank(), 8);
    assert!(cartan.is_valid());
    assert!(cartan.is_simply_laced(), "E₈ is simply-laced");
    assert!(cartan.is_symmetric(), "E₈ Cartan matrix is symmetric");

    // Verify diagonal
    for i in 0..8 {
        assert_eq!(cartan.get(i, i), 2);
    }

    // Determinant
    assert_eq!(cartan.determinant(), 1, "E₈ Cartan determinant is 1");

    // Connected
    assert!(cartan.is_connected());
}

#[test]
fn test_e8_simply_laced_properties() {
    let e8 = E8Group::new();

    // Simply-laced means all roots have same length
    assert!(e8.is_simply_laced());

    // Cartan matrix has only {0, -1} off-diagonal
    let cartan = e8.cartan_matrix();
    for i in 0..8 {
        for j in 0..8 {
            if i != j {
                let entry = cartan.get(i, j);
                assert!(entry == 0 || entry == -1, "Simply-laced: off-diagonal ∈ {{0, -1}}");
            }
        }
    }
}

#[test]
fn test_e8_contains_e7() {
    let atlas = Atlas::new();
    let e7 = atlas_embeddings::groups::E7::from_atlas(&atlas);
    let e8 = E8Group::new();

    // E₇ ⊂ E₈ via Weyl order divisibility
    assert_eq!(e8.weyl_order() % e7.weyl_order(), 0, "Weyl(E₈) divisible by Weyl(E₇)");
    assert_eq!(e8.weyl_order() / e7.weyl_order(), 240, "Weyl index [E₈:E₇] = 240");
}

#[test]
fn test_e8_root_ratio() {
    let atlas = Atlas::new();
    let e7 = atlas_embeddings::groups::E7::from_atlas(&atlas);
    let e8 = E8Group::new();

    // Root count relationship
    assert_eq!(e8.num_roots(), 240);
    assert_eq!(e7.num_roots(), 126);
    assert_eq!(e8.num_roots() - e7.num_roots(), 114, "E₈ has 114 more roots than E₇");
}

#[test]
fn test_e8_is_largest_exceptional() {
    let e8 = E8Group::new();

    // E₈ is the largest exceptional group
    assert_eq!(e8.num_roots(), 240, "E₈ has maximum root count among exceptional groups");
    assert_eq!(e8.rank(), 8, "E₈ has maximum rank among exceptional groups");

    // Weyl order is massive
    assert!(e8.weyl_order() > 600_000_000, "E₈ Weyl group exceeds 600 million");
}

#[test]
fn test_e8_complete_chain() {
    let atlas = Atlas::new();
    let g2 = atlas_embeddings::groups::G2::from_atlas(&atlas);
    let f4 = atlas_embeddings::groups::F4::from_atlas(&atlas);
    let e6 = atlas_embeddings::groups::E6::from_atlas(&atlas);
    let e7 = atlas_embeddings::groups::E7::from_atlas(&atlas);
    let e8 = E8Group::new();

    // Verify complete inclusion chain G₂ ⊂ F₄ ⊂ E₆ ⊂ E₇ ⊂ E₈
    assert!(g2.weyl_order() < f4.weyl_order());
    assert!(f4.weyl_order() < e6.weyl_order());
    assert!(e6.weyl_order() < e7.weyl_order());
    assert!(e7.weyl_order() < e8.weyl_order());

    // Weyl order divisibility
    assert_eq!(f4.weyl_order() % g2.weyl_order(), 0, "F₄ contains G₂");
    assert_eq!(e6.weyl_order() % f4.weyl_order(), 0, "E₆ contains F₄");
    assert_eq!(e7.weyl_order() % e6.weyl_order(), 0, "E₇ contains E₆");
    assert_eq!(e8.weyl_order() % e7.weyl_order(), 0, "E₈ contains E₇");
}
