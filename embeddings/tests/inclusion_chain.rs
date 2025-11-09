//! Inclusion Chain Verification: G₂ ⊂ F₄ ⊂ E₆ ⊂ E₇ ⊂ E₈
//!
//! This test verifies the complete inclusion chain of exceptional Lie groups.

use atlas_embeddings::{
    groups::{E8Group, E6, E7, F4, G2},
    Atlas,
};

#[test]
fn test_complete_inclusion_chain() {
    let atlas = Atlas::new();
    let g2 = G2::from_atlas(&atlas);
    let f4 = F4::from_atlas(&atlas);
    let e6 = E6::from_atlas(&atlas);
    let e7 = E7::from_atlas(&atlas);
    let e8 = E8Group::new();

    // Verify chain G₂ ⊂ F₄ ⊂ E₆ ⊂ E₇ ⊂ E₈

    // Root counts increase
    assert!(g2.num_roots() < f4.num_roots(), "G₂ has fewer roots than F₄");
    assert!(f4.num_roots() < e6.num_roots(), "F₄ has fewer roots than E₆");
    assert!(e6.num_roots() < e7.num_roots(), "E₆ has fewer roots than E₇");
    assert!(e7.num_roots() < e8.num_roots(), "E₇ has fewer roots than E₈");

    // Ranks increase
    assert!(g2.rank() < f4.rank(), "G₂ has smaller rank than F₄");
    assert!(f4.rank() < e6.rank(), "F₄ has smaller rank than E₆");
    assert!(e6.rank() < e7.rank(), "E₆ has smaller rank than E₇");
    assert!(e7.rank() < e8.rank(), "E₇ has smaller rank than E₈");

    // Weyl orders increase dramatically
    assert!(g2.weyl_order() < f4.weyl_order(), "Weyl(G₂) < Weyl(F₄)");
    assert!(f4.weyl_order() < e6.weyl_order(), "Weyl(F₄) < Weyl(E₆)");
    assert!(e6.weyl_order() < e7.weyl_order(), "Weyl(E₆) < Weyl(E₇)");
    assert!(e7.weyl_order() < e8.weyl_order(), "Weyl(E₇) < Weyl(E₈)");
}

#[test]
fn test_weyl_order_divisibility() {
    let atlas = Atlas::new();
    let g2 = G2::from_atlas(&atlas);
    let f4 = F4::from_atlas(&atlas);
    let e6 = E6::from_atlas(&atlas);
    let e7 = E7::from_atlas(&atlas);
    let e8 = E8Group::new();

    // Weyl order divisibility implies inclusion
    assert_eq!(f4.weyl_order() % g2.weyl_order(), 0, "Weyl(F₄) divisible by Weyl(G₂)");
    assert_eq!(e6.weyl_order() % f4.weyl_order(), 0, "Weyl(E₆) divisible by Weyl(F₄)");
    assert_eq!(e7.weyl_order() % e6.weyl_order(), 0, "Weyl(E₇) divisible by Weyl(E₆)");
    assert_eq!(e8.weyl_order() % e7.weyl_order(), 0, "Weyl(E₈) divisible by Weyl(E₇)");
}

#[test]
#[allow(clippy::similar_names)] // Mathematical notation: index_e7_e6, index_e8_e7, etc.
fn test_weyl_indices() {
    let atlas = Atlas::new();
    let g2 = G2::from_atlas(&atlas);
    let f4 = F4::from_atlas(&atlas);
    let e6 = E6::from_atlas(&atlas);
    let e7 = E7::from_atlas(&atlas);
    let e8 = E8Group::new();

    // Compute Weyl indices [G:H] = |Weyl(G)|/|Weyl(H)|
    let index_f4_g2 = f4.weyl_order() / g2.weyl_order();
    let index_e6_f4 = e6.weyl_order() / f4.weyl_order();
    let index_e7_e6 = e7.weyl_order() / e6.weyl_order();
    let index_e8_e7 = e8.weyl_order() / e7.weyl_order();

    // Verify expected indices
    assert_eq!(index_f4_g2, 96, "[F₄:G₂] = 96");
    assert_eq!(index_e6_f4, 45, "[E₆:F₄] = 45");
    assert_eq!(index_e7_e6, 56, "[E₇:E₆] = 56");
    assert_eq!(index_e8_e7, 240, "[E₈:E₇] = 240");

    println!("\nWeyl Indices:");
    println!("  [F₄:G₂] = {index_f4_g2}");
    println!("  [E₆:F₄] = {index_e6_f4}");
    println!("  [E₇:E₆] = {index_e7_e6}");
    println!("  [E₈:E₇] = {index_e8_e7}");
}

#[test]
fn test_root_count_progression() {
    let atlas = Atlas::new();
    let g2 = G2::from_atlas(&atlas);
    let f4 = F4::from_atlas(&atlas);
    let e6 = E6::from_atlas(&atlas);
    let e7 = E7::from_atlas(&atlas);
    let e8 = E8Group::new();

    // Expected root counts
    assert_eq!(g2.num_roots(), 12, "G₂ has 12 roots");
    assert_eq!(f4.num_roots(), 48, "F₄ has 48 roots");
    assert_eq!(e6.num_roots(), 72, "E₆ has 72 roots");
    assert_eq!(e7.num_roots(), 126, "E₇ has 126 roots");
    assert_eq!(e8.num_roots(), 240, "E₈ has 240 roots");

    // Root count ratios
    assert_eq!(f4.num_roots() / g2.num_roots(), 4, "F₄ has 4× roots of G₂");
    assert_eq!(e8.num_roots() / g2.num_roots(), 20, "E₈ has 20× roots of G₂");

    println!("\nRoot Count Progression:");
    println!("  G₂: {:3} roots", g2.num_roots());
    println!("  F₄: {:3} roots", f4.num_roots());
    println!("  E₆: {:3} roots", e6.num_roots());
    println!("  E₇: {:3} roots", e7.num_roots());
    println!("  E₈: {:3} roots", e8.num_roots());
}

#[test]
fn test_rank_progression() {
    let atlas = Atlas::new();
    let g2 = G2::from_atlas(&atlas);
    let f4 = F4::from_atlas(&atlas);
    let e6 = E6::from_atlas(&atlas);
    let e7 = E7::from_atlas(&atlas);
    let e8 = E8Group::new();

    // Verify ranks
    assert_eq!(g2.rank(), 2, "G₂ has rank 2");
    assert_eq!(f4.rank(), 4, "F₄ has rank 4");
    assert_eq!(e6.rank(), 6, "E₆ has rank 6");
    assert_eq!(e7.rank(), 7, "E₇ has rank 7");
    assert_eq!(e8.rank(), 8, "E₈ has rank 8");

    println!("\nRank Progression:");
    println!("  G₂: rank {}", g2.rank());
    println!("  F₄: rank {}", f4.rank());
    println!("  E₆: rank {}", e6.rank());
    println!("  E₇: rank {}", e7.rank());
    println!("  E₈: rank {}", e8.rank());
}

#[test]
fn test_simply_laced_classification() {
    let atlas = Atlas::new();
    let g2 = G2::from_atlas(&atlas);
    let f4 = F4::from_atlas(&atlas);
    let e6 = E6::from_atlas(&atlas);
    let e7 = E7::from_atlas(&atlas);
    let e8 = E8Group::new();

    // Non-simply-laced (have multiple root lengths)
    assert!(!g2.is_simply_laced(), "G₂ is not simply-laced (triple bond)");
    assert!(!f4.is_simply_laced(), "F₄ is not simply-laced (double bond)");

    // Simply-laced (all roots same length)
    assert!(e6.is_simply_laced(), "E₆ is simply-laced");
    assert!(e7.is_simply_laced(), "E₇ is simply-laced");
    assert!(e8.is_simply_laced(), "E₈ is simply-laced");
}

#[test]
fn test_cartan_determinants() {
    let atlas = Atlas::new();
    let g2 = G2::from_atlas(&atlas);
    let f4 = F4::from_atlas(&atlas);
    let e6 = E6::from_atlas(&atlas);
    let e7 = E7::from_atlas(&atlas);
    let e8 = E8Group::new();

    // Cartan matrix determinants
    assert_eq!(g2.cartan_matrix().determinant(), 1, "det(G₂) = 1");
    assert_eq!(f4.cartan_matrix().determinant(), 1, "det(F₄) = 1");
    assert_eq!(e6.cartan_matrix().determinant(), 3, "det(E₆) = 3");
    assert_eq!(e7.cartan_matrix().determinant(), 2, "det(E₇) = 2");
    assert_eq!(e8.cartan_matrix().determinant(), 1, "det(E₈) = 1");

    println!("\nCartan Determinants:");
    println!("  det(G₂) = {}", g2.cartan_matrix().determinant());
    println!("  det(F₄) = {}", f4.cartan_matrix().determinant());
    println!("  det(E₆) = {}", e6.cartan_matrix().determinant());
    println!("  det(E₇) = {}", e7.cartan_matrix().determinant());
    println!("  det(E₈) = {}", e8.cartan_matrix().determinant());
}
