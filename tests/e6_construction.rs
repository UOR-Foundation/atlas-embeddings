//! E₆ Construction Integration Tests

use atlas_embeddings::{groups::E6, Atlas};

#[test]
fn test_e6_basic_properties() {
    let atlas = Atlas::new();
    let e6 = E6::from_atlas(&atlas);

    // Basic counts
    assert_eq!(e6.num_roots(), 72, "E₆ must have 72 roots");
    assert_eq!(e6.rank(), 6, "E₆ must have rank 6");
    assert_eq!(e6.weyl_order(), 51840, "E₆ Weyl group order is 51,840");

    // Simply-laced
    assert!(e6.is_simply_laced(), "E₆ is simply-laced");
}

#[test]
fn test_e6_cartan_matrix() {
    let atlas = Atlas::new();
    let e6 = E6::from_atlas(&atlas);
    let cartan = e6.cartan_matrix();

    // Verify structure
    assert_eq!(cartan.rank(), 6);
    assert!(cartan.is_valid());
    assert!(cartan.is_simply_laced(), "E₆ is simply-laced");
    assert!(cartan.is_symmetric(), "E₆ Cartan matrix is symmetric");

    // Verify diagonal
    for i in 0..6 {
        assert_eq!(cartan.get(i, i), 2);
    }

    // Determinant
    assert_eq!(cartan.determinant(), 3, "E₆ Cartan determinant is 3");

    // Connected
    assert!(cartan.is_connected());
}

#[test]
fn test_e6_degree_partition() {
    let atlas = Atlas::new();
    let e6 = E6::from_atlas(&atlas);

    // E₆ constructed via degree partition: 64 degree-5 + 8 degree-6
    let vertices = e6.vertices();
    assert_eq!(vertices.len(), 72);

    // Count by degree
    let mut degree_5 = 0;
    let mut degree_6 = 0;

    for &v in vertices {
        match atlas.degree(v) {
            5 => degree_5 += 1,
            6 => degree_6 += 1,
            d => panic!("Unexpected degree {d} in E₆"),
        }
    }

    assert_eq!(degree_5, 64, "E₆ has 64 degree-5 vertices");
    assert_eq!(degree_6, 8, "E₆ has 8 degree-6 vertices");
}

#[test]
fn test_e6_atlas_partition() {
    let atlas = Atlas::new();
    let e6 = E6::from_atlas(&atlas);

    // E₆ is 72 of the 96 Atlas vertices
    // Complement has 24 vertices
    assert_eq!(atlas.num_vertices(), 96);
    assert_eq!(e6.num_roots(), 72);
    assert_eq!(atlas.num_vertices() - e6.num_roots(), 24, "Complement has 24 vertices");
}

#[test]
fn test_e6_simply_laced_properties() {
    let atlas = Atlas::new();
    let e6 = E6::from_atlas(&atlas);

    // Simply-laced means all roots have same length
    assert!(e6.is_simply_laced());

    // Cartan matrix has only {0, -1} off-diagonal
    let cartan = e6.cartan_matrix();
    for i in 0..6 {
        for j in 0..6 {
            if i != j {
                let entry = cartan.get(i, j);
                assert!(entry == 0 || entry == -1, "Simply-laced: off-diagonal ∈ {{0, -1}}");
            }
        }
    }
}

#[test]
fn test_e6_weyl_divisibility() {
    let atlas = Atlas::new();
    let f4 = atlas_embeddings::groups::F4::from_atlas(&atlas);
    let e6 = E6::from_atlas(&atlas);

    // F₄ ⊂ E₆ via Weyl order divisibility
    assert_eq!(e6.weyl_order() % f4.weyl_order(), 0, "Weyl(E₆) divisible by Weyl(F₄)");
    assert_eq!(e6.weyl_order() / f4.weyl_order(), 45, "Weyl index [E₆:F₄] = 45");
}

#[test]
fn test_e6_simple_roots_extraction() {
    use atlas_embeddings::e8::E8RootSystem;
    use atlas_embeddings::embedding::AtlasE8Embedding;
    use atlas_embeddings::arithmetic::Rational;

    let atlas = Atlas::new();
    let e6 = E6::from_atlas(&atlas);

    // Extract simple roots using extremal algorithm
    let simple_roots = e6.simple_roots();

    // Must find exactly 6 simple roots
    assert_eq!(simple_roots.len(), 6, "E₆ has 6 simple roots");

    // Verify all simple roots are in E₆ vertex set
    for &root in &simple_roots {
        assert!(e6.vertices().contains(&root), "Simple root {root} must be in E₆ vertices");
    }

    // Verify Cartan matrix from simple roots
    let e8 = E8RootSystem::new();
    let embedding = AtlasE8Embedding::new();

    // Compute Cartan matrix: Cᵢⱼ = ⟨αᵢ, αⱼ⟩
    let mut cartan = vec![vec![0i64; 6]; 6];
    for i in 0..6 {
        for j in 0..6 {
            let e8_i = embedding.map_vertex(simple_roots[i]);
            let e8_j = embedding.map_vertex(simple_roots[j]);
            let root_i = e8.get_root(e8_i);
            let root_j = e8.get_root(e8_j);

            // Inner product
            let mut ip = Rational::new(0, 1);
            for k in 0..8 {
                ip += root_i.get(k).to_rational() * root_j.get(k).to_rational();
            }

            cartan[i][j] = *ip.numer() / *ip.denom();
        }
    }

    // Verify Cartan matrix properties
    for i in 0..6 {
        assert_eq!(cartan[i][i], 2, "Diagonal must be 2");
        for j in 0..6 {
            if i != j {
                assert!(cartan[i][j] <= 0, "Off-diagonal must be ≤ 0");
                assert!(cartan[i][j] == 0 || cartan[i][j] == -1, "Simply-laced: only 0 or -1");
            }
        }
    }

    // Verify E₆ Dynkin shape: 1 branch node (deg 3), 3 endpoints (deg 1)
    let mut degrees = [0; 6];
    for i in 0..6 {
        for j in 0..6 {
            if i != j && cartan[i][j] == -1 {
                degrees[i] += 1;
            }
        }
    }

    let branch_nodes = degrees.iter().filter(|&&d| d == 3).count();
    let endpoints = degrees.iter().filter(|&&d| d == 1).count();

    assert_eq!(branch_nodes, 1, "E₆ must have exactly 1 branch node (degree 3)");
    assert_eq!(endpoints, 3, "E₆ must have exactly 3 endpoints (degree 1)");
}
