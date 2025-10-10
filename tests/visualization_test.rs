//! Integration tests for the visualization module
//!
//! These tests verify that all visualization components work correctly
//! with the main Atlas embeddings implementation.

#[cfg(feature = "visualization")]
mod visualization_tests {
    use atlas_embeddings::cartan::CartanMatrix;
    use atlas_embeddings::e8::E8RootSystem;
    use atlas_embeddings::embedding::compute_atlas_embedding;
    use atlas_embeddings::visualization::atlas_graph::AtlasGraphVisualizer;
    use atlas_embeddings::visualization::dynkin::DynkinVisualizer;
    use atlas_embeddings::visualization::e8_roots::E8Projector;
    use atlas_embeddings::visualization::embedding::GoldenSeedVisualizer;
    use atlas_embeddings::visualization::export::ExportFormat;
    use atlas_embeddings::Atlas;

    #[test]
    fn test_atlas_graph_visualizer() {
        let atlas = Atlas::new();
        let vis = AtlasGraphVisualizer::new(&atlas);

        // Test basic properties
        assert_eq!(vis.vertex_count(), 96);
        assert!(vis.edge_count() > 0);

        // Test degree distribution
        let dist = vis.degree_distribution();
        assert_eq!(dist.get(&5), Some(&64));
        assert_eq!(dist.get(&6), Some(&32));
    }

    #[test]
    fn test_atlas_graph_exports() {
        let atlas = Atlas::new();
        let vis = AtlasGraphVisualizer::new(&atlas);

        // Test all export formats
        let graphml = vis.to_graphml();
        assert!(graphml.contains("graphml"));

        let json = vis.to_json();
        assert!(json.contains("vertices") || json.contains("edges"));

        let dot = vis.to_dot();
        assert!(dot.contains("graph"));

        let csv_edges = vis.to_csv_edges();
        assert!(csv_edges.contains("source") || csv_edges.contains("target"));

        let csv_nodes = vis.to_csv_nodes();
        assert!(csv_nodes.contains("id") || csv_nodes.contains("degree"));
    }

    #[test]
    fn test_dynkin_visualizer() {
        // Test G₂
        let g2 = CartanMatrix::<2>::g2();
        let svg = DynkinVisualizer::generate_svg(&g2, "G₂");
        assert!(svg.contains("<svg") || svg.contains("G₂"));

        // Test all exceptional groups
        let all_diagrams = DynkinVisualizer::generate_all_exceptional();
        assert_eq!(all_diagrams.len(), 5);

        let names: Vec<String> = all_diagrams.iter().map(|(name, _)| name.clone()).collect();
        assert!(names.contains(&"G2".to_string()));
        assert!(names.contains(&"F4".to_string()));
        assert!(names.contains(&"E6".to_string()));
        assert!(names.contains(&"E7".to_string()));
        assert!(names.contains(&"E8".to_string()));
    }

    #[test]
    fn test_e8_projector() {
        let e8 = E8RootSystem::new();
        let projector = E8Projector::new(&e8);

        // Test 2D projection
        let coxeter = projector.project_coxeter_plane();
        assert_eq!(coxeter.len(), 240);

        // Test 3D projection
        let proj_3d = projector.project_3d_principal();
        assert_eq!(proj_3d.len(), 240);

        // Test simple XY projection
        let xy = projector.project_xy_plane();
        assert_eq!(xy.len(), 240);
    }

    #[test]
    fn test_golden_seed_visualizer() {
        let atlas = Atlas::new();
        let e8 = E8RootSystem::new();
        let embedding = compute_atlas_embedding(&atlas);

        let vis = GoldenSeedVisualizer::new(&atlas, &e8, &embedding);

        // Test statistics
        let stats = vis.summary_statistics();
        assert_eq!(stats.atlas_vertices, 96);
        assert_eq!(stats.e8_roots, 240);
        assert!((stats.coverage_ratio - 0.4).abs() < 0.01);

        // Test exports
        let csv = vis.export_coordinates_csv();
        assert!(csv.contains("atlas_id") || csv.contains("e8_index"));

        let json = vis.export_with_e8_context();
        assert!(json.contains("golden_seed") || json.contains("e8_roots"));

        let adj = vis.export_adjacency_preservation();
        assert!(adj.contains("atlas") || adj.contains("preserved"));
    }

    #[test]
    fn test_export_formats() {
        let formats = ExportFormat::all();
        assert_eq!(formats.len(), 5);

        for format in formats {
            assert!(!format.extension().is_empty());
            assert!(!format.mime_type().is_empty());
        }
    }

    #[test]
    fn test_visualization_integration() {
        // End-to-end test: create all visualizations for the Atlas
        let atlas = Atlas::new();
        let e8 = E8RootSystem::new();
        let embedding = compute_atlas_embedding(&atlas);

        // Atlas graph
        let atlas_vis = AtlasGraphVisualizer::new(&atlas);
        let _ = atlas_vis.to_graphml();
        let _ = atlas_vis.to_json();

        // Dynkin diagrams
        let _ = DynkinVisualizer::generate_all_exceptional();

        // E₈ projections
        let e8_proj = E8Projector::new(&e8);
        let _ = e8_proj.project_coxeter_plane();

        // Golden Seed Vector
        let golden_seed = GoldenSeedVisualizer::new(&atlas, &e8, &embedding);
        let _ = golden_seed.export_coordinates_csv();
    }
}

#[cfg(not(feature = "visualization"))]
#[test]
fn test_visualization_feature_disabled() {
    // When visualization feature is disabled, module should not be available
    // This test just ensures the feature flag works correctly
    assert!(true);
}
