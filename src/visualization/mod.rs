//! Visualization Module for Atlas Embeddings
//!
//! This module provides visualization capabilities for the Atlas of Resonance Classes,
//! exceptional Lie groups, and their relationships. All visualizations use exact arithmetic
//! and can export to standard formats (SVG, `GraphML`, JSON, CSV).
//!
//! # Overview
//!
//! The visualization module enables understanding of the Atlas → E₈ embedding and
//! the emergence of exceptional groups through visual representations. This is critical
//! for communicating the **Golden Seed Vector** and the universal mathematical language
//! it represents.
//!
//! # Key Visualizations
//!
//! 1. **Atlas Graph** - 96-vertex graph with degree distribution and mirror symmetry
//! 2. **Dynkin Diagrams** - Standard representations of all five exceptional groups
//! 3. **E₈ Root System** - 240 roots with various projections and colorings
//! 4. **Golden Seed Vector** - The 96-dimensional Atlas embedding within E₈
//! 5. **Categorical Operations** - Visual representation of the five "foldings"
//!
//! # Design Principles
//!
//! - **Exact Arithmetic**: All computations use exact rational arithmetic (no approximations)
//! - **Standard Formats**: Export to widely-supported formats (SVG, `GraphML`, JSON, CSV)
//! - **Reproducible**: Same input always produces identical output
//! - **Well-Documented**: Each visualization includes mathematical context
//! - **Type-Safe**: Compile-time guarantees where possible
//!
//! # Module Organization
//!
//! - [`atlas_graph`] - Atlas 96-vertex graph visualization and export
//! - [`dynkin`] - Dynkin diagram generation (SVG)
//! - [`e8_roots`] - E₈ root system projections and colorings
//! - [`embedding`] - Golden Seed Vector (Atlas → E₈) visualization
//! - [`export`] - Data export utilities (`GraphML`, JSON, CSV)
//!
//! # Examples
//!
//! ## Example 1: Generate Atlas Graph Visualization
//!
//! ```rust
//! use atlas_embeddings::Atlas;
//! use atlas_embeddings::visualization::atlas_graph::AtlasGraphVisualizer;
//!
//! let atlas = Atlas::new();
//! let visualizer = AtlasGraphVisualizer::new(&atlas);
//!
//! // Export to GraphML for external tools (Gephi, Cytoscape, etc.)
//! let graphml = visualizer.to_graphml();
//! // std::fs::write("atlas.graphml", graphml).unwrap();
//!
//! // Export coordinates as JSON
//! let json = visualizer.to_json();
//! // std::fs::write("atlas.json", json).unwrap();
//! ```
//!
//! ## Example 2: Generate Dynkin Diagrams
//!
//! ```rust
//! use atlas_embeddings::cartan::CartanMatrix;
//! use atlas_embeddings::visualization::dynkin::DynkinVisualizer;
//!
//! // Generate SVG for E₈ Dynkin diagram
//! let e8_cartan = CartanMatrix::<8>::e8();
//! let svg = DynkinVisualizer::generate_svg(&e8_cartan, "E₈");
//! // std::fs::write("e8_dynkin.svg", svg).unwrap();
//!
//! // Generate all five exceptional groups
//! let all_diagrams = DynkinVisualizer::generate_all_exceptional();
//! // for (name, svg) in all_diagrams {
//! //     std::fs::write(format!("{}_dynkin.svg", name), svg).unwrap();
//! // }
//! ```
//!
//! ## Example 3: Visualize Golden Seed Vector
//!
//! ```rust
//! use atlas_embeddings::{Atlas, e8::E8RootSystem};
//! use atlas_embeddings::embedding::compute_atlas_embedding;
//! use atlas_embeddings::visualization::embedding::GoldenSeedVisualizer;
//!
//! let atlas = Atlas::new();
//! let e8 = E8RootSystem::new();
//! let embedding = compute_atlas_embedding(&atlas);
//!
//! let visualizer = GoldenSeedVisualizer::new(&atlas, &e8, &embedding);
//!
//! // Export 3D coordinates for the Golden Seed Vector
//! let coordinates = visualizer.export_coordinates_csv();
//! // std::fs::write("golden_seed_vector.csv", coordinates).unwrap();
//!
//! // Export with E₈ context (showing 96 Atlas roots within 240 E₈ roots)
//! let full_context = visualizer.export_with_e8_context();
//! // std::fs::write("golden_seed_in_e8.json", full_context).unwrap();
//! ```
//!
//! ## Example 4: E₈ Root System Projections
//!
//! ```rust
//! use atlas_embeddings::e8::E8RootSystem;
//! use atlas_embeddings::visualization::e8_roots::E8Projector;
//!
//! let e8 = E8RootSystem::new();
//! let projector = E8Projector::new(&e8);
//!
//! // Coxeter plane projection (most symmetric 2D view)
//! let coxeter_2d = projector.project_coxeter_plane();
//! // export_as_csv("e8_coxeter.csv", &coxeter_2d);
//!
//! // 3D projection showing structure
//! let projection_3d = projector.project_3d_principal();
//! // export_as_csv("e8_3d.csv", &projection_3d);
//! ```
//!
//! # Feature Flags
//!
//! The visualization module is enabled by default but can be controlled via features:
//!
//! - `visualization` - Enable all visualization functionality (default)
//! - `svg-export` - Enable SVG generation (requires `visualization`)
//! - `graphml-export` - Enable `GraphML` export (requires `visualization`)
//!
//! # Format Specifications
//!
//! ## `GraphML`
//!
//! `GraphML` exports include:
//! - Node attributes: label, degree, `mirror_pair_id`
//! - Edge attributes: `edge_type` (adjacency, mirror)
//! - Graph metadata: `vertex_count`, `edge_count`
//!
//! ## JSON
//!
//! JSON exports follow this schema:
//! ```json
//! {
//!   "vertices": [{"id": 0, "label": [0,0,0,0,0,0], "degree": 5}],
//!   "edges": [{"source": 0, "target": 1, "type": "adjacency"}],
//!   "metadata": {"vertex_count": 96, "edge_count": 420}
//! }
//! ```
//!
//! ## CSV
//!
//! CSV exports for coordinates:
//! ```csv
//! id,x,y,z,root_type,group
//! 0,0.707,0.000,0.707,half_integer,atlas
//! ```
//!
//! # Performance Considerations
//!
//! All visualization operations are designed to be fast:
//! - Atlas graph generation: < 1ms
//! - Dynkin diagram SVG: < 1ms
//! - E₈ projection: < 10ms
//! - Golden Seed Vector export: < 5ms
//!
//! # References
//!
//! - `GraphML` Specification: <http://graphml.graphdrawing.org/>
//! - SVG Specification: <https://www.w3.org/TR/SVG/>
//! - JSON Schema: <https://json-schema.org/>
//!
//! # Navigation
//!
//! - Up: [Main Page](crate)
//! - Related: [Atlas Module](crate::atlas), [E₈ Module](crate::e8)

// Submodules (stub implementations - to be completed)
pub mod atlas_graph;
pub mod dynkin;
pub mod e8_roots;
pub mod embedding;
pub mod export;
pub mod fractal;

// Re-exports for convenience
pub use atlas_graph::AtlasGraphVisualizer;
pub use dynkin::DynkinVisualizer;
pub use e8_roots::E8Projector;
pub use embedding::GoldenSeedVisualizer;
pub use export::{ExportFormat, Exporter};
pub use fractal::{GoldenSeedFractal, GoldenSeedFractal3D};

#[cfg(test)]
mod tests {
    /// Test that visualization module is available
    #[test]
    fn test_module_available() {
        // This test ensures the module compiles and is accessible
        // If we got here, the module loaded successfully
    }
}
