//! Golden Seed Vector Visualization
//!
//! This module visualizes the **Golden Seed Vector** - the embedding of the
//! 96-vertex Atlas into the 240-root E₈ system. This is the central output
//! of the atlas-embeddings model.
//!
//! # The Golden Seed Vector
//!
//! The Golden Seed Vector is the 96-dimensional configuration produced by
//! embedding Atlas into E₈. It represents a universal mathematical template
//! for constructing symmetric structures.
//!
//! # What This Visualizes
//!
//! - The 96 Atlas vertices as a subset of 240 E₈ roots
//! - Preserved adjacency structure
//! - Mirror pair relationships
//! - Relationship to all five exceptional groups
//!
//! # Examples
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
//! let vis = GoldenSeedVisualizer::new(&atlas, &e8, &embedding);
//! let csv = vis.export_coordinates_csv();
//! ```

use crate::arithmetic::Vector8;
use crate::{e8::E8RootSystem, Atlas};
use num_traits::ToPrimitive;

/// Visualizer for the Golden Seed Vector (Atlas → E₈ embedding)
///
/// Provides methods to export and visualize the Atlas embedding within E₈,
/// showing how the 96 vertices map to specific E₈ roots.
#[derive(Debug)]
pub struct GoldenSeedVisualizer<'a> {
    atlas: &'a Atlas,
    #[allow(dead_code)] // Will be used when export functions are fully implemented
    e8: &'a E8RootSystem,
    #[allow(dead_code)] // Will be used when export functions are fully implemented
    embedding: &'a [Vector8; 96],
}

impl<'a> GoldenSeedVisualizer<'a> {
    /// Create a new Golden Seed Vector visualizer
    ///
    /// # Arguments
    ///
    /// * `atlas` - The Atlas graph
    /// * `e8` - The E₈ root system
    /// * `embedding` - The 96 Atlas vertices mapped to E₈ coordinates
    ///
    /// # Examples
    ///
    /// ```rust
    /// use atlas_embeddings::{Atlas, e8::E8RootSystem};
    /// use atlas_embeddings::embedding::compute_atlas_embedding;
    /// use atlas_embeddings::visualization::embedding::GoldenSeedVisualizer;
    ///
    /// let atlas = Atlas::new();
    /// let e8 = E8RootSystem::new();
    /// let embedding = compute_atlas_embedding(&atlas);
    /// let vis = GoldenSeedVisualizer::new(&atlas, &e8, &embedding);
    /// ```
    #[must_use]
    pub const fn new(atlas: &'a Atlas, e8: &'a E8RootSystem, embedding: &'a [Vector8; 96]) -> Self {
        Self { atlas, e8, embedding }
    }

    /// Export Atlas embedding coordinates as CSV
    ///
    /// # Format
    ///
    /// ```csv
    /// atlas_id,e8_index,x0,x1,x2,x3,x4,x5,x6,x7,degree,mirror_pair
    /// 0,42,0.5,0.5,0.5,0.5,0.5,0.5,0.5,0.5,5,48
    /// ```
    #[must_use]
    #[allow(clippy::cast_precision_loss)] // CSV export only, not used in computation
    #[allow(clippy::format_push_string)] // String building for export
    #[allow(clippy::large_stack_arrays)] // Format strings for CSV export
    pub fn export_coordinates_csv(&self) -> String {
        let mut csv = String::from("atlas_id,x0,x1,x2,x3,x4,x5,x6,x7,degree,mirror_pair\n");

        for atlas_id in 0..96 {
            let root = &self.embedding[atlas_id];
            let degree = self.atlas.degree(atlas_id);
            let mirror = self.atlas.mirror_pair(atlas_id);

            // Convert Vector8 components to f64 for CSV
            let coords = root.coords();
            let x0 = coords[0].to_rational().to_f64().unwrap_or(0.0);
            let x1 = coords[1].to_rational().to_f64().unwrap_or(0.0);
            let x2 = coords[2].to_rational().to_f64().unwrap_or(0.0);
            let x3 = coords[3].to_rational().to_f64().unwrap_or(0.0);
            let x4 = coords[4].to_rational().to_f64().unwrap_or(0.0);
            let x5 = coords[5].to_rational().to_f64().unwrap_or(0.0);
            let x6 = coords[6].to_rational().to_f64().unwrap_or(0.0);
            let x7 = coords[7].to_rational().to_f64().unwrap_or(0.0);

            csv.push_str(&format!(
                "{atlas_id},{x0},{x1},{x2},{x3},{x4},{x5},{x6},{x7},{degree},{mirror}\n"
            ));
        }

        csv
    }

    /// Export with full E₈ context
    ///
    /// Returns JSON showing:
    /// - All 240 E₈ roots
    /// - 96 Atlas roots highlighted
    /// - Adjacency preservation
    ///
    /// # Format
    ///
    /// ```json
    /// {
    ///   "e8_roots": [...],
    ///   "atlas_subset": [0, 1, 2, ...],
    ///   "golden_seed_vector": [...]
    /// }
    /// ```
    #[must_use]
    #[allow(clippy::cast_precision_loss)] // JSON export only, not used in computation
    #[allow(clippy::format_push_string)] // String building for export
    #[allow(clippy::large_stack_arrays)] // Format strings for JSON export
    pub fn export_with_e8_context(&self) -> String {
        let mut json = String::from("{\n  \"e8_total_roots\": 240,\n");
        json.push_str("  \"atlas_vertices\": 96,\n");
        json.push_str("  \"coverage\": 0.4,\n");

        // Export all 240 E₈ roots
        json.push_str("  \"e8_roots\": [\n");
        for i in 0..240 {
            let root = self.e8.get_root(i);
            let coords = root.coords();

            json.push_str("    {");
            json.push_str(&format!("\"id\": {i}, "));
            json.push_str("\"coords\": [");
            for (j, coord) in coords.iter().enumerate() {
                let val = coord.to_rational().to_f64().unwrap_or(0.0);
                json.push_str(&format!("{val}"));
                if j < 7 {
                    json.push_str(", ");
                }
            }
            json.push_str("]}");

            if i < 239 {
                json.push_str(",\n");
            } else {
                json.push('\n');
            }
        }
        json.push_str("  ],\n");

        // Export Atlas embedding (Golden Seed Vector)
        json.push_str("  \"golden_seed_vector\": [\n");
        for atlas_id in 0..96 {
            let root = &self.embedding[atlas_id];
            let coords = root.coords();
            let degree = self.atlas.degree(atlas_id);
            let mirror = self.atlas.mirror_pair(atlas_id);

            json.push_str("    {");
            json.push_str(&format!("\"atlas_id\": {atlas_id}, "));
            json.push_str(&format!("\"degree\": {degree}, "));
            json.push_str(&format!("\"mirror_pair\": {mirror}, "));
            json.push_str("\"coords\": [");
            for (j, coord) in coords.iter().enumerate() {
                let val = coord.to_rational().to_f64().unwrap_or(0.0);
                json.push_str(&format!("{val}"));
                if j < 7 {
                    json.push_str(", ");
                }
            }
            json.push_str("]}");

            if atlas_id < 95 {
                json.push_str(",\n");
            } else {
                json.push('\n');
            }
        }
        json.push_str("  ]\n");
        json.push_str("}\n");

        json
    }

    /// Export adjacency preservation data
    ///
    /// Shows which Atlas adjacencies are preserved in the E₈ embedding.
    ///
    /// # Format
    ///
    /// ```csv
    /// atlas_v1,atlas_v2,inner_product,preserved
    /// 0,1,-1,true
    /// ```
    #[must_use]
    #[allow(clippy::cast_precision_loss)] // CSV export only, not used in computation
    #[allow(clippy::format_push_string)] // String building for export
    #[allow(clippy::large_stack_arrays)] // Format strings for CSV export
    pub fn export_adjacency_preservation(&self) -> String {
        let mut csv = String::from("atlas_v1,atlas_v2,inner_product,preserved\n");

        // Check all adjacencies in Atlas
        for v1 in 0..self.atlas.num_vertices() {
            for v2 in self.atlas.neighbors(v1) {
                // Only count each edge once (undirected graph)
                if v1 < *v2 {
                    // Get the corresponding E₈ roots
                    let root1 = &self.embedding[v1];
                    let root2 = &self.embedding[*v2];

                    // Compute inner product
                    let inner_prod = root1.inner_product(root2);
                    let inner_prod_f64 = inner_prod.to_f64().unwrap_or(0.0);

                    // Check if adjacency is preserved (inner product should be -1)
                    let expected = crate::arithmetic::Rational::from_integer(-1);
                    let preserved = inner_prod == expected;

                    csv.push_str(&format!("{v1},{v2},{inner_prod_f64},{preserved}\n"));
                }
            }
        }

        csv
    }

    /// Generate summary statistics
    ///
    /// Returns key metrics about the Golden Seed Vector:
    /// - Number of Atlas vertices: 96
    /// - Number of E₈ roots: 240
    /// - Coverage: 96/240 = 40%
    /// - Adjacencies preserved: count/total
    #[must_use]
    #[allow(clippy::cast_precision_loss)] // Statistics display only
    #[allow(clippy::float_arithmetic)] // Coverage ratio calculation for display
    pub fn summary_statistics(&self) -> GoldenSeedStatistics {
        let mut preserved_count = 0;
        let mut total_edges = 0;

        // Count adjacency preservation
        for v1 in 0..self.atlas.num_vertices() {
            for v2 in self.atlas.neighbors(v1) {
                // Only count each edge once
                if v1 < *v2 {
                    total_edges += 1;

                    let root1 = &self.embedding[v1];
                    let root2 = &self.embedding[*v2];
                    let inner_prod = root1.inner_product(root2);
                    let expected = crate::arithmetic::Rational::from_integer(-1);

                    if inner_prod == expected {
                        preserved_count += 1;
                    }
                }
            }
        }

        GoldenSeedStatistics {
            atlas_vertices: 96,
            e8_roots: 240,
            coverage_ratio: 96.0 / 240.0,
            adjacencies_preserved: preserved_count,
            adjacencies_total: total_edges,
        }
    }
}

/// Statistics about the Golden Seed Vector embedding
#[derive(Debug, Clone, Copy)]
pub struct GoldenSeedStatistics {
    /// Number of Atlas vertices (always 96)
    pub atlas_vertices: usize,
    /// Number of E₈ roots (always 240)
    pub e8_roots: usize,
    /// Coverage ratio (96/240 = 0.4)
    pub coverage_ratio: f64,
    /// Number of Atlas adjacencies preserved in E₈
    pub adjacencies_preserved: usize,
    /// Total number of Atlas adjacencies
    pub adjacencies_total: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::embedding::compute_atlas_embedding;
    use crate::{e8::E8RootSystem, Atlas};

    #[test]
    fn test_golden_seed_visualizer() {
        let atlas = Atlas::new();
        let e8 = E8RootSystem::new();
        let embedding = compute_atlas_embedding(&atlas);
        let vis = GoldenSeedVisualizer::new(&atlas, &e8, &embedding);

        let stats = vis.summary_statistics();
        assert_eq!(stats.atlas_vertices, 96);
        assert_eq!(stats.e8_roots, 240);
    }

    #[test]
    fn test_export_formats() {
        let atlas = Atlas::new();
        let e8 = E8RootSystem::new();
        let embedding = compute_atlas_embedding(&atlas);
        let vis = GoldenSeedVisualizer::new(&atlas, &e8, &embedding);

        let csv = vis.export_coordinates_csv();
        assert!(csv.contains("atlas_id"));

        let json = vis.export_with_e8_context();
        assert!(json.contains("golden_seed_vector"));
    }
}
