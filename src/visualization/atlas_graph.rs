//! Atlas Graph Visualization
//!
//! This module provides visualization capabilities for the 96-vertex Atlas graph,
//! including degree distribution, mirror symmetry, and adjacency structure.
//!
//! # Overview
//!
//! The Atlas graph is the foundational structure from which all exceptional groups emerge.
//! Visualizing it helps understand:
//! - Bimodal degree distribution (64 vertices of degree-5, 32 of degree-6)
//! - Mirror symmetry τ (involution pairing vertices)
//! - Hamming-1 adjacency structure
//! - 6-tuple coordinate labeling
//!
//! # Export Formats
//!
//! - **`GraphML`**: For graph analysis tools (Gephi, Cytoscape, `NetworkX`)
//! - **JSON**: For web-based visualizations (D3.js, vis.js)
//! - **DOT**: For Graphviz rendering
//! - **CSV**: Edge list and node attributes
//!
//! # Examples
//!
//! ```rust
//! use atlas_embeddings::Atlas;
//! use atlas_embeddings::visualization::atlas_graph::AtlasGraphVisualizer;
//!
//! let atlas = Atlas::new();
//! let vis = AtlasGraphVisualizer::new(&atlas);
//!
//! // Basic graph statistics
//! assert_eq!(vis.vertex_count(), 96);
//! assert_eq!(vis.edge_count(), 256);  // Total adjacencies / 2
//!
//! // Degree distribution
//! let deg_dist = vis.degree_distribution();
//! assert_eq!(deg_dist.get(&5).unwrap(), &64);
//! assert_eq!(deg_dist.get(&6).unwrap(), &32);
//! ```

use crate::Atlas;
use std::collections::HashMap;

/// Visualizer for the Atlas graph
///
/// Provides methods to generate visualizations and export the 96-vertex Atlas graph
/// in various formats for analysis and presentation.
#[derive(Debug)]
pub struct AtlasGraphVisualizer<'a> {
    atlas: &'a Atlas,
}

impl<'a> AtlasGraphVisualizer<'a> {
    /// Create a new Atlas graph visualizer
    ///
    /// # Examples
    ///
    /// ```rust
    /// use atlas_embeddings::Atlas;
    /// use atlas_embeddings::visualization::atlas_graph::AtlasGraphVisualizer;
    ///
    /// let atlas = Atlas::new();
    /// let vis = AtlasGraphVisualizer::new(&atlas);
    /// ```
    #[must_use]
    pub const fn new(atlas: &'a Atlas) -> Self {
        Self { atlas }
    }

    /// Get the number of vertices (always 96 for Atlas)
    #[must_use]
    pub const fn vertex_count(&self) -> usize {
        self.atlas.num_vertices()
    }

    /// Get the number of edges in the graph
    ///
    /// This counts undirected edges (each adjacency counted once).
    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.atlas.num_edges()
    }

    /// Compute degree distribution
    ///
    /// Returns a map from degree → count of vertices with that degree.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use atlas_embeddings::Atlas;
    /// use atlas_embeddings::visualization::atlas_graph::AtlasGraphVisualizer;
    ///
    /// let atlas = Atlas::new();
    /// let vis = AtlasGraphVisualizer::new(&atlas);
    /// let dist = vis.degree_distribution();
    ///
    /// assert_eq!(dist.get(&5), Some(&64));  // 64 vertices of degree 5
    /// assert_eq!(dist.get(&6), Some(&32));  // 32 vertices of degree 6
    /// ```
    #[must_use]
    pub fn degree_distribution(&self) -> HashMap<usize, usize> {
        let mut distribution = HashMap::new();
        for v in 0..self.vertex_count() {
            let degree = self.atlas.degree(v);
            *distribution.entry(degree).or_insert(0) += 1;
        }
        distribution
    }

    /// Export graph to `GraphML` format
    ///
    /// `GraphML` is an XML-based format supported by many graph analysis tools.
    ///
    /// # Format
    ///
    /// - Node attributes: `id`, `label`, `degree`, `mirror_pair`
    /// - Edge attributes: `source`, `target`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use atlas_embeddings::Atlas;
    /// use atlas_embeddings::visualization::atlas_graph::AtlasGraphVisualizer;
    ///
    /// let atlas = Atlas::new();
    /// let vis = AtlasGraphVisualizer::new(&atlas);
    /// let graphml = vis.to_graphml();
    ///
    /// assert!(graphml.contains("<?xml"));
    /// assert!(graphml.contains("<graph"));
    /// ```
    #[must_use]
    #[allow(clippy::format_push_string)] // String building for export is clearer with format!
    #[allow(clippy::set_contains_or_insert)] // Edge deduplication logic is clearer with contains+insert
    pub fn to_graphml(&self) -> String {
        let mut graphml = String::from("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n");
        graphml.push_str("<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\"\n");
        graphml.push_str("         xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"\n");
        graphml.push_str("         xsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns\n");
        graphml.push_str("         http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd\">\n\n");

        // Define node attributes
        graphml.push_str("  <!-- Node attributes -->\n");
        graphml
            .push_str("  <key id=\"d0\" for=\"node\" attr.name=\"degree\" attr.type=\"int\"/>\n");
        graphml.push_str(
            "  <key id=\"d1\" for=\"node\" attr.name=\"mirror_pair\" attr.type=\"int\"/>\n",
        );
        graphml
            .push_str("  <key id=\"d2\" for=\"node\" attr.name=\"label_e1\" attr.type=\"int\"/>\n");
        graphml
            .push_str("  <key id=\"d3\" for=\"node\" attr.name=\"label_e2\" attr.type=\"int\"/>\n");
        graphml
            .push_str("  <key id=\"d4\" for=\"node\" attr.name=\"label_e3\" attr.type=\"int\"/>\n");
        graphml.push_str(
            "  <key id=\"d5\" for=\"node\" attr.name=\"label_d45\" attr.type=\"int\"/>\n",
        );
        graphml
            .push_str("  <key id=\"d6\" for=\"node\" attr.name=\"label_e6\" attr.type=\"int\"/>\n");
        graphml.push_str(
            "  <key id=\"d7\" for=\"node\" attr.name=\"label_e7\" attr.type=\"int\"/>\n\n",
        );

        graphml.push_str("  <graph id=\"Atlas\" edgedefault=\"undirected\">\n");

        // Add nodes
        graphml.push_str("    <!-- Nodes -->\n");
        for v in 0..self.vertex_count() {
            let label = self.atlas.label(v);
            let degree = self.atlas.degree(v);
            let mirror = self.atlas.mirror_pair(v);

            graphml.push_str(&format!("    <node id=\"n{v}\">\n"));
            graphml.push_str(&format!("      <data key=\"d0\">{degree}</data>\n"));
            graphml.push_str(&format!("      <data key=\"d1\">{mirror}</data>\n"));
            graphml.push_str(&format!("      <data key=\"d2\">{}</data>\n", label.e1));
            graphml.push_str(&format!("      <data key=\"d3\">{}</data>\n", label.e2));
            graphml.push_str(&format!("      <data key=\"d4\">{}</data>\n", label.e3));
            graphml.push_str(&format!("      <data key=\"d5\">{}</data>\n", label.d45));
            graphml.push_str(&format!("      <data key=\"d6\">{}</data>\n", label.e6));
            graphml.push_str(&format!("      <data key=\"d7\">{}</data>\n", label.e7));
            graphml.push_str("    </node>\n");
        }

        // Add edges
        graphml.push_str("\n    <!-- Edges -->\n");
        let mut seen_edges = std::collections::HashSet::new();
        let mut edge_id = 0;

        for v in 0..self.vertex_count() {
            for neighbor in self.atlas.neighbors(v) {
                let edge = if v < *neighbor {
                    (v, *neighbor)
                } else {
                    (*neighbor, v)
                };
                if !seen_edges.contains(&edge) {
                    graphml.push_str(&format!(
                        "    <edge id=\"e{edge_id}\" source=\"n{v}\" target=\"n{neighbor}\"/>\n"
                    ));
                    seen_edges.insert(edge);
                    edge_id += 1;
                }
            }
        }

        graphml.push_str("  </graph>\n");
        graphml.push_str("</graphml>\n");

        graphml
    }

    /// Export graph to JSON format
    ///
    /// JSON format suitable for web-based visualizations (D3.js, vis.js, etc.)
    ///
    /// # Schema
    ///
    /// ```json
    /// {
    ///   "vertices": [{"id": 0, "label": [0,0,0,0,0,0], "degree": 5}],
    ///   "edges": [{"source": 0, "target": 1}],
    ///   "metadata": {"vertex_count": 96, "edge_count": 256}
    /// }
    /// ```
    #[must_use]
    #[allow(clippy::format_push_string)] // String building for export is clearer with format!
    #[allow(clippy::set_contains_or_insert)] // Edge deduplication logic is clearer with contains+insert
    #[allow(clippy::large_stack_arrays)] // Format strings for JSON export
    pub fn to_json(&self) -> String {
        let mut json = String::from("{\n  \"vertices\": [\n");

        // Add vertices
        for v in 0..self.vertex_count() {
            let label = self.atlas.label(v);
            let degree = self.atlas.degree(v);
            let mirror = self.atlas.mirror_pair(v);

            json.push_str(&format!(
                "    {{\"id\": {v}, \"degree\": {degree}, \"mirror_pair\": {mirror}, \"label\": [{}, {}, {}, {}, {}, {}]}}",
                label.e1, label.e2, label.e3, label.d45, label.e6, label.e7
            ));

            if v < self.vertex_count() - 1 {
                json.push_str(",\n");
            }
        }

        json.push_str("\n  ],\n  \"edges\": [\n");

        // Add edges
        let mut seen_edges = std::collections::HashSet::new();
        let mut first_edge = true;

        for v in 0..self.vertex_count() {
            for neighbor in self.atlas.neighbors(v) {
                let edge = if v < *neighbor {
                    (v, *neighbor)
                } else {
                    (*neighbor, v)
                };
                if !seen_edges.contains(&edge) {
                    if !first_edge {
                        json.push_str(",\n");
                    }
                    json.push_str(&format!("    {{\"source\": {v}, \"target\": {neighbor}}}"));
                    seen_edges.insert(edge);
                    first_edge = false;
                }
            }
        }

        json.push_str("\n  ],\n  \"metadata\": {\n");
        let vertex_count = self.vertex_count();
        let edge_count = self.edge_count();
        json.push_str(&format!("    \"vertex_count\": {vertex_count},\n"));
        json.push_str(&format!("    \"edge_count\": {edge_count}\n"));
        json.push_str("  }\n}\n");

        json
    }

    /// Export graph to DOT format (Graphviz)
    ///
    /// DOT format for rendering with Graphviz tools (dot, neato, fdp, etc.)
    #[must_use]
    #[allow(clippy::format_push_string)] // String building for export is clearer with format!
    #[allow(clippy::set_contains_or_insert)] // Edge deduplication logic is clearer with contains+insert
    #[allow(clippy::large_stack_arrays)] // Format strings for DOT export
    pub fn to_dot(&self) -> String {
        let mut dot = String::from("graph Atlas {\n");
        dot.push_str("  // Graph attributes\n");
        dot.push_str("  graph [layout=neato, overlap=false];\n");
        dot.push_str("  node [shape=circle, style=filled];\n\n");

        // Add nodes with attributes
        dot.push_str("  // Nodes\n");
        for v in 0..self.vertex_count() {
            let degree = self.atlas.degree(v);
            let color = if degree == 5 {
                "lightblue"
            } else {
                "lightgreen"
            };

            dot.push_str(&format!(
                "  {v} [label=\"{v}\", fillcolor={color}, tooltip=\"degree: {degree}\"];\n"
            ));
        }

        // Add edges
        dot.push_str("\n  // Edges\n");
        let mut seen_edges = std::collections::HashSet::new();

        for v in 0..self.vertex_count() {
            for neighbor in self.atlas.neighbors(v) {
                let edge = if v < *neighbor {
                    (v, *neighbor)
                } else {
                    (*neighbor, v)
                };
                if !seen_edges.contains(&edge) {
                    dot.push_str(&format!("  {v} -- {neighbor};\n"));
                    seen_edges.insert(edge);
                }
            }
        }

        dot.push_str("}\n");
        dot
    }

    /// Export edge list as CSV
    ///
    /// Simple CSV format: source,target
    #[must_use]
    #[allow(clippy::format_push_string)] // String building for export is clearer with format!
    #[allow(clippy::set_contains_or_insert)] // Edge deduplication logic is clearer with contains+insert
    pub fn to_csv_edges(&self) -> String {
        let mut csv = String::from("source,target\n");

        // Track edges we've already added (since graph is undirected)
        let mut seen_edges = std::collections::HashSet::new();

        for v in 0..self.vertex_count() {
            for neighbor in self.atlas.neighbors(v) {
                let edge = if v < *neighbor {
                    (v, *neighbor)
                } else {
                    (*neighbor, v)
                };
                if !seen_edges.contains(&edge) {
                    csv.push_str(&format!("{v},{neighbor}\n"));
                    seen_edges.insert(edge);
                }
            }
        }

        csv
    }

    /// Export node attributes as CSV
    ///
    /// CSV format: `id,degree,label_e1,label_e2,label_e3,label_d45,label_e6,label_e7`
    #[must_use]
    #[allow(clippy::format_push_string)] // String building for export is clearer with format!
    #[allow(clippy::large_stack_arrays)] // Format strings for CSV export
    pub fn to_csv_nodes(&self) -> String {
        let mut csv = String::from(
            "id,degree,label_e1,label_e2,label_e3,label_d45,label_e6,label_e7,mirror_pair\n",
        );

        for v in 0..self.vertex_count() {
            let label = self.atlas.label(v);
            let degree = self.atlas.degree(v);
            let mirror = self.atlas.mirror_pair(v);

            csv.push_str(&format!(
                "{v},{degree},{},{},{},{},{},{},{mirror}\n",
                label.e1, label.e2, label.e3, label.d45, label.e6, label.e7
            ));
        }

        csv
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Atlas;

    #[test]
    fn test_visualizer_creation() {
        let atlas = Atlas::new();
        let vis = AtlasGraphVisualizer::new(&atlas);
        assert_eq!(vis.vertex_count(), 96);
    }

    #[test]
    fn test_edge_count() {
        let atlas = Atlas::new();
        let vis = AtlasGraphVisualizer::new(&atlas);
        let edge_count = vis.edge_count();
        assert!(edge_count > 0);
    }

    #[test]
    fn test_degree_distribution() {
        let atlas = Atlas::new();
        let vis = AtlasGraphVisualizer::new(&atlas);
        let dist = vis.degree_distribution();

        // Atlas has bimodal degree distribution: 64 degree-5, 32 degree-6
        assert_eq!(dist.get(&5), Some(&64));
        assert_eq!(dist.get(&6), Some(&32));
        assert_eq!(dist.len(), 2); // Only two degree values
    }

    #[test]
    fn test_graphml_export_structure() {
        let atlas = Atlas::new();
        let vis = AtlasGraphVisualizer::new(&atlas);
        let graphml = vis.to_graphml();

        assert!(graphml.contains("<?xml"));
        assert!(graphml.contains("graphml"));
    }

    #[test]
    fn test_json_export_structure() {
        let atlas = Atlas::new();
        let vis = AtlasGraphVisualizer::new(&atlas);
        let json = vis.to_json();

        assert!(json.contains("vertices"));
        assert!(json.contains("edges"));
    }
}
