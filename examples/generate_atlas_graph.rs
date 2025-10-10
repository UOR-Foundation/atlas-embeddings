//! Generate Atlas Graph Visualizations
//!
//! This example demonstrates how to create visualizations of the 96-vertex Atlas graph
//! and export them in various formats.
//!
//! # Usage
//!
//! ```bash
//! cargo run --example generate_atlas_graph --features visualization
//! ```
//!
//! This will generate:
//! - `atlas_graph.graphml` - For Gephi, Cytoscape, `NetworkX`
//! - `atlas_graph.json` - For D3.js and web visualizations
//! - `atlas_graph.dot` - For Graphviz rendering
//! - `atlas_edges.csv` and `atlas_nodes.csv` - For data analysis

#[cfg(feature = "visualization")]
fn main() {
    use atlas_embeddings::visualization::atlas_graph::AtlasGraphVisualizer;
    use atlas_embeddings::Atlas;

    println!("Generating Atlas graph visualizations...\n");

    let atlas = Atlas::new();
    let visualizer = AtlasGraphVisualizer::new(&atlas);

    println!("Atlas Properties:");
    println!("  Vertices: {}", visualizer.vertex_count());
    println!("  Edges: {}", visualizer.edge_count());

    // Degree distribution
    let dist = visualizer.degree_distribution();
    println!("\nDegree Distribution:");
    for (degree, count) in &dist {
        println!("  Degree {degree}: {count} vertices");
    }

    // Generate GraphML
    println!("\nGenerating GraphML...");
    let graphml = visualizer.to_graphml();
    if let Err(e) = std::fs::write("atlas_graph.graphml", &graphml) {
        eprintln!("Warning: Could not write GraphML file: {e}");
    } else {
        let size = graphml.len();
        println!("  ✓ atlas_graph.graphml ({size} bytes)");
    }

    // Generate JSON
    println!("Generating JSON...");
    let json = visualizer.to_json();
    if let Err(e) = std::fs::write("atlas_graph.json", &json) {
        eprintln!("Warning: Could not write JSON file: {e}");
    } else {
        let size = json.len();
        println!("  ✓ atlas_graph.json ({size} bytes)");
    }

    // Generate DOT
    println!("Generating DOT (Graphviz)...");
    let dot = visualizer.to_dot();
    if let Err(e) = std::fs::write("atlas_graph.dot", &dot) {
        eprintln!("Warning: Could not write DOT file: {e}");
    } else {
        let size = dot.len();
        println!("  ✓ atlas_graph.dot ({size} bytes)");
    }

    // Generate CSV files
    println!("Generating CSV files...");
    let csv_edges = visualizer.to_csv_edges();
    if let Err(e) = std::fs::write("atlas_edges.csv", &csv_edges) {
        eprintln!("Warning: Could not write edges CSV: {e}");
    } else {
        let size = csv_edges.len();
        println!("  ✓ atlas_edges.csv ({size} bytes)");
    }

    let csv_nodes = visualizer.to_csv_nodes();
    if let Err(e) = std::fs::write("atlas_nodes.csv", &csv_nodes) {
        eprintln!("Warning: Could not write nodes CSV: {e}");
    } else {
        let size = csv_nodes.len();
        println!("  ✓ atlas_nodes.csv ({size} bytes)");
    }

    println!("\n✓ Atlas graph visualization complete!");
    println!("\nNext steps:");
    println!("  - Open atlas_graph.graphml in Gephi or Cytoscape");
    println!("  - Use atlas_graph.json with D3.js for web visualization");
    println!("  - Render atlas_graph.dot with: dot -Tpng atlas_graph.dot -o atlas_graph.png");
}

#[cfg(not(feature = "visualization"))]
fn main() {
    eprintln!("Error: This example requires the 'visualization' feature.");
    eprintln!("Run with: cargo run --example generate_atlas_graph --features visualization");
    std::process::exit(1);
}
