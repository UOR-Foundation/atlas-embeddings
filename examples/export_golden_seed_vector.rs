//! Export the Golden Seed Vector
//!
//! This example exports the Golden Seed Vector - the embedding of the 96-vertex Atlas
//! into the 240-root E₈ system. This is the central output of the atlas-embeddings model.
//!
//! # Usage
//!
//! ```bash
//! cargo run --example export_golden_seed_vector --features visualization
//! ```
//!
//! This will generate:
//! - `golden_seed_vector.csv` - Coordinates of the 96 Atlas vertices in E₈
//! - `golden_seed_context.json` - Full E₈ context showing Atlas subset
//! - `adjacency_preservation.csv` - Verification of adjacency preservation

#[cfg(feature = "visualization")]
#[allow(clippy::float_arithmetic)] // Display only, not used in computation
fn main() {
    use atlas_embeddings::embedding::compute_atlas_embedding;
    use atlas_embeddings::visualization::embedding::GoldenSeedVisualizer;
    use atlas_embeddings::{e8::E8RootSystem, Atlas};

    println!("Exporting the Golden Seed Vector...\n");

    // Construct the Atlas and E₈
    println!("Constructing Atlas graph (96 vertices)...");
    let atlas = Atlas::new();

    println!("Constructing E₈ root system (240 roots)...");
    let e8 = E8RootSystem::new();

    println!("Computing Atlas → E₈ embedding...");
    let embedding = compute_atlas_embedding(&atlas);

    println!("Creating visualizer...");
    let visualizer = GoldenSeedVisualizer::new(&atlas, &e8, &embedding);

    // Display statistics
    let stats = visualizer.summary_statistics();
    println!("\nGolden Seed Vector Statistics:");
    println!("  Atlas vertices: {}", stats.atlas_vertices);
    println!("  E₈ roots: {}", stats.e8_roots);
    println!("  Coverage: {:.1}%", stats.coverage_ratio * 100.0);
    println!("  Adjacencies: {}/{}", stats.adjacencies_preserved, stats.adjacencies_total);

    // Export coordinates
    println!("\nExporting Golden Seed Vector coordinates...");
    let csv = visualizer.export_coordinates_csv();
    if let Err(e) = std::fs::write("golden_seed_vector.csv", &csv) {
        eprintln!("Warning: Could not write CSV file: {e}");
    } else {
        let size = csv.len();
        println!("  ✓ golden_seed_vector.csv ({size} bytes)");
    }

    // Export with E₈ context
    println!("Exporting with full E₈ context...");
    let json = visualizer.export_with_e8_context();
    if let Err(e) = std::fs::write("golden_seed_context.json", &json) {
        eprintln!("Warning: Could not write JSON file: {e}");
    } else {
        let size = json.len();
        println!("  ✓ golden_seed_context.json ({size} bytes)");
    }

    // Export adjacency preservation data
    println!("Exporting adjacency preservation data...");
    let adj_csv = visualizer.export_adjacency_preservation();
    if let Err(e) = std::fs::write("adjacency_preservation.csv", &adj_csv) {
        eprintln!("Warning: Could not write adjacency CSV: {e}");
    } else {
        let size = adj_csv.len();
        println!("  ✓ adjacency_preservation.csv ({size} bytes)");
    }

    println!("\n✓ Golden Seed Vector export complete!");
    println!("\nThe Golden Seed Vector represents:");
    println!("  - The universal mathematical language encoded in Atlas");
    println!("  - The 96-dimensional configuration in E₈ space");
    println!("  - The foundation for all five exceptional groups");
    println!("\nNext steps:");
    println!("  - Visualize golden_seed_vector.csv in 3D (Python, Mathematica, etc.)");
    println!("  - Analyze golden_seed_context.json to see Atlas within E₈");
    println!("  - Verify adjacency preservation in adjacency_preservation.csv");
}

#[cfg(not(feature = "visualization"))]
fn main() {
    eprintln!("Error: This example requires the 'visualization' feature.");
    eprintln!("Run with: cargo run --example export_golden_seed_vector --features visualization");
    std::process::exit(1);
}
