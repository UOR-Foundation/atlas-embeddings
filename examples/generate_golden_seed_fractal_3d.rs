//! Generate Golden Seed Fractal 3D
//!
//! This example generates the Golden Seed Fractal in 3D: a self-similar 3D visualization
//! of the Atlas structure with 96-fold branching at each iteration.
//!
//! # Usage
//!
//! ```bash
//! cargo run --example generate_golden_seed_fractal_3d
//! ```
//!
//! This will generate:
//! - `golden_seed_fractal_3d_depth0.csv` - Base Atlas pattern (96 points)
//! - `golden_seed_fractal_3d_depth1.csv` - One iteration (9,312 points) - RECOMMENDED
//! - `golden_seed_fractal_3d_depth0.json` - JSON format for depth 0
//! - `golden_seed_fractal_3d_depth1.json` - JSON format for depth 1
//!
//! # Mathematical Properties
//!
//! - **96-fold self-similarity**: Each point branches into 96 sub-points
//! - **8 sign classes**: Color-coded with distinct hues (8-fold rotational symmetry)
//! - **Fractal dimension**: D ≈ 4.15 (computed as log₃(96))
//! - **Scaling factor**: 1/3 (matches ternary coordinate d₄₅)
//! - **3D spherical projection**: Emphasizes spatial structure of the Atlas
#[cfg(feature = "visualization")]
fn main() {
    use atlas_embeddings::visualization::fractal::GoldenSeedFractal3D;
    use atlas_embeddings::Atlas;

    println!("Generating Golden Seed Fractal (3D)...\n");
    println!("This fractal exhibits 96-fold self-similarity at each iteration,");
    println!("reflecting the complete structure of the Atlas of Resonance Classes.");
    println!("The 3D projection uses spherical coordinates to reveal spatial structure.");
    println!();

    let atlas = Atlas::new();
    let fractal = GoldenSeedFractal3D::new(&atlas);

    // Generate fractals at different depths
    let depths = vec![
        (0, "Base Atlas pattern (96 vertices)"),
        (1, "One iteration (recommended)"),
        // Depth 2 disabled by default - generates 893,088 points!
        // (2, "Two iterations (warning: large file)"),
    ];

    for (depth, description) in depths {
        println!("Depth {depth}: {description}");

        // Get statistics
        let (point_count, dimension) = fractal.statistics(depth);
        println!("  Points: {}", format_number(point_count));
        println!("  Fractal dimension: {dimension:.3}");

        // Generate CSV
        let csv = fractal.to_csv(depth);
        let filename = format!("golden_seed_fractal_3d_depth{depth}.csv");

        if let Err(e) = std::fs::write(&filename, &csv) {
            eprintln!("  Error: Could not write {filename}: {e}");
        } else {
            println!("  ✓ Written {filename}");
            println!("  Size: {} bytes", format_number(csv.len()));
        }

        // Generate JSON
        let json = fractal.to_json(depth);
        let filename = format!("golden_seed_fractal_3d_depth{depth}.json");

        if let Err(e) = std::fs::write(&filename, &json) {
            eprintln!("  Error: Could not write {filename}: {e}");
        } else {
            println!("  ✓ Written {filename}");
            println!("  Size: {} bytes", format_number(json.len()));
        }
        println!();
    }

    println!("✓ Golden Seed Fractal 3D generation complete!");
    println!();
    println!("Recommended for 3D visualization:");
    println!("  → golden_seed_fractal_3d_depth1.csv");
    println!("  → golden_seed_fractal_3d_depth1.json");
    println!();
    println!("Properties:");
    println!("  - 8 colors represent the 8 sign classes of the Atlas");
    println!("  - Spherical arrangement shows 8-fold octant symmetry");
    println!("  - Each point branches into 96 sub-points (96-fold self-similarity)");
    println!("  - Scaling factor 1/3 matches the ternary coordinate d₄₅");
    println!("  - Fractal dimension D = log₃(96) ≈ 4.15");
    println!();
    println!("Visualization tips:");
    println!("  - Use 3D visualization tools like ParaView, Blender, or matplotlib");
    println!("  - Color points by sign_class for octant symmetry");
    println!("  - Adjust point size by depth for hierarchical structure");
    println!("  - The CSV format is compatible with most 3D plotting libraries");
    println!();
    println!("Mathematical significance:");
    println!("  This 3D fractal reveals the spatial structure of the Atlas that is");
    println!("  hidden in 2D projections. The fractal encodes the complete exceptional");
    println!("  group hierarchy: G₂ → F₄ → E₆ → E₇ → E₈");
}

#[cfg(not(feature = "visualization"))]
fn main() {
    eprintln!("Error: This example requires the 'visualization' feature.");
    eprintln!("Run with: cargo run --example generate_golden_seed_fractal_3d");
    std::process::exit(1);
}

/// Format a number with thousand separators
fn format_number(n: usize) -> String {
    let s = n.to_string();
    let mut result = String::new();
    for (i, ch) in s.chars().rev().enumerate() {
        if i > 0 && i % 3 == 0 {
            result.insert(0, ',');
        }
        result.insert(0, ch);
    }
    result
}
