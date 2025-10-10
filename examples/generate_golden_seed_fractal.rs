//! Generate Golden Seed Fractal Logo
//!
//! This example generates the Golden Seed Fractal: a self-similar 2D visualization
//! of the Atlas structure with 96-fold branching at each iteration.
//!
//! # Usage
//!
//! ```bash
//! cargo run --example generate_golden_seed_fractal
//! ```
//!
//! This will generate:
//! - `golden_seed_fractal_depth0.svg` - Base Atlas pattern (96 points)
//! - `golden_seed_fractal_depth1.svg` - One iteration (9,312 points) - RECOMMENDED FOR LOGO
//! - `golden_seed_fractal_depth2.svg` - Two iterations (893,088 points) - Very large file
//!
//! # Mathematical Properties
//!
//! - **96-fold self-similarity**: Each point branches into 96 sub-points
//! - **8 sign classes**: Color-coded with distinct hues (8-fold rotational symmetry)
//! - **Fractal dimension**: D ≈ 4.15 (computed as log₃(96))
//! - **Scaling factor**: 1/3 (matches ternary coordinate d₄₅)

#[cfg(feature = "visualization")]
fn main() {
    use atlas_embeddings::visualization::fractal::GoldenSeedFractal;
    use atlas_embeddings::Atlas;

    println!("Generating Golden Seed Fractal...\n");
    println!("This fractal exhibits 96-fold self-similarity at each iteration,");
    println!("reflecting the complete structure of the Atlas of Resonance Classes.");
    println!();

    let atlas = Atlas::new();
    let fractal = GoldenSeedFractal::new(&atlas);

    // Generate fractals at different depths
    let depths = vec![
        (0, "Base Atlas pattern (96 vertices)"),
        (1, "One iteration (recommended for logo)"),
        // Depth 2 disabled by default - generates 893,088 points!
        // (2, "Two iterations (warning: large file)"),
    ];

    for (depth, description) in depths {
        println!("Depth {depth}: {description}");

        // Get statistics
        let (point_count, dimension) = fractal.statistics(depth);
        println!("  Points: {}", format_number(point_count));
        println!("  Fractal dimension: {dimension:.3}");

        // Generate SVG
        let svg = fractal.to_svg(depth, 1200, 1200);
        let filename = format!("golden_seed_fractal_depth{depth}.svg");

        if let Err(e) = std::fs::write(&filename, &svg) {
            eprintln!("  Error: Could not write {filename}: {e}");
        } else {
            println!("  ✓ Written {filename}");
            println!("  Size: {} bytes", format_number(svg.len()));
        }
        println!();
    }

    println!("✓ Golden Seed Fractal generation complete!");
    println!();
    println!("Recommended for logo/README:");
    println!("  → golden_seed_fractal_depth1.svg");
    println!();
    println!("Properties:");
    println!("  - 8 colors represent the 8 sign classes of the Atlas");
    println!("  - Radial arrangement shows 8-fold rotational symmetry");
    println!("  - Each point branches into 96 sub-points (96-fold self-similarity)");
    println!("  - Scaling factor 1/3 matches the ternary coordinate d₄₅");
    println!("  - Fractal dimension D = log₃(96) ≈ 4.15");
    println!();
    println!("Mathematical significance:");
    println!("  This fractal is exclusive to the Atlas - no other known mathematical");
    println!("  structure exhibits 96-fold self-similarity with 8-fold symmetry.");
    println!("  The fractal encodes the complete exceptional group hierarchy:");
    println!("    G₂ → F₄ → E₆ → E₇ → E₈");
}

#[cfg(not(feature = "visualization"))]
fn main() {
    eprintln!("Error: This example requires the 'visualization' feature.");
    eprintln!("Run with: cargo run --example generate_golden_seed_fractal");
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
