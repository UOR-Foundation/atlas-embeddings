//! Generate Golden Seed Fractal at Depth 2
//!
//! WARNING: This generates 893,088 points and creates a very large SVG file (~120 MB)

#[cfg(feature = "visualization")]
fn main() {
    use atlas_embeddings::Atlas;
    use atlas_embeddings::visualization::fractal::GoldenSeedFractal;

    println!("Generating Golden Seed Fractal at Depth 2...");
    println!("⚠️  WARNING: This will generate 893,088 points!");
    println!();

    let atlas = Atlas::new();
    let fractal = GoldenSeedFractal::new(&atlas);

    // Generate depth 2
    let depth = 2;
    let (point_count, dimension) = fractal.statistics(depth);

    println!("Depth {depth}: Two iterations");
    println!("  Points: {}", format_number(point_count));
    println!("  Fractal dimension: {dimension:.3}");
    println!();
    println!("⏳ Generating SVG (this may take 30-60 seconds)...");

    let start = std::time::Instant::now();
    let svg = fractal.to_svg(depth, 1200, 1200);
    let elapsed = start.elapsed();

    let filename = "golden_seed_fractal_depth2.svg";

    match std::fs::write(filename, &svg) {
        Ok(_) => {
            println!("  ✓ Written {filename}");
            println!("  Size: {} bytes ({:.1} MB)", format_number(svg.len()), svg.len() as f64 / 1_048_576.0);
            println!("  Generation time: {:.2}s", elapsed.as_secs_f64());
        }
        Err(e) => {
            eprintln!("  ❌ Error: Could not write {filename}: {e}");
        }
    }

    println!();
    println!("✓ Depth 2 fractal generated!");
    println!();
    println!("⚠️  File size warning:");
    println!("  - This file is ~120 MB and contains 893,088 points");
    println!("  - Most browsers will struggle to render it");
    println!("  - Consider using depth 1 for visualization (1.2 MB, 9,312 points)");
    println!();
    println!("Mathematical properties:");
    println!("  - Each of the 9,312 depth-1 points branches into 96 sub-points");
    println!("  - Shows 3 levels of self-similar structure");
    println!("  - Demonstrates the full fractal nature of the Atlas");
}

#[cfg(not(feature = "visualization"))]
fn main() {
    eprintln!("Error: This example requires the 'visualization' feature.");
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
