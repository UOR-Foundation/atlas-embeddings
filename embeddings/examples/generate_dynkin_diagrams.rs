//! Generate Dynkin Diagrams for Exceptional Groups
//!
//! This example generates SVG representations of Dynkin diagrams for all five
//! exceptional Lie groups: G₂, F₄, E₆, E₇, E₈.
//!
//! # Usage
//!
//! ```bash
//! cargo run --example generate_dynkin_diagrams --features visualization
//! ```
//!
//! This will generate SVG files for each group's Dynkin diagram.

#[cfg(feature = "visualization")]
fn main() {
    use atlas_embeddings::visualization::dynkin::DynkinVisualizer;

    println!("Generating Dynkin diagrams for exceptional groups...\n");

    let diagrams = DynkinVisualizer::generate_all_exceptional();

    for (name, svg) in diagrams {
        let filename = format!("{}_dynkin.svg", name.to_lowercase());

        println!("Generating {name}:");
        println!("  File: {filename}");
        let size = svg.len();
        println!("  Size: {size} bytes");

        if let Err(e) = std::fs::write(&filename, &svg) {
            eprintln!("  Warning: Could not write file: {e}");
        } else {
            println!("  ✓ Written successfully");
        }
        println!();
    }

    println!("✓ All Dynkin diagrams generated!");
    println!("\nGenerated files:");
    println!("  - g2_dynkin.svg (rank 2, triple bond)");
    println!("  - f4_dynkin.svg (rank 4, double bond)");
    println!("  - e6_dynkin.svg (rank 6, simply-laced)");
    println!("  - e7_dynkin.svg (rank 7, simply-laced)");
    println!("  - e8_dynkin.svg (rank 8, simply-laced)");
}

#[cfg(not(feature = "visualization"))]
fn main() {
    eprintln!("Error: This example requires the 'visualization' feature.");
    eprintln!("Run with: cargo run --example generate_dynkin_diagrams --features visualization");
    std::process::exit(1);
}
