//! Visualize E₈ Root System Projections
//!
//! This example generates CSV files for various projections of the 240 E₈ roots.
//!
//! # Usage
//!
//! ```bash
//! cargo run --example visualize_e8_projections
//! ```
//!
//! This will generate:
//! - `e8_coxeter_plane.csv` - 2D Coxeter plane projection (30-fold symmetry)
//! - `e8_3d_projection.csv` - 3D coordinate projection
//! - `e8_xy_plane.csv` - Simple XY plane projection

#[cfg(feature = "visualization")]
fn main() {
    use atlas_embeddings::e8::E8RootSystem;
    use atlas_embeddings::visualization::e8_roots::E8Projector;

    println!("Generating E₈ root system projections...\n");

    let e8 = E8RootSystem::new();
    let projector = E8Projector::new(&e8);

    // 1. Coxeter plane projection (2D)
    println!("1. Generating Coxeter plane projection (2D)...");
    let coxeter_2d = projector.project_coxeter_plane();
    let coxeter_csv = projector.export_projection_2d_csv(&coxeter_2d);
    let filename = "e8_coxeter_plane.csv";

    if let Err(e) = std::fs::write(filename, &coxeter_csv) {
        eprintln!("   Warning: Could not write {filename}: {e}");
    } else {
        println!("   ✓ Written {filename}");
        println!("   Size: {} bytes", coxeter_csv.len());
        println!("   Points: {}", coxeter_2d.len());
    }
    println!();

    // 2. 3D projection
    println!("2. Generating 3D coordinate projection...");
    let projection_3d = projector.project_3d_principal();
    let projection_csv = projector.export_projection_csv(&projection_3d);
    let filename = "e8_3d_projection.csv";

    if let Err(e) = std::fs::write(filename, &projection_csv) {
        eprintln!("   Warning: Could not write {filename}: {e}");
    } else {
        println!("   ✓ Written {filename}");
        println!("   Size: {} bytes", projection_csv.len());
        println!("   Points: {}", projection_3d.len());
    }
    println!();

    // 3. XY plane projection (2D)
    println!("3. Generating XY plane projection (2D)...");
    let xy_2d = projector.project_xy_plane();
    let xy_csv = projector.export_projection_2d_csv(&xy_2d);
    let filename = "e8_xy_plane.csv";

    if let Err(e) = std::fs::write(filename, &xy_csv) {
        eprintln!("   Warning: Could not write {filename}: {e}");
    } else {
        println!("   ✓ Written {filename}");
        println!("   Size: {} bytes", xy_csv.len());
        println!("   Points: {}", xy_2d.len());
    }
    println!();

    println!("✓ All E₈ projections generated!");
    println!("\nGenerated files:");
    println!("  - e8_coxeter_plane.csv (2D, 30-fold symmetry)");
    println!("  - e8_3d_projection.csv (3D coordinate projection)");
    println!("  - e8_xy_plane.csv (2D XY plane)");
    println!("\nVisualization notes:");
    println!("  - All 240 E₈ roots are included");
    println!("  - Integer roots (112) and half-integer roots (128) are labeled");
    println!("  - All roots have norm² = 2");
    println!("  - Coxeter plane shows most symmetric 2D view");
}

#[cfg(not(feature = "visualization"))]
fn main() {
    eprintln!("Error: This example requires the 'visualization' feature.");
    eprintln!("Run with: cargo run --example visualize_e8_projections");
    std::process::exit(1);
}
