//! Script to generate language bindings using UniFFI
//!
//! This script generates Python, TypeScript, and other language bindings
//! from the UDL file.

use camino::Utf8Path;
use uniffi_bindgen::{
    bindings::kotlin::gen_kotlin::KotlinBindingGenerator, bindings::python::gen_python::PythonBindingGenerator,
    generate_bindings,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let udl_file = Utf8Path::new("src/hologram_ffi.udl");

    // Auto-detect library path based on build profile
    let profile = std::env::var("PROFILE").unwrap_or_else(|_| "release".to_string());
    let target = std::env::var("TARGET").unwrap_or_else(|_| "unknown".to_string());

    // Determine library extension based on target
    let lib_ext = if target.contains("darwin") {
        "dylib"
    } else if target.contains("windows") {
        "dll"
    } else {
        "so"
    };

    // Use release library path (for binding generation)
    let library_path_str = format!("target/{}/libhologram_ffi.{}", profile, lib_ext);
    let library_path = Utf8Path::new(&library_path_str);

    println!("Using library path: {}", library_path);

    // Generate Python bindings
    println!("Generating Python bindings...");
    let out_dir = Utf8Path::new("interfaces/python");

    // Check if output directory exists
    if !out_dir.exists() {
        std::fs::create_dir_all(out_dir)?;
    }

    generate_bindings(
        udl_file,
        Some(library_path),
        PythonBindingGenerator,
        Some(out_dir),
        None, // config_file - skip config for now
        None, // cargo_metadata
        true, // asyncio
    )?;

    // Generate Kotlin bindings (for TypeScript/JavaScript)
    println!("Generating Kotlin bindings...");
    generate_bindings(
        udl_file,
        Some(library_path),
        KotlinBindingGenerator,
        Some(Utf8Path::new("interfaces/typescript/")),
        None,
        None,
        true,
    )?;

    println!("Language bindings generated successfully!");
    Ok(())
}
