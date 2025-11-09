use std::env;
use std::path::Path;

fn main() {
    println!("Building UniFFI scaffolding for Hologram FFI...");

    // Tell Cargo to rerun this script if the UDL file changes
    println!("cargo:rerun-if-changed=src/hologram_ffi.udl");
    println!("cargo:rerun-if-changed=build.rs");

    // Also watch all .udl files if there are multiple
    let udl_path = Path::new("src/hologram_ffi.udl");
    if udl_path.exists() {
        println!("cargo:rerun-if-changed={}", udl_path.display());
    }

    // Generate UniFFI scaffolding
    uniffi::generate_scaffolding("src/hologram_ffi.udl").expect("Failed to generate UniFFI scaffolding");

    // Build the library in the same build profile
    let profile = env::var("PROFILE").unwrap();
    let build_target = env::var("TARGET").unwrap();

    println!(
        "cargo:warning=Building libhologram_ffi library for profile: {} target: {}",
        profile, build_target
    );

    // Cargo will automatically build the library after this build script
    // The generated .so/.dylib/.dll will be in target/{profile}/

    // Copy the generated library to Python interface directory for development
    let _out_dir = env::var("OUT_DIR").unwrap();
    let profile = env::var("PROFILE").unwrap();

    // Copy to Python interface
    let src = format!("../../target/{}/libhologram_ffi.so", profile);
    let dst = "interfaces/python/hologram_ffi/libuniffi_hologram_ffi.so";

    if Path::new(&src).exists() {
        std::fs::copy(&src, dst).ok(); // Ignore errors if directory doesn't exist
    }
}
