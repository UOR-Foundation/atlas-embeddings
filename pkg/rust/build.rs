use std::env;
use std::path::PathBuf;

fn main() {
    // Get the FFI directory path
    let ffi_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap())
        .parent().unwrap()
        .parent().unwrap()
        .join("ffi");
    
    // Build the minimal wrapper as a static library
    cc::Build::new()
        .file(ffi_dir.join("c/minimal_wrapper.c"))
        .include(ffi_dir.join("c"))
        .compile("uor_minimal");
    
    // Tell cargo to link the library
    println!("cargo:rustc-link-lib=static=uor_minimal");
    
    // Tell cargo to rerun if the wrapper changes
    println!("cargo:rerun-if-changed={}", ffi_dir.join("c/minimal_wrapper.c").display());
    println!("cargo:rerun-if-changed={}", ffi_dir.join("c/uor_ffi_hybrid.h").display());
}