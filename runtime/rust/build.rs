use std::env;
use std::path::PathBuf;

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let project_root = PathBuf::from(&manifest_dir)
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();

    // Build the minimal wrapper for runtime use
    let ffi_dir = project_root.join("ffi/c");
    let minimal_wrapper = ffi_dir.join("minimal_wrapper.c");

    cc::Build::new()
        .file(&minimal_wrapper)
        .include(&ffi_dir)
        .compile("uor_minimal");

    println!("cargo:rerun-if-changed={}", minimal_wrapper.display());
}
