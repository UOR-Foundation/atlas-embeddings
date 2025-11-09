//! Minimal test to check if the basic setup works

use hologram_ffi::get_version;

#[test]
fn test_minimal() {
    let version = get_version();
    assert!(!version.is_empty());
}
