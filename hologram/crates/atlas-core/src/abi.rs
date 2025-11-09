//! C ABI Definitions for atlas-core
//!
//! This module documents the stable C ABI for atlas-core mathematical functions.
//! These function signatures must never change without a major version bump.
//!
//! ## LLVM Integration
//!
//! The JIT compiler generates calls to these functions as external function calls.
//! LLVM treats them as opaque black boxes, preventing reordering or optimization
//! that would violate Atlas invariants.

/// C ABI version
pub const ABI_VERSION: u32 = 1;

/// Get the C ABI version
///
/// This allows runtime checking that the JIT engine and core library are compatible.
#[no_mangle]
pub extern "C" fn atlas_core_abi_version() -> u32 {
    ABI_VERSION
}

// Note: The actual C ABI functions are defined in their respective modules
// (uor.rs, invariants.rs) with #[no_mangle] and extern "C"
//
// This module exists to document the ABI contract.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abi_version() {
        assert_eq!(atlas_core_abi_version(), 1);
    }
}
