# hologram-kernel-runtime

Shared runtime library for all compiled kernels.

## Purpose

This crate provides common infrastructure that all kernels use, avoiding code duplication across kernel binaries. Instead of every `.so` file duplicating the Unmarshaller, ABI types, etc., kernels can link against this shared library.

## What's In This Crate

### `unmarshaller.rs`
- Parameter unpacking from binary data
- Support for all primitive types (u8, i32, f64, etc.)
- Alignment handling for FFI compatibility

### `abi.rs`  
- Standard FFI types (CLaunchConfig, ErrorCode)
- Function signatures for kernel exports
- ABI version constants

### `types.rs`
- POD (Plain Old Data) trait for FFI safety
- Type-safe wrappers for device pointers

## Current Status

✅ Crate created and compiles
⚠️ Not yet integrated into kernel generation
- Need to update `build.rs` to link kernels against this
- Need to update kernel generation to use shared code

## Integration Plan

1. Update `hologram-codegen/build.rs` to:
   - Add `hologram-kernel-runtime` as dependency to generated kernels
   - Generate `use hologram_kernel_runtime::*;` in kernel code
   - Remove duplicated Unmarshaller/ABI code

2. Benefits:
   - ✅ Smaller kernel binaries
   - ✅ Easier to add new parameter types
   - ✅ Single place to fix bugs/improve performance
   - ✅ Can update ABI version in one place
