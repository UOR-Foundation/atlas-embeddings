# Development Scripts

This directory contains scripts for maintaining the hologramapp project.

## FFI Bindings

### `update_ffi_bindings.sh`

Updates FFI language bindings by copying the compiled library to binding directories.

**Usage:**
```bash
# After building hologram-ffi
cargo build --release -p hologram-ffi
./scripts/update_ffi_bindings.sh
```

**What it does:**
1. Detects your platform (Linux/macOS/Windows)
2. Finds the compiled library in `target/release/` or `target/debug/`
3. Copies it to `crates/hologram-ffi/interfaces/python/hologram_ffi/`
4. Reports success or failure

**When to run:**
- After modifying any Rust code in `hologram-ffi`
- When Python bindings load stale library
- Before running Python integration tests
- As part of CI/CD pipeline

See [docs/FFI_DEVELOPMENT.md](../docs/FFI_DEVELOPMENT.md) for complete documentation.
