# FFI Development Guide

This guide explains how to work with the hologram-ffi bindings and keep them in sync during development.

## Quick Start

### Rebuild FFI Bindings (Recommended)

**Two-step process:**

```bash
# 1. Build the FFI library
cargo build-ffi  # or: cargo build --release -p hologram-ffi

# 2. Update bindings (copies library to language directories)
./scripts/update_ffi_bindings.sh
```

This workflow:
1. Builds `libhologram_ffi.so` in release mode
2. Copies it to `crates/hologram-ffi/interfaces/python/hologram_ffi/`
3. Ensures Python/TypeScript/etc. load the latest version

### Debug Builds

For faster iteration during development:

```bash
# Build in debug mode (faster compile)
cargo build -p hologram-ffi

# Update bindings (script auto-detects debug/release)
./scripts/update_ffi_bindings.sh
```

## Understanding the Problem

### Why Manual Updates Are Needed

The FFI bindings have a two-step process:

1. **Build step** (`cargo build`): Compiles `libhologram_ffi.so` to `target/release/`
2. **Copy step**: Copies library to language binding directories

The issue: Cargo's `build.rs` runs **during** compilation, before the library is fully built. This timing issue means the library can't copy itself reliably.

### Previous Issues

- **Deadlock bug**: Fixed in tensor operations (see commit history)
- **Stale bindings**: Python loaded old library even after rebuilding
- **Relative path issues**: `build.rs` used paths that only worked from specific directories

## Available Commands

### Cargo Aliases

```bash
# Build FFI in release mode
cargo build-ffi

# Then manually run:
./scripts/update_ffi_bindings.sh
```

**Why two steps?** Cargo aliases can't run shell commands directly. The two-step approach is simple and explicit.

### Direct Script Usage

```bash
# Update bindings (auto-detects debug/release)
./scripts/update_ffi_bindings.sh

# Make script executable (if needed)
chmod +x scripts/update_ffi_bindings.sh
```

## Testing FFI Changes

### Python Bindings

```bash
# 1. Build FFI
cargo build-ffi

# 2. Update bindings
./scripts/update_ffi_bindings.sh

# 3. Run Python tests
source examples/.venv/bin/activate
python test_tensor_transpose_fix.py
python examples/pytorch_hologram_integration.py
```

### Quick Verification

```bash
# Check library timestamp
ls -lh crates/hologram-ffi/interfaces/python/hologram_ffi/libuniffi_hologram_ffi.so

# Compare with built library
ls -lh target/release/libhologram_ffi.so

# They should have matching timestamps after cargo rebuild-ffi
```

## Regenerating Binding Code

The `scripts/update_ffi_bindings.sh` script only **copies the compiled library**. If you've modified the UDL file (`src/hologram_ffi.udl`), you also need to regenerate the binding code:

```bash
# Regenerate Python/TypeScript/Kotlin bindings from UDL
cd crates/hologram-ffi
cargo run --bin generate_bindings
```

This regenerates:
- `interfaces/python/hologram_ffi/hologram_ffi.py`
- TypeScript/Kotlin bindings (if configured)

## CI/CD Integration

### GitHub Actions Example

```yaml
- name: Build FFI bindings
  run: |
    cargo build --release -p hologram-ffi
    ./scripts/update_ffi_bindings.sh

- name: Test Python bindings
  run: |
    source examples/.venv/bin/activate
    python -m pytest tests/
```

## Troubleshooting

### Problem: Python still loads old library

**Solution:**
```bash
# Force rebuild
cargo clean -p hologram-ffi
cargo build-ffi
./scripts/update_ffi_bindings.sh

# Verify timestamp
ls -lh crates/hologram-ffi/interfaces/python/hologram_ffi/libuniffi_hologram_ffi.so
```

### Problem: "No module named 'hologram_ffi'"

**Solution:**
```bash
# Ensure Python path includes the bindings
export PYTHONPATH="${PYTHONPATH}:$(pwd)/crates/hologram-ffi/interfaces/python"

# Or activate the venv
source examples/.venv/bin/activate
```

### Problem: Script fails with "permission denied"

**Solution:**
```bash
chmod +x scripts/update_ffi_bindings.sh
```

### Problem: Library not found on macOS/Linux

**Solution:**
```bash
# macOS: Check dylib exists
ls target/release/libhologram_ffi.dylib

# Linux: Check so exists
ls target/release/libhologram_ffi.so

# Windows: Check dll exists
ls target/release/hologram_ffi.dll
```

## Best Practices

### During Development

1. **Always run both commands** after changing Rust code:
   - `cargo build-ffi`
   - `./scripts/update_ffi_bindings.sh`
2. **Activate the venv** before running Python tests
3. **Check timestamps** if you suspect stale bindings

### Before Committing

1. Run full test suite: `cargo test --workspace`
2. Test Python bindings: `python examples/pytorch_hologram_integration.py`
3. Verify no deadlocks in tensor operations
4. Check that library is up to date: `./scripts/update_ffi_bindings.sh`

### For Contributors

1. If you modify `hologram-ffi` Rust code → Run `cargo build-ffi && ./scripts/update_ffi_bindings.sh`
2. If you modify `.udl` files → Run `cargo run --bin generate_bindings` (from hologram-ffi dir)
3. Always test Python bindings after FFI changes
4. Document any new FFI functions in the `.udl` file

## Architecture Notes

### Why Not Auto-Copy in build.rs?

**Problem:** `build.rs` runs during compilation, but:
- Library isn't fully compiled yet
- Relative paths are fragile
- Cargo rebuilds can be partial

**Solution:** Explicit post-build script that:
- Runs after library is complete
- Uses absolute paths
- Always succeeds or fails clearly

### Why Not Use a Makefile?

- Not idiomatic in Rust projects
- Cross-platform issues (Windows doesn't have `make` by default)
- Cargo aliases provide better integration
- Developers expect `cargo build` to work

### Why Not Root build.rs?

- Cargo doesn't support workspace-level build scripts well
- Execution order is undefined
- Can't depend on member crates being built
- Timing issues remain

## See Also

- [UniFFI Documentation](https://mozilla.github.io/uniffi-rs/)
- [Cargo Aliases](https://doc.rust-lang.org/cargo/reference/config.html#alias)
- Main README: [/README.md](../README.md)
- FFI README: [crates/hologram-ffi/README.md](../crates/hologram-ffi/README.md)
