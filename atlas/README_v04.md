# Atlas Bridge Context API v0.4

## Overview

The Atlas Bridge Context API v0.4 provides a modern, context-based interface for Atlas bridge operations with enhanced capabilities including binary loaders, AVX2 acceleration, and advanced features for quantum-classical hybrid computations.

## New in v0.4

### 1. Real Lift Forms Loader

**File**: `lift_forms.hex`

The lift forms loader now supports runtime swap and configurable bit-width modes:

- **Runtime Swap**: Dynamically load new lift permutations without recreating context
- **8-bit Mode**: Use only low 8 bits when `N_QBITS=8` flag is set
- **Hex Format**: ASCII hex string with whitespace allowed

```c
// Load from file
atlas_ctx_load_lift_forms(ctx, "lift_forms.hex");

// Or set directly from hex string
atlas_ctx_set_lift_forms_hex(ctx, "deadbeef0123456789abcdef", 24);

// Runtime swap
atlas_ctx_set_lift_forms_hex(ctx, "cafebabe01234567", 16);

// Get current lift forms
char* hex = atlas_ctx_get_lift_forms_hex(ctx);
printf("Current lift forms: %s\n", hex);
free(hex);
```

**File Format**:
- Hex-encoded binary data representing 2^{1+24} embedding lift forms
- Each form is a permutation table or linear combination coefficients
- Whitespace (spaces, newlines, tabs) is ignored during parsing
- When `ATLAS_CTX_LIFT_8BIT` flag is set, only low 8 bits are used

### 2. P_299 Exact Matrix Loader

**File**: `P_299_matrix.bin`

Load dense exact projector matrix with automatic fallback:

- **Binary Format**: N*N doubles in row-major order (native endianness)
- **Symmetric & Idempotent**: Matrix must satisfy P² = P within tolerance
- **Fallback Logic**: If file absent or load fails, uses reduced-rank trace-zero logic

```c
// Enable P_299 support
cfg.flags = ATLAS_CTX_ENABLE_P_299;
AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);

// Try to load exact matrix
if (atlas_ctx_load_p299_matrix(ctx, "P_299_matrix.bin") == 0) {
    printf("Exact P_299 matrix loaded\n");
} else {
    printf("Using fallback reduced-rank logic\n");
}

// Apply projector (uses exact matrix if loaded, fallback otherwise)
atlas_ctx_apply_p_299(ctx, state);

// Check which mode is active
AtlasContextDiagnostics diag;
atlas_ctx_get_diagnostics(ctx, &diag);
if (diag.p_299_exact_loaded) {
    printf("Using exact matrix (better accuracy)\n");
} else {
    printf("Using fallback (faster, approximate)\n");
}
```

**File Format**:
- Binary file size: `N * N * sizeof(double)` bytes (N = block_size)
- Matrix layout: Row-major order
- Requirements: Symmetric (P = P^T) and idempotent (P² = P)
- Verification: Automatic idempotency check during loading

**Memory**:
- Exact matrix: O(N²) storage
- Fallback logic: O(N) storage

### 3. Co1 Real Generator Loader

**File**: `co1_gates.txt`

Load Co1 real generators from text file:

- **Text Format**: One generator per line, comments start with `#`
- **Integration**: Works in tandem with binary MAT gates (row-major N*N doubles)
- **Hybrid Gates**: Enables classical/quantum gate synthesis

```c
// Enable Co1 gates
cfg.flags = ATLAS_CTX_ENABLE_CO1;
AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);

// Load real generators
if (atlas_ctx_load_co1_gates(ctx, "co1_gates.txt") == 0) {
    printf("Co1 gates loaded\n");
}

// Use Co1 mini-gates API
atlas_ctx_apply_page_rotation(ctx, 12, state);
atlas_ctx_apply_mix_lifts(ctx, state);
atlas_ctx_apply_page_parity_phase(ctx, state);
```

**File Format** (`co1_gates.txt`):
```
# Co1 Real Generators
# One generator per line (real coefficient)
1.0
0.707106781
0.5
# Comments start with #
0.866025404
```

### 4. AVX2 SIMD Acceleration

Accelerate Pauli operations with AVX2 vector instructions:

- **Hot Loop Optimization**: 2-4x speedup for Pauli X/Z on large blocks
- **Automatic Fallback**: Gracefully falls back to scalar code if AVX2 unavailable
- **Runtime Detection**: Checked at context creation time

```c
// Enable AVX2 acceleration
cfg.flags = ATLAS_CTX_USE_AVX2;
AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);

// Check if AVX2 is active
if (atlas_ctx_is_avx2_active(ctx)) {
    printf("AVX2 acceleration enabled\n");
} else {
    printf("Using scalar fallback\n");
}

// Pauli operations automatically use AVX2 when available
atlas_ctx_apply_pauli_z(ctx, 0xFF, state);  // Accelerated if AVX2 active
```

**Compilation**:
- Compile with `-mavx2` flag on x86_64 to enable AVX2
- Will auto-detect and use scalar fallback if not compiled with AVX2

**Detection**:
- Compile-time: `#if defined(__AVX2__) && defined(__x86_64__)`
- Runtime: Flag `ATLAS_CTX_USE_AVX2` must be set in config

### 5. Block-Sparse Lift Mixing

Apply 8x8 mixing matrices to specific blocks:

- **Per-Block Mixing**: 8x8 double precision matrix applied to 8-element blocks
- **Bridge Mode**: Useful for structured sparsity in lift operations
- **Row-Major Format**: Standard matrix representation

```c
// Create 8x8 mixing matrix (identity in this example)
double mixing[64];
for (int i = 0; i < 8; i++) {
    for (int j = 0; j < 8; j++) {
        mixing[i * 8 + j] = (i == j) ? 1.0 : 0.0;
    }
}

// Apply to block 0 (indices 0-7 in state vector)
atlas_ctx_apply_block_mixing(ctx, 0, mixing, state);

// Can apply different mixing matrices to different blocks
for (uint32_t block = 0; block < n_blocks; block++) {
    // Customize mixing[64] for this block...
    atlas_ctx_apply_block_mixing(ctx, block, mixing, state);
}
```

**Application**: Useful for:
- Structured sparsity patterns in lift operations
- Block-wise transformations in bridge mode
- Localized mixing operations on sub-blocks

### 6. Enhanced Diagnostics

New diagnostics fields in v0.4:

```c
AtlasContextDiagnostics diag;
atlas_ctx_get_diagnostics(ctx, &diag);

printf("AVX2 available: %d\n", diag.avx2_available);
printf("P_299 exact loaded: %d\n", diag.p_299_exact_loaded);
printf("Co1 gates loaded: %d\n", diag.co1_gates_loaded);
```

### 7. JSON Certificate Enhancements

Certificates now include v0.4 metadata:

```json
{
  "version": "0.4.0",
  "mode": "bridge_test",
  "timestamp": 1699230000,
  "config": {
    "block_size": 12288,
    "n_qubits": 8,
    "twirl_gens": 16,
    "flags": 225,
    "epsilon": 1e-10
  },
  "diagnostics": {
    "op_count": 42,
    "twirl_idempotency": 1.234e-15,
    "p_class_idempotency": 2.345e-15,
    "p_299_idempotency": 3.456e-15,
    "lift_mass": 64.123,
    "last_residual": 1.234e-12,
    "commutant_dim": 0.987,
    "avx2_available": 1,
    "p_299_exact_loaded": 1,
    "co1_gates_loaded": 1
  },
  "lift_forms": "deadbeef0123..."
}
```

## Building

### Standard Build (No AVX2)

```bash
cd atlas
mkdir -p lib

# Compile
gcc -c -fPIC -Iinclude src/atlas_bridge_ctx.c

# Create shared library (Linux)
gcc -shared -o lib/libatlas_bridge_ctx.so atlas_bridge_ctx.o -lm

# Create shared library (macOS)
gcc -dynamiclib -o lib/libatlas_bridge_ctx.dylib atlas_bridge_ctx.o -lm
```

### Build with AVX2 Acceleration

```bash
cd atlas

# Compile with AVX2 support
gcc -c -fPIC -mavx2 -Iinclude src/atlas_bridge_ctx.c

# Create shared library
gcc -shared -o lib/libatlas_bridge_ctx.so atlas_bridge_ctx.o -lm
```

### Build Tests

```bash
# v0.2 compatibility tests
gcc -o tests_ctx tests/tests_ctx.c \
    atlas/src/atlas_bridge_ctx.c \
    -Iatlas/include -lm

# v0.3 extended tests
gcc -o tests_ctx_v03 tests/tests_ctx_v03.c \
    atlas/src/atlas_bridge_ctx.c \
    -Iatlas/include -lm

# v0.4 extended tests (with AVX2)
gcc -mavx2 -o tests_ctx_v04 tests/tests_ctx_v04.c \
    atlas/src/atlas_bridge_ctx.c \
    -Iatlas/include -lm

# Run tests
./tests_ctx        # v0.2 compatibility
./tests_ctx_v03    # v0.3 features
./tests_ctx_v04    # v0.4 features
```

## Python Bindings

Updated Python bindings in `bindings/python/atlas_bridge/_native_ctx.py`:

```python
from bindings.python.atlas_bridge._native_ctx import (
    AtlasBridgeContext,
    ATLAS_CTX_USE_AVX2,
    ATLAS_CTX_LIFT_8BIT,
)

# Create context with AVX2
ctx = AtlasBridgeContext()
ctx.config.flags |= ATLAS_CTX_USE_AVX2

# Load binary files
ctx.load_p299_matrix("P_299_matrix.bin")
ctx.load_co1_gates("co1_gates.txt")

# Runtime lift forms swap
ctx.set_lift_forms_hex("deadbeef0123456789abcdef")

# Block-sparse mixing
mixing_matrix = [1.0 if i == j else 0.0 for i in range(8) for j in range(8)]
ctx.apply_block_mixing(0, mixing_matrix, state)

# Check AVX2 status
if ctx.is_avx2_active():
    print("AVX2 acceleration is active")

# Emit certificate
ctx.emit_certificate("bridge_cert.json", "test_mode")
```

## Performance Notes

### AVX2 Speedup

- **Pauli Z operations**: 2-4x faster on large blocks (12,288 elements)
- **Best on**: x86_64 with AVX2 support
- **Fallback**: Automatic scalar implementation on other platforms

### P_299 Matrix Trade-offs

| Mode | Memory | Accuracy | Speed |
|------|--------|----------|-------|
| Exact matrix | O(N²) | High | Moderate |
| Fallback logic | O(N) | Approximate | Fast |

Recommendation: Use exact matrix when memory allows and high accuracy is required.

### Compilation Flags

```bash
# Maximum performance
gcc -O3 -march=native -mavx2 -ffast-math \
    -c -fPIC -Iinclude src/atlas_bridge_ctx.c

# Maximum portability
gcc -O2 -c -fPIC -Iinclude src/atlas_bridge_ctx.c
```

## Migration from v0.3

### API Changes

All v0.3 APIs remain fully supported. New v0.4 features are optional additions:

1. **Config struct** now includes `n_qbits` field (defaults to 8)
2. **Diagnostics struct** now includes `avx2_available`, `p_299_exact_loaded`, `co1_gates_loaded`
3. **New loaders**: `atlas_ctx_load_p299_matrix()`, `atlas_ctx_load_co1_gates()`
4. **New operations**: `atlas_ctx_apply_block_mixing()`, `atlas_ctx_is_avx2_active()`

### Code Updates

```c
// v0.3 code works unchanged
AtlasBridgeContext* ctx = atlas_ctx_new_default();
atlas_ctx_apply_p_299(ctx, state);  // Uses fallback if no matrix loaded

// v0.4 additions (optional)
atlas_ctx_load_p299_matrix(ctx, "P_299_matrix.bin");  // Now uses exact matrix
atlas_ctx_apply_p_299(ctx, state);  // Same API, better accuracy
```

## CI/CD Integration

Updated workflow in `.github/workflows/atlas-bridge.yml`:

```yaml
- name: Build with AVX2
  run: |
    gcc -mavx2 -c -fPIC -Iinclude src/atlas_bridge_ctx.c
    gcc -shared -o lib/libatlas_bridge_ctx.so atlas_bridge_ctx.o -lm

- name: Run v0.4 tests
  run: ./tests_ctx_v04

- name: Generate certificate
  run: ./cert_generator
  
- name: Upload certificate artifact
  uses: actions/upload-artifact@v3
  with:
    name: bridge-certificate
    path: bridge_cert.json
```

## Backward Compatibility

v0.4 maintains **100% backward compatibility** with v0.3 and v0.2:

- All v0.3 APIs work unchanged
- Default behavior identical to v0.3 when new flags not set
- Graceful degradation when binary files not present
- Same block size, qubit count, and generator defaults

## File Format Reference

### lift_forms.hex

```
# Example lift_forms.hex
deadbeef0123456789abcdef
# Whitespace allowed
0102 0304 0506 0708
# Comments start with #
```

### P_299_matrix.bin

Binary file containing:
- N*N doubles (N = block_size = 12288)
- Row-major order
- Native endianness
- Total size: 12288 * 12288 * 8 = 1,207,959,552 bytes (~1.2 GB)

Generate example:
```python
import numpy as np
N = 12288
P = np.random.rand(N, N)
P = (P + P.T) / 2  # Make symmetric
# Make idempotent (simplified)
P = P @ P  # Not truly idempotent, just for example
P.tofile("P_299_matrix.bin")
```

### co1_gates.txt

```
# Co1 Real Generators
# One real coefficient per line
1.0
0.707106781186547
0.5
# Blank lines and comments ignored
0.866025403784439
```

## Troubleshooting

### AVX2 Not Detected

```c
// Check if AVX2 is available
if (!atlas_ctx_is_avx2_active(ctx)) {
    // Recompile with: gcc -mavx2 ...
    // Or check CPU support: grep avx2 /proc/cpuinfo
}
```

### P_299 Matrix Load Failed

```c
if (atlas_ctx_load_p299_matrix(ctx, "P_299_matrix.bin") != 0) {
    // File not found or not idempotent
    // Fallback logic will be used automatically
}
```

### Memory Issues with Exact Matrix

For large block sizes, exact P_299 matrix requires ~1.2 GB of RAM. If this is too large:

```c
// Option 1: Use fallback (no matrix loading)
cfg.flags = ATLAS_CTX_ENABLE_P_299;  // Don't load matrix

// Option 2: Reduce block size
cfg.block_size = 4096;  // Smaller block
```

## Support and Documentation

- **Header**: `atlas/include/atlas_bridge_ctx.h`
- **Implementation**: `atlas/src/atlas_bridge_ctx.c`
- **Tests**: `tests/tests_ctx_v04.c`
- **Python Bindings**: `bindings/python/atlas_bridge/_native_ctx.py`
- **CI Workflow**: `.github/workflows/atlas-bridge.yml`

## Version History

- **v0.4.0**: Binary loaders, AVX2 acceleration, block-sparse mixing, 8-bit lift mode
- **v0.3.0**: Lift forms loader, exact projectors, Co1 mini-gates, JSON certificates
- **v0.2.0**: Homomorphic lifts, Pauli/Heisenberg, E-twirl, context API
- **v0.1.0**: Initial release
