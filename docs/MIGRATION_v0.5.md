# Atlas Bridge v0.5 Migration Guide

## Overview

Atlas Bridge Deployment Pack v0.5 introduces significant enhancements while maintaining full backward compatibility with v0.4. This guide helps you migrate to the new features and understand the changes.

## What's New in v0.5

### 1. BLAS Acceleration (Optional)

Matrix-vector operations now support BLAS acceleration for improved performance:

- **Automatic Detection**: Build system detects OpenBLAS/CBLAS
- **Graceful Fallback**: Falls back to naive loops if BLAS not available
- **2-4x Speedup**: For large matrix-vector products

**Build with BLAS:**
```bash
cd atlas
make USE_BLAS=auto  # Auto-detect (default)
make USE_BLAS=yes   # Force BLAS (fails if not found)
make USE_BLAS=no    # Disable BLAS
```

**CMake:**
```bash
mkdir build && cd build
cmake -DUSE_BLAS=ON ..
make
```

### 2. Real Artifacts Integration

Production-ready artifact files for bridge operations:

#### lift_forms.hex (Required)
6 hex bytes representing lift forms: `Lx0 Lx1 Lx2  Lz0 Lz1 Lz2`

```bash
# Example lift forms
echo "A7 5C 39 D2 4E 11" > lift_forms.hex
```

Load in code:
```c
atlas_ctx_load_lift_forms(ctx, "lift_forms.hex");
```

#### P_299_matrix.bin (Optional)
Exact dense projector matrix (N×N doubles, row-major)

- **With file**: O(N²) memory, better accuracy
- **Without file**: O(N) memory, fallback trace-zero logic

```c
// Attempt to load exact matrix
if (atlas_ctx_load_p299_matrix(ctx, "P_299_matrix.bin") == 0) {
    printf("Using exact P_299 matrix\n");
} else {
    printf("Using fallback logic\n");
}
```

#### co1_gates.txt (Optional)
Co1 generator configuration

```
# Co1 gates configuration
GENERATOR 0 PAGE_ROT 0
GENERATOR 1 PAGE_ROT 12
GENERATOR 2 PARITY_PHASE
GENERATOR 3 WALSH_MIX
```

Load in code:
```c
atlas_ctx_load_co1_gates(ctx, "co1_gates.txt");
```

### 3. Enhanced Build System

**Makefile** (atlas/Makefile):
- Automatic BLAS detection
- AVX2 support detection
- Static and shared library builds

**CMake** (CMakeLists.txt):
- Cross-platform builds
- Integrated testing with CTest
- BLAS and AVX2 configuration options

### 4. Verification Suite

**atlas/tools/verify_bridge.sh**: Comprehensive verification with threshold enforcement

```bash
bash atlas/tools/verify_bridge.sh
```

Performs:
- BLAS detection
- Library compilation
- Full unit test suite
- Certificate generation with metrics
- Threshold verification:
  - P_class idempotency ≤ 1e-8
  - P_299 idempotency ≤ 1e-8  
  - Commutant dimension < 1.5

### 5. Language Bindings Updates

All language bindings updated to v0.5 with context API:

#### Python
```python
from bindings.python.atlas_bridge._native_ctx import AtlasContext

ctx = AtlasContext()
ctx.load_lift_forms('lift_forms.hex')
ctx.load_p299_matrix('P_299_matrix.bin')  # optional
ctx.load_co1_gates('co1_gates.txt')  # optional

state = [0.0] * ctx.block_size
ctx.apply_p_class(state)
ctx.emit_certificate('cert.json', 'test')
```

#### Rust
```rust
use atlas_bridge::AtlasContext;

let ctx = AtlasContext::new_default()?;
ctx.load_lift_forms("lift_forms.hex")?;
ctx.load_p299_matrix("P_299_matrix.bin").ok();

let mut state = vec![0.0; ctx.block_size()];
ctx.apply_p_class(&mut state)?;
```

#### Node.js
```javascript
const { AtlasContext } = require('@atlas/bridge');

const ctx = new AtlasContext();
ctx.loadLiftForms('lift_forms.hex');
ctx.loadP299Matrix('P_299_matrix.bin');  // optional

const state = new Float64Array(ctx.blockSize);
ctx.applyPClass(state);
```

#### Go
```go
import "github.com/CitizenGardens-org/atlas-hologram/bindings/go/atlas_bridge"

ctx, _ := atlas_bridge.NewAtlasContext(nil)
defer ctx.Free()

ctx.LoadLiftForms("lift_forms.hex")
ctx.LoadP299Matrix("P_299_matrix.bin")  // optional

state := make([]float64, ctx.BlockSize())
ctx.ApplyPClass(state)
```

## Legacy API Deprecation

### Python

⚠️ **DEPRECATED** in v0.5, **REMOVED** in v0.6:
```python
# OLD (deprecated)
from atlas_bridge._native import lib
lib.e_apply(state, x_mask, z_mask)
```

**NEW (use this):**
```python
from atlas_bridge._native_ctx import AtlasContext
ctx = AtlasContext()
ctx.apply_pauli_x(x_mask, state)
ctx.apply_pauli_z(z_mask, state)
```

### C

Legacy non-context functions are deprecated. Use context API:

```c
// OLD (deprecated)
// Direct function calls without context

// NEW (use this)
AtlasBridgeContext* ctx = atlas_ctx_new_default();
atlas_ctx_apply_p_class(ctx, state);
atlas_ctx_free(ctx);
```

## Migration Checklist

- [ ] Update build system to use `atlas/Makefile` or `CMakeLists.txt`
- [ ] Create `lift_forms.hex` file (required for real runs)
- [ ] Optionally create `P_299_matrix.bin` and `co1_gates.txt`
- [ ] Update code to use context-based API
- [ ] Add deprecation warning handling for legacy API usage
- [ ] Test with `atlas/tools/verify_bridge.sh`
- [ ] Update CI to use `.github/workflows/bridge.yml`
- [ ] Verify certificate generation and metrics

## Breaking Changes

**None.** v0.5 is fully backward compatible with v0.4.

However, deprecation warnings will appear when using legacy APIs. These will become errors in v0.6.

## Performance Notes

### With BLAS
- Matrix-vector products: 2-4x faster
- Large projector operations: significantly improved
- Recommended for production deployments

### Without BLAS
- Naive loop fallback
- Fully functional, slower for large operations
- Suitable for development and small-scale testing

## Troubleshooting

### BLAS Not Detected

**Problem:** Build system doesn't find BLAS libraries

**Solutions:**
```bash
# Ubuntu/Debian
sudo apt-get install libopenblas-dev

# macOS (Homebrew)
brew install openblas

# Force BLAS usage (will fail if not found)
make USE_BLAS=yes
```

### Tests Failing

**Problem:** Unit tests fail after upgrade

**Solution:** Rebuild library and tests:
```bash
cd atlas
make clean
make
cd ..
bash atlas/tools/verify_bridge.sh
```

### Certificate Generation Fails

**Problem:** Certificate not generated

**Check:**
1. Ensure `lift_forms.hex` exists
2. Check write permissions for output directory
3. Verify library is built correctly

## Support

For issues or questions:
1. Check `atlas/README_v04.md` for detailed API docs
2. Run `atlas/tools/verify_bridge.sh` for diagnostics
3. Review `.github/workflows/bridge.yml` for CI examples

## Version Timeline

- **v0.5** (current): BLAS acceleration, real artifacts, enhanced bindings
- **v0.4**: AVX2, binary loaders, block mixing
- **v0.3**: Lift forms, P_299, Co1 gates
- **v0.2**: Context API foundation
