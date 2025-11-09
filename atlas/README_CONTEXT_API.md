# Atlas Bridge Context API v0.3

## Overview

The Atlas Bridge Context API v0.3 provides a modern, context-based interface for Atlas bridge operations with enhanced capabilities:

- **Homomorphic lift permutations** via linear forms (Lx, Lz) with **runtime swap and hex file loader** (v0.3)
- **In-block 8-qubit Pauli/Heisenberg action** with block size 12,288 (page×byte), reduced-rank (byte axis)
- **Exact idempotent P_class projector** and **reduced-rank P_299 projector** (trace-zero over page%24 groups) (v0.3)
- **Co1 mini-gates API**: page rotation, Walsh-Hadamard mix lifts, page parity phase (v0.3)
- **JSON certificate emission** with mode, spinlift, lift forms, projector residuals, commutant probes (v0.3)
- **E-twirl group action** over 16 generators with idempotency (projector stable)
- **Opaque context API** with lifecycle management (new/clone/free)
- **Configuration and diagnostics** for monitoring and tuning
- **Full backwards compatibility** with v0.2

## Files

### Core Implementation
- `atlas/include/atlas_bridge_ctx.h` - C header with complete API
- `atlas/src/atlas_bridge_ctx.c` - Implementation

### Tests and Demos
- `tests/tests_ctx.c` - Comprehensive self-test suite (10 tests, v0.2 compatibility)
- `tests/tests_ctx_v03.c` - Extended test suite for v0.3 features (12 tests)
- `tests/test_spinlift_demo.c` - Demo showing lift-mass after twirl

### Bindings
- `bindings/python/atlas_bridge/_native_ctx.py` - Python bindings
- `bindings/python/atlas_bridge/examples/context_api_example.py` - Python example

### CI
- `.github/workflows/atlas-bridge-ctx-snippet.yml` - CI workflow snippet

## Building

### C Library

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

### Tests

```bash
# Build and run self-tests
gcc -o tests_ctx tests/tests_ctx.c atlas/src/atlas_bridge_ctx.c \
    -Iatlas/include -lm
./tests_ctx

# Build and run spinlift demo
gcc -o test_spinlift_demo tests/test_spinlift_demo.c \
    atlas/src/atlas_bridge_ctx.c -Iatlas/include -lm
./test_spinlift_demo
```

## Usage

### C API

```c
#include "atlas_bridge_ctx.h"

// Create context with default config
AtlasBridgeContext* ctx = atlas_ctx_new_default();

// Allocate state vector (block_size = 12288)
double* state = malloc(12288 * sizeof(double));
// ... initialize state ...

// Apply operations
atlas_ctx_apply_lift_x(ctx, state);           // Homomorphic lift Lx
atlas_ctx_apply_pauli_x(ctx, 0x07, state);    // Pauli X on qubits {0,1,2}
atlas_ctx_apply_twirl(ctx, state);            // E-twirl averaging

// Check idempotency
double idem = atlas_ctx_check_twirl_idempotency(ctx, state);
printf("Idempotency: %.6e\n", idem);

// Cleanup
free(state);
atlas_ctx_free(ctx);
```

### Python API

```python
from bindings.python.atlas_bridge._native_ctx import (
    AtlasBridgeContext,
    ATLAS_CTX_ENABLE_TWIRL,
    ATLAS_CTX_ENABLE_LIFT,
)

# Create context
cfg = get_default_config()
cfg.flags = ATLAS_CTX_ENABLE_TWIRL | ATLAS_CTX_ENABLE_LIFT
ctx = AtlasBridgeContext(cfg)

# Create state vector
state = [0.0] * ctx.block_size
# ... initialize state ...

# Apply operations
ctx.apply_lift_x(state)
ctx.apply_pauli_x(0x07, state)
ctx.apply_twirl(state)

# Check diagnostics
diag = ctx.get_diagnostics()
print(f"Operations: {diag.op_count}")
```

## API Reference

### Context Lifecycle

- `atlas_ctx_new(config)` - Create new context with configuration
- `atlas_ctx_new_default()` - Create context with default config
- `atlas_ctx_clone(ctx)` - Deep copy of context
- `atlas_ctx_free(ctx)` - Free context resources

### Homomorphic Lifts

- `atlas_ctx_apply_lift_x(ctx, state)` - Apply Lx permutation (bit-reversal on bytes)
- `atlas_ctx_apply_lift_z(ctx, state)` - Apply Lz permutation (Gray code on bytes)

Properties:
- **Lx² = I** (involutive)
- **Norm-preserving** (permutation)
- **Commutes with Pauli operations** (homomorphic)

### Pauli Operations

- `atlas_ctx_apply_pauli_x(ctx, mask, state)` - Apply X on qubits specified by mask
- `atlas_ctx_apply_pauli_z(ctx, mask, state)` - Apply Z on qubits specified by mask
- `atlas_ctx_apply_heisenberg(ctx, q1, q2, state)` - Heisenberg exchange σ₁·σ₂

Properties:
- **X² = Z² = I**
- **XZ = -ZX** (anticommutation)
- **Reduced-rank** on byte axis (8-qubit in-block)

### Exact Projectors (v0.3)

- `atlas_ctx_apply_p_class(ctx, state)` - Apply exact idempotent P_class projector
- `atlas_ctx_apply_p_299(ctx, state)` - Apply reduced-rank P_299 projector (trace-zero)
- `atlas_ctx_check_p_class_idempotency(ctx, state)` - Check ||P² - P||₂ for P_class
- `atlas_ctx_check_p_299_idempotency(ctx, state)` - Check ||P² - P||₂ for P_299

Properties:
- **P_class² = P_class** (exact idempotent projector to class-stable subspace)
- **P_299² = P_299** (exact idempotent projector to trace-zero subspace)
- **Trace-zero** over page%24 groups (P_299)
- **Reduced-rank** on byte axis

### Co1 Mini-Gates (v0.3)

- `atlas_ctx_apply_page_rotation(ctx, rot, state)` - Rotate pages by `rot` positions
- `atlas_ctx_apply_mix_lifts(ctx, state)` - Walsh-Hadamard mix on lift components
- `atlas_ctx_apply_page_parity_phase(ctx, state)` - Apply phase based on page parity

Properties:
- **Page rotation**: Cyclic permutation of 48 pages, rot=48 is identity
- **Walsh-Hadamard**: H² = I (involutive), norm-preserving unitary
- **Parity phase**: P² = I (involutive), applies (-1) to odd-parity pages

### Lift Forms Loader (v0.3)

- `atlas_ctx_load_lift_forms(ctx, filepath)` - Load custom lift forms from hex file
- `atlas_ctx_set_lift_forms_hex(ctx, hex_data, len)` - Set lift forms from hex string
- `atlas_ctx_get_lift_forms_hex(ctx)` - Get current lift forms as hex string

Properties:
- **Runtime swap**: Change lift forms without recompilation
- **Hex encoding**: Flexible format with whitespace tolerance
- **Reproducibility**: Lift forms included in certificates

See [LIFT_FORMS_README.md](../LIFT_FORMS_README.md) for detailed usage.

### JSON Certificates (v0.3)

- `atlas_ctx_emit_certificate(ctx, filepath, mode)` - Emit JSON certificate with diagnostics
- `atlas_ctx_probe_commutant(ctx, state, with_co1)` - Compute commutant probe values

Properties:
- **Comprehensive diagnostics**: All projector residuals, idempotency measures
- **Lift forms snapshot**: Records active lift forms for reproducibility
- **Commutant probes**: Effective dimension of Comm(E,Co1) with/without Co1 gates
- **Mode tracking**: Identifies computation mode (spinlift, commutant, etc.)

### E-Twirl

- `atlas_ctx_apply_twirl(ctx, state)` - Apply E-twirl projector
- `atlas_ctx_check_twirl_idempotency(ctx, state)` - Check ||T² - T||₂
- `atlas_ctx_get_twirl_generator(ctx, idx, x_mask, z_mask)` - Query generator

Properties:
- **T² = T** (idempotent, up to numerical tolerance)
- **16 generators** from 8-qubit Pauli group
- **Projector stable** (invariant subspace)

### Diagnostics

- `atlas_ctx_get_diagnostics(ctx, diag)` - Get diagnostics structure
- `atlas_ctx_reset_diagnostics(ctx)` - Reset counters
- `atlas_ctx_validate(ctx)` - Check internal consistency
- `atlas_ctx_print_diagnostics(ctx)` - Print to stdout

## Test Results

### v0.2 Tests (Backwards Compatibility)

All 10 v0.2 self-tests pass with v0.3:

1. ✓ Context lifecycle (new/clone/free)
2. ✓ Configuration management
3. ✓ Homomorphic lift permutations (Lx involutive, norm preservation)
4. ✓ Pauli operator relations (X²=I, Z²=I, XZ=-ZX)
5. ✓ E-twirl idempotency (T²=T within tolerance)
6. ✓ Twirl generator queries
7. ✓ Heisenberg exchange operator
8. ✓ Diagnostics and counters
9. ✓ Version and utilities
10. ✓ Combined operations

### v0.3 Extended Tests

All 12 v0.3 tests pass:

1. ✓ Lift forms hex codec (encoding/decoding, whitespace handling)
2. ✓ Lift forms file loader (file I/O, validation)
3. ✓ P_class projector idempotency (||P²-P|| < 1e-12)
4. ✓ P_299 projector idempotency (||P²-P|| < 1e-12, trace-zero)
5. ✓ Co1 page rotation gate (cyclic permutation, full cycle)
6. ✓ Co1 Walsh-Hadamard mix lifts (H² = I, norm preservation)
7. ✓ Co1 page parity phase gate (P² = I, parity verification)
8. ✓ Spinlift homomorphism (Lx² = I, preserved from v0.2)
9. ✓ Pauli relations extended (XZ = -ZX for all qubits)
10. ✓ Commutant probe (Comm(E,Co1) effective dimension)
11. ✓ JSON certificate emission (all required fields present)
12. ✓ Backwards compatibility with v0.2 (graceful degradation)

### Demo Output

The spinlift demo shows:
- **Mass redistribution**: L1 mass drops by ~80% after twirl (spreading effect)
- **Twirl idempotency**: ||T²(v) - T(v)||₂ = 0 (perfect within numerical precision)
- **Norm preservation**: Lift operations preserve L2 norm (permutations)

### Certificate Example

```json
{
  "version": "0.3.0",
  "mode": "spinlift",
  "timestamp": 1762387437,
  "config": {
    "block_size": 12288,
    "n_qubits": 8,
    "twirl_gens": 16,
    "flags": 41,
    "epsilon": 1.000000000000e-10
  },
  "diagnostics": {
    "op_count": 14,
    "twirl_idempotency": 0.000000000000e+00,
    "p_class_idempotency": 8.314381771235e-15,
    "p_299_idempotency": 0.000000000000e+00,
    "lift_mass": 0.000000000000e+00,
    "last_residual": 0.000000000000e+00,
    "commutant_dim": 2.400797369721e-01
  },
  "lift_forms": "0123456789abcdef"
}
```

## Future Upgrade Paths

### 12-Qubit Extension
- Extend Pauli operators from 8-qubit to full 12-qubit representation
- Update block_size calculation for 12-qubit register
- Modify twirl generators for expanded Hilbert space

### Advanced Lift Forms
- Implement composite lifts: L_xy = L_x ∘ L_z
- Add parameterized lift families with continuous parameters
- Support non-homomorphic lift variants for error analysis

### Wiring Co1 Gates
- Integrate Co1 gate family from `atlas_bridge.h`
- Add context-aware Co1 application with twirl compatibility
- Implement Co1-invariant projector subspaces
- Cross-reference: see `atlas/src/co1_gates.c` for gate implementations

### Performance Optimizations
- SIMD vectorization for Pauli operations
- Sparse matrix representations for large blocks
- GPU acceleration hooks for twirl averaging

### Certification
- Add certificate generation for twirl idempotency
- Implement formal verification hooks for Lean4 proofs
- Export witness data for external validation

## Legacy Compatibility

The Context API v0.2 is **fully independent** from the legacy bridge API in `atlas_bridge.h`. No legacy code was modified. Both APIs can coexist:

- **Legacy API**: `atlas_bridge.h` - Original interface (unchanged)
- **Context API v0.2**: `atlas_bridge_ctx.h` - New context-based interface

## Version

Current version: **0.3.0**

Query at runtime:
```c
const char* version = atlas_ctx_version();  // Returns "0.3.0"
```

### What's New in v0.3

- ✅ **Lift forms loader**: Runtime swap with hex file support (`lift_forms.hex`)
- ✅ **Exact projectors**: P_class (idempotent) and P_299 (trace-zero, reduced-rank)
- ✅ **Co1 mini-gates**: Page rotation, Walsh-Hadamard mix, parity phase
- ✅ **JSON certificates**: Complete diagnostics with lift forms, projector residuals, commutant probes
- ✅ **Extended tests**: 12 additional tests for v0.3 features
- ✅ **Backwards compatible**: All v0.2 code works unchanged

### Migration from v0.2

No code changes required! v0.3 is fully backwards compatible:

```c
// v0.2 code works as-is
AtlasBridgeContext* ctx = atlas_ctx_new_default();
atlas_ctx_apply_lift_x(ctx, state);
atlas_ctx_apply_twirl(ctx, state);
atlas_ctx_free(ctx);

// Opt-in to v0.3 features with flags
AtlasContextConfig cfg;
atlas_ctx_config_default(&cfg);
cfg.flags |= ATLAS_CTX_ENABLE_P_CLASS | ATLAS_CTX_ENABLE_CO1;
AtlasBridgeContext* ctx_v3 = atlas_ctx_new(&cfg);
```

## License

Same as main project (see LICENSE files in repository root).
