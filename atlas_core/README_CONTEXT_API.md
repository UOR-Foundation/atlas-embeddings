# Atlas Bridge Context API v0.2

## Overview

The Atlas Bridge Context API v0.2 provides a modern, context-based interface for Atlas bridge operations with enhanced capabilities:

- **Homomorphic lift permutations** via linear forms (Lx, Lz)
- **In-block 8-qubit Pauli/Heisenberg action** with block size 12,288 (page×byte), reduced-rank (byte axis)
- **E-twirl group action** over 16 generators with idempotency (projector stable)
- **Opaque context API** with lifecycle management (new/clone/free)
- **Configuration and diagnostics** for monitoring and tuning

## Files

### Core Implementation
- `atlas_core/include/atlas_bridge_ctx.h` - C header with complete API
- `atlas_core/src/atlas_bridge_ctx.c` - Implementation

### Tests and Demos
- `tests/tests_ctx.c` - Comprehensive self-test suite (10 tests)
- `tests/test_spinlift_demo.c` - Demo showing lift-mass after twirl

### Bindings
- `bindings/python/atlas_bridge/_native_ctx.py` - Python bindings
- `bindings/python/atlas_bridge/examples/context_api_example.py` - Python example

### CI
- `.github/workflows/atlas-bridge-ctx-snippet.yml` - CI workflow snippet

## Building

### C Library

```bash
cd atlas_core
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
gcc -o tests_ctx tests/tests_ctx.c atlas_core/src/atlas_bridge_ctx.c \
    -Iatlas_core/include -lm
./tests_ctx

# Build and run spinlift demo
gcc -o test_spinlift_demo tests/test_spinlift_demo.c \
    atlas_core/src/atlas_bridge_ctx.c -Iatlas_core/include -lm
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

All 10 self-tests pass:

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

### Demo Output

The spinlift demo shows:
- **Mass redistribution**: L1 mass drops by ~80% after twirl (spreading effect)
- **Twirl idempotency**: ||T²(v) - T(v)||₂ = 0 (perfect within numerical precision)
- **Norm preservation**: Lift operations preserve L2 norm (permutations)

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
- Cross-reference: see `atlas_core/src/co1_gates.c` for gate implementations

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

Current version: **0.2.0**

Query at runtime:
```c
const char* version = atlas_ctx_version();  // Returns "0.2.0"
```

## License

Same as main project (see LICENSE files in repository root).
