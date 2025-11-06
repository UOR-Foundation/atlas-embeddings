# Atlas Component

Atlas is the numerical/runtime core of the hologram monorepo.

## Overview

The Atlas component provides:
- Context-based C API for Atlas Bridge operations
- Exact extraspecial 2-group action on blocks with XOR lift routing
- P_class and P_299 projectors
- Co1 gate support with pluggable generators
- Deterministic diagnostics and certificate emission
- Optional SIMD (AVX2) and BLAS acceleration

## Building

From the atlas directory:

```bash
cd atlas
bash tools/verify_bridge.sh
```

Or use the root Makefile:

```bash
make atlas-build
make atlas-test
make atlas-cert
```

## Key Files

- `src/atlas_bridge_ctx.c` - Core implementation
- `include/atlas_bridge_ctx.h` - Public API
- `tests/tests_ctx.c` - Unit tests
- `tools/verify_bridge.sh` - Build and verification script

## Artifacts

Optional artifacts in `artifacts/`:
- `lift_forms.hex` - 6 hex bytes for lift routing
- `P_299_matrix.bin` - Exact linear projector matrix
- `co1_gates.txt` - Co1 generator configuration

## Bindings

Language bindings available in `bindings/`:
- Python
- Rust
- Node.js
- Go

## Certificate

The verification script generates `bridge_cert.json` with:
- Mode and configuration flags
- Projector idempotency metrics
- Commutant dimension probes
- BLAS/AVX2 status

## Thresholds

- P_class idempotency: ≤ 1e-8 (target), ≤ 1e-12 (practice)
- P_299 idempotency: ≤ 1e-8
- Commutant effective dim: < 1.5

