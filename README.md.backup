# Hologram APEX Monorepo

**Components:** Atlas • Embeddings • Sigmatics

This repository hosts a cohesive stack for moonshine‑inspired computation. It brings together a fast classical/bridge **Atlas** core, **Embeddings** that map data into Atlas spaces, and **Sigmatics** for symbolic + programmatic workflows. The stack is designed for rigorous experiments around Conway–Monster structures while remaining practical for ML/quant‑adjacent workloads.

**v0.5 Update:** Atlas Bridge Deployment Pack integrated with BLAS acceleration, real artifact support, and enhanced language bindings.

---

## Contents
- [Architecture](#architecture)
- [Components](#components)
  - [Atlas](#atlas)
  - [Embeddings](#embeddings)
  - [Sigmatics](#sigmatics)
- [Quickstart](#quickstart)
- [Repository Layout](#repository-layout)
- [Configuration Files](#configuration-files)
- [Build, Test, and Certificates](#build-test-and-certificates)
- [Python Bindings](#python-bindings)
- [Status & Roadmap](#status--roadmap)
- [Contributing](#contributing)
- [License](#license)

---

## Architecture
At a high level, the stack is a **hybrid classical/bridge system** with a hard 2B interface and an opt‑in Conway–Monster bridge.

- **Classical layer (base):** `W_class = 24 × 4096` reduced in code to a practical 12,288‑dimensional block (48×256).
- **Bridge (Monster‑adjacent):** an 8‑lift expansion driven by the extraspecial group `E = 2^{1+24}` and reduced Co1 actions. In practice, we use an 8‑lift XOR action keyed by linear forms of `(x,z)`.
- **Projectors and diagnostics:** executable `P_class` and `P_299` projectors, commutant probes, leakage and idempotency metrics. A CI certificate (`bridge_cert.json`) records thresholds.

> The Atlas core runs standalone. Embeddings and Sigmatics consume Atlas as a library and provide higher‑level experiments.

---

## Components

### Atlas
The Atlas component is the numerical/runtime core.

**Highlights**
- Context‑based C API (`atlas_bridge_ctx.h/.c`)
- Exact extraspecial 2‑group action on blocks with XOR lift routing
- `P_class` and `P_299` projectors (reduced‑rank exact; optional full linear projector via external matrix)
- Minimal Co1 “mini‑gates” + pluggable dense generators
- Deterministic diagnostics: projector idempotency, commutant proxy, certificate emission
- Optional SIMD (AVX2) and BLAS acceleration

**Key files**
- `atlas_bridge_ctx.h/.c` — core API and implementation
- `tests_ctx.c` — unit tests (homomorphism, Pauli relations, projector idempotency, commutant collapse)
- `.github/workflows/bridge.yml` — CI to build, test, and publish `bridge_cert.json`

**Thresholds**
- `‖P_class^2 − P_class‖ ≤ 1e−8` (target), `≤ 1e−12` in practice
- `Comm(E,Co1)` effective dim < 1.5

---

### Embeddings
The Embeddings component turns structured or unstructured inputs into vectors living in Atlas spaces for analysis or downstream learning.

**Capabilities**
- Dataset adapters → Atlas‑compatible tensors
- Feature heads producing 12,288‑length vectors (base) or 8‑lift stacks (bridge)
- Optional training/eval loops for reconstruction and projector‑consistency losses

**Typical workflow**
1. Prepare data adapter producing `(page, byte)` structured views or raw vectors.
2. Encode to 12,288 and run `P_class` / `P_299` consistency checks.
3. If needed, lift to bridge mode and evaluate leakage and commutant metrics.

**Key entrypoints**
- `embeddings/…` (Python): dataset loaders, model wrappers, evaluation scripts
- `docs/embeddings.md`: format specs and examples

---

### Sigmatics
Sigmatics is the symbolic and orchestration layer: notebooks, proof‑sketch runners, and Sage/Atlas glue.

**Capabilities**
- Sage‑Atlas bridge: generate lift forms, sanity‑check linear forms, export `lift_forms.hex`
- Scripted experiments around `S²(24)` trace‑zero features and projector synthesis
- Batch drivers to run Atlas diagnostics across seeds and datasets

**Key entrypoints**
- `sigmatics/…` (Sage/Python): generators, exporters, experiment runners
- `docs/sigmatics.md`: setup and recipes

---

## Quickstart

### v0.5 What's New

**Atlas Bridge Deployment Pack v0.5** brings significant enhancements:
- **BLAS Acceleration**: Optional OpenBLAS/CBLAS support for matrix-vector operations with automatic fallback
- **Real Artifacts**: Production-ready `lift_forms.hex`, optional `P_299_matrix.bin`, optional `co1_gates.txt`
- **Enhanced Build System**: Makefile and CMake with automatic BLAS detection (`make` in `atlas_core/` or `cmake ..`)
- **Verification Suite**: `tools/verify_bridge.sh` runs full test suite with metrics threshold enforcement
- **Language Bindings**: Python, Rust, Node.js, Go bindings all updated with context API
- **Deprecation Warnings**: Legacy non-context APIs marked deprecated, will be removed in v0.6
- **CI Integration**: `.github/workflows/bridge.yml` publishes certificates on every PR

### Prereqs
- C toolchain supporting C11
- Python 3.10+
- Optional: OpenBLAS (recommended) and AVX2 for better performance

### Build & test Atlas
```bash
# From repo root
bash tools/verify_bridge.sh
```
If you have your own lift forms:
```bash
echo "A7 5C 39 D2 4E 11" > lift_forms.hex
bash tools/verify_bridge.sh
```
The script compiles the ctx library, runs the full unit suite, and emits `bridge_cert.json`.

### Minimal Python usage
```python
from bindings.python.atlas_bridge._native_ctx import lib, AtlasCtx

ctx = lib.atlas_new()
lib.atlas_set_mode(ctx, 1)          # BRIDGE
lib.atlas_spinlift_enable(ctx, 1)
lib.emit_bridge_cert_ctx(ctx, b"bridge_cert.json")
lib.atlas_free(ctx)
```

---

## Repository Layout
```
repo/
  atlas_bridge_ctx.h
  atlas_bridge_ctx.c
  tests_ctx.c
  tools/
    verify_bridge.sh
    emit_cert.c
    check_metrics.c
  bindings/
    python/
      atlas_bridge/
        _native_ctx.py
  sigmatics/              # symbolic & Sage helpers (planned/optional)
  embeddings/             # dataset adapters + training/eval (planned/optional)
  docs/
    atlas.md
    embeddings.md
    sigmatics.md
  .github/workflows/bridge.yml
  lift_forms.hex          # required for real runs
  P_299_matrix.bin        # optional: exact projector matrix
  co1_gates.txt           # optional: Co1 generator registry
```

---

## Configuration Files
- **`lift_forms.hex`** — 6 hex bytes: `Lx0 Lx1 Lx2  Lz0 Lz1 Lz2` (low 8 bits used when `N_QBITS=8`).
- **`P_299_matrix.bin`** — optional exact linear projector (row‑major `N×N` doubles; `N=12288` or `98304`).
- **`co1_gates.txt`** — optional DSL for registering Co1 gates. `MAT` entries point to dense `N×N` binaries.

---

## Build, Test, and Certificates
- **Build:** `tools/verify_bridge.sh` compiles the library, runs tests, and emits a certificate.
- **CI:** `.github/workflows/bridge.yml` runs the same checks on every PR and uploads `bridge_cert.json` as an artifact.
- **Certificate:** includes mode, spin‑lift, lift forms, projector idempotency, and commutant proxies.

---

## Python Bindings
Bindings live under `bindings/python/atlas_bridge`. The ctx API is loaded from a shared library (`libatlas_bridge_ctx.so`).

- `AtlasCtx*` lifecycle: `atlas_new` → `atlas_free`
- Core ops: `e_apply`, `e_twirl`, `P_class_apply_ctx`, `P_299_apply_ctx`, `co1_apply_ctx`
- Diagnostics: `projector_residual_ctx`, `commutant_probe_ctx`, `emit_bridge_cert_ctx`

> Legacy non‑ctx entry points are deprecated. Use the ctx API exclusively.

---

## Status & Roadmap
- **Done:** ctx API; lift routing via linear forms; in‑block Pauli; `P_class`/`P_299` projectors; Co1 mini‑gates; diagnostics; CI certs; optional BLAS/AVX2.
- **Planned:** full 12‑qubit base block; richer Co1 generator sets; dataset‑specific embeddings; Sigmatics proof runners and exporters.

---

## Contributing
- Open an issue describing your change.
- Keep CI green. New features must add unit tests.
- If you contribute projectors or generators, include a loader and a small verifier.

---

## License
MIT (or project’s chosen license). Add `LICENSE` at repo root.
