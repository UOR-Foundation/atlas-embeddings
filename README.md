# Atlas Hologram Monorepo

**Components:** Atlas • Embeddings • Sigmatics

This repository hosts a cohesive stack for moonshine-inspired computation, bringing together a fast classical/bridge **Atlas** core, **Embeddings** for mapping data into Atlas spaces, and **Sigmatics** for symbolic + programmatic workflows.

## Quick Start

### Prerequisites
- C toolchain supporting C11
- Python 3.10+
- Optional: OpenBLAS and AVX2 for better performance

### Build Everything

```bash
make all
```

### Build Individual Components

```bash
make atlas-build      # Build Atlas core
make atlas-test       # Test Atlas
make atlas-cert       # Generate certificate
```

### Verify Installation

```bash
bash atlas/tools/verify_bridge.sh
```

This runs the full Atlas test suite and generates `bridge_cert.json`.

## Repository Structure

```
atlas-hologram/
├── atlas/               # Atlas core (C library + bindings)
│   ├── src/            # C implementation
│   ├── include/        # Public headers
│   ├── tests/          # Unit tests
│   ├── tools/          # Build/verify scripts
│   ├── bindings/       # Language bindings (Python, Rust, Node, Go)
│   ├── artifacts/      # Optional: lift_forms.hex, P_299_matrix.bin, co1_gates.txt
│   └── README.md
│
├── embeddings/         # Data embedding layer (planned)
│   ├── src/
│   ├── tests/
│   ├── examples/
│   └── README.md
│
├── sigmatics/          # Symbolic algebra layer (planned)
│   ├── src/
│   ├── tests/
│   ├── examples/
│   └── README.md
│
├── tools/
│   └── copilot_repo_setup.md  # This bootstrap script
│
├── Makefile            # Root build orchestration
└── README.md          # This file
```

## Components

### Atlas
The numerical/runtime core providing:
- Context-based C API for bridge operations
- Exact 2-group actions with XOR lift routing
- P_class and P_299 projectors
- Co1 gate support
- Certificate generation with metric verification

See [atlas/README.md](atlas/README.md) for details.

### Embeddings
Dataset adapters and feature encoders for mapping data into Atlas spaces.

🚧 Planned component - stubs available.

### Sigmatics
Symbolic algebra and orchestration layer using Sage/Python.

🚧 Planned component - stubs available.

## Makefile Targets

Build targets:
- `make all` - Build all components
- `make atlas-build` - Build Atlas library
- `make atlas-test` - Run Atlas tests
- `make atlas-cert` - Generate bridge certificate
- `make clean` - Clean all build artifacts

## Configuration Files

- **`atlas/artifacts/lift_forms.hex`** - 6 hex bytes for lift routing (required)
- **`atlas/artifacts/P_299_matrix.bin`** - Optional exact projector matrix
- **`atlas/artifacts/co1_gates.txt`** - Optional Co1 generator config

## CI/CD

The repository includes GitHub Actions workflows:
- `.github/workflows/atlas_bridge.yml` - Builds, tests, and publishes certificates

## Certificate

Atlas generates `bridge_cert.json` with:
- Configuration flags (mode, BLAS, AVX2)
- Projector idempotency metrics
- Commutant dimension probes

Thresholds:
- P_class idempotency: ≤ 1e-8
- P_299 idempotency: ≤ 1e-8
- Commutant effective dim: < 1.5

## License

MIT (see LICENSE file)

## Contributing

1. Open an issue describing your change
2. Keep CI green
3. Add tests for new features
4. Follow existing code style

