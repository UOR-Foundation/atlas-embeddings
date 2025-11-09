# Ethics Commutation AEP

Atlas-Embedding Proof system that validates ethical compute invariants.

## Overview

The `ethics_commutation` AEP verifies two critical invariants:

1. **Commutation**: `[M, E_α] = M·E_α - E_α·M` has norm ≤ `atol` (default: 1e-12)
2. **Forbidden Channels**: All Δ-channels matching forbidden patterns have magnitude ≤ `atol`

## Quick Start

### Prerequisites

- Python 3.10+
- numpy

Install dependencies:
```bash
pip install numpy
```

### Running

```bash
cd aep_ethics_commutation
python3 runner.py
```

Exit codes:
- `0`: All invariants satisfied (PASS)
- `2`: Invariant violation (FAIL)

Results are written to `out/result.json`.

## Configuration

### aep.toml

Main configuration file defining:
- **claim**: AEP metadata (id, kind, description)
- **constraints**: Tolerance settings (`atol`)
- **evidence**: Paths to evidence files (delta_channels.json, optional resonance snapshots)
- **forbidden**: Patterns for forbidden Δ-channels
- **backend**: Array backend (numpy or cupy)

### kernel.atlas

Kernel configuration defining:
- **operators**: Paths to M.npy and E_alpha.npy operator matrices
- **probes**: Forbidden channel patterns
- **context**: Optional state identifiers

## File Structure

```
aep_ethics_commutation/
├── aep.toml              # Main configuration
├── kernel.atlas          # Kernel configuration
├── runner.py             # Main runner script
├── ops/                  # Operator matrices
│   ├── M.npy            # Primary operator M
│   └── E_alpha.npy      # Secondary operator E_α
├── evidence/            # Evidence files
│   └── delta_channels.json  # Δ-channel measurements
└── out/                 # Output directory
    └── result.json      # Execution results
```

## Evidence Format

### delta_channels.json

Dictionary mapping channel names to values:

```json
{
  "channel_a": 0.0,
  "Δ/forbidden_1": 0.0,
  "forbidden/test": 0.0,
  "allowed/channel": 1e-15
}
```

### Operator Matrices

Numpy `.npy` files containing square matrices. Must be compatible dimensions for matrix multiplication.

Example (creating diagonal matrices):
```python
import numpy as np
M = np.diag([1.0, 2.0, 3.0, 4.0])
E_alpha = np.diag([0.5, 1.5, 2.5, 3.5])
np.save("ops/M.npy", M)
np.save("ops/E_alpha.npy", E_alpha)
```

## GPU Support

Use CuPy for GPU acceleration:

```bash
pip install cupy
AEP_ARRAY_BACKEND=cupy python3 runner.py
```

Falls back to numpy if CuPy is unavailable.

## Output Format

```json
{
  "status": "pass",
  "ok_commutation": true,
  "ok_forbidden_channels": true,
  "comm_norm": 0.0,
  "atol": 1e-12,
  "delta_violations": [],
  "res_delta_norm": null,
  "proof_id": "9bd1da95...",
  "verified": true
}
```

Fields:
- `status`: Overall status ("pass" or "fail")
- `ok_commutation`: Whether commutator norm ≤ atol
- `ok_forbidden_channels`: Whether forbidden channels are zero
- `comm_norm`: Computed commutator norm
- `atol`: Absolute tolerance used
- `delta_violations`: List of channel violations (empty if pass)
- `res_delta_norm`: Optional resonance delta norm
- `proof_id`: Deterministic proof identifier
- `verified`: Whether proof verification succeeded

## Forbidden Patterns

Patterns use glob-style matching:
- `Δ/*`: Matches all channels starting with "Δ/"
- `forbidden/*`: Matches all channels starting with "forbidden/"
- `*_restricted`: Matches all channels ending with "_restricted"

Configure in `aep.toml` under `[forbidden]` or `kernel.atlas` under `[probes]`.

## Integration

The runner uses `ProofManager` from `multiplicity_core` for deterministic proof generation and verification. Proofs are local hashes and not cryptographically secure by default.

To integrate with blockchain or external verifiers, replace the `ProofManager.submit_on_chain()` stub with your submission logic.
