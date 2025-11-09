# Phase 2 — Executor and Evaluator

This directory implements the Phase 2 executor and evaluator for the Sigmatics × Multiplicity runtime pipeline.

## Overview

Phase 2 takes compiled programs from Phase 1 and executes them on signal vectors and relation graphs, computing resonance metrics to validate the theoretical framework.

## Architecture

```
phase2/
├── executor.py               # Main executor and evaluator implementation
├── __init__.py              # Module exports
├── README.md                # This file
└── test_phase2.py           # Test suite (to be added)
```

## Components

### Executor

The `Executor` class implements operations on two parallel paths:

1. **Signal Path (X ∈ ℝ^n)**: 
   - Cyclic rotations R^k
   - Permutations π
   - Residue-class projectors A^{(p^r)} and Δ_{(p^r)}

2. **Relation Path (H)**:
   - Adjacency dict representation
   - Quotient-contraction modulo m
   - Node relabeling under permutations/rotations

### Operations

- `copy` — Comultiplication (identity on signal)
- `rotate` — Cyclic shift by k positions
- `permute` — Apply permutation π
- `projector` — Apply A^{(m)} or Δ_{(m)} projector
- `split` — Record split granularity
- `merge` — Merge split classes
- `modal_enter` — Enter modal context (from quote)
- `modal_exit` — Exit modal context (from evaluate)

### Evaluator

Computes resonance metrics to validate alignment quality:

1. **EVR (Energy Explained Ratio)**: 
   - Energy ratio after projector application
   - Compared against random-permutation baseline

2. **Retrieval Uplift**:
   - R² score for residue-class prediction
   - Baseline comparison with shuffled indices

3. **Relation Consistency**:
   - Jaccard similarity of edge sets
   - Tracks structural preservation through split/merge

## Artifacts

Phase 2 execution produces three output files:

1. **program.json** — Resolved program with n and obligations
2. **trace.jsonl** — Per-operation execution trace
3. **metrics.json** — Summary metrics and baselines

### Trace Format (JSONL)

Each line is a JSON object with:

```json
{
  "op": "projector",
  "note": "UNPROVEN policy",
  "pre": {"energy": 12287.45, "mean": 0.01, "std": 1.0},
  "post": {"energy": 8192.33, "mean": 0.01, "std": 0.82},
  "mark": {"p": 3, "r": 1, "m": 3, "mode": "Δ"},
  "dt_ms": 15
}
```

### Metrics Format

```json
{
  "n": 12288,
  "last_m": 3,
  "evr_A": 0.333,
  "evr_Delta": 0.667,
  "baseline_evr_A": {"mean": 0.333, "std": 0.001},
  "retrieval_uplift": {
    "r2": 0.0,
    "baseline_mean": 0.0,
    "baseline_std": 0.0
  },
  "relation_consistency": {
    "jaccard_orig_split": 0.0,
    "jaccard_split_merge": 1.0,
    "jaccard_orig_merge": 0.0,
    "|E0|": 12288.0,
    "|Es|": 3.0,
    "|Em|": 3.0
  }
}
```

## Usage

### Command Line

```bash
# Execute a compiled program
python -m sigmatics.phase2.executor \
  --program compiled_program.json \
  --outdir results/ \
  --seed 42
```

### Python API

```python
from sigmatics.phase2 import run
import json

# Load compiled program from Phase 1
with open("compiled_program.json") as f:
    program = json.load(f)

# Execute and compute metrics
metrics = run(program, outdir="results/", seed=42)

print(f"EVR (A): {metrics['evr_A']:.3f}")
print(f"EVR (Δ): {metrics['evr_Delta']:.3f}")
print(f"Baseline: {metrics['baseline_evr_A']['mean']:.3f} ± {metrics['baseline_evr_A']['std']:.3f}")
```

## Integration with Phase 1

Phase 2 consumes the output of Phase 1 compilation:

```python
from sigmatics.phase1 import compile_program, Policies, lower
from sigmatics.phase2 import run

# Phase 1: Compile Sigmatics to Multiplicity
script = 'mark@{"p":3,"r":1}; rho[17]; copy;'
lowered = lower(script, src_name="example.sig")
program = compile_program(lowered["lowered"], Policies())

# Phase 2: Execute and evaluate
metrics = run(program, outdir="results/", seed=42)
```

## Constants

- **n = 12,288** — Index dimension (2^12 × 3^1)
- **PAGE_SIZE = 256** — Memory page size
- **PAGES = 48** — Number of pages (n / PAGE_SIZE)

## Policies (UNPROVEN)

Phase 2 inherits policy decisions from Phase 1:

- `primePolicy(d)` — Default prime p = 3
- `levelPolicy(d)` — Default level r = 1
- `markMode(d)` — Default mode = "Δ"
- `permPolicy(ctx, n)` — Default permutation = identity
- `arityPolicy(ctx)` — Default arity = 2

All policies are marked **UNPROVEN** and tracked in obligations.

## Admissibility

Operations on projectors require **admissibility**: p^r must divide n.

For n = 12,288 = 2^12 × 3^1:

- ✓ Admissible: (2,1), (2,2), ..., (2,12), (3,1)
- ✗ Not admissible: (5,1), (2,13), (3,2), ...

## Graph Representation

Relations are represented as adjacency dictionaries:

```python
H = {
    0: [1],
    1: [2],
    2: [0],
    ...
}
```

Initial graph: Ring graph (cyclic chain) with n nodes.

### Quotient Graph

Quotient by modulus m contracts nodes by residue:

```python
# Original: 0 → 1 → 2 → 3 → 0
# Quotient mod 2: 0 → 1 → 0
```

## Testing

```bash
# Run Phase 2 tests
python -m pytest sigmatics/phase2/test_phase2.py -v

# Test with example program
cd sigmatics/phase2
python executor.py --program ../../examples/example_program.json --outdir /tmp/phase2_test
```

## Limitations

### Current Limitations

- **Policies UNPROVEN**: Default implementations lack mathematical verification
- **Minimal split/merge**: No true inverse lift for merge operation
- **No parallelism**: Sequential execution only
- **Fixed dimension**: Hard-coded n = 12,288

### Future Work

1. **Policy verification**: Mathematical proofs for all policy functions
2. **Full split/merge**: Implement proper inverse lift for merge
3. **Parallel execution**: Support parallel composition from Sigmatics
4. **Dynamic dimension**: Support variable n from program
5. **Advanced metrics**: Additional resonance and alignment measures
6. **Optimization**: Operator fusion and dead code elimination

## Status Summary

| Component | Status | Notes |
|-----------|--------|-------|
| Executor | ✓ Complete | All operations implemented |
| Signal path | ✓ Complete | R^k, π, A, Δ operators |
| Relation path | ✓ Complete | Graph operations |
| JSONL trace | ✓ Complete | Per-op stats logged |
| Evaluator | ✓ Complete | All metrics computed |
| EVR metrics | ✓ Complete | With baseline comparison |
| Retrieval uplift | ✓ Complete | R² with baseline |
| Relation consistency | ✓ Complete | Jaccard similarity |
| CLI tool | ✓ Complete | Full execution pipeline |
| Policies | ⚠ UNPROVEN | Need verification |
| Split/merge | ⚠ Minimal | Full lift not implemented |

## References

- **Phase 1**: Front-end compiler and lowering
- **Multiplicity Runtime**: ACE projectors and contractive updates
- **Sigmatics Algebra**: Seven generators and 96-class structure

---

**Version**: 0.1.0  
**Status**: Phase 2 implementation complete, policies UNPROVEN  
**Date**: 2025-11-09
