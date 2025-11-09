# Phase 3 — Validation & KPIs

This directory implements Phase 3 of the Sigmatics × Multiplicity pipeline: validation of unit properties, round-trip integrity checks, and KPI computation.

## Overview

Phase 3 combines functionality from Phase 1 (lowering & compilation) and Phase 2 (execution) with additional validation and metrics computation to provide comprehensive quality assurance for the Sigmatics pipeline.

## Architecture

```
phase3/
├── phase3.py                 # Main validation and KPI implementation
├── __init__.py              # Module exports
├── README.md                # This file
├── test_phase3.py           # Test suite
└── demo.py                  # Full pipeline demonstration
```

## Components

### Unit Property Validation

Phase 3 validates fundamental mathematical properties:

1. **Projector Idempotence**: A² = A and Δ² = Δ
   - Validates that projectors A and Δ are truly idempotent
   - Tests across multiple random seeds and admissible moduli

2. **Non-Commutation Witness**: A_p W_q ≠ W_q A_p
   - Demonstrates that certain permutations don't commute with projectors
   - Uses deterministic within-page stride permutation W^(q)

3. **Rotation Closure**: R^n = Identity
   - Validates that n rotations return to original state
   - Tests on random vectors

4. **Split-Merge Round-trip**: split ∘ merge preservation
   - Checks structural consistency through split/merge operations
   - Validates edge counts in contracted graphs

### Round-Trip Integrity

Tests the pipeline's ability to reconstruct source from compiled form:

- Source → Lowered → Compiled → Pretty-print → Lowered'
- Validates hash equality and structural consistency
- Only tests supported subset (excludes permute operations)

### KPI Computation

Computes key performance indicators:

1. **Resonance Uplift**: EVR_A - Baseline_mean
   - Measures alignment quality vs. random baseline
   
2. **Wall Time**: Compilation and execution timing
   
3. **Determinism Rate**: Hash stability under formatting variations
   
4. **Obligation Counts**: Tracking UNPROVEN policies and violations

## Artifacts

Phase 3 produces six output files in the specified `--outdir`:

1. **program.json** — Resolved program (if compiled from source)
2. **trace.jsonl** — Per-operation execution trace
3. **metrics.json** — EVR, baseline, and relation metrics
4. **validation_report.json** — Unit property test results
5. **roundtrip.json** — Round-trip integrity check results
6. **kpis.json** — Summary KPIs

### Validation Report Format

```json
{
  "projector_idempotence": {
    "A": [
      {"m": 3, "max_abs_err": 1.4210854715202004e-14}
    ],
    "Delta": [
      {"m": 3, "max_abs_err": 1.4210854715202004e-14}
    ]
  },
  "noncommutation_witness": {
    "p": 3,
    "q": 5,
    "noncommute_trials": 5,
    "trials": 5,
    "max_diff": 0.573,
    "min_diff": 0.512
  },
  "rotation_closure": {
    "R^n_identity_max_abs_err": 0.0
  },
  "split_merge_roundtrip": {
    "contracted_edges": 3,
    "roundtrip_equal": true
  }
}
```

### KPIs Format

```json
{
  "n": 12288,
  "resonance_uplift_vs_baseline": 0.0,
  "evr_A": 0.333,
  "baseline_evr_A_mean": 0.333,
  "wall_time_compile_s": 0.001,
  "wall_time_exec_s": 0.023,
  "determinism_rate_lowering": 1.0,
  "obligation_counts": {
    "UNPROVEN": 5,
    "VIOLATION": 0
  },
  "noncommute_trials": 5,
  "noncommute_trials_total": 5
}
```

## Usage

### Command Line

Phase 3 can accept either a compiled program (from Phase 1) or a source file:

```bash
# From compiled program
python -m sigmatics.phase3.phase3 \
  --program compiled_program.json \
  --outdir results/ \
  --seed 42

# From source (Phase 1 + 2 + 3 in one go)
python -m sigmatics.phase3.phase3 \
  --source example.sig \
  --outdir results/ \
  --seed 42
```

### Python API

```python
from sigmatics.phase3 import (
    lower, compile_program, Policies,
    exec_program, unit_projector_idempotence,
    unit_noncommutation_witness, roundtrip_check,
    determinism_rate, obligation_counts
)

# Compile from source
script = 'mark@{"p":3,"r":1,"mode":"delta"}; rho[7]; copy;'
lowered = lower(script, src_name="example.sig")
program = compile_program(lowered["lowered"], Policies())

# Execute and get metrics
metrics = exec_program(program, outdir="results/", seed=42)

# Unit properties
idempotence = unit_projector_idempotence(trials=5)
noncommute = unit_noncommutation_witness(p=3, q=5, trials=5)

# Round-trip check
rt = roundtrip_check(script)

# KPIs
det_rate = determinism_rate(script, variants=20)
oblig = obligation_counts(program)

print(f"Resonance uplift: {metrics['evr_A'] - metrics['baseline_evr_A']['mean']:.3f}")
print(f"Determinism rate: {det_rate:.1%}")
print(f"UNPROVEN obligations: {oblig['UNPROVEN']}")
```

## Constants

- **n = 12,288** — Index dimension (2^12 × 3^1)
- **PAGE_SIZE = 256** — Memory page size
- **PAGES = 48** — Number of pages (n / PAGE_SIZE)

## Witness Permutation W^(q)

The non-commutation witness uses a deterministic permutation:

- Within each 256-byte page, maps offset → (offset × q) mod 256
- Requires q coprime to 256 (e.g., q = 5)
- Preserves page boundaries while creating non-trivial permutation

## Integration with Phases 1 & 2

Phase 3 embeds subsets of Phase 1 and Phase 2 for standalone operation:

**Phase 1 Subset**:
- Tokenization and parsing
- Deterministic lowering with SHA-1 hashing
- Compilation with Π-first reduction
- Policy application and obligation tracking

**Phase 2 Subset**:
- Signal path operations (rotate, permute, project)
- Relation path operations (graph quotients)
- Execution trace logging
- EVR and baseline metrics

This allows Phase 3 to be used as:
1. **Standalone validator**: `--source example.sig`
2. **Phase 1 output consumer**: `--program compiled.json`

## Policies (UNPROVEN)

Phase 3 inherits and tracks all UNPROVEN policies:

- `primePolicy(d)` — Default p = 3
- `levelPolicy(d)` — Default r = 1
- `markMode(d)` — Default mode = "Δ"
- `permPolicy(ctx, n)` — Default permutation = identity
- `arityPolicy(ctx)` — Default arity = 2

All policies are marked **UNPROVEN** in obligations and output.

## Admissibility

Projector operations require **admissibility**: p^r must divide n.

For n = 12,288 = 2^12 × 3^1:

- ✓ Admissible: (2,1), (2,2), ..., (2,12), (3,1)
- ✗ Not admissible: (5,1), (2,13), (3,2), ...

Phase 3 inherits admissibility checks from Phase 1 compilation.

## Testing

```bash
# Run Phase 3 tests
python -m pytest sigmatics/phase3/test_phase3.py -v

# Test with example source
cd sigmatics/phase3
python phase3.py --source ../phase1/example.sig --outdir /tmp/phase3_test --seed 42
```

## Limitations

### Current Limitations

- **Pretty-print round-trip**: Only works for supported subset (excludes permute ops)
- **Policies UNPROVEN**: Default implementations lack mathematical verification
- **Fixed dimension**: Hard-coded n = 12,288
- **Sequential execution**: No parallelism

### Future Work

1. **Full round-trip**: Support all operations including permute
2. **Policy verification**: Mathematical proofs for all policies
3. **Dynamic dimension**: Support variable n
4. **Advanced validation**: Additional unit properties
5. **Performance profiling**: Detailed timing breakdowns
6. **Comparative benchmarks**: Cross-implementation validation

## Status Summary

| Component | Status | Notes |
|-----------|--------|-------|
| Unit properties | ✓ Complete | 4 fundamental properties validated |
| Non-commutation witness | ✓ Complete | Deterministic W^(q) construction |
| Round-trip checks | ⚠ Partial | Supported subset only |
| KPI computation | ✓ Complete | All metrics implemented |
| Phase 1 integration | ✓ Complete | Embedded lowering & compilation |
| Phase 2 integration | ✓ Complete | Embedded execution & metrics |
| CLI tool | ✓ Complete | Full validation pipeline |
| Policies | ⚠ UNPROVEN | Need verification |

## References

- **Phase 1**: Front-end compiler and lowering
- **Phase 2**: Executor and evaluator
- **Multiplicity Runtime**: ACE projectors and contractive updates
- **Sigmatics Algebra**: Seven generators and 96-class structure

---

**Version**: 0.1.0  
**Status**: Phase 3 implementation complete, policies UNPROVEN  
**Date**: 2025-11-09
