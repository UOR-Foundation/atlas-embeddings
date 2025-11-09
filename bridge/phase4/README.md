# Phase 4 — Three-Week Timeline & Ship Plan

**Status**: ✅ Complete  
**Version**: v0.1.0  
**Date**: 2025-11-09

## Overview

Phase 4 consolidates the Sigmatics × Multiplicity bridge (Phases 1-3) into a complete, reproducible release package. This represents the culmination of the three-week ship plan with all required artifacts, CLI workflows, and KPI reports.

## Three-Week Timeline

### Week 1 — Indexing, Schemas, Π, R/T
✅ **Complete** (leverages Phase 1)

- Index size fixed: n = 12,288 (48 × 256 = 2^12 × 3^1)
- Index map published with default belt handling
- JSON schemas finalized
- Π operations (A, Δ) with admissibility checks
- R/T mapping (ρ/τ → rotate operations)

### Week 2 — W^(p)_π, split/merge, logging + metrics
✅ **Complete** (leverages Phase 2-3)

- W^(p)_π deterministic permutation families
- Split/merge on H with quotient round-trip
- Logging and metrics extended
- Non-commutation witness validated

### Week 3 — Resonance metrics, CLI, KPIs report
✅ **Complete** (this module)

- CLI workflows operational
- KPI consolidation and reporting
- Markdown report auto-generation
- Pretty-print round-trip (supported subset)
- Obligation tally system
- Release packaging

## Components

### Main Module: `phase4.py`

The core implementation providing:

1. **Index map examples generation**
   - Demonstrates indexing policy
   - Corner cases and boundaries
   - Inverse mapping examples

2. **KPI consolidation**
   - Resonance uplift vs baseline
   - Wall times (compile + exec)
   - Determinism rate
   - Obligation counts
   - Unit test summaries

3. **Report generation**
   - Auto-generated markdown report
   - Executive summary
   - Week-by-week deliverables
   - Reproducibility instructions
   - Artifact inventory

4. **Full pipeline orchestration**
   - Phase 1: Lower and compile
   - Phase 2: Execute and evaluate
   - Phase 3: Validate and compute KPIs
   - Phase 4: Generate index examples and report

### CLI Wrappers

#### `phase2_executor_evaluator.py`

Convenience wrapper for Phase 2 execution:

```bash
python phase2_executor_evaluator.py --program compiled.json --outdir results/
```

Outputs:
- `trace.jsonl` — Per-operation execution trace
- `metrics.json` — EVR, baseline, relation metrics

#### `phase3_validation_kpis.py`

Convenience wrapper for Phase 3 validation:

```bash
python phase3_validation_kpis.py --program compiled.json --source example.sig --outdir results/
```

Outputs:
- `validation_report.json` — Unit property tests
- `roundtrip.json` — Round-trip integrity checks
- `kpis.json` — Consolidated KPI summary

## Usage

### Full Pipeline

Run the complete Phase 1-2-3-4 pipeline:

```bash
python phase4.py --source ../../sigmatics/phase1/example.sig --outdir output/ --seed 42 --verbose
```

This generates all artifacts:
- `compiled_program.json`
- `trace.jsonl`
- `metrics.json`
- `validation_report.json`
- `roundtrip.json`
- `kpis.json`
- `index_map_examples.json`
- `report.md`

### Index Map Examples Only

Generate just the index map examples:

```bash
python phase4.py --index-only --outdir output/
```

### Step-by-Step

Run phases individually:

```bash
# Phase 1: Compile
cd ../../sigmatics/phase1
python sigmaticsc.py example.sig -o compiled_program.json

# Phase 2: Execute
cd ../../../bridge/phase4
python phase2_executor_evaluator.py --program ../../sigmatics/phase1/compiled_program.json --outdir results/

# Phase 3: Validate
python phase3_validation_kpis.py --program ../../sigmatics/phase1/compiled_program.json --source ../../sigmatics/phase1/example.sig --outdir results/

# Phase 4: Generate report
python phase4.py --source ../../sigmatics/phase1/example.sig --outdir results/
```

## Artifacts

Phase 4 generates the following artifacts:

### Core Artifacts (from Phases 1-3)

1. **`schemas/*.json`** — JSON Schemas
   - `sigmatics_word.schema.json`
   - `multiplicity_word.schema.json`
   - `program.schema.json`

2. **`compiled_program.json`** — Compiled program
   - Multiplicity runtime instructions
   - Obligations tracking

3. **`trace.jsonl`** — Execution trace
   - Per-operation log
   - Pre/post energy, dt_ms

4. **`metrics.json`** — Execution metrics
   - EVR (Explained Variance Ratio)
   - Baseline comparisons
   - Relation metrics

5. **`validation_report.json`** — Unit tests
   - Projector idempotence
   - Non-commutation witness
   - Rotation closure
   - Split-merge round-trip

6. **`roundtrip.json`** — Round-trip checks
   - Hash equality
   - Supported subset validation

### Phase 4 Artifacts

7. **`index_map_examples.json`** — Index mapping examples
   - Demonstrates indexing policy
   - Corner cases and boundaries

8. **`kpis.json`** — Consolidated KPIs
   - Resonance uplift
   - Determinism rate
   - Obligation counts
   - Unit test summary

9. **`report.md`** — Auto-generated report
   - Executive summary
   - KPI results
   - Week-by-week deliverables
   - Reproducibility instructions

## KPIs

The following KPIs are computed and tracked:

| KPI | Target | Status |
|-----|--------|--------|
| Resonance uplift vs baseline | ≥ 0 | ✓ |
| Lowering determinism rate | ≥ 0.95 | ✓ |
| VIOLATION obligations | 0 | ✓ |
| Unit tests | All pass | ✓ |

### Unit Tests

1. **Projector idempotence**: A² = A, Δ² = Δ
2. **Rotation closure**: R^n = Identity
3. **Non-commutation witness**: A_p W_q ≠ W_q A_p (max diff > 1e-9)
4. **Split-merge round-trip**: Quotient consistency

## Constants

- **n = 12,288** — Index dimension (2^12 × 3^1)
- **PAGE_SIZE = 256** — Memory page size
- **PAGES = 48** — Number of pages

## Indexing Policy

Default mode (v0): `index(page, belt, offset) = page*256 + offset`

- Belt treated as metadata (not encoded)
- No padding in v0
- Bijective mapping with inverse

## Obligations

All policies are marked **UNPROVEN** and tracked:

- `primePolicy(d) → p` (default: 3)
- `levelPolicy(d) → r` (default: 1)
- `permPolicy(d) → π` (default: identity)
- `arityPolicy` (default: 2)
- `markMode` (default: "Δ")

**VIOLATION count must be 0** in shipped examples.

## Scope

### In Scope (v0)

✓ Indexing policy  
✓ JSON schemas  
✓ Π operations (A/Δ)  
✓ R/T mapping  
✓ W^(p)_π deterministic families  
✓ Split/merge on H  
✓ Logging and metrics  
✓ CLI workflows  
✓ KPIs and reporting

### Out of Scope (v0)

✗ Performance tuning  
✗ Non-identity permPolicy beyond fixed families  
✗ Advanced modal semantics  
✗ Padding semantics

## Exit Criteria

All exit criteria met:

✓ All unit tests pass  
✓ Lowering determinism rate ≥ 0.95  
✓ Non-commutation witness max diff > 1e-9  
✓ Split-merge round-trip verified  
✓ Zero VIOLATION in shipped examples  
✓ Reproducible from clean environment

## Prerequisites

- Python 3.11+
- NumPy
- NetworkX
- jsonschema

Install:
```bash
pip install numpy networkx jsonschema
```

## Testing

Run the full pipeline test:

```bash
# From repository root
cd bridge/phase4
python test_phase4.py
```

Or test components individually:

```bash
# Test Phase 1
cd ../../sigmatics/phase1
python test_phase1.py

# Test Phase 3
cd ../phase3
python test_phase3.py
```

## Directory Structure

```
bridge/
└── phase4/
    ├── __init__.py                      # Package exports
    ├── phase4.py                        # Main implementation
    ├── phase2_executor_evaluator.py    # Phase 2 wrapper
    ├── phase3_validation_kpis.py       # Phase 3 wrapper
    ├── README.md                        # This file
    └── test_phase4.py                   # Test suite
```

## Integration

Phase 4 integrates with existing phases:

- **Phase 1**: `sigmatics/phase1/` (lowering, compilation)
- **Phase 2**: `sigmatics/phase2/` (execution, evaluation)
- **Phase 3**: `sigmatics/phase3/` (validation, KPIs)

All imports are designed to work from the bridge directory or as standalone modules.

## Reproducibility

### From Clean Environment

```bash
# Clone repository
git clone https://github.com/CitizenGardens-org/Hologram-APEX.git
cd Hologram-APEX

# Install dependencies
pip install numpy networkx jsonschema

# Run full pipeline
cd bridge/phase4
python phase4.py --source ../../sigmatics/phase1/example.sig --outdir output/ --seed 42 --verbose

# Check artifacts
ls -la output/
```

### Expected Output

```
output/
├── compiled_program.json
├── trace.jsonl
├── metrics.json
├── validation_report.json
├── roundtrip.json
├── kpis.json
├── index_map_examples.json
└── report.md
```

## Versioning

- **v0.1.0**: Initial release
  - All Week 1-3 deliverables complete
  - Minimal v0 scope honored
  - Policies marked UNPROVEN

## Future Work

1. **Policy verification**: Mathematical proofs
2. **Full round-trip**: Support all operations
3. **Padding semantics**: Define and implement
4. **Performance tuning**: Optimize critical paths
5. **Advanced modal semantics**: Beyond quote/evaluate
6. **Lean/Coq formalization**: Machine-checked proofs

## References

- **Problem Statement**: Phase 4 — Three-Week Timeline & Ship Plan
- **Phase 1 README**: `sigmatics/phase1/README.md`
- **Phase 2 README**: `sigmatics/phase2/README.md`
- **Phase 3 README**: `sigmatics/phase3/README.md`
- **Phase 0 Summary**: `PHASE0_SUMMARY.md`

## License

See repository `LICENSE` file.

## Contact

UOR Foundation  
Hologram APEX Project

---

**Generated**: 2025-11-09  
**Status**: ✅ Complete and Verified
