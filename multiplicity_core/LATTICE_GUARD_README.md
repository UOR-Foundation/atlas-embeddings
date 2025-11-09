# Atlas Boundary Lattice Guard

Enforcement of the 96×12,288 Atlas boundary substrate addressing with (Z/2)^11 subgroup action.

## Overview

The lattice guard system provides:

1. **Boundary Lattice** - Core 96×12,288 addressing with 48×256 boundary folding
2. **Lattice Guard** - Context validation and enrichment for step scheduling
3. **Subgroup Certificate** - Verification of (Z/2)^11 group structure
4. **Audit Runner** - Fairness and compliance checking for ledger entries

## Structure

### Constants

- **Classes**: 96 resonance classes
- **Anchors**: 6 anchor points for orbit decomposition
- **Orbit**: 2048 elements per orbit (2^11 from (Z/2)^11)
- **Coordinates**: 12,288 total coordinates (48 × 256)
- **Fold**: 48 rows × 256 columns boundary grid

### Addressing

The system maps between three coordinate systems:

1. **(class, coord)** - Class identifier [0,95] and linear coordinate [0,12287]
2. **(class, anchor, v_bits)** - Class with anchor [0,5] and orbit element [0,2047]
3. **(class, row, col)** - Class with boundary fold position (row [0,47], col [0,255])

All three representations are equivalent and can be converted between.

## Usage

### Generate Subgroup Certificate

```python
from multiplicity_core.boundary_lattice import save_certificate

save_certificate("subgroup_certificate.json")
```

Or use the command-line tool:

```bash
python -m multiplicity_core.certify_subgroup
```

This generates a JSON certificate with:
- Group structure verification
- Orbit properties
- Anchor coordinates
- Checksum for integrity

### Guard Step Contexts

```python
from multiplicity_core.lattice_guard import guard_context

# Using linear coordinate
ctx = {"class": 5, "coord": 777}
guarded = guard_context(ctx)
# Returns: {'class': 5, 'coord': 777, 'anchor': 0, 'v_bits': 777, 'row': 3, 'col': 9}

# Using anchor and v_bits
ctx = {"class": 10, "anchor": 2, "v_bits": 100}
guarded = guard_context(ctx)
# Returns: {'class': 10, 'anchor': 2, 'v_bits': 100, 'coord': 4196, 'row': 16, 'col': 100}
```

The guard:
- Validates all parameters are in bounds
- Converts between coordinate systems
- Enriches context with all representations
- Preserves additional context fields

### Audit a Ledger

```bash
python -m multiplicity_core.audit_runner \
  --schedule atlas_schedule.toml \
  --bundle multiplicity_core/audit_bundle.toml \
  --ledger my_ledger.json
```

The auditor checks:
- **Class fairness**: Distribution across 96 classes within tolerance
- **Anchor fairness**: Distribution across 6 anchors within tolerance
- **PETC compliance**: Every committed ace_step has a corresponding petc entry
- **Audit intervals**: Audit entries at expected frequencies (default: every 768 steps)

### Audit Bundle Configuration

Edit `audit_bundle.toml`:

```toml
[policy]
class_skew_tolerance = 1      # Max deviation from expected class count
anchor_skew_tolerance = 1     # Max deviation from expected anchor count

[intervals]
audit_every = 768             # Expected audit entry frequency

[required_kinds]
per_step = ["ace_step", "petc"]  # Entry kinds that must appear

[indexing]
classes = 96
anchors = 6
fold_rows = 48
fold_cols = 256
```

## Mathematical Structure

### Linear Indexing

The mapping `(anchor, v_bits) ↔ coord_idx` is:

```
coord_idx = anchor × 2048 + v_bits
anchor = coord_idx ÷ 2048
v_bits = coord_idx mod 2048
```

### Boundary Folding

The 48×256 fold uses row-major ordering:

```
row = coord_idx ÷ 256
col = coord_idx mod 256
coord_idx = row × 256 + col
```

### Subgroup Action

The group U ≅ (Z/2)^11 acts on each orbit:

```
(anchor, v_bits) · u = (anchor, (v_bits + u) mod 2048)
```

Properties:
- **Free**: No fixed points except identity (u=0)
- **Transitive**: Reaches all 2048 orbit elements
- **Disjoint**: Six orbits partition all 12,288 coordinates

## Testing

Run the test suite:

```bash
# From repository root or /tmp to avoid conftest issues
python -m pytest tests/test_boundary_lattice.py tests/test_lattice_guard.py tests/test_audit_runner.py -v
```

All tests verify:
- Linear indexing round-trips
- Boundary fold consistency
- Address validation
- Subgroup action properties
- Context guarding
- Audit fairness checking

## Example

See `examples/lattice_guard_example.py` for a complete workflow demonstration:

```bash
python examples/lattice_guard_example.py
```

This generates:
- `example_subgroup_certificate.json` - Group structure verification
- `example_ledger.json` - Fair ledger with 768 steps
- `example_audit_report.json` - Compliance report

## Integration

To integrate with the scheduler:

```python
from multiplicity_core.scheduler import executor, load_schedule
from multiplicity_core.ledger import Ledger
from multiplicity_core.lattice_guard import guard_context

ledger = Ledger()
schedule = load_schedule("atlas_schedule.toml")

# Guard contexts before or after ACE steps
for step in range(768):
    c = step % 96
    a = step % 6
    
    ctx = {"class": c, "anchor": a, "v_bits": 0, "step": step}
    guarded_ctx = guard_context(ctx)
    
    # Use guarded_ctx in ledger entries
    ledger.append({
        "kind": "ace_step",
        "context": guarded_ctx,
        "status": "committed"
    })
```

## Files

- **multiplicity_core/boundary_lattice.py** - Core addressing functions
- **multiplicity_core/lattice_guard.py** - Context validation and guarding
- **multiplicity_core/certify_subgroup.py** - Certificate generation CLI
- **multiplicity_core/audit_runner.py** - Ledger auditing CLI
- **multiplicity_core/audit_bundle.toml** - Audit policy configuration
- **tests/test_boundary_lattice.py** - Boundary lattice tests
- **tests/test_lattice_guard.py** - Lattice guard tests
- **tests/test_audit_runner.py** - Audit runner tests
- **examples/lattice_guard_example.py** - Complete usage example

## Limits

- Subgroup certificate is constructive verification, not a formal cryptographic proof
- Auditor checks pragmatic fairness, not full Byzantine fault tolerance
- Linear indexing assumes the packing used in boundary_lattice.py

## References

- `atlas/aep/petc.py` - Original 48×256 boundary group definition
- `atlas/aep/ace_runtime.py` - ACE runtime with lattice structure
- `multiplicity_core/scheduler.py` - Round-robin scheduling
- `multiplicity_core/ledger.py` - Append-only ledger
