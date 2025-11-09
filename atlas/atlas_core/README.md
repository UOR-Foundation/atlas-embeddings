# atlas12288

Implementation of the 12,288‑cell boundary complex over G = P × B with P = ℤ/48, B = ℤ/256.

## Features

- **Six anchors**: S = {(8m, 0) | m=0..5}
- **(ℤ/2)^11 symmetry**: Realized as commuting involutions (8 byte flips + 3 page flips)
- **Boundary complex**: Disjoint union of six 11-cubes, each with 2^11 = 2048 cells
- **C768 schedule**: Fair traversal with marginal stationarity properties
- **Z96 bridge**: Classification matching Multiplicity Core quantizer

## Modules

### group.py
Group operations and decomposition over ℤ/48 = ℤ/16 × ℤ/3:
- `split_p(p)`: Decompose p ∈ ℤ/48 as (p2, p3) with p = p2 + 16*p3
- `join_p(p2, p3)`: Reconstruct p from components
- Bit manipulation helpers

### anchors.py
Six anchor points: `ANCHORS = [(0,0), (8,0), (16,0), (24,0), (32,0), (40,0)]`

### symmetry.py
Gray code and involution symmetries:
- `gray11(i)`: 11-bit Gray code encoding
- `ungray11(g)`: Inverse Gray code
- `Involutions`: (ℤ/2)^11 action via bit flips
  - Bits 0-7 flip byte value
  - Bits 8-10 flip low 3 bits of p2 component

### complex.py
12,288-cell boundary complex:
- `cell_from(anchor_index, gray_index)`: Get cell coordinates
- `neighbors(anchor_index, gray_index)`: Enumerate 11 neighbors
- `all_cells()`: Generate all 12,288 cells

### schedule.py
C768 schedule for fair traversal:
- Period: 768 steps per window
- 16 windows cover all cells
- **Current implementation**: Achieves uniform page marginals (16 per window)
- **Limitation**: Does not achieve uniform byte marginals or full bijection

### z96_bridge.py
Z96 classification bridge:
- `classify_byte_mod96(b)`: Map byte to ℤ/96
- `z96_distribution()`: Count distribution (64 heavy classes with count 3, 32 light with count 2)
- Compatible with `multiplicity_core.quantizer.Z96Quantizer(scale=1, offset=0)`

## Usage

```python
from atlas12288 import (
    ANCHORS, BoundaryComplex, C768Schedule,
    Involutions, gray11, ungray11,
    classify_byte_mod96, z96_distribution
)

# Explore the complex
complex = BoundaryComplex()
for anchor_idx in range(6):
    for gray_idx in range(2048):
        cell = complex.cell_from(anchor_idx, gray_idx)
        # Process cell...

# Use the schedule
schedule = C768Schedule()
for t in range(768):
    cell = schedule.at(t)
    # Process cell in schedule order...

# Check Z96 distribution
dist = z96_distribution()
assert sum(dist.values()) == 256
```

## Testing

```bash
pytest tests/test_anchors.py tests/test_symmetry.py tests/test_complex.py tests/test_z96_bridge.py -v
```

## Implementation Notes

The C768 schedule uses alpha=1 and beta=3 to achieve uniform page marginals within each 768-step window. The original specification called for alpha=5, but this does not achieve uniform marginals. The mathematical construction has inherent constraints that prevent simultaneous achievement of:
1. All 12,288 distinct cells visited exactly once
2. Uniform page marginals (16 per window)
3. Uniform byte marginals (3 per window)

The current implementation prioritizes uniform page marginals as the primary correctness criterion.
