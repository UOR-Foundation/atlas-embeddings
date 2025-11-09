# Phase 0 — Hard Constraints Implementation

This document describes the Phase 0 implementation for the Hologram APEX project, establishing the minimal, testable bridge between Sigmatics and Multiplicity.

## Overview

Phase 0 implements hard constraints that form the foundation for the Sigmatics-to-Multiplicity compilation pipeline:

1. **Fixed index size**: n = 12,288 (48×256)
2. **Index map**: index(page, belt, offset)
3. **Projector admissibility**: p^r | n enforcement
4. **Policies**: primePolicy, levelPolicy, permPolicy (marked UNPROVEN)
5. **Bridge compiler**: Sigmatics → Multiplicity with Π-first reduction

## Implementation Files

### Core Modules

- **`multiplicity_core/phase0_index.py`**: Index map, projector admissibility, and policies
- **`multiplicity_core/sigmatics_bridge.py`**: Sigmatics-to-Multiplicity compiler with Π-first reduction

### Tests

- **`tests/test_phase0_index.py`**: Tests for index map and policies
- **`tests/test_sigmatics_bridge.py`**: Tests for bridge compilation
- **`tests/test_phase0_xhr.py`**: X (numeric), H (structural), and R (baseline) tests

## 1. Fixed Index Size

The index size is fixed to **n = 12,288**, computed as:

```
n = 48 × 256 = 12,288
```

Where:
- 48 pages
- 256 bytes per page

This size has the prime factorization:

```
12,288 = 2^12 × 3^1
```

This factorization determines which projectors are admissible.

### Constants

```python
from multiplicity_core.phase0_index import INDEX_SIZE, NUM_PAGES, BYTES_PER_PAGE

assert INDEX_SIZE == 12288
assert NUM_PAGES == 48
assert BYTES_PER_PAGE == 256
```

## 2. Index Map

The index map provides a total ordering over the 12,288 addresses with two modes:

### Default Mode (Belt as Metadata)

```python
index(page, belt, offset) = page * 256 + offset
```

Belt is treated as metadata and not encoded in the linear address.

**Example:**
```python
from multiplicity_core.phase0_index import index_map, inverse_index_map

# Forward mapping
idx = index_map(17, 0, 46)  # page=17, belt=0, offset=46
assert idx == 4398

# Inverse mapping
page, belt, offset = inverse_index_map(4398)
assert (page, belt, offset) == (17, 0, 46)
```

### Belt Encoding Mode (Optional)

```python
index(page, belt, offset) = page * (256 * B) + belt * 256 + offset
```

Where B is the number of belts. This packs belt into the address.

**Example:**
```python
# With belt encoding
idx = index_map(17, 0, 46, encode_belt=True)
```

### Address Utilities

```python
from multiplicity_core.phase0_index import make_address, decode_address

# Create address
addr = make_address(17, 0, 46)
print(addr)  # IndexAddress(page=17, belt=0, offset=46, index=4398)

# Decode address
addr = decode_address(4398)
print(addr.page, addr.offset)  # 17, 46
```

## 3. Projector Admissibility

A projector with prime p and level r is **admissible** if and only if:

```
p^r | n  (p^r divides n)
```

For n = 12,288 = 2^12 × 3^1, the admissible projectors are:

- **(p=2, r=1..12)**: 2^1, 2^2, ..., 2^12
- **(p=3, r=1)**: 3^1

### Usage

```python
from multiplicity_core.phase0_index import (
    check_projector_admissibility,
    max_admissible_level,
    list_admissible_projectors
)

# Check admissibility
assert check_projector_admissibility(2, 8) == True   # 2^8 = 256 divides 12288
assert check_projector_admissibility(3, 1) == True   # 3^1 = 3 divides 12288
assert check_projector_admissibility(5, 1) == False  # 5 does not divide 12288

# Find maximum level
assert max_admissible_level(2) == 12  # 2^12 divides 12288, but 2^13 does not
assert max_admissible_level(3) == 1   # 3^1 divides 12288, but 3^2 does not

# List all admissible projectors
projectors = list_admissible_projectors(max_prime=20)
# [(2,1), (2,2), ..., (2,12), (3,1)]
```

### Enforcement

All projector operations must verify admissibility before use:

```python
def apply_projector(p: int, r: int):
    if not check_projector_admissibility(p, r):
        raise ValueError(f"Projector (p={p}, r={r}) is not admissible for n={INDEX_SIZE}")
    # ... apply projector
```

## 4. Policies (UNPROVEN)

Three policy functions determine how modalities map to primes, levels, and permutations:

### Prime Policy

```python
primePolicy(d) → p
```

Maps modality d to prime p.

**Default**: p = 3 for all d (unless class metadata forces another prime)

```python
from multiplicity_core.phase0_index import prime_policy_default

p = prime_policy_default(d=0)  # Returns 3
```

### Level Policy

```python
levelPolicy(d) → r
```

Maps modality d to level r.

**Default**: r = 1 for all d

```python
from multiplicity_core.phase0_index import level_policy_default

r = level_policy_default(d=0)  # Returns 1
```

### Permutation Policy

```python
permPolicy(d) → π
```

Maps modality d to permutation π.

**Default**: identity permutation (empty list)

```python
from multiplicity_core.phase0_index import perm_policy_default

pi = perm_policy_default(d=0)  # Returns []
```

### Status: UNPROVEN

⚠️ **All policies are marked UNPROVEN until mathematically fixed and verified.**

```python
from multiplicity_core.phase0_index import DEFAULT_POLICIES

assert DEFAULT_POLICIES.status == "UNPROVEN"
```

When using the default policy set, a warning is issued:

```
UserWarning: PolicySet status is UNPROVEN. These policies are not mathematically verified.
```

### Custom Policies

You can define custom policies:

```python
from multiplicity_core.phase0_index import PolicySet

def my_prime_policy(d: int) -> int:
    return 2 if d == 0 else 3

policies = PolicySet(
    prime_policy=my_prime_policy,
    level_policy=level_policy_default,
    perm_policy=perm_policy_default,
    status="CUSTOM_UNPROVEN"
)
```

## 5. Sigmatics to Multiplicity Bridge

The bridge compiles Sigmatics operational words to Multiplicity runtime words with **Π-first reduction**.

### Π-First Reduction

The Π-first reduction strategy processes product projectors (Π-atoms) before other operations:

1. **Extract Π-atoms**: Identify generators with modality parameters
2. **Reorder**: Place Π-atoms first
3. **Compile**: Convert to Multiplicity words

**Rationale**: Π-atoms represent fundamental projector updates that should be applied before other transformations.

### Basic Usage

```python
from multiplicity_core.sigmatics_bridge import bridge_compile

# Sigmatics operational words (from evaluator)
sigmatics_words = ["phase[h₂=0]", "mark[d=0]", "evaluate"]

# Compile with Π-first reduction
result = bridge_compile(sigmatics_words, apply_pi_first=True)

print(result.summary())
```

**Output:**
```
Compilation Summary
============================================================
Input: 3 Sigmatics words
Output: 3 Multiplicity words
Π-first reduction: Applied

Sigmatics words:
  phase[h₂=0]
  mark[d=0]
  evaluate

Multiplicity words:
  MARK(0)
  SET_QUADRANT(0)
  EVALUATE()
============================================================
```

### Word Classification

The bridge classifies Sigmatics words into types:

- **PHASE**: Phase control (h₂ quadrant)
- **GENERATOR**: Atlas generators (mark, copy, swap, merge, split, quote, evaluate)
- **ROTATE**: Rotate transform (→ρ, ←ρ)
- **TWIST**: Twist/march transform
- **MIRROR**: Mirror transform (~)

```python
from multiplicity_core.sigmatics_bridge import classify_word

word = classify_word("mark[d=0]")
print(word.type)    # WordType.GENERATOR
print(word.name)    # "mark"
print(word.params)  # {"d": 0}
```

### Compilation Pipeline

The full compilation pipeline:

1. **Classify**: Parse word strings → SigmaticsWord objects
2. **Reorder** (optional): Apply Π-first reduction
3. **Compile**: SigmaticsWord → MultiplicityWord

```python
from multiplicity_core.sigmatics_bridge import compile_sigmatics_to_multiplicity

sigmatics = ["phase[h₂=0]", "copy[d=1]", "evaluate", "mark[d=0]"]

# Without Π-first (original order)
result_no_pi = compile_sigmatics_to_multiplicity(sigmatics, apply_pi_first=False)
# Order: SET_QUADRANT, COPY, EVALUATE, MARK

# With Π-first (Π-atoms first)
result_pi = compile_sigmatics_to_multiplicity(sigmatics, apply_pi_first=True)
# Order: COPY, MARK, SET_QUADRANT, EVALUATE
```

### Multiplicity Words

Compiled words have:
- **opcode**: Operation code (e.g., "MARK", "COPY", "SET_QUADRANT")
- **args**: Arguments (e.g., modality value)
- **metadata**: Additional information

```python
mult_word = result.multiplicity_words[0]
print(mult_word.opcode)    # "MARK"
print(mult_word.args)      # [0]
print(mult_word.metadata)  # {"modality": 0}
```

## 6. Testing Framework

The implementation includes three test categories:

### X Tests: Numeric Tests

Validate numeric properties and computations:

- **X1**: Index size arithmetic (12,288 = 48×256)
- **X2**: Index map linearity
- **X3**: Index coverage (bijection)
- **X4**: Projector divisibility
- **X5**: Page/offset bounds
- **X6**: Address determinism
- **X7**: Prime factorization

```bash
python3 -m pytest tests/test_phase0_xhr.py::TestNumericX -v
```

### H Tests: Structural Tests

Validate structural and algebraic properties:

- **H1**: Index map bijection
- **H2**: Inverse map consistency
- **H3**: Projector lattice structure
- **H4**: Bridge compilation structure
- **H5**: Π-first preservation of atoms
- **H6**: Page partition structure

```bash
python3 -m pytest tests/test_phase0_xhr.py::TestStructuralH -v
```

### R Tests: Baseline Scoring

Compare against trivial baseline:

- **R1**: Index map vs trivial (p+o)
- **R2**: Bridge compilation vs identity
- **R3**: Π-first effectiveness

```bash
python3 -m pytest tests/test_phase0_xhr.py::TestBaselineR -v
```

### Running All Tests

```bash
# All Phase 0 tests
python3 -m pytest tests/test_phase0_*.py -v

# Specific module tests
python3 -m pytest tests/test_phase0_index.py -v
python3 -m pytest tests/test_sigmatics_bridge.py -v
python3 -m pytest tests/test_phase0_xhr.py -v
```

## 7. Validation and Diagnostics

### Phase 0 Summary

Print a summary of Phase 0 configuration:

```python
from multiplicity_core.phase0_index import print_phase0_summary

print_phase0_summary()
```

**Output:**
```
======================================================================
Phase 0 — Hard Constraints Summary
======================================================================
Index size n = 12,288 (fixed)
Pages: 48
Bytes per page: 256
Formula: 48 × 256 = 12,288

Prime factorization: 12288 = 2^12 × 3^1

Admissible projectors (p^r | n, p ≤ 20):
  (p=2, r=1): 2^1 = 2
  (p=2, r=2): 2^2 = 4
  ...
  (p=2, r=12): 2^12 = 4096
  (p=3, r=1): 3^1 = 3

Policies (status: UNPROVEN):
  primePolicy(d) → p (default: p=3)
  levelPolicy(d) → r (default: r=1)
  permPolicy(d) → π (default: identity)

⚠️  All policies are UNPROVEN until mathematically fixed and verified.
======================================================================
```

### Validation

Run validation checks:

```python
from multiplicity_core.phase0_index import validate_phase0_constraints

results = validate_phase0_constraints()
print(results)
```

**Output:**
```python
{
    'index_size': 12288,
    'index_size_check': True,
    'pages': 48,
    'bytes_per_page': 256,
    'factorization': {2: 12, 3: 1},
    'admissible_projectors': [(2,1), (2,2), ..., (3,1)],
    'policies_status': 'UNPROVEN',
    'size_consistency': True
}
```

## 8. Compatibility

### Compatibility with boundary_lattice

The Phase 0 implementation is compatible with the existing `boundary_lattice` module:

```python
from multiplicity_core.boundary_lattice import (
    COORDINATES, FOLD_ROWS, FOLD_COLS,
    boundary_fold_48x256, boundary_unfold_48x256
)
from multiplicity_core.phase0_index import (
    INDEX_SIZE, NUM_PAGES, BYTES_PER_PAGE,
    inverse_index_map
)

# Constants match
assert INDEX_SIZE == COORDINATES
assert NUM_PAGES == FOLD_ROWS
assert BYTES_PER_PAGE == FOLD_COLS

# Index maps are compatible
idx = 4398
row, col = boundary_fold_48x256(idx)
page, belt, offset = inverse_index_map(idx)
assert (row, col) == (page, offset)
```

## 9. Examples

### Example 1: Computing Addresses

```python
from multiplicity_core.phase0_index import make_address

# Create addresses
addr1 = make_address(0, 0, 0)      # First address
addr2 = make_address(47, 0, 255)   # Last address
addr3 = make_address(17, 0, 46)    # Middle address

print(addr1)  # IndexAddress(page=0, belt=0, offset=0, index=0)
print(addr2)  # IndexAddress(page=47, belt=0, offset=255, index=12287)
print(addr3)  # IndexAddress(page=17, belt=0, offset=46, index=4398)
```

### Example 2: Checking Projectors

```python
from multiplicity_core.phase0_index import (
    check_projector_admissibility,
    list_admissible_projectors
)

# Check specific projectors
print(check_projector_admissibility(2, 8))   # True (256 divides 12288)
print(check_projector_admissibility(3, 1))   # True (3 divides 12288)
print(check_projector_admissibility(5, 1))   # False (5 doesn't divide 12288)

# List all admissible projectors
for p, r in list_admissible_projectors(max_prime=10):
    print(f"p={p}, r={r}: {p**r} divides {12288}")
```

### Example 3: Compiling Sigmatics Expressions

```python
from multiplicity_core.sigmatics_bridge import bridge_compile

# Sequential composition: copy . evaluate
sigmatics = ["copy[d=0]", "evaluate"]
result = bridge_compile(sigmatics)

print(result.summary())

# Access compiled words
for word in result.multiplicity_words:
    print(f"{word.opcode}({', '.join(map(str, word.args))})")
```

### Example 4: Π-First Reduction in Action

```python
from multiplicity_core.sigmatics_bridge import bridge_compile

# Mixed operations
sigmatics = ["phase[h₂=1]", "mark[d=2]", "evaluate", "copy[d=0]"]

# Without Π-first
result_no_pi = bridge_compile(sigmatics, apply_pi_first=False)
print("Without Π-first:")
for w in result_no_pi.multiplicity_words:
    print(f"  {w.opcode}")
# Output: SET_QUADRANT, MARK, EVALUATE, COPY

# With Π-first
result_pi = bridge_compile(sigmatics, apply_pi_first=True)
print("\nWith Π-first:")
for w in result_pi.multiplicity_words:
    print(f"  {w.opcode}")
# Output: MARK, COPY, SET_QUADRANT, EVALUATE
```

## 10. Status and Next Steps

### Current Status

✅ **Implemented:**
- Fixed index size n = 12,288
- Index map with default (belt as metadata) and encoding modes
- Projector admissibility enforcement
- Prime, level, and permutation policies (default implementations)
- Sigmatics-to-Multiplicity bridge with Π-first reduction
- Comprehensive test suite (X, H, R tests)

⚠️ **UNPROVEN:**
- All policy functions (primePolicy, levelPolicy, permPolicy)
- Mathematical correctness of Π-first reduction strategy
- Physical interpretation beyond pure mathematics

### Next Steps (Future Phases)

1. **Mathematically verify policies**: Prove correctness of prime, level, and permutation policies
2. **Formal verification**: Add Lean/Coq proofs for core properties
3. **Extended bridge**: Add support for more Sigmatics constructs
4. **Runtime integration**: Connect compiled Multiplicity words to ACE runtime
5. **Performance optimization**: Optimize compilation and index map operations
6. **Documentation**: Add formal specification document

## 11. References

- Main README: `/home/runner/work/Hologram-APEX/Hologram-APEX/README.md`
- Sigmatics README: `/home/runner/work/Hologram-APEX/Hologram-APEX/sigmatics/README.md`
- Multiplicity core: `/home/runner/work/Hologram-APEX/Hologram-APEX/multiplicity_core/`
- Boundary lattice: `/home/runner/work/Hologram-APEX/Hologram-APEX/multiplicity_core/boundary_lattice.py`

## 12. API Reference

See inline documentation in:
- `multiplicity_core/phase0_index.py`
- `multiplicity_core/sigmatics_bridge.py`

For usage examples, see test files:
- `tests/test_phase0_index.py`
- `tests/test_sigmatics_bridge.py`
- `tests/test_phase0_xhr.py`
