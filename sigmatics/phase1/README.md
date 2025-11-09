# Phase 1 — Front end and compiler

This directory implements the Phase 1 Sigmatics front-end compiler that:

1. **Lexes and parses** a minimal Sigmatics DSL
2. **Lowers** to deterministic JSON words with metadata
3. **Compiles** to Multiplicity runtime instructions
4. Performs **Π-first reduction** (projectors first)
5. Enforces **admissibility checks** (p^r | n)
6. Tracks **obligations** for UNPROVEN policies

## Architecture

```
phase1/
├── lexer_parser.py          # Lexer and parser for Sigmatics DSL
├── lowering.py              # Deterministic lowering to JSON
├── policies.py              # Policy functions (UNPROVEN)
├── compiler.py              # Sigmatics → Multiplicity compiler
├── sigmaticsc.py            # CLI tool
├── schemas/                 # JSON Schemas
│   ├── sigmatics_word.schema.json
│   ├── multiplicity_word.schema.json
│   └── program.schema.json
├── example.sig              # Example Sigmatics script
├── demo.py                  # Full pipeline demonstration
└── README.md                # This file
```

## Sigmatics DSL Grammar

The minimal Sigmatics DSL supports these operations (semicolon-terminated):

```
copy                         # Comultiplication
swap@c_d                     # Swap channels/labels c and d
~                            # Mirror operation
merge                        # Fold/meet operation
split@ℓ:type                 # Split with type annotation
mark@{...}                   # Mark with JSON modality (creates Π-atom)
quote                        # Suspend computation (modal enter)
evaluate                     # Force computation (modal exit)
rho[k]                       # Rotation +k
tau[k]                       # Rotation -k (tau negates)
mu[p]                        # Permutation policy p
```

### Example Script

```sigmatics
mark@{"p":3,"r":1,"mode":"delta"};
rho[17];
copy;
swap@c_d;
split@ℓ:int;
merge;
quote;
~;
evaluate;
mu[5];
```

## Deterministic Lowering

The lowering phase converts Sigmatics statements to JSON words with:

- **Stable JSON serialization** (sorted keys, compact separators)
- **Source metadata** (file name, character spans)
- **Deterministic hashing** (SHA-1 of canonical form)

**Key property**: Identical semantic content produces identical hash, regardless of whitespace or formatting.

### Lowered Word Format

```json
{
  "op": "mark",
  "args": {"d": {"p": 3, "r": 1, "mode": "delta"}},
  "meta": {"src": "example.sig", "span": [0, 42]}
}
```

## Compilation Pipeline

The compiler performs these steps:

1. **Parse** each lowered word
2. **Classify** operations (projectors vs. others)
3. **Apply policies** for unspecified parameters:
   - `primePolicy(d) → p` (default: 3)
   - `levelPolicy(d) → r` (default: 1)
   - `permPolicy(ctx, n) → π` (default: identity)
   - `arityPolicy(ctx) → int` (default: 2)
   - `markMode(d) → str` (default: "Δ")
4. **Check admissibility**: p^r must divide n (12,288)
5. **Track obligations** for UNPROVEN policies
6. **Apply Π-first reduction**: projectors before other operations

### Multiplicity Operations

The compiler emits these Multiplicity runtime operations:

- `projector` — Π-atom (p, r, mode)
- `permute` — Permutation (π array)
- `rotate` — Rotation (k steps)
- `copy` — Comultiplication
- `merge` — Fold (with arity)
- `split` — Case analysis (with type)
- `modal_enter` — Suspend (from quote)
- `modal_exit` — Force (from evaluate)

### Compiled Program Format

```json
{
  "n": 12288,
  "words": [
    {"op": "projector", "p": 3, "r": 1, "mode": "Δ", "note": "UNPROVEN policy"},
    {"op": "rotate", "k": 17},
    {"op": "copy"},
    ...
  ],
  "obligations": [
    {"type": "policy", "name": "primePolicy/levelPolicy/markMode", "status": "UNPROVEN", ...},
    ...
  ]
}
```

## Admissibility Constraints

For n = 12,288 = 2^12 × 3^1:

- ✓ **Admissible**: (2,1), (2,2), ..., (2,12), (3,1)
- ✗ **Not admissible**: (5,1), (2,13), (3,2), ...

The compiler **rejects** programs with inadmissible projectors.

## Obligations

All policies are marked **UNPROVEN** until mathematically verified. The compiler tracks obligations for:

- **Policy decisions**: prime/level/perm/arity choices
- **Semantic constructs**: quote/evaluate meanings
- **Admissibility violations**: p^r ∤ n

## Usage

### CLI Tool

```bash
# Compile a Sigmatics script
python sigmaticsc.py example.sig -o compiled_program.json

# Verbose output with lowered JSON
python sigmaticsc.py example.sig -o compiled.json --lowered lowered.json -v
```

### Python API

```python
from phase1 import lower, compile_program, Policies

# Lower script
script = 'mark@{"p":3,"r":1}; copy;'
lowered = lower(script, src_name="inline.sig")

# Compile to Multiplicity
policies = Policies()
program = compile_program(lowered["lowered"], policies)

print(f"Hash: {lowered['lowering_hash']}")
print(f"Words: {len(program['words'])}")
print(f"Obligations: {len(program['obligations'])}")
```

### Full Demonstration

```bash
# Run complete pipeline demo
python demo.py
```

Output:
```
======================================================================
Phase 1 — Front end and compiler demonstration
======================================================================

1. Example Sigmatics script:
----------------------------------------------------------------------
mark@{"p":3,"r":1,"mode":"delta"};
rho[17];
copy;
...

2. Lowering to JSON words...
----------------------------------------------------------------------
Lowering hash: a1b2c3d4e5f6...
Number of words: 10

3. Verifying deterministic lowering...
----------------------------------------------------------------------
Script 1 hash: a1b2c3d4e5f6...
Script 2 hash: a1b2c3d4e5f6...
Deterministic: True ✓

4. Compiling to Multiplicity program...
----------------------------------------------------------------------
Index size n: 12288
Compiled words: 10
Obligations tracked: 7

5. First 5 compiled words (Π-first order):
----------------------------------------------------------------------
  1. projector (p=3, r=1, mode=Δ) — UNPROVEN policy
  2. rotate (k=17)
  3. copy
  4. permute — UNPROVEN policy
  5. split (type=int)

6. Obligations (UNPROVEN items):
----------------------------------------------------------------------
  1. policy: primePolicy/levelPolicy/markMode — UNPROVEN
  2. policy: permPolicy — UNPROVEN
  3. policy: arityPolicy — UNPROVEN
  4. semantics: quote — UNPROVEN
  5. policy: permPolicy — UNPROVEN
  6. semantics: evaluate — UNPROVEN
  7. policy: permPolicy — UNPROVEN

======================================================================
Summary:
  ✓ Deterministic lowering: True
  ✓ Lowering hash: a1b2c3d4e5f6...
  ✓ Π-first reduction applied
  ✓ Admissibility checks passed
  ! 7 UNPROVEN obligations tracked
======================================================================

Artifacts written to artifacts/
  - lowered.json
  - compiled_program.json
```

## JSON Schemas

Three schemas are provided in `schemas/`:

1. **sigmatics_word.schema.json** — Lowered Sigmatics words
2. **multiplicity_word.schema.json** — Multiplicity runtime words
3. **program.schema.json** — Complete Multiplicity program

All schemas follow JSON Schema Draft 2020-12.

## Testing

```python
# Test deterministic lowering
from phase1 import lower, verify_determinism

script1 = "mark@{\"p\":3}; copy;"
script2 = "\n  mark@{\"p\":3};   copy;  \n"

assert verify_determinism(script1, script2)

# Test admissibility
from phase1 import admissible

assert admissible(3, 1, 12288)  # 3^1 = 3 divides 12288
assert not admissible(5, 1, 12288)  # 5 does not divide 12288
```

## Integration with Multiplicity Runtime

The compiled Multiplicity program is ready for execution in the runtime:

1. **Π-atoms first**: Projectors are guaranteed to appear before other operations
2. **Index compatible**: All operations respect n = 12,288
3. **Obligations tracked**: Runtime can validate or reject UNPROVEN items

## Limitations & Future Work

### Current Limitations

- **Policies are UNPROVEN**: Default implementations need mathematical verification
- **No parallel composition**: Only sequential composition supported
- **Limited type system**: Type annotations are strings, not structured types
- **No optimization**: Compiled words are not optimized or fused

### Future Work

1. **Verify policies**: Mathematical proofs for prime/level/perm selection
2. **Type system**: Rich type system with inference
3. **Parallel composition**: Support `||` operator from Sigmatics
4. **Optimization passes**: Dead code elimination, fusion, constant folding
5. **Runtime integration**: Direct execution in Multiplicity runtime
6. **Error messages**: Better diagnostics with source locations

## Status Summary

| Component | Status | Notes |
|-----------|--------|-------|
| Lexer/Parser | ✓ Complete | Full DSL grammar supported |
| Deterministic lowering | ✓ Complete | Hash-stable under formatting |
| JSON Schemas | ✓ Complete | Draft 2020-12 compliant |
| Compiler | ✓ Complete | Π-first reduction |
| Admissibility checks | ✓ Complete | p^r \| n enforced |
| Obligation tracking | ✓ Complete | All UNPROVEN items tracked |
| CLI tool | ✓ Complete | Full compilation pipeline |
| Policies | ⚠ UNPROVEN | Need verification |
| Semantics | ⚠ UNPROVEN | quote/evaluate need definition |

## References

- **Phase 0**: Index map and hard constraints (n = 12,288)
- **Multiplicity Runtime**: ACE projectors and contractive updates
- **Sigmatics Algebra**: Seven generators and 96-class structure

---

**Version**: 0.1.0  
**Status**: Phase 1 implementation complete, policies UNPROVEN  
**Date**: 2025-11-09
