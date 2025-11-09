# Phase 1 — Front end and compiler

- Sigmatics DSL → deterministic lowering to JSON words + meta.
- JSON Schemas shipped in `schemas/`.
- Compiler performs Π-first reduction and `p^r | n` checks.
- Obligations carried for UNPROVEN policies and semantics.

Deterministic lowering: True
Lowering hash: 6181e7b1d06c14a74b64f02b8bc09ece47315585

## Artifacts

- `lowered.json` — Lowered Sigmatics words with metadata
- `compiled_program.json` — Compiled Multiplicity program with obligations
- `schemas/` — JSON Schemas for words and programs

## Hash Computation

The lowering hash is computed from semantic content only:
- Includes: `op` and `args` fields
- Excludes: `meta` (source file, spans)

This ensures deterministic hashing under whitespace and formatting changes.

## Example

Input script (example.sig):
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

Output:
- 10 lowered words
- 10 compiled words (Π-first order)
- 7 UNPROVEN obligations

First compiled word (Π-first):
```json
{
  "op": "projector",
  "p": 3,
  "r": 1,
  "mode": "Δ",
  "note": "UNPROVEN policy"
}
```

## Admissibility

For n = 12,288 = 2^12 × 3^1:
- ✓ Admissible: (2,1..12), (3,1)
- ✗ Rejected: (5,1), (2,13), (3,2)

## Status

✅ All requirements met:
- ✅ Lexer/Parser implemented
- ✅ Deterministic lowering (semantic content only)
- ✅ JSON Schemas provided
- ✅ Π-first reduction applied
- ✅ Admissibility checks enforced
- ✅ Obligations tracked (7 UNPROVEN)
- ✅ Sample artifacts generated

⚠️ Policies marked UNPROVEN until mathematically verified
