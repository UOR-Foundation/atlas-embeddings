# Formal verification checklist

- [x] Stub modules compile: **Lean 4** (`lake build`), **Coq** (`make`).
- [ ] Replace `Q` stubs with rationals in Lean; define `ip` over vectors.
- [ ] Instantiate `RE8` with a concrete model; prove `norm_two` and `ip_range`.
- [ ] Prove `Atlas_to_E8_embedding` from constructive pipeline.
- [ ] Prove lemmas for RC, ⊠, quotient, filtration, augmentation.
- [ ] Connect Φ-specifications to computational artifacts.

## Coverage map

| Area | Lean | Coq | Status |
|------|------|-----|--------|
| E8 roots | stubs | stubs | pending proofs |
| Φ-adjacency | stub | stub | pending |
| ResGraph + morphism | defs | defs | ready |
| Embedding theorem | axiom | axiom | pending |
| RC / ⊠ / quotient / filt / aug | stubs | stubs | pending |

Commands
# Lean
cd formal/lean && lake build

# Coq
cd formal/coq && make

# Docs
mkdocs build --strict
