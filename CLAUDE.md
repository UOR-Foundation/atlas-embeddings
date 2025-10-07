# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**atlas-embeddings** is a mathematically rigorous Rust crate implementing the first-principles construction of exceptional Lie groups (G₂, F₄, E₆, E₇, E₈) from the Atlas of Resonance Classes. This is peer-reviewable mathematical code where tests serve as formal proofs.

## Core Principles (CRITICAL)

1. **NO floating point arithmetic** - All computations use exact rational arithmetic (`Fraction`, `i64`, `HalfInteger`)
   - Clippy denies: `float_arithmetic`, `float_cmp`, `float_cmp_const`
   - Use `num-rational::Ratio<i64>` for all rational numbers

2. **NO unsafe code** - `#![forbid(unsafe_code)]` is enforced

3. **First principles only** - Do NOT import Cartan matrices, Dynkin diagrams, or Lie theory from external sources
   - All exceptional groups MUST emerge from Atlas categorical operations
   - Verify properties computationally from Atlas structure

4. **Documentation as paper** - Comprehensive rustdoc with mathematical exposition
   - Mathematical background comes BEFORE implementation
   - Theorems stated in doc comments, proofs are tests
   - All public items must be documented

## Build Commands

```bash
# Development
make build              # Standard build
make test               # Run all tests (unit, integration, doc tests)
make test-unit          # Run unit tests only (cargo test --lib)
make test-int           # Run integration tests (cargo test --test '*')
make test-doc           # Run doc tests

# Quality checks
make check              # Cargo check with/without default features
make lint               # Clippy with strictest settings
make format             # Format code
make format-check       # Check formatting without changes
make verify             # Full CI equivalent: format-check + check + lint + test + docs

# Documentation
make docs               # Build docs
make docs-open          # Build and open docs in browser
make docs-private       # Include private items

# Benchmarks
make bench              # Run all benchmarks (uses criterion)
make bench-save         # Save baseline for comparison

# Maintenance
make clean              # Remove all build artifacts
make audit              # Security audit
make deps               # Show dependency tree
```

## Architecture

### Module Structure

```
src/
├── lib.rs              - Crate-level documentation and re-exports
├── atlas/              - 96-vertex Atlas graph from action functional
├── arithmetic/         - Exact rational arithmetic (NO FLOATS)
│   ├── mod.rs          - Rational, HalfInteger, Vector8 types
│   └── matrix.rs       - RationalMatrix, RationalVector
├── e8/                 - E₈ root system (240 roots, exact coordinates)
├── embedding/          - Atlas → E₈ embedding
├── groups/             - Exceptional group constructions
│   ├── G₂: Product (Klein × ℤ/3) → 12 roots, rank 2
│   ├── F₄: Quotient (96/±) → 48 roots, rank 4
│   ├── E₆: Filtration (degree partition) → 72 roots, rank 6
│   ├── E₇: Augmentation (96+30) → 126 roots, rank 7
│   └── E₈: Direct embedding → 240 roots, rank 8
├── cartan/             - Cartan matrices and Dynkin diagrams
├── weyl/               - Weyl groups and reflections
└── categorical/        - Categorical operations (product, quotient, filtration)
```

### Key Data Structures

- **Atlas**: 96-vertex graph with canonical labels `(e1, e2, e3, d45, e6, e7)`
  - e1-e3, e6-e7 are binary (0/1)
  - d45 is ternary (-1/0/+1) representing e4-e5 difference
  - Mirror symmetry τ: flips e7 coordinate (τ² = identity)

- **E8RootSystem**: 240 roots (112 integer + 128 half-integer)
  - Integer roots: ±eᵢ ± eⱼ for i ≠ j
  - Half-integer roots: all coords ±1/2 with even # of minus signs
  - All roots have norm² = 2 (exact)

- **CartanMatrix<N>**: Rank N encoded at type level
  - Diagonal entries = 2
  - Off-diagonal ≤ 0
  - Simply-laced: off-diagonal ∈ {0, -1} only

- **HalfInteger**: Exact half-integers (numerator/2)
  - Used for E₈ coordinates
  - Preserves mathematical structure

## Testing Strategy

Tests serve as **certifying proofs** of mathematical claims:

- **Unit tests**: Verify individual component properties
- **Integration tests** (`tests/`): End-to-end group constructions
  - `g2_construction.rs`: Klein quartet → 12 roots
  - `f4_construction.rs`: Quotient → 48 roots
  - `e6_construction.rs`: Filtration → 72 roots
  - `e7_construction.rs`: Augmentation → 126 roots
  - `e8_embedding.rs`: Full E₈ → 240 roots
  - `inclusion_chain.rs`: Verify G₂ ⊂ F₄ ⊂ E₆ ⊂ E₇ ⊂ E₈
- **Property tests** (`property_tests.rs`): Algebraic invariants
- **Doc tests**: Examples in documentation must compile and pass

## Clippy Configuration

Strictest settings (`.clippy.toml`):
- `cognitive-complexity-threshold = 15`
- `too-many-arguments-threshold = 5`
- `missing-docs-in-crate-items = true`
- Disallowed names: `foo`, `bar`, `baz`, `tmp`, `temp`
- Doc valid idents: `Atlas`, `E6`, `E7`, `E8`, `F4`, `G2`, `Dynkin`, `Cartan`, `Weyl`

## Dependencies

**Production** (all with `default-features = false`):
- `num-rational` - Exact rational arithmetic
- `num-integer`, `num-traits` - Number traits
- `thiserror` - Error types

**Dev dependencies**:
- `criterion` - Benchmarking with HTML reports
- `proptest`, `quickcheck` - Property-based testing
- `pretty_assertions`, `test-case` - Test utilities

## Common Development Tasks

### Adding a New Exceptional Group Construction

1. Implement in `src/groups/mod.rs` with constructor `from_atlas(&Atlas)`
2. Provide methods: `num_roots()`, `rank()`, `weyl_order()`, `cartan_matrix()`
3. Write comprehensive doc comments with mathematical background
4. Add integration test in `tests/{group}_construction.rs`
5. Verify invariants: root count, rank, Cartan matrix properties
6. Update `inclusion_chain.rs` if applicable

### Verifying Mathematical Properties

Use exact arithmetic assertions:
```rust
// Good: exact rational comparison
assert_eq!(root.norm_squared(), Rational::from_integer(2));

// Bad: would use floating point
// assert!((root.norm_squared() - 2.0).abs() < 1e-10);
```

### Running Individual Test

```bash
cargo test --test e6_construction       # Specific integration test
cargo test atlas::tests::test_mirror    # Specific unit test by path
cargo test --doc groups::E6             # Doc test for E6
```
