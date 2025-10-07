# atlas-embeddings

[![CI](https://github.com/UOR-Foundation/atlas-embeddings/workflows/CI/badge.svg)](https://github.com/UOR-Foundation/atlas-embeddings/actions)
[![Documentation](https://docs.rs/atlas-embeddings/badge.svg)](https://docs.rs/atlas-embeddings)
[![Crates.io](https://img.shields.io/crates/v/atlas-embeddings.svg)](https://crates.io/crates/atlas-embeddings)
[![License: MIT OR Apache-2.0](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue.svg)](https://github.com/UOR-Foundation/atlas-embeddings#license)

> First-principles construction of exceptional Lie groups from the Atlas of Resonance Classes

## Overview

This crate provides a **mathematically rigorous, peer-reviewed implementation** of the Atlas of Resonance Classes and its embedding into E₈, demonstrating the emergence of all five exceptional Lie groups (G₂, F₄, E₆, E₇, E₈) through categorical operations.

### Key Features

- ✅ **Exact Arithmetic** - All computations use rational numbers (`Fraction`), no floating point
- ✅ **First Principles** - Constructions from Atlas structure alone, no external Lie theory assumptions
- ✅ **Type Safety** - Compile-time guarantees of mathematical properties via Rust's type system
- ✅ **Certifying Proofs** - Tests serve as formal verification of mathematical claims
- ✅ **Documentation as Paper** - Primary exposition through comprehensive rustdoc
- ✅ **No-std Compatible** - Can run in embedded/WASM environments

## Mathematical Background

The **Atlas of Resonance Classes** is a 96-vertex graph arising as the stationary configuration of an action functional on a 12,288-cell boundary. It encodes the structure of exceptional Lie groups through:

1. **G₂** (rank 2, 12 roots) - Klein quartet × Z/3 product
2. **F₄** (rank 4, 48 roots) - Quotient operation 96/±
3. **E₆** (rank 6, 72 roots) - Degree-partition filtration
4. **E₇** (rank 7, 126 roots) - Augmentation 96 + 30 orbits
5. **E₈** (rank 8, 240 roots) - Direct embedding into root system

### Principle of Informational Action

The Atlas is **NOT** constructed algorithmically. It **IS** the unique stationary configuration of the action functional:

$$S[\phi] = \sum_{\text{cells}} \phi(\partial \text{cell})$$

This first-principles approach ensures mathematical correctness without approximation.

## Quick Start

Add to your `Cargo.toml`:

```toml
[dependencies]
atlas-embeddings = "0.1"
```

### Example: Constructing E₆

```rust
use atlas_embeddings::{Atlas, groups::E6};

// Atlas construction (from first principles)
let atlas = Atlas::new();

// E₆ emerges via degree-partition: 64 + 8 = 72 roots
let e6 = E6::from_atlas(&atlas);

// Extract simple roots
let simple_roots = e6.simple_roots();
assert_eq!(simple_roots.len(), 6);

// Compute Cartan matrix
let cartan = e6.cartan_matrix();
assert!(cartan.is_simply_laced());
assert_eq!(cartan.determinant(), 3);

// Verify Dynkin diagram structure
let dynkin = cartan.dynkin_diagram();
assert_eq!(dynkin.branch_nodes().len(), 1); // E₆ has 1 branch point
assert_eq!(dynkin.endpoints().len(), 3);     // 3 arms
```

## Development

### Prerequisites

- Rust 1.75 or later
- `cargo`, `rustfmt`, `clippy` (via `rustup`)

### Building

```bash
# Clone repository
git clone https://github.com/UOR-Foundation/atlas-embeddings
cd atlas-embeddings

# Build
make build

# Run tests
make test

# Generate documentation
make docs-open

# Run all checks (formatting, linting, tests, docs)
make verify
```

### Documentation

The primary exposition is through rustdoc. Build and view:

```bash
cargo doc --open
```

Key documentation sections:

- **[Module: `atlas`]** - Atlas construction from action functional
- **[Module: `groups`]** - Exceptional group constructions (G₂, F₄, E₆, E₇, E₈)
- **[Module: `cartan`]** - Cartan matrix extraction and Dynkin diagrams
- **[Module: `categorical`]** - Categorical operations (product, quotient, filtration)

### Testing

```bash
# All tests
make test

# Unit tests only
make test-unit

# Integration tests
make test-int

# Documentation tests
make test-doc
```

### Benchmarking

```bash
# Run all benchmarks
make bench

# Save baseline
make bench-save
```

## Project Structure

```
atlas-embeddings/
├── src/
│   ├── lib.rs              # Main crate documentation
│   ├── atlas/              # Atlas graph structure
│   ├── arithmetic/         # Exact rational arithmetic
│   ├── e8/                 # E₈ root system and embedding
│   ├── groups/             # G₂, F₄, E₆, E₇, E₈ constructions
│   ├── cartan/             # Cartan matrices and Dynkin diagrams
│   ├── weyl/               # Weyl groups and reflections
│   └── categorical/        # Categorical operations
├── tests/                  # Integration tests
├── benches/                # Performance benchmarks
├── docs/                   # Additional documentation
└── Makefile                # Development tasks
```

## Design Principles

### 1. Exact Arithmetic

**NO floating point arithmetic** is used anywhere in this crate. All coordinates are represented as:

- **Integers** (`i64`) for whole numbers
- **Rationals** (`Fraction` from `num-rational`) for non-integers
- **Half-integers** (multiples of 1/2) for E₈ coordinates

### 2. Type-Level Guarantees

```rust
// Rank encoded at type level
struct CartanMatrix<const N: usize>;

// Simply-laced property enforced
trait SimplyLaced {
    fn off_diagonal_entries(&self) -> &[i8]; // Only 0, -1
}
```

### 3. Documentation-Driven Development

Every module begins with comprehensive mathematical exposition. Code serves as the formal proof.

### 4. No External Dependencies on Lie Theory

The exceptional groups **emerge** from the Atlas structure. We do not import Cartan matrices or Dynkin diagrams from external sources.

## Peer Review

This crate is designed for **rigorous peer review**:

- ✅ All mathematical claims are verifiable from code
- ✅ Tests serve as formal proofs of properties
- ✅ Documentation provides complete mathematical context
- ✅ No approximations or heuristics
- ✅ Deterministic, reproducible results

## Standards

- **Linting**: Strictest clippy configuration (`pedantic`, `nursery`, `cargo`)
- **Formatting**: Enforced `rustfmt` configuration
- **Unsafe Code**: **FORBIDDEN** (`#![forbid(unsafe_code)]`)
- **Floating Point**: **DENIED** (clippy: `deny(float_arithmetic)`)
- **Documentation**: All public items documented
- **Testing**: Comprehensive unit, integration, and property-based tests

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT License ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.

## About UOR Foundation

This work is published by the [UOR Foundation](https://uor.foundation), dedicated to advancing universal object reference systems and foundational research in mathematics, physics, and computation.

## Citation

If you use this crate in academic work, please cite:

```bibtex
@software{atlas_embeddings,
  title = {atlas-embeddings: First-principles construction of exceptional Lie groups},
  author = {{UOR Foundation}},
  year = {2025},
  url = {https://github.com/UOR-Foundation/atlas-embeddings},
}
```

## References

1. Conway, J. H., & Sloane, N. J. A. (1988). *Sphere Packings, Lattices and Groups*
2. Baez, J. C. (2002). *The Octonions*
3. Wilson, R. A. (2009). *The Finite Simple Groups*
4. Carter, R. W. (2005). *Lie Algebras of Finite and Affine Type*

## Contact

- Homepage: https://uor.foundation
- Issues: https://github.com/UOR-Foundation/atlas-embeddings/issues
- Discussions: https://github.com/UOR-Foundation/atlas-embeddings/discussions
