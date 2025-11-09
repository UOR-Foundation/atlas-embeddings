# Documentation Strategy

## Overview

This crate uses **documentation-driven development** where the documentation serves as the primary exposition of the mathematical theory, and the code serves as the formal proof/certificate of correctness.

## Structure

### 1. Module-Level Documentation (`//!`)

Each module begins with comprehensive mathematical context:

```rust
//! # G₂ from Klein Quartet
//!
//! ## Mathematical Background
//!
//! G₂ is the smallest exceptional Lie group with 12 roots and rank 2.
//! It emerges from the Atlas via the categorical product operation:
//!
//! $$\text{Klein} \times \mathbb{Z}/3 = 2 \times 3 = 6 \text{ vertices}$$
//!
//! ## Construction
//!
//! 1. **Klein quartet**: Vertices $\{0, 1, 48, 49\}$ form $V_4$
//! 2. **3-cycle extension**: 12-fold divisibility throughout Atlas
//! 3. **Product structure**: Categorical product gives 12 roots
//!
//! ## Verification
//!
//! The construction is verified by:
//! - Cartan matrix has correct form
//! - Weyl group has order 12
//! - Root system closed under addition
```

### 2. Item Documentation (`///`)

Every public item (struct, function, constant) has:

- **Purpose**: What it represents mathematically
- **Invariants**: Properties guaranteed by type system
- **Examples**: Concrete usage with tests
- **References**: Citations to relevant theory

```rust
/// Cartan matrix for a simply-laced Lie algebra.
///
/// # Mathematical Properties
///
/// A Cartan matrix $C$ for a simply-laced algebra satisfies:
/// - $C_{ii} = 2$ (diagonal entries)
/// - $C_{ij} \in \{0, -1\}$ for $i \neq j$ (off-diagonal)
/// - $C_{ij} = C_{ji}$ (symmetry)
///
/// # Type Invariants
///
/// The type parameter `N` encodes the rank, ensuring dimension correctness
/// at compile time.
///
/// # Examples
///
/// ```
/// use atlas_embeddings::cartan::CartanMatrix;
///
/// let g2 = CartanMatrix::<2>::g2();
/// assert_eq!(g2[(0, 0)], 2);
/// assert_eq!(g2[(0, 1)], -1);
/// ```
pub struct CartanMatrix<const N: usize> { /* ... */ }
```

### 3. Inline Comments

Used sparingly for:
- Non-obvious implementation details
- References to specific mathematical theorems
- Explanation of algorithmic choices

```rust
// Use BFS to find spanning tree (Theorem 3.2)
// This is NOT heuristic - the tree structure is unique
// given the adjacency constraints from unity positions
```

## Mathematical Notation

We use KaTeX for rendering mathematics in the generated documentation:

- Inline math: `$x^2$`
- Display math: `$$\sum_{i=1}^n x_i$$`
- LaTeX commands: `\mathbb{Z}`, `\alpha_i`, `\langle \cdot, \cdot \rangle`

## Documentation as Paper

The generated `cargo doc` output serves as the primary "paper":

1. **Introduction**: Main crate documentation in `src/lib.rs`
2. **Theory**: Module-level documentation for each construction
3. **Proofs**: Function documentation with verified properties
4. **Results**: Test documentation showing verification
5. **Appendices**: Benchmark results, implementation notes

## Building Documentation

```bash
# Local build with private items
make docs

# Build for docs.rs (with all features)
cargo doc --all-features --no-deps

# Open in browser
make docs-open
```

## Standards

1. **Every public item must be documented** (enforced by `#![warn(missing_docs)]`)
2. **Mathematical notation must be precise** (use standard LaTeX commands)
3. **Examples must be tested** (use `cargo test --doc`)
4. **References must be accurate** (cite specific theorems/papers)
5. **No hand-waving** (every claim must be verifiable from code)

## Review Checklist

Before submitting documentation:

- [ ] All mathematical notation renders correctly
- [ ] Examples compile and pass tests
- [ ] Claims are backed by code or tests
- [ ] Complexity is explained, not hidden
- [ ] Cross-references are correct
- [ ] ASCII diagrams (Dynkin, etc.) render properly
