# Hologramapp

**High-performance compute acceleration through canonical form compilation**

Hologramapp provides general-purpose compute acceleration by compiling operations to their canonical forms using **Sigmatics** - a pattern-based canonicalization engine that reduces operation count through geometric rewriting.

## Overview

Hologramapp transforms computational operations into their minimal canonical representations, enabling:

- **Canonical Compilation** - Operations compiled to optimal geometric form
- **Pattern-Based Optimization** - Automatic reduction through rewrite rules (H²=I, X²=I, etc.)
- **Generator Execution** - 7 fundamental operations execute all compute
- **Cross-Language Support** - UniFFI bindings for Python, Swift, Kotlin, TypeScript
- **Lowest Latency** - Fewer operations = faster execution

## Architecture

```
Application Code
    ↓ calls
Hologram Core (ops::math, ops::reduce, ops::activation, etc.)
    ↓ compiles via
Sigmatics Canonicalization (pattern rewriting)
    ↓ produces
Canonical Generator Sequence (minimal form)
    ↓ executes as
Optimized Kernel (lowest latency)
```

### Core Components

- **[sigmatics](crates/sigmatics/)** - Canonical circuit compilation engine
- **[hologram-core](crates/hologram-core/)** - High-level operations library
- **[hologram-ffi](crates/hologram-ffi/)** - UniFFI cross-language bindings
- **[hologram-tracing](crates/hologram-tracing/)** - Performance instrumentation
- **[atlas-core](crates/atlas-core/)** - Foundational geometric primitives

## Quick Start

### Rust

```rust
use hologram_core::{Executor, ops};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create executor
    let exec = Executor::new()?;

    // Allocate buffers
    let mut a = exec.allocate::<f32>(1024)?;
    let mut b = exec.allocate::<f32>(1024)?;
    let mut c = exec.allocate::<f32>(1024)?;

    // Fill with data
    let data_a: Vec<f32> = (0..1024).map(|i| i as f32).collect();
    let data_b: Vec<f32> = (0..1024).map(|i| (i * 2) as f32).collect();

    a.copy_from_slice(&exec, &data_a)?;
    b.copy_from_slice(&exec, &data_b)?;

    // Execute operation (compiles to canonical form automatically)
    ops::math::vector_add(&exec, &a, &b, &mut c, 1024)?;

    // Get results
    let results = c.to_vec(&exec)?;
    println!("Result[0] = {}", results[0]); // 0.0
    println!("Result[1] = {}", results[1]); // 3.0

    Ok(())
}
```

### Sigmatics Circuit Compilation

```rust
use hologram_compiler::SigmaticsCompiler;

// Compile circuit to canonical form
let compiled = SigmaticsCompiler::compile("copy@c05 . mark@c21")?;

println!("Original ops: {}", compiled.stats.original_ops);
println!("Canonical ops: {}", compiled.stats.canonical_ops);
println!("Reduction: {}%", compiled.stats.reduction_percent);
```

## Features

### Operations Library

**Math Operations** (`ops::math`):

- Arithmetic: add, sub, mul, div
- Comparisons: min, max
- Unary: abs, neg, relu
- Element-wise operations on vectors

**Activation Functions** (`ops::activation`):

- sigmoid, tanh, gelu, softmax
- Neural network building blocks

**Reductions** (`ops::reduce`):

- sum, min, max
- Parallel reduction with optimal scheduling

**Loss Functions** (`ops::loss`):

- MSE, cross-entropy, binary cross-entropy
- Gradient-ready implementations

### Sigmatics Canonicalization

**Pattern Rewriting**:

- `H² = I` (Hadamard self-inverse)
- `X² = I` (Pauli-X self-inverse)
- `Z² = I` (Pauli-Z self-inverse)
- `HXH = Z` (Hadamard conjugation)
- `S² = Z` (Phase gate composition)
- `I·I = I` (Identity elimination)

**7 Fundamental Generators**:

1. `mark` - Initialize state
2. `copy` - Duplicate information
3. `swap` - Exchange positions
4. `merge` - Combine data
5. `split` - Divide data
6. `quote` - Preserve structure
7. `evaluate` - Compute result

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
hologram-core = "0.1"
sigmatics = "0.1"
```

## Building from Source

```bash
# Clone repository
git clone https://github.com/UOR-Foundation/hologramapp.git
cd hologramapp

# Build all crates
cargo build --workspace --release

# Run tests
cargo test --workspace

# Build documentation
cargo doc --no-deps --workspace
```

## Testing

```bash
# Run all tests (430 total)
cargo test --workspace

# Run specific crate tests
cargo test -p sigmatics      # 244 tests
cargo test -p hologram-core  # 74 tests
cargo test -p hologram-ffi   # 11 tests

# Run with output
cargo test --workspace -- --nocapture

# Run benchmarks
cargo bench --workspace
```

## Documentation

- **[Sigmatics Guide](docs/SIGMATICS_GUIDE.md)** - Comprehensive canonicalization guide
- **[Sigmatics Implementation Review](docs/SIGMATICS_IMPLEMENTATION_REVIEW.md)** - Technical architecture
- **[CLAUDE.md](CLAUDE.md)** - Development guide for contributors
- **Crate Documentation**:
  - [sigmatics](crates/sigmatics/README.md)
  - [hologram-core](crates/hologram-core/README.md)
  - [hologram-tracing](crates/hologram-tracing/README.md)

## Development

### Prerequisites

- Rust 1.70+ (2021 edition)
- Cargo

### Code Quality

```bash
# Format code
cargo fmt --all

# Check formatting
cargo fmt --all --check

# Lint with Clippy
cargo clippy --workspace --all-targets -- -D warnings

# Build documentation
cargo doc --no-deps --workspace
```

### Contributing

See [CLAUDE.md](CLAUDE.md) for:

- Development workflow
- Testing standards
- Code organization
- Architectural principles
- Common patterns

## Performance

Sigmatics canonicalization provides significant performance benefits:

- **Typical reduction**: 60-80% fewer operations
- **Best case**: 87.5% reduction (H² circuit: 8 ops → 1 op)
- **Idempotent**: Multiple canonicalization passes converge
- **Predictable**: Pattern-based rewriting with formal guarantees

## License

MIT OR Apache-2.0

## Links

- **Repository**: https://github.com/UOR-Foundation/hologramapp
- **Documentation**: https://docs.rs/hologram-core
- **Issues**: https://github.com/UOR-Foundation/hologramapp/issues

---

Built with ❤️ by the UOR Foundation
