# Hologram Compiler

> **Atlas Sigil Algebra Compiler** — Compiles quantum-inspired circuits to optimized backend operations

[![Tests](https://img.shields.io/badge/tests-passing-brightgreen)]()
[![Rust](https://img.shields.io/badge/rust-1.70%2B-orange)]()

## Overview

Hologram Compiler implements the Atlas Sigil Algebra as a **pure compiler** for quantum-inspired circuits. It transforms circuit expressions into optimized generator call sequences through pattern-based canonicalization.

For circuit execution, see [hologram-core](../hologram-core).

### Key Features

- ✅ **Circuit Compiler** (SigmaticsCompiler)
- ✅ **Pattern-Based Canonicalization** (H²=I, X²=I, Z²=I, HXH=Z, S²=Z, I·I=I)
- ✅ **7 Fundamental Generators** (mark, copy, swap, merge, split, quote, evaluate)
- ✅ **96-Class System** (canonical forms)
- ✅ **Range Operations** (multi-class vectors)
- ✅ **Transform Algebra** (rotate, twist, mirror)

## Quick Start

### Compile Circuit

```rust
use hologram_compiler::SigmaticsCompiler;

// Compile circuit with canonicalization
let circuit = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";  // H²
let compiled = SigmaticsCompiler::compile(circuit)?;

// View optimization results
println!("Original: {} ops", compiled.original_ops);   // 4
println!("Canonical: {} ops", compiled.canonical_ops); // 1
println!("Reduction: {:.1}%", compiled.reduction_pct); // 75.0%

// compiled.calls contains the optimized generator sequence
```

### Canonicalization Only

```rust
use hologram_compiler::Canonicalizer;

// Parse and canonicalize (no execution)
let result = Canonicalizer::parse_and_canonicalize(
    "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21"  // H²
)?;

println!("Rewrites: {}", result.rewrite_count);  // 1
println!("Rules: {:?}", result.applied_rules);   // ["H² = I"]
```

## Compilation Pipeline

```
Circuit String → Parse → Canonicalize → Translate → GeneratorCall Sequence
     ↓             ↓           ↓            ↓              ↓
"H² circuit"    AST      Rewrite      Optimize      [Mark{class:0}]
                        (4 ops→1 op)   (75% reduce)
                                                           ↓
                                            [hologram-core executes this]
```

## Pattern-Based Canonicalization

Hologram Compiler automatically optimizes circuits using quantum gate identities:

| Rule | Circuit | Canonical | Reduction |
|------|---------|-----------|-----------|
| H² = I | `copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21` | `mark@c00` | 75% (4→1) |
| X² = I | `mark@c21 . mark@c21` | `mark@c00` | 50% (2→1) |
| Z² = I | `mark@c42 . mark@c42` | `mark@c00` | 50% (2→1) |
| S² = Z | `mark@c07 . mark@c07` | `mark@c42` | 50% (2→1) |
| I·I = I | `mark@c00 . mark@c00` | `mark@c00` | 50% (2→1) |

## Expression Syntax

### Basic Operations

```
mark@c21          # Mark generator, class 21
copy@c05->c06     # Copy generator, source class 5 to destination class 6
merge@c10         # Merge generator (addition)
```

### Composition

```
op1 . op2         # Sequential composition (right-to-left)
op1 || op2        # Parallel composition
(op1 . op2) || op3  # Grouped composition
```

### Transforms

**Prefix:**
```
R+1@ mark@c00     # Rotate by +1
T-2@ mark@c00     # Twist by -2
~@ mark@c21       # Mirror
R+1 T-2 ~@ mark@c00  # Combined transforms
```

**Postfix:**
```
mark@c00^+3       # Rotate by +3
mark@c00~         # Mirror
mark@c00^+3~      # Combined
```

### Multi-Class Ranges

Process large vectors spanning multiple classes:

```
mark@c[0..9]           # 10 classes (30,720 f32 elements)
merge@c[0..32]         # 33 classes (101,376 f32 elements)
merge@c[5..14]^+1~     # Range with transforms
```

**Range Capacity:**
```
c[0..9]    → 30,720 f32   (10 classes)
c[0..32]   → 101,376 f32  (33 classes, 100K)
c[0..95]   → 294,912 f32  (96 classes, max)
```

**Compilation Example:**
```rust
let circuit = "merge@c[0..32]";  // 100K elements
let compiled = SigmaticsCompiler::compile(circuit)?;

// Produces: GeneratorCall::MergeRange { start: 0, end: 32, variant: Add }
assert_eq!(compiled.calls.len(), 1);
```

**Supported on ranges:** mark, merge, quote, evaluate
**Not supported:** copy, swap, split (require explicit source/destination)

## API Reference

### SigmaticsCompiler

```rust
pub struct SigmaticsCompiler;

impl SigmaticsCompiler {
    /// Compile circuit with canonicalization
    pub fn compile(circuit: &str) -> Result<CompiledCircuit, String>;

    /// Compile without canonicalization
    pub fn compile_raw(circuit: &str) -> Result<Vec<GeneratorCall>, String>;
}

pub struct CompiledCircuit {
    pub calls: Vec<GeneratorCall>,       // Generator sequence
    pub original_expr: String,            // Original circuit
    pub canonical_expr: String,           // Canonical form
    pub original_ops: usize,              // Ops before optimization
    pub canonical_ops: usize,             // Ops after optimization
    pub reduction_pct: f64,               // Percentage reduction
}
```

### Canonicalizer

```rust
pub struct Canonicalizer;

impl Canonicalizer {
    /// Parse and canonicalize expression
    pub fn parse_and_canonicalize(expr: &str)
        -> Result<RewriteResult, ParseError>;

    /// Get canonical form as string
    pub fn canonical_form(expr: &str)
        -> Result<String, ParseError>;
}
```

### Execution

For executing compiled circuits, see [hologram-core](../hologram-core):

```rust
use hologram_compiler::SigmaticsCompiler;
use hologram_core::Executor;

let compiled = SigmaticsCompiler::compile(circuit)?;
let executor = Executor::new()?;
// Execute operations using compiled circuit
```

## Generator Operations

| Generator | Operation | Example |
|-----------|-----------|---------|
| `mark` | Introduce/remove mark | `mark@c21` |
| `copy` | Copy data | `copy@c05->c06` (src→dst) |
| `swap` | Exchange data | `swap@c10<->c11` (a↔b) |
| `merge` | Combine (add) | `merge@c10[c11,c12]` (src+ctx→dst) |
| `split` | Decompose (sub) | `split@c10[c11,c12]` (src-ctx→dst) |
| `quote` | Suspend computation | `quote@c15` |
| `evaluate` | Force computation | `evaluate@c15` |

### Generator Variants

**Merge variants:** Add, Mul, Min, Max
**Split variants:** Sub, Div

```rust
GeneratorCall::Merge {
    src_class: 10,
    dst_class: 10,
    context_class: 11,
    variant: MergeVariant::Add,  // or Mul, Min, Max
}
```

## Performance Characteristics

### Compilation
- **Parse:** O(n) where n = expression length
- **Canonicalize:** O(n×r×i) where r=rules, i=iterations (typically i≤3)
- **Translate:** O(n) to GeneratorCall sequence

### Execution
- **CircuitExecutor:** Executes compiled GeneratorCall sequences
- **Class operations:** 12,288 bytes per class (3,072 f32 elements)
- **Range operations:** Linear in total elements, constant overhead

## Examples

### Compile and Optimize

```rust
use hologram_compiler::SigmaticsCompiler;

// H⁴ = (H²)² = I² = I
let circuit = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 . \
               copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";

let compiled = SigmaticsCompiler::compile(circuit)?;

assert_eq!(compiled.original_ops, 8);
assert_eq!(compiled.canonical_ops, 1);
assert_eq!(compiled.reduction_pct, 87.5);
```

### Circuit Builder

```rust
use hologram_compiler::CircuitBuilder;

let circuit = CircuitBuilder::new()
    .mark(21)
    .copy(5, 6)
    .mark(21)
    .build()?;

let compiled = SigmaticsCompiler::compile(&circuit)?;
```

### Range Processing

```rust
let circuit = "merge@c[0..32]";  // Process 100K elements
let compiled = SigmaticsCompiler::compile(circuit)?;

// Single range operation compiled
assert_eq!(compiled.calls.len(), 1);
assert!(matches!(
    compiled.calls[0],
    GeneratorCall::MergeRange { .. }
));
```

## Testing

```bash
# Run all tests
cargo test -p hologram-compiler

# Run specific test suite
cargo test -p hologram-compiler --test quantum_gates

# Run benchmarks
cargo bench -p hologram-compiler
```

## Architecture

### Crate Structure

```
hologram-compiler/
├── src/
│   ├── lib.rs              # Public API
│   ├── compiler.rs         # Circuit → GeneratorCall compiler
│   ├── canonicalization.rs # Pattern-based optimization
│   ├── parser.rs           # String → AST parser
│   ├── lexer.rs            # Tokenization
│   ├── ast.rs              # AST types
│   ├── rewrite.rs          # Rewrite engine
│   ├── pattern.rs          # Pattern matching
│   ├── rules.rs            # Rewrite rules
│   ├── types.rs            # Core types
│   ├── class_system.rs     # 96-class system
│   ├── multi_class.rs      # Range operations
│   ├── generators.rs       # Generator definitions
│   └── circuit.rs          # Circuit builder
├── tests/                  # Integration tests
└── benches/                # Performance benchmarks
```

For execution components (executor, memory, generators), see [hologram-core](../hologram-core).

### Compilation Flow

1. **Parse:** Circuit string → AST (Phrase)
2. **Canonicalize:** Apply rewrite rules (H²=I, etc.)
3. **Translate:** AST → GeneratorCall sequence
4. **Execute:** (via [hologram-core](../hologram-core))

## Documentation

- [Hologram Core](../hologram-core) - Circuit execution engine
- [Sigmatics Guide](../../docs/SIGMATICS_GUIDE.md) - Comprehensive guide
- [Implementation Review](../../docs/SIGMATICS_IMPLEMENTATION_REVIEW.md) - Architecture details

## License

See LICENSE file in repository root.

## Contributing

This project implements the Atlas Sigil Algebra specification. All contributions should maintain:
- Pure compilation focus (no JIT/dynamic runtime)
- Pattern-based canonicalization
- Quantum gate identity preservation
- Comprehensive test coverage
