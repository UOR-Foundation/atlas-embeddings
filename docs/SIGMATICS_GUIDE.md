# Sigmatics: Atlas Sigil Algebra Implementation Guide

## Overview

Sigmatics is a Rust implementation of the Atlas Sigil Algebra formal specification v1.0, providing a symbolic computation system built on 7 fundamental generators and a 96-class resonance structure (≡₉₆).

**Key Features:**

- **7 Fundamental Generators**: mark, copy, swap, merge, split, quote, evaluate
- **96-Class Equivalence System**: Maps 256 bytes → 96 canonical classes
- **Pattern-Based Canonicalization**: Quantum gate identities (H²=I, X²=I, Z²=I, etc.)
- **O(1) Equivalence Checking**: Byte comparison after canonicalization
- **Dual Evaluation Backends**: Literal (bytes) and operational (words)
- **Belt Addressing**: Content-addressable 12,288-slot memory (48 pages × 256 bytes)

## Quick Start

### Basic Usage

```rust
use hologram_compiler::Atlas;

// Evaluate a simple expression to canonical bytes
let result = Atlas::evaluate_bytes("mark@c21")?;
println!("Bytes: {:?}", result.bytes); // [42] (0x2A)

// Sequential composition
let result = Atlas::evaluate_bytes("copy@c05 . mark@c21")?;
println!("Bytes: {:?}", result.bytes); // [10, 42]

// Check equivalence: H² = I
assert!(Atlas::equivalent(
    "copy@c05 . mark@c21 . copy@c05 . mark@c21",  // H²
    "mark@c00"                                      // I
)?);
```

### Canonicalization and Rewriting

```rust
use hologram_compiler::Atlas;

// H² reduces to identity
let result = Atlas::parse_and_canonicalize(
    "copy@c05 . mark@c21 . copy@c05 . mark@c21"
)?;

println!("Rewrite count: {}", result.rewrite_count);      // 1
println!("Applied rules: {:?}", result.applied_rules);    // ["H² = I"]

// Verify reduction: 4 operations → 1 operation (75% reduction)
let (original, canonical, reduction) = Atlas::canonicalization_stats(
    "copy@c05 . mark@c21 . copy@c05 . mark@c21"
)?;

assert_eq!(original, 4);
assert_eq!(canonical, 1);
assert_eq!(reduction, 75.0);
```

## Architecture

### Core Components

```
┌─────────────────────────────────────────────┐
│           Atlas High-Level API              │
│  (parse, evaluate, canonicalize, equivalent)│
└─────────────────────────────────────────────┘
                    │
    ┌───────────────┼───────────────┐
    │               │               │
    ▼               ▼               ▼
┌────────┐    ┌──────────┐    ┌──────────┐
│ Parser │    │ Rewriter │    │Evaluator │
└────────┘    └──────────┘    └──────────┘
    │               │               │
    │         ┌─────┴─────┐         │
    ▼         ▼           ▼         ▼
┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐
│  AST   │ │Pattern │ │ Rules  │ │ Types  │
└────────┘ └────────┘ └────────┘ └────────┘
                │                     │
                └─────────┬───────────┘
                          ▼
                  ┌──────────────┐
                  │ Class System │
                  │  (96 classes)│
                  └──────────────┘
```

### Module Organization

- **`atlas`**: High-level API (`Atlas` struct with static methods)
- **`parser`**: Expression parsing (lexer + recursive descent parser)
- **`ast`**: Abstract syntax tree types (`Phrase`, `Parallel`, `Sequential`, `Term`)
- **`rewrite`**: Pattern-based rewriting with convergence detection
- **`pattern`**: Pattern matching engine for rewrite rules
- **`rules`**: Quantum gate identity rules (H²=I, X²=I, etc.)
- **`evaluator`**: Dual backends (literal bytes and operational words)
- **`types`**: Core type definitions (generators, transforms, sigils)
- **`class_system`**: 96-class equivalence system with canonical forms
- **`generators`**: 7 fundamental generators and their semantics
- **`belt`**: Belt addressing system (48 pages × 256 bytes)

## Expression Syntax

### Basic Operations

```
operation ::= generator '@' sigil ['@' page]
generator ::= 'mark' | 'copy' | 'swap' | 'merge' | 'split' | 'quote' | 'evaluate'
sigil     ::= 'c' class_index [postfix_transforms]
class_index ::= 0..95
page      ::= 0..47
```

Examples:

```rust
"mark@c21"       // Mark generator, class 21
"copy@c05@17"    // Copy generator, class 5, page 17
"mark@c00"       // Identity operation (class 0)
```

### Composition

**Sequential** (`.` operator, right-to-left execution):

```rust
"copy@c05 . mark@c21"  // Execute mark@c21 first, then copy@c05
```

**Parallel** (`||` operator):

```rust
"mark@c21 || mark@c42"  // Execute both in parallel
```

**Grouping**:

```rust
"(copy@c05 . mark@c21) || mark@c42"
```

### Transforms

**Prefix transforms** (apply before operation):

```rust
"R+1@ mark@c00"        // Rotate by +1
"T-2@ mark@c00"        // Twist by -2
"~@ mark@c21"          // Mirror
"R+1 T-2 ~@ mark@c00"  // Combined transforms
```

**Postfix transforms** (apply after operation):

```rust
"mark@c00^+3"          // Rotate by +3
"mark@c00~"            // Mirror
"mark@c00^+3~"         // Combined postfix
```

**Transform semantics**:

- **R (Rotate)**: Modifies h₂ quadrant (mod 4)
- **T (Twist)**: Modifies ℓ context slot (mod 8)
- **M (Mirror)**: Flips modality (1↔2, 0→0)

## Canonical Property

### The 96-Class System

Sigmatics implements a 96-class equivalence structure over the 256-byte space:

**Formula**: `class = 24*h₂ + 8*d + ℓ`

Where:

- `h₂` ∈ [0,3] — Scope quadrant
- `d` ∈ [0,1,2] — Modality (Neutral=0, Produce=1, Consume=2)
- `ℓ` ∈ [0,7] — Context slot

**Canonical form**: All bytes are normalized to have LSB = 0

```rust
// All 96 classes produce canonical bytes (LSB=0)
for class in 0..96 {
    let expr = format!("mark@c{}", class);
    let result = Atlas::evaluate_bytes(&expr)?;
    assert_eq!(result.bytes[0] & 1, 0);  // LSB always 0
}
```

### Quantum Gate Identities

Sigmatics implements pattern-based rewriting for quantum gate identities:

| Identity | Pattern | Reduction    |
| -------- | ------- | ------------ |
| H² = I   | 4 ops   | → 1 op (75%) |
| X² = I   | 2 ops   | → 1 op (50%) |
| Z² = I   | 2 ops   | → 1 op (50%) |
| I·I = I  | 2 ops   | → 1 op (50%) |
| S² = Z   | 2 ops   | → 1 op (50%) |
| HXH = Z  | 5 ops   | → 1 op (80%) |

**Gate definitions**:

- **H** (Hadamard): `copy@c05 . mark@c21`
- **X** (Pauli-X): `mark@c21`
- **Z** (Pauli-Z): `mark@c42`
- **S** (Phase): `mark@c07`
- **I** (Identity): `mark@c00`

### O(1) Equivalence Checking

After canonicalization, equivalence reduces to byte comparison:

```rust
// Complex circuit equivalence
let circuit1 = "copy@c05 . mark@c21 . copy@c05 . mark@c21";  // H²
let circuit2 = "mark@c21 . mark@c21";                        // X²
let identity = "mark@c00";                                    // I

// All three are equivalent (all reduce to identity)
assert!(Atlas::equivalent(circuit1, identity)?);
assert!(Atlas::equivalent(circuit2, identity)?);
assert!(Atlas::equivalent(circuit1, circuit2)?);
```

**Performance**: Equivalence checking is O(1) because it only compares canonical bytes after rewriting.

## Dual Evaluation Backends

### Literal Backend (Byte Semantics)

Produces canonical byte values:

```rust
use hologram_compiler::Atlas;

let result = Atlas::evaluate_bytes("copy@c05 . mark@c21")?;
println!("Bytes: {:?}", result.bytes);  // [10, 42]

// With belt addressing
let result = Atlas::evaluate_bytes("mark@c21@5")?;  // Page 5
println!("Addresses: {:?}", result.addresses);      // Some([1322])
// Address = 256*5 + 42 = 1322
```

### Operational Backend (Word Semantics)

Produces generator words with modality annotations:

```rust
use hologram_compiler::Atlas;

let result = Atlas::evaluate_words("mark@c21")?;
println!("Words: {:?}", result.words);  // ["phase[h₂=0]", "mark[d=1]"]

// With transforms
let result = Atlas::evaluate_words("R+1@ mark@c00")?;
println!("Words: {:?}", result.words);
// ["→ρ[1]", "phase[h₂=1]", "mark[d=0]", "←ρ[1]"]
```

**Word format**:

- Generator words: `"generator[d=modality]"` (e.g., `"mark[d=1]"`)
- Phase words: `"phase[h₂=quadrant]"` (e.g., `"phase[h₂=2]"`)
- Transform entry: `"→ρ[k]"`, `"→τ[k]"`, `"→μ"`
- Transform exit: `"←μ"`, `"←τ[k]"`, `"←ρ[k]"`

## Pattern Matching and Rewriting

### Pattern Elements

```rust
use hologram_compiler::{Pattern, PatternElement, Generator};

// Exact match: specific generator and class
let pattern = Pattern::new(vec![
    PatternElement::exact(Generator::Mark, 21),
    PatternElement::exact(Generator::Mark, 21),
], "X² pattern");

// Wildcard class: any class for specific generator
let pattern = Pattern::new(vec![
    PatternElement::any_class(Generator::Copy),
    PatternElement::any_class(Generator::Mark),
], "Copy-Mark pattern");

// Full wildcard: any operation
let pattern = Pattern::new(vec![
    PatternElement::Any,
    PatternElement::Any,
], "Any two operations");
```

### Rewrite Rules

```rust
use hologram_compiler::{RewriteRule, Pattern, PatternElement, Sequential, Term};
use hologram_compiler::Generator;

// Define X² = I rule
let x_squared_pattern = Pattern::new(vec![
    PatternElement::exact(Generator::Mark, 21),
    PatternElement::exact(Generator::Mark, 21),
], "X² pattern");

let identity_replacement = Sequential::new(vec![
    Term::Operation {
        generator: Generator::Mark,
        sigil: ClassSigil::new(0).unwrap(),  // Class 0 = Identity
    }
]);

let rule = RewriteRule::new(
    x_squared_pattern,
    identity_replacement,
    "X² = I"
);
```

### Rewrite Engine

```rust
use hologram_compiler::{RewriteEngine, parse};

let engine = RewriteEngine::new();  // Uses standard rules
let phrase = parse("mark@c21 . mark@c21")?;

let result = engine.rewrite(&phrase);
println!("Changed: {}", result.changed);              // true
println!("Rewrite count: {}", result.rewrite_count);  // 1
println!("Applied rules: {:?}", result.applied_rules);// ["X² = I"]
```

**Convergence**: The engine iterates up to 100 times, detecting convergence via phrase hashing.

## Belt Addressing

The belt provides content-addressable memory organized in 48 pages of 256 bytes each.

### Address Calculation

**Formula**: `address = 256 * page + byte`

**Total slots**: 48 × 256 = 12,288

```rust
use hologram_compiler::{compute_belt_address, Atlas};

// Compute belt address for page 17, byte 42
let addr = compute_belt_address(17, 42)?;
assert_eq!(addr.page, 17);
assert_eq!(addr.byte, 42);
assert_eq!(addr.address, 256*17 + 42);  // 4394

// Evaluate with belt addressing
let result = Atlas::evaluate_bytes("mark@c21@17")?;
assert!(result.addresses.is_some());
println!("Belt addresses: {:?}", result.addresses);
```

### Page-Addressed Operations

```rust
// Single operation with page
"mark@c21@5"           // Mark at class 21, page 5

// Sequential with different pages
"copy@c05@1 . mark@c21@2"

// Parallel with pages
"mark@c21@0 || mark@c42@1"
```

## Performance Characteristics

### Benchmarks

Run benchmarks with:

```bash
cargo bench -p sigmatics --bench canonicalization
```

**Key measurements**:

| Operation           | Time (approx) | Notes                               |
| ------------------- | ------------- | ----------------------------------- |
| Parse simple        | ~1-2 μs       | Single operation                    |
| Parse sequential    | ~3-5 μs       | 4 operations                        |
| H² canonicalization | ~5-10 μs      | 4 ops → 1 op                        |
| H⁴ canonicalization | ~10-20 μs     | Multiple iterations                 |
| Equivalence check   | ~10-15 μs     | Full parse + canonicalize + compare |
| All 96 classes      | ~100-200 μs   | Evaluate all classes                |

### Scaling

Circuit size scaling is **linear** in the number of operations for parsing and evaluation.

Equivalence checking is **O(1)** in the size of the canonical form (typically 1 byte after reduction).

## Testing

### Test Coverage

**Total: 118 tests passing**

- 89 unit tests (library)
- 24 integration tests (quantum gates)
- 5 doc tests

Run tests:

```bash
cargo test -p sigmatics
```

### Test Categories

**Unit tests**:

- AST construction
- Lexer tokenization
- Parser grammar
- Pattern matching
- Rewrite rules
- Class system invariants
- Generator semantics
- Belt addressing
- Evaluator backends

**Integration tests**:

- Quantum gate identities
- Equivalence checking
- Canonicalization statistics
- Complex circuit reduction
- Parallel composition
- Transform preservation
- Error handling

**Property tests**:

- All 96 classes produce canonical bytes (LSB=0)
- Roundtrip encode/decode
- Transform composition
- Equivalence transitivity

## Examples

### Example 1: Verify H² = I

```rust
use hologram_compiler::Atlas;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let h_squared = "copy@c05 . mark@c21 . copy@c05 . mark@c21";
    let identity = "mark@c00";

    // Check equivalence
    assert!(Atlas::equivalent(h_squared, identity)?);

    // Get canonicalization stats
    let (original, canonical, reduction) =
        Atlas::canonicalization_stats(h_squared)?;

    println!("Original operations: {}", original);     // 4
    println!("Canonical operations: {}", canonical);   // 1
    println!("Reduction: {:.1}%", reduction);          // 75.0%

    Ok(())
}
```

### Example 2: Complex Circuit Reduction

```rust
use hologram_compiler::Atlas;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // H² . X² . Z² should reduce to I . I . I = I
    let complex = "copy@c05 . mark@c21 . copy@c05 . mark@c21 . \
                   mark@c21 . mark@c21 . \
                   mark@c42 . mark@c42";

    let result = Atlas::parse_and_canonicalize(complex)?;

    println!("Changed: {}", result.changed);
    println!("Rewrites: {}", result.rewrite_count);
    println!("Rules: {:?}", result.applied_rules);

    // Verify final equivalence to identity
    assert!(Atlas::equivalent(complex, "mark@c00")?);

    Ok(())
}
```

### Example 3: Parallel Circuit Canonicalization

```rust
use hologram_compiler::Atlas;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // H² || X² should reduce to I || I
    let parallel = "copy@c05 . mark@c21 . copy@c05 . mark@c21 || \
                    mark@c21 . mark@c21";

    let result = Atlas::parse_and_canonicalize(parallel)?;

    // Both branches should be rewritten
    assert!(result.rewrite_count >= 2);

    // Verify equivalence to I || I
    assert!(Atlas::equivalent(parallel, "mark@c00 || mark@c00")?);

    Ok(())
}
```

### Example 4: Transform Application

```rust
use hologram_compiler::Atlas;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Prefix transform
    let with_rotate = "R+1@ mark@c00";
    let result = Atlas::evaluate_bytes(with_rotate)?;
    println!("Rotated byte: {:?}", result.bytes);

    // Postfix transform
    let with_twist = "mark@c00^+3";
    let result = Atlas::evaluate_bytes(with_twist)?;
    println!("Twisted byte: {:?}", result.bytes);

    // Combined transforms
    let combined = "R+1 T-2 ~@ mark@c00^+3~";
    let result = Atlas::evaluate_bytes(combined)?;
    println!("Combined byte: {:?}", result.bytes);

    Ok(())
}
```

### Example 5: Belt-Addressed Computation

```rust
use hologram_compiler::Atlas;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Operations with belt addressing
    let expr = "mark@c21@5 . copy@c05@10";

    let result = Atlas::evaluate_bytes(expr)?;

    println!("Bytes: {:?}", result.bytes);
    println!("Addresses: {:?}", result.addresses);

    // Addresses should be:
    // mark@c21@5:  256*5 + byte  = 1280 + byte
    // copy@c05@10: 256*10 + byte = 2560 + byte

    Ok(())
}
```

## Advanced Topics

### Custom Rewrite Rules

You can define custom rewrite rules beyond the standard quantum gate identities:

```rust
use hologram_compiler::{Pattern, PatternElement, Sequential, Term, RewriteRule};
use hologram_compiler::Generator;

// Define a custom pattern
let pattern = Pattern::new(vec![
    PatternElement::exact(Generator::Copy, 5),
    PatternElement::exact(Generator::Swap, 10),
], "Custom pattern");

// Define replacement
let replacement = Sequential::new(vec![
    Term::Operation {
        generator: Generator::Merge,
        sigil: ClassSigil::new(15).unwrap(),
    }
]);

let rule = RewriteRule::new(pattern, replacement, "Copy-Swap to Merge");
```

### Extending the Evaluator

Both evaluators traverse the AST and apply semantics:

- **Literal**: Computes canonical bytes with LSB=0
- **Operational**: Generates generator words with modality

You can implement custom evaluation semantics by following the same traversal pattern.

### Generator Semantics

Each generator has specific operational semantics:

| Generator | Modality Signature | Description              |
| --------- | ------------------ | ------------------------ |
| mark      | (0→1)              | Produce a mark           |
| copy      | (0→2)              | Produce two copies       |
| swap      | (2→2)              | Swap two values          |
| merge     | (2→1)              | Merge two values         |
| split     | (1→2)              | Split one value          |
| quote     | (1→1)              | Quote (delay evaluation) |
| evaluate  | (1→1)              | Evaluate (unquote)       |

## Troubleshooting

### Common Errors

**Parse error: "Invalid class index"**

```rust
// ERROR: class must be 0..95
let result = Atlas::evaluate_bytes("mark@c96");

// CORRECT:
let result = Atlas::evaluate_bytes("mark@c95");
```

**Parse error: "Invalid page"**

```rust
// ERROR: page must be 0..47
let result = Atlas::evaluate_bytes("mark@c00@48");

// CORRECT:
let result = Atlas::evaluate_bytes("mark@c00@47");
```

**Parse error: "Invalid generator"**

```rust
// ERROR: invalid generator name
let result = Atlas::evaluate_bytes("invalid@c00");

// CORRECT: use valid generator
let result = Atlas::evaluate_bytes("mark@c00");
```

### Debugging Canonicalization

To debug rewrite rules:

```rust
let result = Atlas::parse_and_canonicalize(expression)?;

println!("Changed: {}", result.changed);
println!("Rewrite count: {}", result.rewrite_count);
println!("Applied rules: {:?}", result.applied_rules);
println!("Canonical form: {:?}", result.phrase);
```

### Performance Tips

1. **Reuse expressions**: Canonicalization is cached per expression string
2. **Batch equivalence checks**: Use parallel processing for multiple checks
3. **Profile with benchmarks**: Run `cargo bench` to identify bottlenecks
4. **Minimize rewrites**: Simpler expressions canonicalize faster

## References

- [Atlas Sigil Algebra Specification v1.0](https://github.com/UOR-Foundation/atlas-12288)
- [Integration Guide](./INTEGRATION_GUIDE.md)
- [Quantum Gate Identities](https://en.wikipedia.org/wiki/Quantum_gate)
- [Criterion Benchmarking](https://github.com/bheisler/criterion.rs)

## License

See repository root for license information.

---

**For more information or questions, see the crate documentation or open an issue on GitHub.**
