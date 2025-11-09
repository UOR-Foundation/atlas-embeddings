# Sigmatics – Atlas Sigil Algebra Reference Implementation

A complete TypeScript implementation of the **Atlas Sigil Algebra** formal specification v1.0 - a symbolic computation system built on 7 fundamental generators and a 96-class resonance structure (≡₉₆).

Sigmatics is stewarded by the [UOR Foundation](https://uor.foundation), a 501(c)(3) non-profit dedicated to advancing Universal Object Reference concepts.

## Repository Structure

This is a **monorepo workspace** containing:

- **`packages/core/`** - The core Atlas library (published as `@uor-foundation/sigmatics`)
- **`apps/playground-web/`** - Interactive React playground for exploring Atlas
- **`apps/playground-cli/`** - Command-line demonstration and exploration tool
- **`examples/`** - Practical usage examples and patterns
- **`tools/`** - Development utilities and validation tools
- **`docs/`** - Comprehensive documentation and specifications

## Quick Start

### For Library Users

```bash
npm install @uor-foundation/sigmatics
```

```typescript
import { Atlas } from '@uor-foundation/sigmatics';

// Parse and evaluate a sigil expression
const result = Atlas.evaluate('evaluate@c21 . copy@c05');

console.log(result.literal.bytes); // [0x2A, 0x0A]
console.log(result.operational.words); // ["phase[h₂=0]", "evaluate", ...]

// Pretty print
console.log(Atlas.prettyPrint('mark@c42^+3~@17'));
```

### For Contributors

```bash
# Clone the repository
git clone https://github.com/UOR-Foundation/sigmatics.git
cd sigmatics

# Install all dependencies
npm install

# Build the core library
cd packages/core && npm run build

# Run tests
npm test

# Run examples
cd ../../examples && npm start

# Start the web playground
cd ../apps/playground-web && npm run dev
```

## Features

- ✨ **Dual Semantics**: Both literal (byte) and operational (word) backends
- 🎯 **96-Class System**: Authoritative ≡₉₆ equivalence structure over 256 bytes
- 🔄 **Transform Algebra**: Rotate (R), Twist (T), and Mirror (M) operations
- 📐 **Formal Grammar**: Complete parser for sigil expressions
- 🌐 **Belt Addressing**: Content-addressable 12,288-slot belt (48 pages × 256 bytes)
- ✅ **Verified**: Includes all specification test vectors
- 🚀 **Zero Dependencies**: Pure TypeScript implementation
- 📦 **Modular Architecture**: Well-organized package structure for extensibility

## Packages

### Core Library (`packages/core/`)

The main Atlas Sigil Algebra implementation. See [`packages/core/README.md`](packages/core/README.md) for detailed API documentation.

```typescript
// Main API
import { Atlas } from '@uor-foundation/sigmatics';

// Sub-module imports for advanced usage
import { tokenize } from '@uor-foundation/sigmatics/lexer';
import { Parser } from '@uor-foundation/sigmatics/parser';
import { evaluateLiteral } from '@uor-foundation/sigmatics/evaluator';
import type { Phrase } from '@uor-foundation/sigmatics/types';
```

**Module structure:**

- `api/` - High-level Atlas class
- `lexer/` - Tokenization
- `parser/` - AST construction
- `evaluator/` - Dual backends (literal/operational)
- `class-system/` - 96-class equivalence and transforms
- `types/` - TypeScript type definitions

### Applications

- **`apps/playground-web/`** - Interactive browser-based playground built with React and Vite
- **`apps/playground-cli/`** - Command-line exploration tool

### Examples & Tools

- **`examples/`** - Practical usage demonstrations
- **`tools/validate/`** - Quick validation utilities

### The Seven Generators

1. **mark** - Introduce/remove distinction
2. **copy** - Comultiplication (fan-out)
3. **swap** - Symmetry/braid operation
4. **merge** - Fold/meet operation
5. **split** - Case analysis/deconstruct
6. **quote** - Suspend computation
7. **evaluate** - Force/discharge thunk

### The 96-Class Structure (≡₉₆)

Every byte maps to one of 96 equivalence classes based on:

- **h₂** (scope): Quadrant position {0,1,2,3}
- **d** (modality): • neutral, ▲ produce, ▼ consume {0,1,2}
- **ℓ** (context): 8-ring position {0..7}

Formula: `class = 24*h₂ + 8*d + ℓ`

### Sigil Expression Grammar

```
<phrase>     ::= [ <transform> "@" ] <par>
<par>        ::= <seq> { "||" <seq> }              // parallel ⊗
<seq>        ::= <term> { "." <term> }             // sequential ∘
<term>       ::= <op> | "(" <par> ")"
<op>         ::= <generator> "@" <sigil>
<sigil>      ::= "c" <0..95> ["^" ("+"|"-") <k>] ["~"] ["@" <λ:0..47>]
<transform>  ::= [ "R" ("+"|"-") <q> ] [ "T" ("+"|"-") <k> ] [ "~" ]
```

## Documentation Map

- **[`packages/core/README.md`](packages/core/README.md)** - Core library API reference and usage
- **[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)** - System architecture and module interactions
- **[`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)** - Contributor workflow and coding conventions
- **[`QUICKSTART.md`](QUICKSTART.md)** - Quick installation and usage guide
- **[`docs/atlas_sigil_algebra_formal_specification_v_1.md`](docs/atlas_sigil_algebra_formal_specification_v_1.md)** - Formal specification reference

## Core Concepts

### High-Level API

```typescript
// Parse sigil expressions
const ast = Atlas.parse('copy@c05 . swap@c10');

// Evaluate to bytes (literal backend)
const bytes = Atlas.evaluateBytes('mark@c21');
// → { bytes: [0x2A], addresses?: [...] }

// Evaluate to words (operational backend)
const words = Atlas.evaluateWords('evaluate@c21');
// → { words: ["phase[h₂=0]", "evaluate"] }

// Complete evaluation (both backends)
const result = Atlas.evaluate('copy@c05');
// → { ast, literal, operational }

// Pretty print results
const output = Atlas.prettyPrint('mark@c42');
```

### Class System API

```typescript
// Get class index from byte
const classIdx = Atlas.classIndex(0x2a); // → 21

// Get canonical byte for class
const byte = Atlas.canonicalByte(21); // → 0x2A

// Test equivalence
const equiv = Atlas.equivalent(0x00, 0x01); // → true (both class 0)

// Get all bytes in a class
const members = Atlas.equivalenceClass(0); // → [0x00, 0x01, 0x30, 0x31, ...]

// Get class info
const info = Atlas.classInfo(0x2a);
// → { classIndex: 21, components: {h2:0, d:2, l:5}, canonicalByte: 0x2A }
```

### Belt System API

```typescript
// Compute belt address
const addr = Atlas.beltAddress(17, 0x2e);
// → { page: 17, byte: 46, address: 4398 }

// Decompose belt address
const decomp = Atlas.decodeBeltAddress(4398);
// → { page: 17, byte: 46, address: 4398 }
```

### Introspection

```typescript
// Get all 96 classes
const classes = Atlas.allClasses();
// → [{ index: 0, byte: 0x00 }, { index: 1, byte: 0x02 }, ...]

// Get complete byte→class mapping
const mapping = Atlas.byteClassMapping();
// → [{ byte: 0, classIndex: 0 }, { byte: 1, classIndex: 0 }, ...]
```

## Examples

### Example 1: Simple Operations

```typescript
import Atlas from '@uor-foundation/sigmatics';

// Single operation
Atlas.evaluateBytes('mark@c00');
// → { bytes: [0x00] }

// Sequential composition (right-to-left execution)
Atlas.evaluateBytes('evaluate@c21 . copy@c05');
// → { bytes: [0x2A, 0x0A] }

// Parallel composition
Atlas.evaluateBytes('mark@c01 || mark@c02');
// → { bytes: [0x02, 0x04] }
```

### Example 2: Transforms

```typescript
// Prefix transform (applies to whole expression)
Atlas.evaluateBytes('R+1@ (copy@c05 . evaluate@c21)');
// → { bytes: [0x1A, 0x2E] }

// Postfix transform (applies to single sigil)
Atlas.evaluateBytes('mark@c42^+3~');
// → { bytes: [0x2E] }

// Combined transforms
Atlas.evaluateBytes('R+2 T+3 ~@ mark@c07');
// → { bytes: [0x84] }
```

### Example 3: Belt Addressing

```typescript
// With page index
const result = Atlas.evaluateBytes('mark@c42^+3~@17');
// → { bytes: [0x2E], addresses: [4398] }

// Multiple operations with pages
Atlas.evaluateBytes('mark@c00@0 || mark@c01@1');
// → { bytes: [0x00, 0x02], addresses: [0, 258] }
```

### Example 4: Class Exploration

```typescript
// Find all bytes equivalent to 0x2A
const classIdx = Atlas.classIndex(0x2a); // 21
const equiv = Atlas.equivalenceClass(classIdx);
console.log(`Class ${classIdx} has ${equiv.length} members`);

// Check if two bytes are equivalent
console.log(Atlas.equivalent(0x00, 0x01)); // true
console.log(Atlas.equivalent(0x00, 0x02)); // false
```

### Example 5: Operational Backend

```typescript
// Get generator words
const result = Atlas.evaluateWords('copy@c05 . merge@c13');
console.log(result.words);
// ["merge[d=1]", "copy[d=0]"]

// Transform control words
const result2 = Atlas.evaluateWords('R+1@ evaluate@c21');
console.log(result2.words);
// ["→ρ[1]", "phase[h₂=1]", "evaluate", "←ρ[1]"]
```

## Test Suite

Run the complete test suite including all specification test vectors:

```bash
npm test
```

Test coverage includes:

- ✓ All 8 specification test vectors
- ✓ Class system (≡₉₆ structure)
- ✓ Parser (all grammar forms)
- ✓ Evaluator (both backends)
- ✓ Belt addressing
- ✓ Integration tests

## Architecture

The core library follows a modular architecture:

```
packages/core/src/
├── api/              # Main Atlas class and high-level API
├── types/            # TypeScript type definitions
├── class-system/     # Class system and ≡₉₆ structure
├── lexer/            # Tokenizer
├── parser/           # Parser (tokens → AST)
└── evaluator/        # Dual backends (literal + operational)
```

## Specification Compliance

This implementation fully complies with:

- **Atlas Sigil Algebra — Formal Specification v1.0**
- **Atlas Sigil Parser Spec + Test Vectors v1.0**

All 8 specification test vectors pass:

1. Single sigil
2. Sequential and parallel composition
3. Prefix transforms
4. Postfix transforms with belt addressing
5. Context marching (twist)
6. Mirror modality
7. Combined rotate + twist
8. Error handling

## Implementation Notes

### Transform Distribution

Transforms distribute over composition:

```typescript
R(s₁ ∘ s₂) = R(s₁) ∘ R(s₂)
R(s₁ ⊗ s₂) = R(s₁) ⊗ R(s₂)
```

Prefix transforms in the grammar apply to the entire subtree.

### Canonical Bytes

Each class has a **canonical representative** with:

- `b0 = 0` (LSB always 0)
- `(b4,b5)` maps modality: `0→(0,0)`, `1→(1,0)`, `2→(0,1)`

This ensures unique, deterministic byte output.

### Composition Order

Sequential composition reads **right-to-left**:

```typescript
's2 . s1'; // execute s1 first, then s2
```

This matches mathematical composition: `(f ∘ g)(x) = f(g(x))`.

## Theory Background

Atlas implements a **resonance logic** where:

- Truth = conservation of resonance budget
- Equivalence = indistinguishability under the 7 generators
- The 96 classes form natural neighborhoods in byte space
- Content addressing emerges from class structure

The system exhibits:

- **Soundness**: typed programs preserve budgets
- **Completeness**: 7 generators suffice for all computations
- **Determinism**: both evaluators are deterministic
- **Verifiability**: three-pass architecture enables intrinsic verification

## Contributing

This implementation is based on the formal specification v1.0. When modifying:

1. Maintain specification compliance
2. Ensure all tests pass
3. Preserve the zero-dependency constraint
4. Document additions clearly

## License

MIT

## References

- Atlas Seven Layers of Meaning (conceptual framework)
- Atlas Sigil Algebra — Formal Specification v1.0
- Atlas Sigil Parser Spec + Test Vectors v1.0

---

Built with ❤️ for symbolic computation and formal verification.
