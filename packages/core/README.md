# @uor-foundation/sigmatics

The core Atlas Sigil Algebra library - a complete TypeScript implementation of the formal specification v1.0.

## Installation

```bash
npm install @uor-foundation/sigmatics
```

## Quick Start

```typescript
import { Atlas } from '@uor-foundation/sigmatics';

// Parse and evaluate a sigil expression
const result = Atlas.evaluate('evaluate@c21 . copy@c05');

console.log(result.literal.bytes); // [0x2A, 0x0A]
console.log(result.operational.words); // ["phase[h₂=0]", "evaluate", ...]
```

## Module Structure

This package is organized into focused modules:

- **`api`** - High-level `Atlas` class and convenience methods
- **`types`** - TypeScript interfaces and type definitions
- **`lexer`** - Tokenization of sigil expressions
- **`parser`** - AST construction from tokens
- **`evaluator`** - Dual backends (literal/operational)
- **`class-system`** - 96-class equivalence structure and transforms

## Sub-module Imports

You can import specific modules for fine-grained control:

```typescript
// Import specific modules
import { tokenize } from '@uor-foundation/sigmatics/lexer';
import { Parser } from '@uor-foundation/sigmatics/parser';
import { evaluateLiteral } from '@uor-foundation/sigmatics/evaluator';
import type { Phrase, ClassInfo } from '@uor-foundation/sigmatics/types';
```

## API Reference

### Main API

```typescript
// Parse expressions
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
```

### Class Utilities

```typescript
// Get class information
const info = Atlas.classInfo(0x2A);
// → { classIndex: 21, components: {...}, canonicalByte: 0x2A }

// Test equivalence
Atlas.equivalent(0x2A, 0x2B); // → true (same class)

// Get equivalence class
Atlas.equivalenceClass(21); // → [0x2A, 0x2B]
```

### Belt Addressing

```typescript
// Compute belt address
const addr = Atlas.beltAddress(17, 0x2A);
// → { page: 17, byte: 42, address: 4394 }

// Decode address
Atlas.decodeBeltAddress(4394);
// → { page: 17, byte: 42, address: 4394 }
```

## Features

- ✨ **Dual Semantics**: Both literal (byte) and operational (word) backends
- 🎯 **96-Class System**: Authoritative ≡₉₆ equivalence structure
- 🔄 **Transform Algebra**: Rotate (R), Twist (T), and Mirror (M) operations
- 📐 **Formal Grammar**: Complete parser for sigil expressions
- 🌐 **Belt Addressing**: Content-addressable 12,288-slot belt
- ✅ **Verified**: Includes all specification test vectors
- 🚀 **Zero Dependencies**: Pure TypeScript implementation

## Development

```bash
# Build
npm run build

# Test
npm test

# Watch mode
npm run watch
```

## License

MIT © UOR Foundation
