# Atlas Quick Start Guide

## Installation

1. **Install dependencies:**

```bash
npm install
```

2. **Build the project:**

```bash
npm run build
```

3. **Run tests:**

```bash
npm test
```

4. **Run examples:**

```bash
npm run example
```

## Instant Usage (No Build Required)

You can use `ts-node` to run TypeScript directly in the workspace:

```bash
# Run tests from core package
cd packages/core && npx ts-node test/index.ts

# Run examples
cd examples && npx ts-node basic-usage.ts

# Try your own code (from root)
npx ts-node -e "
import Atlas from '@uor-foundation/sigmatics';
console.log(Atlas.prettyPrint('mark@c42'));
"
```

## Basic Usage Patterns

### 1. Parse and Evaluate

```typescript
import Atlas from '@uor-foundation/sigmatics';

// Simple evaluation
const result = Atlas.evaluateBytes('mark@c21');
console.log(result.bytes); // [0x2A]

// Get both backends
const full = Atlas.evaluate('copy@c05');
console.log(full.literal.bytes); // byte output
console.log(full.operational.words); // word output
```

### 2. Class System

```typescript
// Check class membership
const classIdx = Atlas.classIndex(0x2a); // 21

// Get canonical byte
const byte = Atlas.canonicalByte(21); // 0x2A

// Test equivalence
Atlas.equivalent(0x00, 0x01); // true - same class
```

### 3. Transforms

```typescript
// Rotate quadrant
Atlas.evaluateBytes('R+1@ mark@c00');

// Twist context ring
Atlas.evaluateBytes('T+4@ mark@c00');

// Mirror modality
Atlas.evaluateBytes('~@ mark@c13');

// Combine transforms
Atlas.evaluateBytes('R+2 T+3 ~@ mark@c07');
```

### 4. Belt Addressing

```typescript
// Compute address
const addr = Atlas.beltAddress(17, 0x2e);
console.log(addr.address); // 4398

// Use in expressions
Atlas.evaluateBytes('mark@c42@17');
```

### 5. Complex Expressions

```typescript
// Sequential composition (right-to-left)
'copy@c05 . evaluate@c21';

// Parallel composition
'mark@c01 || mark@c02';

// Nested with transforms
'R+1@ (copy@c05 . evaluate@c21 || swap@c42)';
```

## File Structure

```
packages/core/src/
├── api/              # Main Atlas class and high-level API
├── types/            # TypeScript type definitions
├── class-system/     # Class system and ≡₉₆ structure
├── lexer/            # Tokenizer
├── parser/           # Parser (tokens → AST)
└── evaluator/        # Dual backends (literal + operational)
```

## Common Tasks

### Check if bytes are equivalent

```typescript
if (Atlas.equivalent(byte1, byte2)) {
  console.log('Same class!');
}
```

### Get all equivalent bytes

```typescript
const members = Atlas.equivalenceClass(21);
console.log(members); // all bytes in class 21
```

### Pretty print any expression

```typescript
console.log(Atlas.prettyPrint('mark@c42^+3~@17'));
```

### Explore class structure

```typescript
const info = Atlas.classInfo(0x2a);
console.log(info);
// {
//   classIndex: 21,
//   components: { h2: 0, d: 2, l: 5 },
//   canonicalByte: 0x2A
// }
```

## Next Steps

1. Read `README.md` for comprehensive documentation
2. Run `examples/basic-usage.ts` to see all patterns in action
3. Check `packages/core/test/index.ts` for test vectors
4. Start building your own expressions!

## Quick Reference

**Generators:** mark, copy, swap, merge, split, quote, evaluate

**Transforms:**

- `R±k` - rotate quadrant (mod 4)
- `T±k` - twist context ring (mod 8)
- `~` - mirror modality

**Composition:**

- `.` - sequential (right-to-left)
- `||` - parallel

**Sigil:** `c<0..95>` with optional `^±k`, `~`, `@<0..47>`

**Transform prefix:** Apply to whole expression: `R+1@ (...)`

**Transform postfix:** Apply to single sigil: `c42^+3~`
