# Migration Guide

This guide helps existing Sigmatics users migrate to the new modular structure introduced in v0.2.0.

## Summary of Changes

The codebase has been refactored from a flat file structure to a **modular monorepo workspace architecture**:

- **Before:** All code in root directory (`atlas-*.ts` files)
- **After:** Organized into `packages/core/` with subdirectories for each module

**Good News:** ✅ **Zero breaking changes to the public API**

If you're using the standard import (`import { Atlas } from '@uor-foundation/sigmatics'`), your code will continue to work without modifications.

## What Changed

### File Locations

| Old Location (v0.1.x) | New Location (v0.2.0+)                     |
| --------------------- | ------------------------------------------ |
| `atlas-types.ts`      | `packages/core/src/types/types.ts`         |
| `atlas-lexer.ts`      | `packages/core/src/lexer/lexer.ts`         |
| `atlas-parser.ts`     | `packages/core/src/parser/parser.ts`       |
| `atlas-evaluator.ts`  | `packages/core/src/evaluator/evaluator.ts` |
| `atlas-class.ts`      | `packages/core/src/class-system/class.ts`  |
| `atlas.ts`            | `packages/core/src/api/index.ts`           |
| `atlas-test.ts`       | `packages/core/test/index.ts`              |
| `index.tsx`           | `apps/playground-web/src/App.tsx`          |
| `examples.ts`         | `examples/basic-usage.ts`                  |
| `playground.ts`       | `apps/playground-cli/src/index.ts`         |

### Import Patterns

The package now supports **sub-module imports** for more granular access:

```typescript
// Main entry point (unchanged)
import { Atlas } from '@uor-foundation/sigmatics';

// NEW: Sub-module imports for specific functionality
import { tokenize } from '@uor-foundation/sigmatics/lexer';
import { Parser } from '@uor-foundation/sigmatics/parser';
import { evaluateLiteral, evaluateOperational } from '@uor-foundation/sigmatics/evaluator';
import { encodeComponentsToByte, applyTransforms } from '@uor-foundation/sigmatics/class-system';
import type { Phrase, Token, LiteralResult } from '@uor-foundation/sigmatics/types';
```

## Migration Scenarios

### Scenario 1: Basic Usage (No Changes Required)

If you're using the high-level `Atlas` class, **no changes are needed**:

```typescript
// This continues to work exactly as before
import { Atlas } from '@uor-foundation/sigmatics';

const atlas = new Atlas();
const result = atlas.evaluate('c42');
console.log(result);
```

✅ **No migration required**

### Scenario 2: Direct Function Imports

If you were importing specific functions from the old flat structure:

**Before (v0.1.x):**

```typescript
import { tokenize } from '@uor-foundation/sigmatics';
import { Parser } from '@uor-foundation/sigmatics';
import { evaluateLiteral } from '@uor-foundation/sigmatics';
```

**After (v0.2.0+):**

```typescript
// Option 1: Continue using main entry (unchanged)
import { tokenize, Parser, evaluateLiteral } from '@uor-foundation/sigmatics';

// Option 2: Use new sub-module imports (recommended for tree-shaking)
import { tokenize } from '@uor-foundation/sigmatics/lexer';
import { Parser } from '@uor-foundation/sigmatics/parser';
import { evaluateLiteral } from '@uor-foundation/sigmatics/evaluator';
```

Both options work identically. Sub-module imports are recommended for better tree-shaking in bundled applications.

### Scenario 3: Type Imports

Type imports work the same way:

**Before (v0.1.x):**

```typescript
import type { Phrase, Token, LiteralResult } from '@uor-foundation/sigmatics';
```

**After (v0.2.0+):**

```typescript
// Option 1: Main entry (unchanged)
import type { Phrase, Token, LiteralResult } from '@uor-foundation/sigmatics';

// Option 2: Types sub-module (recommended)
import type { Phrase, Token, LiteralResult } from '@uor-foundation/sigmatics/types';
```

### Scenario 4: Contributing or Extending

If you're contributing to Sigmatics or maintaining a fork:

**Within the core package**, import patterns have changed:

**Before:**

```typescript
// In any atlas-*.ts file
import { Token } from './atlas-types';
import { tokenize } from './atlas-lexer';
```

**After:**

```typescript
// In packages/core/src/parser/parser.ts
import type { Token } from '../types';
import { tokenize } from '../lexer';
```

Key points:

- Use **relative imports** (`../module`) within the core package
- Each module has a barrel export (`index.ts`)
- The main entry (`packages/core/src/index.ts`) re-exports everything

## New Features in v0.2.0

### Sub-Module Exports

You can now import from specific modules for better code organization:

```typescript
// Lexer module
import { tokenize } from '@uor-foundation/sigmatics/lexer';

// Parser module
import { Parser } from '@uor-foundation/sigmatics/parser';

// Evaluator module
import { evaluateLiteral, evaluateOperational } from '@uor-foundation/sigmatics/evaluator';

// Class system module
import {
  encodeComponentsToByte,
  decodeByteToComponents,
  applyTransforms,
  computeBeltAddress,
} from '@uor-foundation/sigmatics/class-system';

// Types module
import type {
  Phrase,
  Token,
  Sigil,
  LiteralResult,
  OperationalResult,
} from '@uor-foundation/sigmatics/types';

// API module (Atlas class)
import { Atlas } from '@uor-foundation/sigmatics/api';
```

### Monorepo Structure

The repository is now organized as an npm workspace:

```
sigmatics/
├── packages/core/          # Published library
├── apps/playground-web/    # React playground
├── apps/playground-cli/    # CLI demo
├── examples/               # Usage examples
└── tools/                  # Development utilities
```

This enables better separation of concerns and makes it easier to add new packages in the future.

## Compatibility Matrix

| Package Version | Node.js | TypeScript | Breaking Changes      |
| --------------- | ------- | ---------- | --------------------- |
| v0.1.x          | ≥14     | ≥4.0       | N/A                   |
| v0.2.0          | ≥14     | ≥5.0       | None (API compatible) |

## Troubleshooting

### Import Errors After Upgrade

**Problem:** `Cannot find module '@uor-foundation/sigmatics/lexer'`

**Solution:** Make sure you're using version 0.2.0 or later:

```bash
npm install @uor-foundation/sigmatics@latest
```

### TypeScript Type Errors

**Problem:** Types not resolving for sub-module imports

**Solution:** Ensure your `tsconfig.json` has `moduleResolution` set to `node16` or `bundler`:

```json
{
  "compilerOptions": {
    "moduleResolution": "node16"
  }
}
```

### Build Errors in Monorepo

**Problem:** Building from source in a cloned repository fails

**Solution:** Install workspace dependencies from the root:

```bash
npm install
cd packages/core
npm run build
```

## Getting Help

If you encounter issues during migration:

1. Check the [ARCHITECTURE.md](./ARCHITECTURE.md) for module structure details
2. Review [DEVELOPMENT.md](./DEVELOPMENT.md) for workspace setup
3. See [examples/](../examples/) for usage patterns
4. Open an issue on GitHub with your migration question

## Summary Checklist

- ✅ Main `Atlas` class import works without changes
- ✅ All exported functions available from main entry
- ✅ New sub-module imports available for granular access
- ✅ Types work from both main entry and `/types` sub-module
- ✅ Zero breaking changes to public API
- ✅ Internal file structure reorganized (doesn't affect consumers)
- ✅ Monorepo workspace structure (for contributors)

**Bottom Line:** Update to v0.2.0 and your existing code will continue to work. Explore sub-module imports when you're ready to optimize your bundle size.
