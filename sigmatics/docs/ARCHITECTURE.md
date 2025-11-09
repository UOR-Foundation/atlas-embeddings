# Sigmatics Architecture Guide

Sigmatics implements the Atlas Sigil Algebra specification in TypeScript using a **modular monorepo workspace architecture**. This guide summarizes the moving parts of the codebase so future contributors can reason about changes without re-reading the entire source.

## Repository Structure

```
sigmatics/
├── packages/
│   └── core/                    # Published library (@uor-foundation/sigmatics)
│       ├── src/
│       │   ├── api/            # High-level Atlas class
│       │   ├── lexer/          # Tokenization
│       │   ├── parser/         # AST construction
│       │   ├── evaluator/      # Literal & operational backends
│       │   ├── class-system/   # 96-class structure & transforms
│       │   ├── types/          # TypeScript type definitions
│       │   └── index.ts        # Main entry point
│       ├── test/               # Test suite
│       └── dist/               # Compiled output
│
├── apps/
│   ├── playground-web/         # React/Vite playground
│   └── playground-cli/         # Command-line demo
│
├── examples/                   # Usage demonstrations
├── tools/                      # Development utilities
└── docs/                       # Documentation
```

## High-Level Pipeline

```
┌──────────────┐   tokenize    ┌─────────────┐   parse    ┌──────────────┐
│ source text  │ ───────────▶  │ Token[]     │ ─────────▶ │ AST (Phrase) │
└──────────────┘               └─────────────┘            └──────────────┘
                                                             │      ▲
                                               evaluateLiteral│      │evaluateOperational
                                                             ▼      │
                                                       ┌───────────────┐
                                                       │ Literal bytes │
                                                       │ Operational   │
                                                       │ words         │
                                                       └───────────────┘
```

1. **Lexer** (`packages/core/src/lexer/`) turns sigil text into tokens, preserving position metadata for accurate error messages.
2. **Parser** (`packages/core/src/parser/`) converts the token stream into an AST shaped by types. Transforms (`R`, `T`, `~`) can appear either as prefixes (wrapping subtrees) or postfix modifiers on sigils.
3. **Evaluator** (`packages/core/src/evaluator/`) interprets the AST twice: `evaluateLiteral` yields canonical byte representatives and (optionally) belt addresses, while `evaluateOperational` produces human-readable control words.
4. **Class System** (`packages/core/src/class-system/`) exposes utilities for translating between bytes, class indices, sigil components, and belt addresses. Both evaluators delegate to this module for canonicalization and transform algebra.
5. **API** (`packages/core/src/api/`) is the façade consumed by library users. The `Atlas` class orchestrates the pipeline and provides convenience methods.

## Module Overview

### `packages/core/src/types/`

Defines the AST, sigil metadata, result shapes, and class/belt structures. Sequential
composition runs right-to-left; parallel composition holds independent sequential
branches.

**Location:** `packages/core/src/types/types.ts`

### `packages/core/src/lexer/`

A single-pass lexer. It skips whitespace/comments, recognizes `||` as parallel, and
maps generator keywords to the `GENERATOR` token type. Unexpected characters raise
error-highlighted errors (tests assert on substrings, so preserve message wording).

**Location:** `packages/core/src/lexer/lexer.ts`

### `packages/core/src/parser/`

Recursive descent parser with explicit lookahead for transforms. It guarantees all
tokens are consumed (final `EOF` check) and emits helpful range validation errors for
classes (`c0..c95`) and pages (`0..47`). Nested transforms use the same AST node as
prefix transforms at the phrase level, so rewrite passes can treat them uniformly.

**Location:** `packages/core/src/parser/parser.ts`

### `packages/core/src/evaluator/`

Contains two mutually independent traversals:

- `evaluateLiteral` walks the AST, pushes transformed sigils through
  `encodeComponentsToByte`, and collects optional belt addresses. Transforms are
  combined via `combineTransforms`, ensuring postfix modifiers apply before prefix
  scopes.
- `evaluateOperational` lowers the AST to a sequence of control words. The walker
  inserts `⊗_*` markers only when actual parallelism is present, mirroring the spec.

Shared helper functions live beside these walkers. The design keeps the evaluator free
from parsing/lexical concerns, making it safe to reuse from other AST producers.

**Location:** `packages/core/src/evaluator/evaluator.ts`

### `packages/core/src/class-system/`

Authoritative implementation of the 96-class resonance structure and belt addressing.
Key exports include:

- `decodeByteToComponents` / `encodeComponentsToByte`
- `componentsToClassIndex` / `classIndexToCanonicalByte`
- `applyTransforms` (`R`, `T`, `M` semantics) and friends
- `computeBeltAddress` / `decomposeBeltAddress`

Both evaluators defer to these helpers for canonical forms and error checking, keeping
transform rules in one place.

**Location:** `packages/core/src/class-system/class.ts`

### `packages/core/src/api/`

The high-level façade consumed by library users. The `Atlas` class orchestrates the
entire pipeline (tokenize → parse → evaluate) and provides convenience methods for
common operations like `parse()`, `evaluate()`, `evaluateBytes()`, `evaluateWords()`,
`prettyPrint()`, and formatting utilities.

**Location:** `packages/core/src/api/index.ts`

### `packages/core/test/`

The spec-aligned test harness. It uses `runTest` to standardize output, covers all
formal vectors, and doubles as working documentation. Add new unit tests through the
existing sections (lexer/parser/class/evaluator/belt/integration) to keep output
consistent.

**Location:** `packages/core/test/index.ts`

### `apps/playground-web/`

React playground that wraps the library for exploratory use. Built with Vite, it
relies on the same bundler configuration as eventual documentation builds. Changing
API surfaces in the core library may require keeping this UI in sync.

**Main component:** `apps/playground-web/src/App.tsx`  
**Entry point:** `apps/playground-web/src/main.tsx`

## Build & Distribution

**Monorepo Workflow:**

- Root `npm install` installs all workspace dependencies
- `cd packages/core && npm run build` compiles TypeScript sources to `dist/`
- `cd apps/playground-web && npm run build` runs Vite to bundle the playground
- `cd packages/core && npm test` runs the test suite with ts-node

**Package Publishing:**

- The published npm package (`@uor-foundation/sigmatics`) exports from `packages/core/`
- Main entry: `packages/core/src/index.ts` re-exports all modules
- Sub-module exports available: `@uor-foundation/sigmatics/lexer`, `/parser`, etc.
- Zero runtime dependencies (only dev dependencies: typescript, ts-node, @types/node)

**GitHub Pages Deployment:**

- Workflow: `.github/workflows/deploy-pages.yml`
- Steps:
  1. Install with `npm ci` at root (installs all workspaces)
  2. Build core: `cd packages/core && npm run build`
  3. Build site: `cd apps/playground-web && npm run build`
  4. Deploy `apps/playground-web/dist/` to GitHub Pages

## Extending the System

1. **New generators**: update `packages/core/src/evaluator/evaluator.ts` (`lowerOperation`)
   and extend the `GeneratorName` type in `packages/core/src/types/types.ts`. Tests should
   cover both literal and operational semantics.
2. **Transform logic**: adjust `packages/core/src/class-system/class.ts` (never duplicate
   logic in evaluators) and ensure spec wording remains in errors for compatibility with
   existing tests.
3. **Parser updates**: modify grammar helpers in `packages/core/src/parser/parser.ts` and
   update tests to assert on ambiguous constructs. Lexer changes often require parser/test
   adjustments in tandem.
4. **Public API**: mirror new helpers in `packages/core/src/api/index.ts` (the Atlas class)
   and ensure they're re-exported in `packages/core/src/index.ts` for package consumers.
5. **New modules**: Create new directory under `packages/core/src/`, add implementation files,
   create `index.ts` barrel export, and update main `packages/core/src/index.ts` to re-export.

## Testing Workflow

Run tests from the core package:

```bash
cd packages/core
npm test
```

The test suite (`packages/core/test/index.ts`) covers:

- Lexer: Token types, error recovery, position tracking
- Parser: AST construction, transform precedence, validation
- Class System: Byte encoding, transform application, equivalence classes
- Evaluator: Both literal and operational backends, spec vectors
- Belt Addressing: Computation and decomposition
- Integration: End-to-end pipeline tests

All tests use the `runTest` helper for consistent output formatting.

- `npm test` executes `packages/core/test/index.ts` via `ts-node`, printing sectioned output.
- Provisionary scripts: `npm run lint` (ESLint) and `npm run format` (Prettier).
- CI relies on these being clean before publish; the GitHub Pages workflow will fail on
  build regressions.

## Related Documentation

- `README.md` – high-level introduction and API samples.
- `QUICKSTART.md` – step-by-step install, build, and transform examples.
- `IMPLEMENTATION_SUMMARY.md` – catalogue of included files and artefacts.
- `docs/` – formal specs, byte mappings, and this architecture guide.

Use this document as a starting point when planning significant changes. Update the
relevant sections in tandem with code to keep the repository documentation-driven.
