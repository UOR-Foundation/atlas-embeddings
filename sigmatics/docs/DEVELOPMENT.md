# Sigmatics Development Reference

This document captures the day-to-day workflows for contributors using a
"documentation-driven" mindset. Every change should update the relevant sections
here or in other docs so the repository remains self-explanatory.

## Project Setup

**Initial Setup:**

```bash
npm install     # install all workspace dependencies (run from root)
```

**Core Package Development:**

```bash
cd packages/core
npm run build   # compile TypeScript sources to dist/
npm test        # run spec-aligned test suite (ts-node)
```

**Playground Development:**

```bash
cd apps/playground-web
npm run dev     # start Vite dev server at http://localhost:3000
npm run build   # build production bundle
```

**CLI Playground:**

```bash
cd apps/playground-cli
npm start       # run interactive demonstration
```

**Examples:**

```bash
cd examples
npm start       # run cookbook-style demonstrations
```

Optional tooling (when available):

- `npm run lint` runs ESLint across the TypeScript sources
- `npm run format` applies Prettier to code and Markdown

## Repository Layout

```
packages/
  core/             # Published library (@uor-foundation/sigmatics)
    src/
      api/          # High-level Atlas class façade
      lexer/        # Tokenization (sigil text → tokens)
      parser/       # AST construction (tokens → Phrase)
      evaluator/    # Literal & operational backends
      class-system/ # 96-class structure, transforms, belt addressing
      types/        # Shared TypeScript definitions
      index.ts      # Main entry point, re-exports all modules
    test/           # Spec-aligned test suite
    dist/           # Compiled output (after build)

apps/
  playground-web/   # React/Vite interactive playground
  playground-cli/   # Command-line demonstration tool

examples/           # Usage demonstrations
tools/              # Development utilities (validation, etc.)
docs/               # Specifications, guides, architecture notes
```

## Monorepo Workspace Structure

Sigmatics uses **npm workspaces** for package management:

- Root `package.json` declares workspaces: `packages/*`, `apps/*`, `examples`, `tools/*`
- Each workspace has its own `package.json` with dependencies
- Core package can be imported as `@uor-foundation/sigmatics` from other workspaces
- Changes to core automatically visible to playground/examples during development

**Adding a New Workspace:**

1. Create directory under appropriate category (`packages/`, `apps/`, `tools/`)
2. Add `package.json` with unique name
3. Reference core package via workspace protocol if needed: `"@uor-foundation/sigmatics": "workspace:*"`
4. Run `npm install` from root to link workspaces

## Coding Conventions

- **Zero runtime dependencies**: keep the core library dependency-free. Utilities must live
  in the existing modules under `packages/core/src/`; additional packages are only for
  tooling or UI builds.
- **Modular structure**: each module lives in its own directory with a barrel export
  (`index.ts`). Main entry (`packages/core/src/index.ts`) re-exports all modules for
  external consumers.
- **Import patterns**:
  - Within core: use relative imports (`import { tokenize } from '../lexer'`)
  - External packages: use package imports (`import { Atlas } from '@uor-foundation/sigmatics'`)
  - Sub-module imports available: `@uor-foundation/sigmatics/lexer`, `/parser`, etc.
- **Transforms first-class**: centralize rotation/twist/mirror logic in
  `packages/core/src/class-system/class.ts`. Evaluators should call into the helpers
  instead of reimplementing algebra.
- **Right-to-left sequencing**: sequential composition (`Sequential`) executes last item first.
  Tests assert on both literal and operational outputs—maintain this invariant when
  rewriting traversals.
- **Error messaging**: lexer/parser errors are asserted by substring in tests. Preserve
  wording when changing validation checks.
- **Documentation driven**: whenever behaviour changes, update the test suite and
  relevant Markdown (README, guides, this file) in the same commit.

## Testing Strategy

The test suite in `packages/core/test/index.ts` provides comprehensive coverage:

- **Specification vectors** validate parity with the formal spec
- **Unit suites** cover lexer, parser, class system, evaluator, belt, and integration
  behaviours
- `runTest` standardizes success/failure reporting. If you add new sections, follow the
  existing pattern so human-readable output stays consistent

**Running Tests:**

```bash
cd packages/core
npm test        # runs all tests with ts-node
```

Supplemental testing ideas:

- Extend `examples/basic-usage.ts` with real-world scenarios and verify outputs manually
- Build the playground (`cd apps/playground-web && npm run build`) and inspect the UI
  when making API changes
- Run CLI playground (`cd apps/playground-cli && npm start`) to verify interactive features

## Release Workflow

**Pre-release Checks:**

```bash
cd packages/core
npm run build   # compile TypeScript to dist/
npm test        # ensure all tests pass
```

**Publishing:**

1. Update version in `packages/core/package.json`
2. Update CHANGELOG (if maintained)
3. Ensure `dist/` artifacts exist
4. Publish: `cd packages/core && npm publish --access public`
5. Tag release in git: `git tag v0.2.0 && git push origin v0.2.0`
6. Push to `main`; GitHub Pages workflow publishes playground automatically

**Package Structure:**

- Published package: `@uor-foundation/sigmatics`
- Main entry: `dist/index.js` (compiled from `src/index.ts`)
- Sub-module exports: `/lexer`, `/parser`, `/evaluator`, `/class-system`, `/types`, `/api`
- TypeScript types included in distribution

## GitHub Pages Deployment

The workflow at `.github/workflows/deploy-pages.yml`:

**Build Steps:**

1. Checkout code
2. Run `npm ci` (installs all workspace dependencies)
3. Build core package: `cd packages/core && npm run build`
4. Build playground: `cd apps/playground-web && npm run build`
5. Deploy `apps/playground-web/dist/` to GitHub Pages

**Local Verification:**

```bash
# From root
npm install
cd packages/core && npm run build
cd ../apps/playground-web && npm run build
# Check apps/playground-web/dist/ for output
```

The workflow automatically adjusts the base path for org/user repositories (`*.github.io`).
Verify changes locally before pushing to avoid deployment surprises.

## Documentation Checklist

Before merging a feature or fix:

1. Update README snippets if the public API changed
2. Add or refresh examples/tests demonstrating new behaviour
3. Touch the most relevant guide (`ARCHITECTURE.md`, `DEVELOPMENT.md`, Quickstart) so
   future contributors can pick up the context without spelunking the git history
4. Update module README if adding new exports (`packages/core/README.md`)
5. Re-run `npm run format` (if available) to keep Markdown and code consistent

**File Locations:**

- Main README: `/README.md` (monorepo overview, quick start)
- Core package README: `/packages/core/README.md` (API documentation)
- Architecture guide: `/docs/ARCHITECTURE.md` (module structure, pipeline)
- Development guide: `/docs/DEVELOPMENT.md` (this file - workflows)
- Quickstart: `/QUICKSTART.md` (tutorial-style introduction)
- Specifications: `/docs/atlas_*.md` (formal specs)

Maintaining the docs alongside code keeps Sigmatics accessible and reduces ramp-up time
for new contributors.

## Adding New Modules

To add a new module to the core package:

1. **Create module directory:** `packages/core/src/my-module/`
2. **Add implementation:** `packages/core/src/my-module/my-feature.ts`
3. **Create barrel export:** `packages/core/src/my-module/index.ts`
   ```typescript
   export * from './my-feature';
   ```
4. **Update main entry:** Add to `packages/core/src/index.ts`
   ```typescript
   export * from './my-module';
   ```
5. **Update package.json exports:** Add sub-module export in `packages/core/package.json`
   ```json
   "exports": {
     "./my-module": {
       "import": "./dist/my-module/index.js",
       "types": "./dist/my-module/index.d.ts"
     }
   }
   ```
6. **Add tests:** Create test section in `packages/core/test/index.ts`
7. **Document:** Update `packages/core/README.md` and `docs/ARCHITECTURE.md`

This pattern ensures consistency with existing modules and maintains the clean import structure.
