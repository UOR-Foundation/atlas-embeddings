# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**atlas-embeddings** is a mathematically rigorous Rust crate implementing the first-principles construction of exceptional Lie groups (G₂, F₄, E₆, E₇, E₈) from the Atlas of Resonance Classes. This is peer-reviewable mathematical code where tests serve as formal proofs.

## Core Principles (CRITICAL)

1. **NO floating point arithmetic** - All computations use exact rational arithmetic (`Fraction`, `i64`, `HalfInteger`)
   - Clippy denies: `float_arithmetic`, `float_cmp`, `float_cmp_const`
   - Use `num-rational::Ratio<i64>` for all rational numbers

2. **NO unsafe code** - `#![forbid(unsafe_code)]` is enforced

3. **First principles only** - Do NOT import Cartan matrices, Dynkin diagrams, or Lie theory from external sources
   - All exceptional groups MUST emerge from Atlas categorical operations
   - Verify properties computationally from Atlas structure

4. **Documentation as paper** - Comprehensive rustdoc with mathematical exposition
   - Mathematical background comes BEFORE implementation
   - Theorems stated in doc comments, proofs are tests
   - All public items must be documented

## Build Commands

### Rust Commands

```bash
# Development
make build              # Standard build
make test               # Run all tests (unit, integration, doc tests)
make test-unit          # Run unit tests only (cargo test --lib)
make test-int           # Run integration tests (cargo test --test '*')
make test-doc           # Run doc tests

# Quality checks
make check              # Cargo check with/without default features
make lint               # Clippy with strictest settings
make format             # Format code
make format-check       # Check formatting without changes
make verify             # Full CI equivalent: format-check + check + lint + test + docs

# Documentation
make docs               # Build docs
make docs-open          # Build and open docs in browser
make docs-private       # Include private items

# Benchmarks
make bench              # Run all benchmarks (uses criterion)
make bench-save         # Save baseline for comparison

# Maintenance
make clean              # Remove all build artifacts
make audit              # Security audit
make deps               # Show dependency tree
```

### Lean 4 Commands

```bash
# Setup and dependencies (run from lean4/ directory)
lake update             # Fetch mathlib4 and dependencies
lake exe cache get      # Download prebuilt mathlib4 binaries (faster)

# Building
lake build              # Build entire project (ALWAYS use this, not module-specific targets)

# Development workflow
lean <file.lean>        # Check single file for errors
lake env lean <file>    # Check file with project dependencies

# Verification (NO `sorry` allowed)
lake build              # All theorems must compile without `sorry`
grep -r "sorry" AtlasEmbeddings/  # Verify no `sorry`s in source

# Cleaning
lake clean              # Remove build artifacts
rm -rf .lake lake-packages  # Deep clean (redownload dependencies)
```

**IMPORTANT**: Always use `lake build` (without module targets) to build the project. Module-specific targets like `lake build AtlasEmbeddings.E8` can cause build issues.

### Lean 4 Development Principles

1. **NO `sorry` POLICY** - Every theorem must be proven
   - This is achievable because all data is finite and explicit
   - Use `decide`, `norm_num`, `fin_cases`, `rfl` for automatic proofs

2. **Exact arithmetic only** - Use `ℚ` (rationals) not `ℝ` (reals)
   - `HalfInteger n` becomes `(n : ℚ) / 2`
   - All E₈ roots are exactly representable

3. **Computational proofs** - Let Lean compute on finite data
   - 240 E₈ roots: explicit list, verify with `decide`
   - 96 Atlas vertices: explicit enumeration
   - All properties decidable on finite domains

## Architecture

### Module Structure

```
src/
├── lib.rs              - Crate-level documentation and re-exports
├── atlas/              - 96-vertex Atlas graph from action functional
├── arithmetic/         - Exact rational arithmetic (NO FLOATS)
│   ├── mod.rs          - Rational, HalfInteger, Vector8 types
│   └── matrix.rs       - RationalMatrix, RationalVector
├── e8/                 - E₈ root system (240 roots, exact coordinates)
├── embedding/          - Atlas → E₈ embedding
├── groups/             - Exceptional group constructions
│   ├── G₂: Product (Klein × ℤ/3) → 12 roots, rank 2
│   ├── F₄: Quotient (96/±) → 48 roots, rank 4
│   ├── E₆: Filtration (degree partition) → 72 roots, rank 6
│   ├── E₇: Augmentation (96+30) → 126 roots, rank 7
│   └── E₈: Direct embedding → 240 roots, rank 8
├── cartan/             - Cartan matrices and Dynkin diagrams
├── weyl/               - Weyl groups and reflections
└── categorical/        - Categorical operations (product, quotient, filtration)
```

### Key Data Structures

- **Atlas**: 96-vertex graph with canonical labels `(e1, e2, e3, d45, e6, e7)`
  - e1-e3, e6-e7 are binary (0/1)
  - d45 is ternary (-1/0/+1) representing e4-e5 difference
  - Mirror symmetry τ: flips e7 coordinate (τ² = identity)

- **E8RootSystem**: 240 roots (112 integer + 128 half-integer)
  - Integer roots: ±eᵢ ± eⱼ for i ≠ j
  - Half-integer roots: all coords ±1/2 with even # of minus signs
  - All roots have norm² = 2 (exact)

- **CartanMatrix<N>**: Rank N encoded at type level
  - Diagonal entries = 2
  - Off-diagonal ≤ 0
  - Simply-laced: off-diagonal ∈ {0, -1} only

- **HalfInteger**: Exact half-integers (numerator/2)
  - Used for E₈ coordinates
  - Preserves mathematical structure

## Testing Strategy

Tests serve as **certifying proofs** of mathematical claims:

- **Unit tests**: Verify individual component properties
- **Integration tests** (`tests/`): End-to-end group constructions
  - `g2_construction.rs`: Klein quartet → 12 roots
  - `f4_construction.rs`: Quotient → 48 roots
  - `e6_construction.rs`: Filtration → 72 roots
  - `e7_construction.rs`: Augmentation → 126 roots
  - `e8_embedding.rs`: Full E₈ → 240 roots
  - `inclusion_chain.rs`: Verify G₂ ⊂ F₄ ⊂ E₆ ⊂ E₇ ⊂ E₈
- **Property tests** (`property_tests.rs`): Algebraic invariants
- **Doc tests**: Examples in documentation must compile and pass

## Clippy Configuration

Strictest settings (`.clippy.toml`):
- `cognitive-complexity-threshold = 15`
- `too-many-arguments-threshold = 5`
- `missing-docs-in-crate-items = true`
- Disallowed names: `foo`, `bar`, `baz`, `tmp`, `temp`
- Doc valid idents: `Atlas`, `E6`, `E7`, `E8`, `F4`, `G2`, `Dynkin`, `Cartan`, `Weyl`

## Dependencies

**Production** (all with `default-features = false`):
- `num-rational` - Exact rational arithmetic
- `num-integer`, `num-traits` - Number traits
- `thiserror` - Error types

**Dev dependencies**:
- `criterion` - Benchmarking with HTML reports
- `proptest`, `quickcheck` - Property-based testing
- `pretty_assertions`, `test-case` - Test utilities

## Work Guidelines (CRITICAL)

### DO NOT Create Intermediate Artifacts

**NEVER** create the following types of files:
- Status reports (e.g., `IMPLEMENTATION_STATUS.md`)
- Fix plans (e.g., `FOUNDATIONS_DOC_FIX.md`)
- Verification summaries
- Progress tracking documents
- TODO lists in separate files

**INSTEAD**:
- Fix issues directly in the actual source files
- Use the TodoWrite tool for tracking (not files)
- Verify by running actual commands (`cargo test`, `cargo doc`)
- Report results directly to the user

### When Errors Occur

1. **Identify the root cause** from compiler output
2. **Fix the actual source files** immediately
3. **Verify the fix** by running the appropriate command
4. **Report concisely** what was wrong and what was fixed

Do NOT create analysis documents or fix plans - just fix it.

## Common Development Tasks

### Adding a New Exceptional Group Construction

1. Implement in `src/groups/mod.rs` with constructor `from_atlas(&Atlas)`
2. Provide methods: `num_roots()`, `rank()`, `weyl_order()`, `cartan_matrix()`
3. Write comprehensive doc comments with mathematical background
4. Add integration test in `tests/{group}_construction.rs`
5. Verify invariants: root count, rank, Cartan matrix properties
6. Update `inclusion_chain.rs` if applicable

### Verifying Mathematical Properties

Use exact arithmetic assertions:
```rust
// Good: exact rational comparison
assert_eq!(root.norm_squared(), Rational::from_integer(2));

// Bad: would use floating point
// assert!((root.norm_squared() - 2.0).abs() < 1e-10);
```

### Running Individual Test

```bash
cargo test --test e6_construction       # Specific integration test
cargo test atlas::tests::test_mirror    # Specific unit test by path
cargo test --doc groups::E6             # Doc test for E6
```

### Lean 4 Common Development Tasks

#### Minimal Complete Progress Strategy (CRITICAL)

**Problem**: Attempting to prove everything at once leads to:
- Compilation errors from incomplete proofs
- Difficulty debugging which theorem fails
- Context switching between multiple unfinished proofs

**Solution**: Build the **minimal complete foundation** incrementally:

1. **Identify the smallest buildable unit**
   - What's the absolute minimum needed for the next layer?
   - Example: `HalfInteger` needs only `add_comm` and `zero_add` to be usable

2. **Implement minimal structure + 2-3 theorems max**
   - Define the structure and instances
   - Prove ONLY the theorems needed immediately
   - Skip theorems that can be added later

3. **Build and verify (NO `sorry`)**
   ```bash
   lake build  # Must succeed
   grep -n "sorry" ModuleName.lean  # Must be empty
   ```

4. **Commit the complete minimal unit**
   - This gives a stable foundation to build on
   - If next steps fail, you can revert to working code

5. **Iterate: Add next minimal layer**
   - Example: With `HalfInteger` proven → build `Vector8`
   - Each layer builds on previous complete layer

**Example: HalfInteger Foundation (78 lines, 2 theorems)**
```lean
structure HalfInteger where
  numerator : ℤ

-- Minimal operations
def new (n : ℤ) : HalfInteger := ⟨n⟩
def zero : HalfInteger := ⟨0⟩
instance : Add HalfInteger := ⟨fun x y => ⟨x.numerator + y.numerator⟩⟩

-- ONLY 2 theorems (not 10)
theorem add_comm (x y : HalfInteger) : x + y = y + x := by ...
theorem zero_add (x : HalfInteger) : zero + x = x := by ...

-- Build it: lake build ✓
-- No sorrys: grep finds nothing ✓
-- Ready for Vector8 ✓
```

This beats trying to prove `toRat_add`, `add_assoc`, `add_zero`, `neg_add_cancel`, etc. all at once.

#### Adding a New Lean Module

1. **Start minimal**: Create file in `lean4/AtlasEmbeddings/ModuleName.lean`
2. Add mathematical background in doc comment at top
3. Import ONLY required mathlib modules (don't over-import)
4. Define core structure and 3-5 essential operations (not all)
5. Prove **2-3 theorems max** (only what's immediately needed)
6. Build and verify: `lake build` (must succeed)
7. Verify zero sorrys: `grep -n "sorry" ModuleName.lean` (must be empty)
8. Add to `lean4/AtlasEmbeddings.lean` imports
9. **Only then** add more theorems if needed for next layer

#### Proving Theorems in Lean 4

**Tactic Strategy for NO `sorry` proofs:**

1. **For structure equality**: Use `apply ext` first
   ```lean
   theorem add_comm (x y : HalfInteger) : x + y = y + x := by
     apply ext  -- Reduces to proving numerators equal
     -- Now goal is: (x + y).numerator = (y + x).numerator
     show x.numerator + y.numerator = y.numerator + x.numerator
     ring  -- Integer arithmetic
   ```

2. **For definitional equality**: Use `show` to make goal explicit
   ```lean
   theorem zero_add (x : HalfInteger) : zero + x = x := by
     apply ext
     show (zero + x).numerator = x.numerator
     show 0 + x.numerator = x.numerator  -- Unfold zero
     ring  -- Proves 0 + n = n
   ```

3. **For computations on finite data**: Use `rfl` or `decide`
   ```lean
   theorem e8_has_240_roots : roots.length = 240 := by
     rfl  -- Lean computes this automatically

   theorem atlas_is_unique : atlas.vertices.length = 96 := by
     decide  -- Decidable computation
   ```

4. **For integer/rational arithmetic**: Use `ring`
   - Works on ℤ and ℚ
   - Does NOT work with division (use `field_simp` or avoid)
   ```lean
   -- Good
   theorem int_arith : x + y = y + x := by ring

   -- Avoid (ring doesn't handle /)
   -- theorem rat_div : (x + y) / 2 = x / 2 + y / 2 := by ring  -- FAILS
   ```

5. **For case analysis**: Use `fin_cases` on finite types
   ```lean
   theorem norm_is_two (r : E8Root) : normSq r = 2 := by
     fin_cases r  -- Check all 240 cases
     all_goals norm_num  -- Prove each numerically
   ```

6. **When stuck**: Use `unfold` then `simp only` then `ring`
   ```lean
   theorem complex_proof : foo = bar := by
     unfold foo bar  -- Expand definitions
     simp only [Add.add, Neg.neg]  -- Simplify specific things
     ring  -- Finish with algebra
   ```

**Common proof pattern for HalfInteger/Vector8:**
```lean
theorem some_property : lhs = rhs := by
  apply ext          -- 1. Reduce to field equality
  show lhs.field = rhs.field  -- 2. Make it explicit
  ring               -- 3. Solve with algebra
```

#### Verifying No `sorry`s

```bash
cd lean4
grep -r "sorry" AtlasEmbeddings/  # Must return empty
lake build                        # All theorems must compile
```
