# Claude Development Guide for Hologramapp

This document provides guidelines for AI-assisted development (specifically Claude) when working on the hologramapp project. It ensures consistency, quality, and adherence to project standards.

## Core Policy: No Backwards Compatibility

**🚨 CRITICAL: We do NOT support backwards compatibility. If code is obsolete, delete it.**

When migrating to new architectures or patterns:

- **Delete old code** - Don't mark it as `#[deprecated]` or `#[ignore]`
- **Don't add feature gates** - No `#[cfg(feature = "old-api")]`
- **Don't write migration helpers** - Just delete the old API
- **Clean removal over preservation** - Dead code creates technical debt

**Examples**:

- ❌ `#[deprecated(since = "2.0.0", note = "Use new_api instead")]`
- ❌ `#[ignore = "Legacy architecture"]`
- ❌ `#[cfg(feature = "backwards-compat")]`
- ✅ **Just delete it**

This keeps the codebase clean, maintainable, and forward-focused.

## Core Principle: Ruthless Simplicity

**🎯 CRITICAL: Keep files and methods as simple as necessary. Be ruthless in implementing with simplicity.**

When writing code:

- **Favor simplicity over cleverness** - Simple code is maintainable code
- **Delete unnecessary abstractions** - Don't add layers "for future flexibility"
- **Inline small functions** - Don't abstract until you have 3+ use cases
- **Remove unused parameters** - If it's not used, delete it
- **Eliminate dead code paths** - No "just in case" branches

**Examples**:

- ❌ Creating a trait with one implementation "for future backends"
- ❌ Adding `Option<T>` parameters that are always `Some` or always `None`
- ❌ Writing 5-line helper functions used once
- ❌ Keeping commented-out code "for reference"
- ✅ **Direct implementation** - Solve the actual problem at hand
- ✅ **Refactor when needed** - Add abstraction when you have real use cases

**YAGNI (You Aren't Gonna Need It)**: Don't build for imaginary future requirements.

## Project Vision: General Compute Acceleration

**🎯 PRIMARY GOAL: High-performance compute through canonical form compilation**

Hologramapp provides general compute acceleration by compiling operations to their canonical forms. This enables:

- **Canonical Compilation** - Operations compiled to optimal geometric representation
- **Hologram Compiler-Powered** - Pattern-based canonicalization reduces operations to minimal form
- **Lowest Latency** - Canonical forms enable fastest possible execution
- **Universal Compute** - General-purpose acceleration, not domain-specific

### Key Architectural Principles

1. **Canonical Form Compilation**: All operations reduced to canonical geometric representation
2. **Hologram Compiler Canonicalization**: Pattern-based rewriting (H²=I, X²=I, etc.) minimizes operation count
3. **Generator-Based Execution**: 7 fundamental generators (mark, copy, swap, merge, split, quote, evaluate)
4. **Performance through Simplification**: Fewer operations = lower latency
5. **🚨 ABSOLUTELY NO CPU FALLBACKS**: All operations MUST be implemented using hologram-compiler generators. If primitives are missing, extend hologram-compiler itself - never fall back to CPU implementations

## Core Principle: Task Completion Discipline

**🚨 CRITICAL: Complete every task fully. No shortcuts, no excuses.**

When working on a task:

1. **Never stop before completion** - If you start a task, finish it completely
2. **No excuses about constraints** - Do not cite "time constraints", "token limits", or "efficiency" as reasons to shortcut work
3. **Do the work sequentially** - If there are 50 files to update, update all 50 files one by one
4. **No "script-based approaches" to avoid work** - Actually do the edits, don't suggest automation as an excuse
5. **Finish what you start** - If you create a todo list with 26 items, complete all 26 items

### Anti-Patterns to Avoid

❌ "Given the time constraints, let me create a more efficient approach..."
❌ "Due to token limits, I'll write a script instead..."
❌ "To save time, let me batch these changes..."
❌ "I'll stub this out for now..."

✅ **Just do the work.** Edit every file. Complete every function. Finish every test.

### Why This Matters

Incomplete work compounds:

- Leaves the codebase in a broken state
- Creates technical debt that must be fixed later
- Wastes the user's time when they have to ask again
- Undermines trust in the development process

**If you're asked to complete 10 operations rewrites, rewrite all 10 operations. Period.**

### Completion Criteria

**A feature is not complete if the workspace tests don't pass or if there are compiler warnings.**

Before marking any task as complete:

- Run `cargo test --workspace` and ensure all tests pass
- Fix any test failures before moving to the next task
- Run `cargo clippy --workspace -- -D warnings` and fix all warnings
- Ensure the code compiles without any warnings (`cargo build --workspace`)
- Tests are the ultimate source of truth for correctness

## Core Principle: Test-Driven Development

**🚨 CRITICAL: No feature is complete without comprehensive tests.**

Every piece of code written must include:

1. **Unit tests** for individual functions and methods
2. **Integration tests** for component interactions
3. **Property-based tests** (using `proptest`) for mathematical invariants
4. **Documentation tests** in doc comments

### Test Coverage Requirements

- **Minimum 80% code coverage** for all crates
- **100% coverage** for hologram-compiler canonicalization rules and generator compilation
- **All public APIs** must have examples in doc comments that serve as tests
- **All error paths** must be tested
- **Canonicalization correctness** tests for all rewrite rules

## Development Workflow

### 1. Before Writing Code

1. **Understand the requirement** fully
2. **Review existing architecture** and patterns
3. **Write test cases first** (TDD approach)
4. **Design the API** (function signatures, types, traits)

### 2. Writing Code

1. **Implement incrementally** - small, testable chunks
2. **Run tests frequently** - `cargo test` after each change
3. **Document as you go** - doc comments with examples
4. **Follow Rust idioms** and best practices

### 3. After Writing Code

1. **Run full test suite**: `cargo test --workspace` - Fix all test failures
2. **Run clippy**: `cargo clippy --workspace -- -D warnings` - Fix all warnings (zero warnings required)
3. **Verify clean build**: `cargo build --workspace` - Ensure no compiler warnings
4. **Check formatting**: `cargo fmt --check` - Fix any formatting issues
5. **Verify documentation**: `cargo doc --no-deps --workspace`
6. **Update integration tests** if APIs changed

**CRITICAL**: All tests must pass and all warnings must be fixed before proceeding to the next task.

## Testing Standards

### Unit Tests

Every module must have a `#[cfg(test)]` section:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_functionality() {
        // Arrange
        let input = create_test_input();

        // Act
        let result = function_under_test(input);

        // Assert
        assert_eq!(result, expected_value);
    }

    #[test]
    fn test_error_handling() {
        let invalid_input = create_invalid_input();
        assert!(function_under_test(invalid_input).is_err());
    }
}
```

### Property-Based Tests

For canonicalization and class operations, use `proptest`:

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_class_index_in_bounds(class in 0..96u8) {
        // All class operations stay in valid range
        let result = perform_class_operation(class);
        prop_assert!(result < 96);
    }

    #[test]
    fn test_canonicalization_idempotent(expr: String) {
        // Canonicalizing twice gives same result
        let once = Canonicalizer::canonicalize(&expr)?;
        let twice = Canonicalizer::canonicalize(&once)?;
        prop_assert_eq!(once, twice);
    }

    #[test]
    fn test_rewrite_preserves_semantics(circuit: String) {
        // Canonical form evaluates to same result
        let original = evaluate_circuit(&circuit)?;
        let canonical = Canonicalizer::canonicalize(&circuit)?;
        let canonical_result = evaluate_circuit(&canonical)?;
        prop_assert_eq!(original, canonical_result);
    }
}
```

### Integration Tests

Create `tests/` directories for integration tests:

```rust
// tests/integration_test.rs
use hologram_core::{ops, Executor, Result};

#[test]
fn test_full_operation_flow() -> Result<()> {
    let exec = Executor::new()?;

    // Allocate buffers
    let mut input = exec.allocate::<f32>(256)?;
    let mut output = exec.allocate::<f32>(256)?;

    // Setup data
    let data: Vec<f32> = (0..256).map(|i| i as f32).collect();
    input.copy_from_slice(&data)?;

    // Execute operation
    ops::math::vector_add(&exec, &input, &input, &mut output, 256)?;

    // Verify results
    let result = output.to_vec()?;
    assert_eq!(result[0], 0.0);
    assert_eq!(result[1], 2.0);

    Ok(())
}
```

### Documentation Tests

All public APIs must have examples in doc comments:

````rust
/// Compute element-wise sum of two vectors
///
/// # Example
///
/// ```
/// use hologram_core::{ops, Executor};
///
/// let exec = Executor::new().unwrap();
/// let mut a = exec.allocate::<f32>(4).unwrap();
/// let mut b = exec.allocate::<f32>(4).unwrap();
/// let mut c = exec.allocate::<f32>(4).unwrap();
///
/// a.copy_from_slice(&[1.0, 2.0, 3.0, 4.0]).unwrap();
/// b.copy_from_slice(&[5.0, 6.0, 7.0, 8.0]).unwrap();
///
/// ops::math::vector_add(&exec, &a, &b, &mut c, 4).unwrap();
///
/// let result = c.to_vec().unwrap();
/// assert_eq!(result, vec![6.0, 8.0, 10.0, 12.0]);
/// ```
pub fn vector_add<T: bytemuck::Pod>(
    exec: &Executor,
    a: &Buffer<T>,
    b: &Buffer<T>,
    c: &mut Buffer<T>,
    n: usize,
) -> Result<()> {
    // Implementation
}
````

## Code Organization Standards

### Documentation Organization

**All `.md` documentation files should be stored in the `docs/` directory**, with two exceptions:

- `README.md` - Project overview at repository root
- `CLAUDE.md` - This development guide at repository root

**CRITICAL: When creating new TODOs or markdown documentation files, they MUST be placed in the `/docs` directory only.**

Examples of files that belong in `docs/`:

- Architecture documentation
- Schema implementation guides
- API references
- Tutorial and how-to guides
- Design documents
- TODO lists and task tracking documents
- Any new markdown files created during development

### Module Structure

```
crate_name/
└── src/
    ├── lib.rs           # Public API and re-exports
    ├── types.rs         # Core type definitions
    ├── error.rs         # Error types (using thiserror)
    ├── module1.rs       # Focused functionality
    └── module2.rs
```

### Naming Conventions

- **Types**: `PascalCase` (e.g., `ClassIndex`, `GeneratorCall`)
- **Functions**: `snake_case` (e.g., `canonicalize`, `compile_circuit`)
- **Constants**: `SCREAMING_SNAKE_CASE` (e.g., `CLASS_COUNT`, `MAX_GENERATORS`)
- **Traits**: `PascalCase`, descriptive (e.g., `Canonicalizer`, `Executor`)

### Error Handling

Use `thiserror` for error types:

```rust
#[derive(Debug, thiserror::Error)]
pub enum MyError {
    #[error("Invalid value: {0}")]
    InvalidValue(String),

    #[error("Operation failed: {0}")]
    OperationFailed(#[from] std::io::Error),
}

pub type Result<T> = std::result::Result<T, MyError>;
```

## Canonicalization Correctness

### Sigmatics Pattern Rewriting

When implementing features that use Sigmatics canonicalization, **always verify**:

1. **Pattern Equivalence**: Rewrite rules preserve semantics

   ```rust
   // H² = I (Hadamard squared equals identity)
   assert!(sigmatics::equivalent(
       "copy@c05 . mark@c21 . copy@c05 . mark@c21",  // H²
       "mark@c00"                                      // I
   )?);
   ```

2. **Reduction Property**: Canonicalization reduces operation count

   ```rust
   let (original, canonical, reduction) =
       sigmatics::canonicalization_stats("H² circuit")?;
   assert!(canonical <= original);  // Never increases ops
   assert_eq!(reduction, 75.0);     // 4 ops → 1 op
   ```

3. **Idempotence**: Multiple canonicalization passes converge

   ```rust
   let once = Canonicalizer::parse_and_canonicalize(expr)?;
   let twice = Canonicalizer::parse_and_canonicalize(&once.canonical)?;
   assert_eq!(once.canonical, twice.canonical);  // Converged
   ```

4. **96-Class Bounds**: All class indices in valid range

   ```rust
   assert!(class_index < 96);  // All classes in [0, 96)
   ```

### Testing Canonicalization Properties

Create dedicated test modules for canonicalization invariants:

```rust
#[cfg(test)]
mod canonicalization_invariants {
    use super::*;

    #[test]
    fn test_self_inverse_gates_reduce_to_identity() {
        // H² = I
        assert!(sigmatics::equivalent("H.H", "I")?);
        // X² = I
        assert!(sigmatics::equivalent("X.X", "I")?);
        // Z² = I
        assert!(sigmatics::equivalent("Z.Z", "I")?);
    }

    #[test]
    fn test_conjugation_identity() {
        // HXH = Z
        assert!(sigmatics::equivalent("H.X.H", "Z")?);
    }
}
```

## Common Patterns

### Safe Construction with Validation

```rust
pub struct MyType {
    value: u8,
}

impl MyType {
    /// Create with validation
    pub fn new(value: u8) -> Result<Self> {
        if value >= LIMIT {
            return Err(MyError::InvalidValue);
        }
        Ok(Self { value })
    }

    /// Create without validation (unsafe)
    ///
    /// # Safety
    ///
    /// Caller must ensure value < LIMIT
    pub const unsafe fn new_unchecked(value: u8) -> Self {
        Self { value }
    }
}
```

### Thread-Safe State

Use parking_lot for locks:

```rust
use parking_lot::{Mutex, RwLock};
use std::sync::Arc;

#[derive(Clone)]
pub struct SharedState {
    data: Arc<RwLock<Data>>,
}

impl SharedState {
    pub fn read(&self) -> Data {
        *self.data.read()
    }

    pub fn write(&self, value: Data) {
        *self.data.write() = value;
    }
}
```

## Performance Considerations

### Avoid Unnecessary Allocations

```rust
// ❌ Bad: allocates for every call
fn process(items: Vec<Item>) -> Vec<Result> {
    items.into_iter().map(|i| transform(i)).collect()
}

// ✅ Good: use iterators
fn process(items: &[Item]) -> impl Iterator<Item = Result> + '_ {
    items.iter().map(|i| transform(i))
}
```

### Use const where possible

```rust
// ✅ Good: compile-time constants
pub const PAGES: u32 = 48;
pub const BYTES_PER_PAGE: u32 = 256;
pub const TOTAL_ELEMENTS: usize = (PAGES * BYTES_PER_PAGE) as usize;
```

### Benchmark Critical Paths

Create `benches/` directory for criterion benchmarks:

```rust
use criterion::{criterion_group, criterion_main, Criterion};
use hologram_compiler::SigmaticsCompiler;

fn benchmark_canonicalization(c: &mut Criterion) {
    c.bench_function("canonicalize_h_squared", |b| {
        b.iter(|| {
            // Benchmark H² → I canonicalization
            SigmaticsCompiler::compile("copy@c05 . mark@c21 . copy@c05 . mark@c21")
        });
    });
}

criterion_group!(benches, benchmark_canonicalization);
criterion_main!(benches);
```

## Documentation Standards

### Module-Level Documentation

Every module should have header documentation:

````rust
//! # Module Name - Brief Description
//!
//! Longer description of what this module provides.
//!
//! ## Example
//!
//! ```
//! use crate_name::module_name::Type;
//!
//! let value = Type::new();
//! ```
````

### Type Documentation

```rust
/// A class index in the 96-class geometric system
///
/// Represents one of 96 canonical classes in the Sigmatics class system.
/// Each class provides a canonical geometric representation.
#[derive(Debug, Clone, Copy)]
pub struct ClassIndex(u8);
```

### Function Documentation

Use standard sections:

````rust
/// Brief description of what the function does
///
/// # Arguments
///
/// * `arg1` - Description of arg1
/// * `arg2` - Description of arg2
///
/// # Returns
///
/// Description of return value
///
/// # Errors
///
/// Returns `Err` if...
///
/// # Examples
///
/// ```
/// use crate_name::function_name;
///
/// let result = function_name(arg1, arg2)?;
/// assert_eq!(result, expected);
/// ```
pub fn function_name(arg1: Type1, arg2: Type2) -> Result<ReturnType> {
    // Implementation
}
````

## Codebase Architecture

### Crate Structure

The project is organized into two primary crates:

#### **sigmatics** - Geometric Canonicalization Engine

- **Circuit Compiler**: Parses and compiles sigil expressions to generator sequences
- **Pattern-Based Canonicalization**: Applies rewrite rules (H²=I, X²=I, Z²=I, HXH=Z, S²=Z, I·I=I)
- **96-Class System**: Geometric representation with canonical forms
- **AST & Parser**: Expression parsing with lexer and recursive descent parser
- **Rewrite Engine**: Pattern matching and iterative simplification
- **7 Fundamental Generators**: mark, copy, swap, merge, split, quote, evaluate
- **Transform Algebra**: Rotate (R), Twist (T), and Mirror (M) operations
- **Range Operations**: Multi-class vectors for large data processing

**Key responsibility**: Compile circuit expressions to minimal canonical generator sequences

See `crates/sigmatics/README.md` for complete specification

#### **hologram-core** - Operations Library

- **High-Level Operations**: Pre-built operations that compile to canonical kernels
  - `ops::math`: Arithmetic operations (add, sub, mul, div, min, max, abs, neg, relu, etc.)
  - `ops::reduce`: Reductions (sum, min, max)
  - `ops::activation`: Neural network activations (sigmoid, tanh, gelu, softmax)
  - `ops::loss`: Loss functions (mse, cross_entropy, binary_cross_entropy)
  - `ops::linalg`: Linear algebra (gemm, matvec)
  - `ops::memory`: Memory operations (copy, fill)
- **Executor**: High-level interface for operation execution
- **Buffer<T>**: Type-safe memory abstraction
- **Tensor<T>**: Multi-dimensional arrays with PyTorch-like operations
- **Kernel Compilation**: Operations compile to canonical Sigmatics generator sequences

**Key responsibility**: Provide composable operations that leverage Sigmatics canonicalization

See `crates/hologram-core/src/` for operation implementations

### Key Concepts

#### Execution Model

The compilation and execution flow:

```
Application Code
    ↓ calls
Hologram Core Operations (ops::math, ops::reduce, etc.)
    ↓ compiles via
Sigmatics Canonicalization (pattern rewriting)
    ↓ produces
Canonical Generator Sequence (minimal operation count)
    ↓ executes as
Optimized Kernel (lowest latency)
```

**Key principle**: Operations → Canonical Form → Fast Execution

Example:

```rust
// Application calls high-level operation
ops::math::vector_add(&exec, &a, &b, &mut c, n)?;

// ↓ Compiles to canonical Sigmatics circuit
"merge@c[0..N]"  // Addition as merge generator

// ↓ Canonicalization reduces if possible
// Pattern rewriting applies (e.g., merge·merge → merge)

// ↓ Executes minimal canonical form
GeneratorCall::MergeRange { start: 0, end: N, variant: Add }
```

#### Buffer Allocation and Operations

```rust
use hologram_core::{Executor, ops, Result};

let exec = Executor::new()?; // Creates executor

// Allocate buffers
let mut input = exec.allocate::<f32>(1024)?;
let mut output = exec.allocate::<f32>(1024)?;

// Copy data to buffers
input.copy_from_slice(&data)?;

// Execute operations (compiled to canonical kernels)
ops::math::vector_add(&exec, &input, &input, &mut output, 1024)?;

// Copy results back
let results = output.to_vec()?;
```

#### Tensor Operations

```rust
use hologram_core::{Tensor, ops};

// Create tensor from buffer
let tensor_a = Tensor::<f32>::from_buffer(buf_a, vec![4, 8])?;
let tensor_b = Tensor::<f32>::from_buffer(buf_b, vec![8, 3])?;

// Matrix multiplication
let result = tensor_a.matmul(&exec, &tensor_b)?;

// Zero-copy operations
let sliced = tensor.select(0, 2)?;       // Select index along dimension
let narrowed = tensor.narrow(1, 0, 4)?;  // Narrow range
let transposed = tensor.transpose()?;     // 2D transpose

// Check broadcasting compatibility
assert!(tensor_a.is_broadcast_compatible_with(&tensor_b));
```

#### Core Operations Pattern

All operations follow the pattern: `ops::module::function(&exec, inputs, &mut outputs, sizes)`

```rust
// Element-wise operations
ops::math::vector_add(&exec, &a, &b, &mut c, n)?;
ops::math::relu(&exec, &input, &mut output, n)?;

// Activations
ops::activation::sigmoid(&exec, &x, &mut y, n)?;
ops::activation::softmax(&exec, &input, &mut output, n)?;

// Reductions (output needs 3 elements for temporaries)
let mut sum_out = exec.allocate::<f32>(3)?;
ops::reduce::sum(&exec, &input, &mut sum_out, n)?;

// Loss functions (output needs 3 elements)
let mut loss = exec.allocate::<f32>(3)?;
ops::loss::mse(&exec, &pred, &target, &mut loss, n)?;
```

### Development Patterns

#### Writing New Operations

Operations in hologram-core compile to canonical Sigmatics generator sequences:

```rust
pub fn my_op<T: bytemuck::Pod>(
    exec: &Executor,
    input: &Buffer<T>,
    output: &mut Buffer<T>,
    n: usize,
) -> Result<()> {
    // Build circuit expression for this operation
    let circuit = format!("merge@c[0..{}]", calculate_class_range(n));

    // Compile to canonical form via Sigmatics
    let compiled = SigmaticsCompiler::compile(&circuit)?;

    // compiled.calls contains minimal generator sequence:
    // - Original: 50 ops
    // - Canonical: 12 ops (76% reduction)
    // - Reduction enables lowest latency execution

    // Execute canonical generator sequence
    exec.execute_compiled(&compiled)?;

    Ok(())
}
```

**Key steps**:

1. Express operation as Sigmatics circuit
2. Compile circuit → canonical generator sequence
3. Canonicalization automatically reduces operation count
4. Execute minimal canonical form
5. Add comprehensive tests verifying canonicalization

**Performance benefit**: Canonicalization reduces 4-8x operations for typical circuits, directly improving latency.

See existing operations in `hologram-core/src/ops/` for complete examples.

#### Testing Strategy

- **Unit tests**: In each module's `#[cfg(test)]` section
- **Integration tests**: In `tests/integration_test.rs`
- **Property tests**: Use `proptest` for mathematical invariants
- **Run frequently**: `cargo test --workspace`

### Important Implementation Notes

#### Reduction and Loss Function Output Buffers

Reduction operations (`sum`, `min`, `max`) and loss functions (`mse`, `cross_entropy`) require **at least 3 elements** in the output buffer for internal temporaries:

```rust
// ✅ Correct: output buffer has 3 elements
let mut sum_out = exec.allocate::<f32>(3)?;
ops::reduce::sum(&exec, &input, &mut sum_out, n)?;
let result = sum_out.to_vec()?[0];  // Result is in first element

// ❌ Wrong: output buffer too small
let mut sum_out = exec.allocate::<f32>(1)?;  // Will error!
ops::reduce::sum(&exec, &input, &mut sum_out, n)?;
```

#### Buffer Mutability

When passing buffers to operations:

- Input buffers: `&Buffer<T>` (immutable reference)
- Output buffers: `&mut Buffer<T>` (mutable reference)

```rust
ops::math::vector_add(&exec, &input_a, &input_b, &mut output, n)?;
                            //  ^         ^          ^^^^ mutable
                            //  |         immutable
                            //  immutable
```

#### Tensor Memory Layout

Tensors use row-major layout (C-style). For a 2D tensor `[M, N]`:

- Element at `[i, j]` is at linear index `i * N + j`
- Strides are computed automatically: `[N, 1]`

Zero-copy operations (select, narrow, slice, transpose) modify only shape/strides/offset, not data.

## Continuous Integration

Before committing code, run:

```bash
# Build everything (must produce zero warnings)
cargo build --workspace --all-targets

# Run all tests (must all pass)
cargo test --workspace

# Check formatting (must pass)
cargo fmt --check

# Run clippy (must produce zero warnings)
cargo clippy --workspace -- -D warnings

# Run integration tests (must all pass)
cargo test --workspace --test '*'
```

**🚨 CRITICAL: All commands must complete successfully with zero warnings before committing code.**

**IMPORTANT: Do NOT run `cargo doc` - it crashes the IDE. Skip documentation building in CI.**

## Checklist for New Features

- [ ] Feature implemented with clear, idiomatic Rust
- [ ] Unit tests written for all functions
- [ ] Property-based tests for mathematical properties
- [ ] Integration tests for cross-component functionality
- [ ] Documentation written with examples
- [ ] Error cases handled and tested
- [ ] Performance considered (benchmarks if critical)
- [ ] Code formatted (`cargo fmt`)
- [ ] **Zero compiler warnings** (`cargo build --workspace` produces no warnings)
- [ ] **Zero clippy warnings** (`cargo clippy --workspace -- -D warnings` passes)
- [ ] **All tests pass** (`cargo test --workspace`)
- [ ] Documentation builds (`cargo doc`)

## Checklist for Bug Fixes

- [ ] Root cause identified
- [ ] Test case added that reproduces the bug
- [ ] Fix implemented
- [ ] Test case now passes
- [ ] Related tests still pass
- [ ] Regression tests added to prevent recurrence
- [ ] **Zero compiler warnings** (`cargo build --workspace` produces no warnings)
- [ ] **Zero clippy warnings** (`cargo clippy --workspace -- -D warnings` passes)
- [ ] **All workspace tests pass** (`cargo test --workspace`)

## Review Criteria

When reviewing code (or having Claude review):

1. **Correctness**: Does it work? Are edge cases handled?
2. **Test Coverage**: Are there sufficient tests?
3. **Documentation**: Is the API documented with examples?
4. **Performance**: Are there obvious inefficiencies?
5. **Maintainability**: Is the code clear and well-organized?
6. **Idioms**: Does it follow Rust best practices?

## Common Pitfalls to Avoid

### Arbitrary Planning

Plan tasks based on architecture. Avoid time estimations for tasks.

### Type Conversions

```rust
// ❌ Bad: can overflow or wrap
let value = (large_number as u8) % LIMIT;

// ✅ Good: explicit range checking
let value = if large_number >= LIMIT as u64 {
    return Err(Error::OutOfRange);
} else {
    large_number as u8
};
```

### Iterator Ranges

```rust
// ❌ Bad: byte overflow (256 wraps to 0)
for byte in 0..BYTES_PER_PAGE as u8 {
    // This never executes!
}

// ✅ Good: use inclusive range
for byte in 0..=255u8 {
    // Correctly iterates over all 256 values
}
```

### Unsafe Code

```rust
// ✅ Always document safety invariants
/// # Safety
///
/// Caller must ensure class_index < 96
pub const unsafe fn new_unchecked(class_index: u8) -> Self {
    Self(class_index)
}

// ✅ Use safe constructor in tests
#[cfg(test)]
let class = unsafe { ClassIndex::new_unchecked(42) };
```

### Non-Production Code

Never output code that is non-production ready, such as:

- "In a real implementation..."
- "For demonstration purposes..."
- "This is a simplified version..."
- "This is a stub..."
- "Placeholder"
- "For simplicity..."

## Resources

### External Resources

- [The Rust Book](https://doc.rust-lang.org/book/)
- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- [Effective Rust](https://www.lurklurk.org/effective-rust/)

### Project Documentation

- [Sigmatics Guide](docs/SIGMATICS_GUIDE.md)
- [Sigmatics Implementation Review](docs/SIGMATICS_IMPLEMENTATION_REVIEW.md)
- [Backend Architecture](docs/BACKEND_ARCHITECTURE.md)
- [Backend Trait Architecture](docs/BACKEND_TRAIT_ARCHITECTURE.md)
- [CPU Backend Tracing](docs/CPU_BACKEND_TRACING.md)

## Contact

For questions or clarifications on development practices, refer to:

- Project documentation in `docs/`
- Existing code patterns in the codebase
- Sigmatics documentation

---

**Remember: The goal is correct, well-tested, maintainable code. Take the time to do it right.**
