# Sigmatics-Hologram Integration Architecture

## Overview

This document describes how hologram-core operations integrate with sigmatics canonicalization to achieve lowest-latency execution through automatic circuit optimization.

## Execution Flow

```
Application Code
    ↓ calls
Hologram Core Operations (ops::math_v2, ops::reduce_v2, etc.)
    ↓ compiles via
Sigmatics Canonicalization (pattern rewriting)
    ↓ produces
Canonical Generator Sequence (minimal operation count)
    ↓ executes as
Optimized Kernel (lowest latency)
```

## Current Implementation (Manual)

**Before Integration:**

```rust
pub fn vector_add<T>(exec: &mut Executor, a: &Buffer<T>, b: &Buffer<T>,
                     c: &mut Buffer<T>, n: usize) -> Result<()> {
    let class_a = get_primary_class(a)?;
    let class_b = get_primary_class(b)?;
    let class_c = get_primary_class(c)?;

    // Manual generator sequence construction
    let mut seq = GeneratorSequence::new();
    seq.merge(class_a, class_c, class_b);
    let seq = seq.finalize();

    exec.execute_generators(seq)?;
    Ok(())
}
```

**Issues:**

- No canonicalization - operation count not minimized
- Manual generator construction - error-prone
- No pattern-based optimization
- Cannot benefit from automorphism group transformations

## Integrated Implementation (Sigmatics)

**After Integration:**

```rust
use hologram_compiler::SigmaticsCompiler;

pub fn vector_add<T>(exec: &mut Executor, a: &Buffer<T>, b: &Buffer<T>,
                     c: &mut Buffer<T>, n: usize) -> Result<()> {
    let class_a = get_primary_class(a)?;
    let class_b = get_primary_class(b)?;
    let class_c = get_primary_class(c)?;

    // Express operation as sigmatics circuit
    let circuit = format!("merge@c{:02}", class_a);

    // Compile through sigmatics with canonicalization
    let compiled = SigmaticsCompiler::compile(&circuit)?;

    // Log reduction statistics
    tracing::debug!(
        original_ops = compiled.original_ops,
        canonical_ops = compiled.canonical_ops,
        reduction_pct = compiled.reduction_pct,
        "sigmatics_canonicalization"
    );

    // Execute canonical generator sequence
    exec.execute_sigmatics_generators(&compiled)?;

    Ok(())
}
```

**Benefits:**

- ✅ Automatic canonicalization reduces operation count
- ✅ Pattern-based optimization (H²=I, X²=I, etc.)
- ✅ Automorphism group transformations find optimal views
- ✅ Build-time precomputation for common circuits
- ✅ Zero runtime overhead for optimization decisions

## Integration Patterns

### 1. Single Generator Operations

**Vector Add** (single merge):

```rust
let circuit = format!("merge@c{:02}", class_a);
let compiled = SigmaticsCompiler::compile(&circuit)?;
```

### 2. Composite Operations

**Hadamard² = Identity** (4 ops → 1 op):

```rust
// Before canonicalization: copy . mark . copy . mark
let circuit = "copy@c05 . mark@c21 . copy@c05 . mark@c21";
let compiled = SigmaticsCompiler::compile(&circuit)?;

// After canonicalization: mark@c00 (identity)
// Reduction: 75% (4 ops → 1 op)
```

### 3. Range Operations

**Vector operations on large tensors**:

```rust
// Multi-class range for 30K element vector
let circuit = format!("merge@c[0..9]");  // 10 classes
let compiled = SigmaticsCompiler::compile(&circuit)?;
```

### 4. Transformed Operations

**With automorphism transformations**:

```rust
// Apply rotation transform for optimal alignment
let circuit = format!("merge@c{:02}^+2", class_a);  // R²
let compiled = SigmaticsCompiler::compile(&circuit)?;
```

## Canonicalization Examples

### Example 1: H² → I (Identity Elimination)

```rust
// Original circuit (4 generators)
let h_squared = "copy@c05 . mark@c21 . copy@c05 . mark@c21";

// Sigmatics canonicalization recognizes H² = I pattern
let compiled = SigmaticsCompiler::compile(h_squared)?;

// Result: mark@c00 (identity, 1 generator)
// Reduction: 75% (4 → 1)
```

### Example 2: HXH → Z (Gate Conjugation)

```rust
// Original circuit (3 generators)
let hxh = "copy@c05 . copy@c15 . copy@c05";

// Sigmatics recognizes HXH = Z pattern
let compiled = SigmaticsCompiler::compile(hxh)?;

// Result: copy@c31 (Z gate, 1 generator)
// Reduction: 67% (3 → 1)
```

### Example 3: I·I → I (Identity Composition)

```rust
// Original circuit (2 identities)
let identity_comp = "mark@c00 . mark@c00";

// Sigmatics eliminates redundant identity
let compiled = SigmaticsCompiler::compile(identity_comp)?;

// Result: mark@c00 (1 generator)
// Reduction: 50% (2 → 1)
```

## Reduction Statistics

From build-time precomputation:

| Pattern | Original Ops | Canonical Ops | Reduction |
| ------- | ------------ | ------------- | --------- |
| H² = I  | 4            | 1             | 75%       |
| X² = I  | 4            | 1             | 75%       |
| Z² = I  | 4            | 1             | 75%       |
| HXH = Z | 3            | 1             | 67%       |
| H⁴ = I  | 16           | 1             | 93.75%    |
| I·I = I | 2            | 1             | 50%       |

## Performance Impact

### Latency Reduction

**Direct correlation**: Fewer generators = Lower latency

```
Operation Count Reduction → Direct Latency Improvement
4 ops → 1 op (75% reduction) = 75% latency improvement
```

### Expected Speedups

- **H²/X²/Z² circuits**: 4× faster (4 ops → 1 op)
- **HXH conjugations**: 3× faster (3 ops → 1 op)
- **Complex circuits**: 5-10× faster (aggressive canonicalization)

### Zero Runtime Overhead

All canonicalization happens at compile time:

1. Circuit expression parsed once
2. Pattern matching performed once
3. Canonical form computed once
4. Result cached and reused

## Implementation Guidelines

### For Operation Developers

1. **Express as Circuit**: Represent operation as sigmatics circuit expression
2. **Use SigmaticsCompiler**: Compile via `SigmaticsCompiler::compile()`
3. **Execute Canonical**: Execute the resulting canonical generator sequence
4. **Log Metrics**: Report original_ops, canonical_ops, reduction_pct

### For Performance Engineers

1. **Profile Reductions**: Monitor `reduction_pct` for each operation type
2. **Identify Patterns**: Look for circuits with low reduction percentages
3. **Add Rewrite Rules**: Contribute new pattern-based rules to sigmatics
4. **Benchmark Impact**: Measure end-to-end latency improvements

## Migration Path

### Phase 1: Opt-In (Current)

- Keep existing manual implementations
- Add sigmatics-based variants (e.g., `vector_add_canonical()`)
- Benchmark and compare performance

### Phase 2: Gradual Migration

- Migrate operations one-by-one
- Verify correctness with integration tests
- Measure reduction ratios

### Phase 3: Full Integration

- Replace all manual generator construction
- All operations use sigmatics canonicalization
- Deprecated manual APIs

## Testing Strategy

### Correctness Tests

```rust
#[test]
fn test_vector_add_canonical_correctness() {
    let exec = Executor::new()?;
    let a = exec.allocate::<f32>(1024)?;
    let b = exec.allocate::<f32>(1024)?;
    let mut c_manual = exec.allocate::<f32>(1024)?;
    let mut c_canonical = exec.allocate::<f32>(1024)?;

    // Compare manual vs canonical results
    ops::math_v2::vector_add(&exec, &a, &b, &mut c_manual, 1024)?;
    ops::math_canonical::vector_add(&exec, &a, &b, &mut c_canonical, 1024)?;

    assert_eq!(c_manual.to_vec()?, c_canonical.to_vec()?);
}
```

### Reduction Tests

```rust
#[test]
fn test_h_squared_reduction() {
    let circuit = "copy@c05 . mark@c21 . copy@c05 . mark@c21";
    let compiled = SigmaticsCompiler::compile(circuit)?;

    assert_eq!(compiled.original_ops, 4);
    assert_eq!(compiled.canonical_ops, 1);
    assert_eq!(compiled.reduction_pct, 75.0);
}
```

### Performance Tests

```rust
#[bench]
fn bench_vector_add_canonical(b: &mut Bencher) {
    let exec = Executor::new().unwrap();
    let a = exec.allocate::<f32>(1024).unwrap();
    let b = exec.allocate::<f32>(1024).unwrap();
    let mut c = exec.allocate::<f32>(1024).unwrap();

    b.iter(|| {
        ops::math_canonical::vector_add(&exec, &a, &b, &mut c, 1024).unwrap();
    });
}
```

## Future Enhancements

### 1. Quantum Search (Phase 7)

Use quantum algorithms to search the 2048 automorphism views:

```
Classical Search: O(2048) = 2048 evaluations
Quantum Search:   O(√2048) ≈ 45 evaluations

Speedup: 45× faster automorphism search
```

### 2. Profile-Guided Optimization

Learn optimal automorphism views from runtime profiles:

```rust
// Discover best view for this workload
let profiler = SigmaticsProfiler::new();
let optimal_view = profiler.discover_optimal_view(&circuit, &workload)?;

// Use optimal view for subsequent executions
let compiled = SigmaticsCompiler::compile_with_view(&circuit, optimal_view)?;
```

### 3. Multi-Operation Fusion

Fuse multiple operations into single canonical circuit:

```rust
// Fuse: add(a,b) + mul(c,d) → single canonical circuit
let fused = SigmaticsCompiler::fuse(&[
    "merge@c05",  // add
    "merge@c10",  // mul
])?;

// Execute as single optimized kernel
exec.execute_sigmatics_generators(&fused)?;
```

## References

- [Sigmatics Guide](SIGMATICS_GUIDE.md)
- [Automorphism Group](../crates/sigmatics/src/automorphism_group.rs)
- [Canonical Representation](../crates/sigmatics/src/canonical_repr.rs)
- [Build-Time Configuration](../crates/sigmatics/build.rs)
- [CLAUDE.md Development Guide](../CLAUDE.md)
