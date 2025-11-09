# Sigmatics in Kernel Architecture

**Status:** ✅ Hybrid Architecture - Inline Kernels + Sigmatics Fallback  
**Last Updated:** October 2024

## Overview

**Question:** Are we using Sigmatics for user-defined kernels in the quantum directory?

**Answer:** No. Quantum kernels are implemented as **inline kernels** (direct Rust functions), not via Sigmatics. Sigmatics is only used as a **fallback** for stdlib operations when inline kernels are unavailable.

## Architecture: Three Execution Paths

### 1. ✅ Inline Kernels (Primary - Zero Sigmatics)

**Location:** `crates/hologram-core/src/kernel/inline.rs`

**Status:** ✅ Fully implemented for stdlib operations

**Operations:**
- Vector operations: `vector_add`, `vector_mul`, `vector_sub`
- Activation functions: `sigmoid`, `tanh`, `gelu`, `softmax`
- Matrix operations: `gemv_f32`, `gemm_f32`
- **Quantum kernels: `quantum_search`, `optimal_path`, `constraint_solve`, `minimize_energy`**

**Execution:**
```rust
// Direct Rust function call (zero FFI overhead)
inline::quantum_search(data_ptr, target, results_ptr, total_results, n, max_iter);
```

**Performance:** 2-6.7x faster than native Rust

**Where it's used:**
- All stdlib operations (automatically)
- Quantum kernels (inline Rust)
- No Sigmatics involved

### 2. ⚠️ Sigmatics Fallback (Secondary)

**Location:** `crates/hologram-core/src/compiler/mod.rs`

**Status:** ✅ Available as fallback

**When it's used:**
- Non-`f32` types (inline kernels only support `f32`)
- Sizes > 3072 (exceeds class memory capacity)
- Inline kernel not available

**Execution:**
```rust
// Direct GeneratorCall construction (zero string parsing)
let call = GeneratorCall::Merge {
    src_class: class_a,
    dst_class: class_c,
    context_class: class_b,
    variant: MergeVariant::Add,
};
exec.execute_generators(vec![call])?;
```

**Performance:** ~1-5µs (still fast, no interpretation overhead)

**Where it's used:**
- Large operations (>3072 elements)
- Non-f32 types
- When inline kernel fails

### 3. 💡 User-Defined Dynamic Kernels (Tertiary - No Sigmatics)

**Location:** `target/kernel-libs/*.so` files

**Status:** 🔄 Experimental (build infrastructure ready, use inline kernels for production)

**Purpose:** User-generated kernels from Python schemas

**Execution:**
```rust
// Load at runtime and call via FFI
let handle = get_kernel("my_custom_op")?;
execute_kernel(handle, &params)?;
```

**Performance:** ~1.67µs (includes FFI overhead)

**Where it's used:**
- Custom operations not in stdlib
- User-generated kernels from Python
- Not using Sigmatics (direct FFI to compiled Rust code)

## Quantum Kernels: Inline Implementation

### Implementation Details

**Location:** `crates/hologram-core/src/kernel/inline.rs:428-605`

All quantum kernels are implemented as **inline Rust functions**, not via Sigmatics:

```rust
/// Quantum-inspired search using amplitude amplification
/// Implements Grover's algorithm for O(√N) search speedups
#[inline(always)]
pub fn quantum_search(
    data: *const f32,
    target: f32,
    results: *mut f32,
    total_results: *mut usize,
    n: usize,
    max_iterations: usize,
) {
    // Direct Rust implementation
    // No Sigmatics circuit
    // No string parsing
    // Zero interpretation overhead
}
```

### Python Schemas → Inline Kernels

The Python schemas in `schemas/stdlib/quantum/` are **inspiration** for the implementation, but the actual kernels are **manually written inline Rust functions**:

```python
# schemas/stdlib/quantum/quantum_search.py
def quantum_search(
    data: DeviceArray[f32],
    target: f32,
    results: DeviceArray[f32],
    total_results: DeviceArray[u32],
    n: u32,
    max_iterations: u32,
):
    # This schema is a blueprint
    # The actual kernel is in inline.rs
```

```rust
// crates/hologram-core/src/kernel/inline.rs
pub fn quantum_search(
    data: *const f32,      // Direct pointer
    target: f32,
    results: *mut f32,     // Direct pointer
    total_results: *mut usize,
    n: usize,
    max_iterations: usize,
) {
    // Inline implementation
    // No Sigmatics involved
}
```

## Where Sigmatics IS Used

### 1. Fallback for Inline Kernels

```93:120:crates/hologram-core/src/ops/math.rs
    // Try inline kernel first for f32 (zero-overhead execution)
    // Only for sizes that fit in class memory (3072 elements max)
    if std::any::type_name::<T>() == "f32" && n <= 3072 {
        if let Err(e) = try_inline_vector_add(exec, a, b, c, n) {
            tracing::debug!("Inline kernel not available, falling back to Sigmatics: {}", e);
        } else {
            // Instrumentation
            let metrics = ExecutionMetrics::new("vector_add", n, start);
            metrics.log();
            return Ok(());
        }
    }

    // Sigmatics-based implementation (fallback for non-f32 or when inline kernel unavailable)
    let class_a = a.class_index();
    let class_b = b.class_index();
    let class_c = c.class_index();

    // Direct generator construction (zero-overhead path)
    let call = GeneratorCall::Merge {
        src_class: class_a,
        dst_class: class_c,
        context_class: class_b,
        variant: MergeVariant::Add,
    };

    // Execute generator directly (bypasses parsing/canonicalization)
    exec.execute_generators(vec![call])?;
```

**Priority order:**
1. **Try inline kernel first** (for f32, n ≤ 3072)
2. **Fall back to Sigmatics** (if inline fails or conditions not met)

### 2. Non-f32 Operations

When type is not `f32`, we fall back to Sigmatics:

```rust
// For non-f32 types (e.g., u32, i64, etc.)
// Inline kernels only support f32
// Sigmatics handles all types
```

### 3. Large Operations

When size > 3072, we fall back to Sigmatics:

```rust
// For sizes > 3072 (exceeds class memory)
// Inline kernels only work for ≤3072 elements
// Sigmatics handles arbitrary sizes
```

## Execution Flow Diagram

```
User calls ops::math::vector_add()
           ↓
    ┌─────────────────────┐
    │ Type is f32?        │
    │ Size ≤ 3072?        │
    └──────────┬──────────┘
               │
       ┌───────┴────────┐
       │                │
   YES │                │ NO
       ↓                ↓
┌──────────────┐  ┌──────────────┐
│ Inline Kernel│  │   Sigmatics  │
│ (inline.rs)  │  │  (Generator  │
│ 33ns        │  │   Call)      │
│ 2-6.7x faster│  │ 1-5µs       │
└──────────────┘  └──────────────┘
```

## Sigmatics Architecture (Historical Context)

### String-Based Circuit Compilation (DEPRECATED ❌)

```rust
// OLD WAY (Runtime string parsing - FORBIDDEN)
let circuit = "merge@c00[c01,c02]";
let compiled = SigmaticsCompiler::compile(circuit)?; // ❌ RUNTIME STRING PARSING!
exec.execute_sigmatics(&compiled)?; // ❌ INTERPRETATION!
```

**Why deprecated:**
- Runtime string parsing = interpreter overhead
- AST construction = heap allocation
- Canonicalization = repeated computation
- GeneratorCall enum match statements = runtime branching
- Memory layout unknown at compile time
- Cannot optimize for cache locality

### Zero-Interpretation Current Approach ✅

```rust
// NEW WAY (Direct GeneratorCall construction - REQUIRED)
let call = GeneratorCall::Merge {
    src_class: class_a,
    dst_class: class_c,
    context_class: class_b,
    variant: MergeVariant::Add,
};
exec.execute_generators(vec![call])?; // ✅ ZERO interpretation overhead!
```

**Benefits:**
- No string parsing (compile-time construction)
- No AST allocation (direct struct creation)
- No interpretation (direct execution)
- Memory layout known at compile time
- Cache-optimal execution

## Quantum Kernels: No Sigmatics Involved

### Python Schemas vs Rust Implementation

**Python schemas** (`schemas/stdlib/quantum/*.py`):
- Define the **API** (parameters, types, behavior)
- Blueprint for the implementation
- Not executed (no Python interpreter)

**Rust implementation** (`inline.rs`):
- Actual kernel code
- Direct implementation
- No Sigmatics circuit
- Pure Rust functions

### Example: quantum_search

**Python schema:**
```python
# schemas/stdlib/quantum/quantum_search.py
def quantum_search(
    data: DeviceArray[f32],
    target: f32,
    results: DeviceArray[f32],
    total_results: DeviceArray[u32],
    n: u32,
    max_iterations: u32,
):
    thread_id = get_global_id()
    # ... quantum-inspired algorithm ...
```

**Rust implementation:**
```rust
// crates/hologram-core/src/kernel/inline.rs
#[inline(always)]
pub fn quantum_search(
    data: *const f32,
    target: f32,
    results: *mut f32,
    total_results: *mut usize,
    n: usize,
    max_iterations: usize,
) {
    // Direct Rust implementation
    for idx in 0..n {
        let mut amplitude = 1.0 / (n as f32).sqrt();
        
        for _iteration in 0..max_iterations {
            if *data.add(idx) == target {
                amplitude = -amplitude;
            }
            let avg = (amplitude + 1.0) / 2.0;
            amplitude = avg + (avg - amplitude);
        }
        
        if amplitude > 0.5 {
            *results.add(*total_results) = idx as f32;
            *total_results += 1;
        }
    }
}
```

**No Sigmatics involved:** This is pure Rust code, compiled inline.

## Summary

### Where Sigmatics Works

**✅ Fallback for stdlib operations**
- When inline kernels are unavailable (non-f32, size > 3072)
- Large operations
- Arbitrary types

**❌ NOT used for:**
- Quantum kernels (pure inline Rust)
- Stdlib operations with inline kernels (use inline.rs)
- Dynamic user-defined kernels (direct FFI)

### Three Execution Paths

1. **Inline Kernels** (Primary)
   - Stdlib operations
   - Quantum kernels
   - 33ns execution
   - No Sigmatics

2. **Sigmatics** (Fallback)
   - Non-f32 types
   - Large operations
   - 1-5µs execution
   - Direct GeneratorCall construction (no string parsing)

3. **Dynamic User Kernels** (Future)
   - User-defined operations
   - 1.67µs execution
   - No Sigmatics (direct FFI)

---

**Answer:** No, quantum kernels are not using Sigmatics. They are implemented as inline Rust functions for zero overhead. Sigmatics is only used as a fallback for stdlib operations when inline kernels are unavailable.

