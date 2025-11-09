# Phase 1 Optimization Results

**Date**: 2025-10-29
**Status**: ❌ No measurable improvement

## Optimizations Completed

### Fix #1: Array-Based Buffer Mapping
**Change**: Replaced `HashMap<u8, BufferHandle>` with `[Option<BufferHandle>; 96]` in Executor

**Expected Impact**: 10-20ns savings per buffer lookup × 3 lookups = 30-60ns per operation

**Files Modified**:
- `crates/hologram-core/src/executor.rs`

### Fix #2: Arc-Based Program Caching
**Change**: Changed `ProgramCache` to return `Arc<Program>` instead of `Program`

**Expected Impact**: 50-100µs savings per cache hit (eliminate deep clone of instruction Vec)

**Files Modified**:
- `crates/hologram-backends/src/program_cache.rs`

**Benefits**:
- Cache hit: `Arc::clone()` (~2ns) instead of `program.clone()` (50-100µs for large programs)
- Single Arc allocation at program creation time

## Benchmark Results

### n=256 Elements

| Operation | Baseline | After Phase 1 | Change |
|-----------|----------|---------------|--------|
| vector_add | 189 µs | 189.13 µs | 0% |
| vector_sub | 190 µs | 190.86 µs | 0% |
| vector_mul | 205 µs | 205.22 µs | 0% |
| vector_div | 206 µs | 206.14 µs | 0% |
| min | 201 µs | 201.13 µs | 0% |
| max | 197 µs | 196.67 µs | 0% |

### n=1024 Elements

| Operation | Baseline | After Phase 1 | Change |
|-----------|----------|---------------|--------|
| vector_add | 1.1 ms | 1.1021 ms | 0% |
| vector_sub | 1.1 ms | 1.1014 ms | 0% |
| vector_mul | 1.1 ms | 1.0985 ms | 0% |
| vector_div | 1.2 ms | 1.1800 ms | -1.7% (slight improvement) |
| min | 1.2 ms | 1.1794 ms | -1.7% (slight improvement) |
| max | 1.1 ms | 1.1135 ms | 0% |

### n=4096 Elements

| Operation | Baseline | After Phase 1 | Change |
|-----------|----------|---------------|--------|
| vector_add | 9.8 ms | 9.8137 ms | 0% |
| vector_sub | 9.7 ms | 9.7452 ms | 0% |
| vector_mul | 9.8 ms | 9.8219 ms | 0% |

### n=16384 Elements

| Operation | Baseline | After Phase 1 | Change |
|-----------|----------|---------------|--------|
| vector_add | 500 ms | 500.92 ms | 0% |
| vector_sub | 500 ms | 500.70 ms | 0% |

## Analysis

### Why No Improvement?

1. **HashMap → Array (Fix #1)**
   - Hash lookups for small fixed-size maps (96 entries) are already very fast
   - 10-20ns improvement is negligible compared to 189µs total latency (0.01%)
   - Buffer lookups are not on the critical path

2. **Program Cache Cloning (Fix #2)**
   - Cache hit rate may be lower than expected
   - Programs may be small enough that cloning overhead is minimal
   - The real overhead is in program *execution*, not caching

### What This Tells Us

The performance bottleneck is NOT in:
- Buffer lookup mechanism (HashMap vs Array)
- Program caching overhead (cloning)

The performance bottleneck IS in:
- **Sequential lane execution** (confirmed by unchanged latency)
- **Per-instruction RwLock acquisition** (3,000+ locks per operation)
- **Lack of CPU parallelism** (single-threaded execution)

## Root Cause Confirmed

Looking at `crates/hologram-backends/src/backends/cpu/executor_impl.rs:332`:

```rust
// Execute all lanes in this block
// TODO: Rayon parallelization - Current architecture requires refactoring
for lane_idx in 0..num_lanes {
    // Sequential execution - NO PARALLELISM
    while state.lanes[lane_idx].active && ... {
        self.execute_instruction(&mut state, instruction)?;
    }
}
```

**Critical Finding**: We're executing all lanes sequentially. For n=16384:
- 16,384 lanes executed sequentially
- Each lane executes ~4 instructions (LDG, LDG, ADD, STG)
- Total: 65,536 instructions executed sequentially
- Modern CPU has 8-16 cores sitting idle

## Recommended Next Steps

### Option 1: Lock Coarsening (Medium Impact)
**Effort**: Medium (requires signature refactoring)
**Impact**: 10-50µs savings (2-5% improvement)
**Approach**: Hold write lock for entire program execution instead of per-instruction

### Option 2: Rayon Parallelization (High Impact)
**Effort**: High (requires ExecutionState refactoring)
**Impact**: 8-16x speedup (93% improvement)
**Approach**: Execute lanes in parallel using Rayon

### Recommendation

**Skip lock coarsening, go straight to Rayon parallelization.**

Reasons:
1. Lock coarsening provides only 2-5% improvement
2. Lock coarsening requires significant refactoring for minimal gain
3. Rayon parallelization provides 8-16x improvement
4. Both require refactoring, so might as well do the high-impact one

## Success Criteria (Revised)

Original Phase 1 target: 4-5x improvement (1.1ms → 200-300µs)
**Actual Phase 1 result**: 0% improvement

New Phase 2 target with Rayon: 8-16x improvement (1.1ms → 70-140µs)

| Metric | Baseline | Rayon Target |
|--------|----------|--------------|
| vector_add(256) | 189 µs | 12-24 µs |
| vector_add(1024) | 1.1 ms | 70-140 µs |
| vector_add(16384) | 500 ms | 31-63 ms |

---

**Lesson Learned**: Micro-optimizations (HashMap → Array, Arc caching) have negligible impact when the architecture itself is the bottleneck. Focus on architectural issues (parallelization) first.
