# LOOP Instruction Optimization - Findings

**Date**: 2025-10-29
**Status**: ❌ Not beneficial for current architecture

## Summary

Attempted to optimize ISA program generation by replacing unrolled loops with loop instructions (manual loop using SUB+SETcc+BRA pattern). **Result**: Performance degradation of 3-12% across all sizes.

## Performance Comparison

| Size | Baseline (Unrolled) | Loop-Based | Change |
|------|---------------------|------------|--------|
| 256 | 189µs | 212µs | +12% slower |
| 1024 | 1.1ms | 1.2ms | +9% slower |
| 4096 | 9.8ms | 10.1ms | +3% slower |
| 16384 | 500ms | 497ms | ~0% (noise) |

## Root Cause Analysis

### Instruction Count Per Iteration

**Unrolled version** (4 instructions/element):
```
LDG r1, a[offset_i]      # Hardcoded offset = i * elem_size
LDG r2, b[offset_i]      # Hardcoded offset
OP r3, r1, r2
STG c[offset_i], r3      # Hardcoded offset
```

**Loop-based version** (8 instructions/iteration):
```
LDG r1, a[offset_reg]    # Dynamic offset from register
LDG r2, b[offset_reg]
OP r3, r1, r2
STG c[offset_reg], r3
ADD offset_reg, offset_reg, incr  # Update offset
SUB counter, counter, 1           # Update loop counter
SETcc p0, counter > 0             # Check condition
BRA p0, loop_body                 # Conditional branch
```

### Why Loop-Based is Slower

1. **2x instruction count**: 8 instructions vs 4 per element
2. **Extra register operations**: ADD offset, SUB counter, SETcc, BRA
3. **Branch misprediction**: Conditional BRA may mispredict
4. **RegisterIndirectComputed overhead**: Dynamic address calculation vs static

### Total Instructions

For n=1024 elements:
- **Unrolled**: 1024 × 4 = 4,096 instructions
- **Loop-based**: 7 setup + (1024 × 8) = 8,199 instructions

**Loop-based has 2x MORE instructions!**

## What This Tells Us

### ❌ Program Generation is NOT the Bottleneck

- Generating 4,096 vs 8 instructions takes ~microseconds
- Storing in Vec is negligible
- The bottleneck is **execution**, not generation

### ✅ Actual Bottlenecks (from profiling)

Based on code analysis and measurements:

1. **Sequential Lane Execution** (CRITICAL)
   - No parallelism utilized
   - Modern CPUs have 8-16 cores sitting idle
   - Expected improvement: **8-16x with Rayon parallelization**

2. **RwLock Contention** (HIGH)
   - Every LDG/STG acquires RwLock
   - For n=1024: 2,048 LDG + 1,024 STG = 3,072 lock acquisitions
   - Expected improvement: **10-50µs per operation**

3. **HashMap Buffer Lookups** (MEDIUM)
   - 3 HashMap lookups per operation (classes for a, b, c)
   - ~10-20ns overhead per lookup
   - Expected improvement: **30-60ns per operation**

4. **Program Cache Cloning** (MEDIUM)
   - Deep clones of instruction Vec on cache hits
   - For n=1024: Cloning 4,096-instruction Vec
   - Expected improvement: **50-100µs per operation**

## Recommendations

### DO NOT

use loop instructions for element-wise operations. The overhead outweighs any benefits.

### DO

Focus on these optimizations in priority order:

1. **Parallel Lane Execution**: Refactor to use Rayon (8-16x speedup potential)
2. **Lock Coarsening**: Hold RwLock for entire operation, not per-instruction
3. **Array-Based Buffer Mapping**: Replace HashMap with direct array indexing
4. **Arc-Based Program Caching**: Eliminate deep clones

## Conclusion

The performance bottleneck is **execution model**, not instruction count:
- Unrolled loops are fine for small-medium n
- For large n, we need parallel execution, not better loops
- ISA-level optimizations (like loop instructions) are premature

**Next steps**: Revert loop changes, focus on parallelization and lock contention.

---

**Lesson Learned**: Measure first, optimize second. The "obvious" optimization (loop vs unroll) was actually counter-productive.
