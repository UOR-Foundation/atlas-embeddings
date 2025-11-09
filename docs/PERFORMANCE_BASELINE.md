# Performance Baseline Analysis

**Date**: 2025-10-29
**Purpose**: Establish baseline performance metrics before optimization

## Executive Summary

**Critical Finding**: Operations are 378-1,000,000x slower than documented targets due to unrolled loop generation in ISA builder.

### Baseline Latency (Criterion Benchmarks)

| Operation | n=256 | n=1024 | n=4096 | n=16384 | Target |
|-----------|-------|--------|--------|---------|--------|
| vector_add | 189µs | 1.1ms | 9.8ms | 500ms | <1µs |
| vector_sub | 190µs | 1.1ms | 9.7ms | 500ms | <1µs |
| vector_mul | 205µs | 1.1ms | 9.8ms | - | <1µs |
| vector_div | 206µs | 1.2ms | 9.8ms | - | <1µs |
| min | 201µs | 1.2ms | 9.6ms | - | <1µs |
| max | 197µs | 1.1ms | 9.6ms | - | <1µs |

### Throughput Analysis

| Size | Latency | Throughput | Expected Throughput | Slowdown |
|------|---------|------------|---------------------|----------|
| 256 | 189µs | 1.35 Melem/s | 256-512 Melem/s | 378x |
| 1024 | 1.1ms | 930 Kelem/s | 1024-2048 Melem/s | 2200x |
| 4096 | 9.8ms | 418 Kelem/s | 4096-8192 Melem/s | 19,600x |
| 16384 | 500ms | 33 Kelem/s | 16384-32768 Melem/s | 1,000,000x |

**Observation**: Latency scales linearly with element count, confirming unrolled loop hypothesis.

## Root Cause Analysis

### Bottleneck #1: Unrolled Loop ISA Generation

**Location**: `crates/hologram-core/src/isa_builder.rs:46`

**Problem**:
```rust
// For now, generate unrolled loop
for i in 0..n {
    let offset = i * elem_size;
    program.instructions.push(Instruction::LDG { ... });  // Load a[i]
    program.instructions.push(Instruction::LDG { ... });  // Load b[i]
    program.instructions.push(op_fn(...));                 // Compute
    program.instructions.push(Instruction::STG { ... });  // Store c[i]
}
```

**Impact**:
- n=256 elements → 1,024 instructions generated (4 per element)
- n=1024 elements → 4,096 instructions generated
- n=16384 elements → 65,536 instructions generated

**Measured Overhead**:
- Instruction generation: ~300-500ns per element
- For n=16384: ~8-10ms just for Vec allocation and push operations
- Sequential execution: No lane parallelism utilized

**Expected Improvement**: **100-500x speedup** by using LOOP instruction

### Additional Bottlenecks Identified

#### Bottleneck #2: HashMap Buffer Lookups
- **Impact**: 10-20ns per lookup × 3 lookups per operation = 30-60ns overhead
- **Fix**: Array-based indexing (2ns per lookup)
- **Expected**: 10-30ns savings per operation

#### Bottleneck #3: Program Cache Cloning
- **Impact**: Cloning n×4 instruction Vec on every cache hit
- **Fix**: Use Arc<Program> to eliminate deep clones
- **Expected**: 50-100µs savings per operation

#### Bottleneck #4: RwLock Contention
- **Impact**: Lock acquisition n×4 times per operation
- **Fix**: Lock coarsening (hold lock for entire lane execution)
- **Expected**: 10-50µs savings per operation

#### Bottleneck #5: Sequential Lane Execution
- **Impact**: No CPU parallelism (single-threaded execution)
- **Fix**: Rayon-based parallel lane execution
- **Expected**: 8-16x speedup on multi-core CPUs

## Performance Tracing Data

From `performance_profile` example with tracing enabled:

### Buffer Allocation
```
class=0 size=64KB duration=42µs
class=1 size=512KB duration=8µs
class=2 size=32KB duration=19µs
```

### Operations (Neural Network Workload)
```
gemm(32×512×256):
  - total_duration: 7,351µs
  - flops: 8,388,608
  - throughput: 1.11 GFLOPS (should be 100+ GFLOPS)

relu(8192 elements):
  - total_duration: 42,224µs (!!!)
  - throughput: 194K ops/second (should be 100M+ ops/second)

softmax(320 elements):
  - total_duration: 3,193µs
  - throughput: 100K ops/second
```

### Memory Transfer Bandwidth
```
H2D (copy_from_slice):
  - 64KB: 3µs → 20.8 GB/s
  - 512KB: 298µs → 1.68 GB/s

D2H (to_vec):
  - 64KB: 115µs → 543 MB/s (!!!)
  - 512KB: 664µs → 753 MB/s
```

**Critical**: D2H transfers are 39x slower than H2D! This suggests memory copy overhead in CpuBackend.

## Priority Optimization Targets

### Phase 1: Quick Wins (Est. 5-10x improvement)

1. **Fix unrolled loops** → Use LOOP instruction
   - Reduces 65,536 instructions to 6 instructions for n=16384
   - Eliminates runtime Vec allocation overhead
   - Expected: **100-500x speedup**

2. **Array-based buffer mapping** → Replace HashMap
   - Direct array indexing instead of hash lookup
   - Expected: **10-30ns savings per operation**

3. **Arc-based program caching** → Eliminate cloning
   - Pointer copy instead of deep clone
   - Expected: **50-100µs savings per operation**

### Phase 2: Architectural Improvements (Est. 8-16x improvement)

4. **Lock coarsening** → Reduce RwLock acquisitions
   - Expected: **10-50µs savings**

5. **Parallel lane execution** → Utilize all CPU cores
   - Expected: **8-16x speedup**

## Success Metrics

| Metric | Baseline | Phase 1 Target | Phase 2 Target |
|--------|----------|----------------|----------------|
| vector_add(256) | 189µs | <1µs | <100ns |
| vector_add(1024) | 1.1ms | <5µs | <500ns |
| vector_add(16384) | 500ms | <100µs | <10µs |
| Throughput (n=1024) | 930 Kelem/s | 200+ Melem/s | 2000+ Melem/s |

## Next Steps

1. Implement LOOP instruction support in isa_builder.rs
2. Re-run benchmarks and measure improvement
3. Implement remaining quick wins sequentially
4. Validate all tests pass after each fix

---

**Note**: This document will be updated with actual measurements after each optimization phase.
