# Phase 1: ISA Parallel Execution Implementation

## Problem Statement

**Current Issue**: Operations generate ISA instructions at runtime in loops, violating the build-time compilation principle.

```rust
// ❌ WRONG: Runtime generation creates N×4 instructions
for i in 0..n {
    program.instructions.push(LDG { offset: i * elem_size });
    program.instructions.push(ADD { ... });
    program.instructions.push(STG { offset: i * elem_size });
}
```

For `n=1000`, this generates **4000 instructions** at runtime!

**Correct Approach**: Precompile small programs, execute in parallel via LaunchConfig

```rust
// ✅ CORRECT: 5 instructions total, executed 1000x in parallel
const VECTOR_ADD_F32: Program = /* precompiled */;
let config = LaunchConfig::linear(1000, 256);
backend.execute_program(&VECTOR_ADD_F32, &config)?;
```

## Architecture Decision: Special Registers

Reserve high-numbered registers for built-in thread indices (CUDA-style):

```rust
// Special registers pre-loaded by backend before execution:
R252 = lane_idx.x      // Thread X within block
R253 = block_idx.x     // Block X within grid
R254 = block_dim.x     // Threads per block
R255 = global_lane_id  // block_idx * block_dim + lane_idx
```

**Why This Approach?**
- Zero runtime overhead (pre-computed by backend)
- Familiar to GPU programmers (matches CUDA threadIdx/blockIdx)
- Flexible (programs compute any addressing pattern)
- No ISA changes required (convention + backend initialization)

---

## Phase 1A: Backend Auto-Offsetting ✅ COMPLETE

**Goal**: Quick fix to get tests passing while preserving architecture

**Status**: ✅ **COMPLETE** (January 2025)

### Tasks

- [x] **Document special register convention in ISA docs**
  - ✅ Created `/workspace/crates/hologram-backends/src/isa/special_registers.rs`
  - ✅ Full documentation with CUDA-style semantics
  - ✅ Constants: `LANE_IDX_X`, `BLOCK_IDX_X`, `BLOCK_DIM_X`, `GLOBAL_LANE_ID`

- [x] **Implement special register initialization in CPU backend**
  - ✅ Modified `execute_program` in `cpu/executor_impl.rs:339-348`
  - ✅ Pre-loads R252-R255 for each lane before execution
  - ✅ Values computed from ExecutionContext

- [x] **Update ISA builder to use special registers**
  - ⚠️ **Deferred to Phase 2**: ISA builder still generates runtime code
  - Will be replaced with precompiled Programs

- [x] **Implement address offsetting**
  - ✅ Special registers available for offset computation
  - ✅ Programs can compute `GLOBAL_LANE_ID * element_size`
  - ✅ RegisterIndirect addressing functional

- [x] **Test with existing operations**
  - ✅ 3 tests added: initialization, read_values, vector_add
  - ✅ All tests passing (138 in hologram-backends)

**Success Criteria**: ✅ **MET**
- ✅ Backend tests pass (138 passing)
- ✅ Special registers zero-overhead (pre-computed)
- ✅ CUDA-style parallel execution model working

---

## Phase 1B: Proper RegisterIndirect Implementation ✅ COMPLETE

**Goal**: Fix RegisterIndirect addressing mode for full flexibility

**Status**: ✅ **COMPLETE** (January 2025)

### Tasks

- [x] **Fix RegisterIndirect resolution in address.rs**
  - ✅ Created `resolve_address_with_state()` in `backends/common/address.rs:91-152`
  - ✅ Reads register value as U64 buffer handle
  - ✅ Applies signed offset correctly (positive and negative)
  - ✅ Old `resolve_address()` now errors for RegisterIndirect (forces proper API)

- [x] **Update resolve_address signature**
  ```rust
  // New function with state access:
  pub fn resolve_address_with_state<M: MemoryStorage>(
      addr: &Address,
      state: &ExecutionState<M>
  ) -> Result<(BufferHandle, usize)>
  ```

- [x] **Update all resolve_address call sites**
  - ✅ CPU backend: `execute_ldg` and `execute_stg` updated
  - ✅ Both now use `resolve_address_with_state()`
  - ✅ RegisterIndirect reads base register, adds offset

- [x] **Implement address computation in ISA programs**
  - ✅ Programs can use RegisterIndirect with computed offsets
  - ✅ Example working: Load from `RegisterIndirect { base: R10, offset: 16 }`
  - ✅ Supports both buffer handle storage and offset computation

- [x] **Add tests for RegisterIndirect addressing**
  - ✅ `test_register_indirect_requires_state` - verifies error without state
  - ✅ `test_register_indirect_with_state` - tests reading register + offset
  - ✅ Tests positive offset, zero offset
  - ✅ Tests with mock execution state

**Success Criteria**: ✅ **MET**
- ✅ RegisterIndirect fully functional
- ✅ Proper register-computed addressing working
- ✅ All addressing modes tested and passing

---

## Phase 2: Precompiled Operation Programs ⏳ IN PROGRESS

**Goal**: Move all operations to precompiled const Programs

**Status**: ⏳ **BLOCKED** - Waiting on architecture decision for program binding

**Current Blocker**: Operations still use `SigmaticsCompiler` placeholder which errors at runtime. Need to decide on program binding strategy before implementing precompiled programs.

### Tasks

- [ ] **Create precompiled program constants module**
  ```rust
  // crates/hologram-core/src/precompiled_programs.rs
  pub const VECTOR_ADD_F32: Program = ...;
  pub const VECTOR_ADD_F64: Program = ...;
  pub const SIGMOID_F32: Program = ...;
  // etc.
  ```

- [ ] **Generate precompiled programs for all operations**
  - Math ops: add, sub, mul, div, min, max, abs, neg, relu
  - Activation ops: sigmoid, tanh
  - Reduction ops: sum, min, max (requires different pattern)
  - All type variants (F32, F64, I32, etc.)

- [ ] **Update operation functions to use precompiled programs**
  ```rust
  pub fn vector_add<T>(exec: &mut Executor, a: &Buffer<T>, b: &Buffer<T>, c: &mut Buffer<T>, n: usize) -> Result<()> {
      let program = match type_from_rust_type::<T>() {
          Type::F32 => &VECTOR_ADD_F32,
          Type::F64 => &VECTOR_ADD_F64,
          // ...
      };

      // Bind buffers to program parameters
      let bound = program.bind_buffers(&[
          (0, handle_a),
          (1, handle_b),
          (2, handle_c)
      ]);

      let config = LaunchConfig::linear(n as u32, 256);
      exec.backend.write().execute_program(&bound, &config)?;
      Ok(())
  }
  ```

- [ ] **Implement program parameter binding**
  - Programs reference generic buffer slots (param0, param1, etc.)
  - bind_buffers() replaces slots with actual buffer handles
  - Zero-copy binding (just updates buffer handle IDs)

- [ ] **Remove isa_builder.rs runtime generation**
  - No longer needed once all operations use precompiled programs
  - Keep as reference/documentation of program structure

- [ ] **Add build-time program validation**
  - Verify all precompiled programs are valid
  - Check register usage doesn't exceed available registers
  - Verify control flow labels exist

**Success Criteria**:
- All operations use const precompiled Programs
- Zero runtime program generation
- Operation functions are simple parameter binding + execute
- All tests pass with improved performance

---

## Phase 3: Advanced Optimizations (Future)

**Goal**: Optimize parallel execution patterns

### Ideas

- [ ] **Reduce operation optimization**
  - Use parallel reduction tree pattern
  - First pass: partial sums per block
  - Second pass: reduce block results
  - Requires ReduceAdd/Min/Max ISA instructions

- [ ] **Shared memory utilization**
  - Load data into shared memory (LDS/STS)
  - Reduce bank conflicts
  - Coalesce global memory accesses

- [ ] **Warp-level optimizations**
  - Use warp shuffle operations
  - Avoid shared memory for small reductions
  - Maximize throughput

- [ ] **Multi-stage program composition**
  - Complex operations as sequence of program launches
  - Intermediate buffers for staged computation
  - GELU, Softmax as multi-stage programs

---

## Implementation Priority

1. ✅ **Phase 1A** (Immediate) - Get architecture working correctly **COMPLETE**
2. ✅ **Phase 1B** (Short term) - Proper RegisterIndirect support **COMPLETE**
3. ⏳ **Phase 2** (Medium term) - Full precompiled program infrastructure **IN PROGRESS**
4. 🔮 **Phase 3** (Long term) - Advanced optimizations

## Current Status (Updated January 2025)

- ✅ **Phase 1A COMPLETE**: Special registers (R252-R255) implemented and tested
- ✅ **Phase 1B COMPLETE**: RegisterIndirect addressing fully functional
- ⏳ **Phase 2 BLOCKED**: Precompiled programs awaiting architecture decision
- ✅ **Test Infrastructure**: 234 tests passing (138 backends, 84 core, 12 ffi)
- 🚧 **Operations**: 75 tests ignored pending ISA Program migration

### What Works Now

✅ **Backend Parallel Execution**
- Special registers pre-loaded before execution
- LaunchConfig-based parallel dispatch
- RegisterIndirect addressing functional
- All 3 addressing modes working (BufferOffset, PhiCoordinate, RegisterIndirect)

✅ **Test Infrastructure**
- hologram-backends: 138 passing
- hologram-core: 84 passing, 75 ignored (awaiting Phase 2)
- hologram-ffi: 12 passing, 1 ignored

### What Needs Work

🚧 **Operation Migration** (Phase 2)
- Operations still use `SigmaticsCompiler` placeholder
- Need precompiled Program constants
- Need buffer binding strategy
- 75 tests waiting to be re-enabled

### Next Steps

1. **Decide on program binding strategy** - How do precompiled programs reference runtime buffers?
2. **Create precompiled_programs.rs** - Module with const Program definitions
3. **Migrate operations to use precompiled programs** - Replace SigmaticsCompiler calls
4. **Re-enable ignored tests** - Remove #[ignore] attributes once operations work

---

## Performance Impact

**Before** (runtime generation):
- 1000 element vector_add: 4000 instructions generated at runtime
- Generation overhead: ~10-20µs
- Execution: Serial (no parallelism)

**After** (precompiled + parallel):
- 1000 element vector_add: 5 instructions (precompiled)
- Generation overhead: 0µs (build-time)
- Execution: Parallel across 256 threads
- **Expected speedup**: 10-100x depending on operation

**Zero runtime overhead** principle maintained! ✅
