# Shareable Instruction Implementation Analysis

## Executive Summary

**Key Finding:** Approximately **1,800-2,000 lines (~80%)** of the remaining CPU executor.rs instruction implementations can be moved to a common `instruction_ops` module and shared across all backends.

**Current State:**
- CPU backend: 2,756 lines remaining (after moving ~1,300 lines to common)
- executor.rs: 2,275 lines
- 51 instruction implementations total

**Recommendation:** Create `backends/common/instruction_ops.rs` to house all backend-agnostic instruction implementations.

---

## Detailed Analysis by Instruction Category

### ✅ **100% Shareable - Register-Only Operations** (~1,500 lines)

These instructions only manipulate registers and are **completely backend-agnostic**:

#### Data Movement (2 instructions, ~150 lines)
- **MOV** - Register-to-register copy (52 lines)
- **CVT** - Type conversion between registers (122 lines)
  - Handles all type conversions: int↔int, float↔float, int↔float, signed↔unsigned
  - Uses macro for code generation
  - Pure register operations

#### Arithmetic (10 instructions, ~550 lines)
- **ADD, SUB, MUL, DIV** - Basic arithmetic (~60 lines each)
- **MAD** - Multiply-add fused operation (~40 lines)
- **FMA** - Fused multiply-add (IEEE-compliant) (~25 lines)
- **MIN, MAX** - Minimum/maximum (~60 lines each)
- **ABS, NEG** - Absolute value, negation (~30 lines each)

**Pattern:** Read 1-3 source registers → compute → write destination register

#### Bitwise/Logical (6 instructions, ~350 lines)
- **AND, OR, XOR** - Bitwise operations (~50 lines each)
- **NOT** - Bitwise negation (~40 lines)
- **SHL, SHR** - Bit shifts (~50 lines each)

**Pattern:** Integer register operations with wrapping semantics

#### Comparison (1 instruction, ~110 lines)
- **SETcc** - Set predicate based on comparison
  - Supports: EQ, NE, LT, LE, GT, GE
  - Compares two registers, sets predicate register

#### Control Flow (5 instructions, ~80 lines)
- **BRA** - Conditional/unconditional branch (~23 lines)
  - Reads predicate, updates PC via labels
- **CALL** - Function call (~16 lines)
  - Pushes return address to call stack
- **RET** - Return from call (~15 lines)
  - Pops call stack
- **LOOP** - Loop construct (~29 lines)
  - Decrements counter register, branches if non-zero
- **EXIT** - Terminate execution (~5 lines)
  - Sets lane.active = false

**Key Insight:** Control flow uses ExecutionState fields (labels, pc, call_stack, active) - all in common!

#### Math Functions (11 instructions, ~170 lines)
- **SIN, COS, TAN** - Trigonometric functions
- **TANH, SIGMOID** - Hyperbolic/activation functions
- **EXP, LOG, LOG2, LOG10** - Exponential/logarithm
- **SQRT, RSQRT** - Square root, reciprocal square root

**Pattern:** Read float register → apply Rust float method → write result
- Uses native Rust methods: `f32::sin()`, `f64::exp()`, etc.
- CPU/GPU/TPU all support these via standard libraries

#### Selection (1 instruction, ~95 lines)
- **SEL** - Predicate-based selection
  - Reads predicate + 2 source registers
  - Writes one source to destination based on predicate

#### Reductions (4 instructions, ~185 lines)
- **ReduceAdd, ReduceMin, ReduceMax, ReduceMul**
  - Reduces range of registers to single value
  - Sequential loop over src_base..src_base+count
  - GPU backend would parallelize, but semantics identical

**Total: ~1,500 lines of pure register operations - 100% shareable**

---

### ✅ **95% Shareable - Pool Operations** (~135 lines)

Pool instructions use the `MemoryStorage` trait, making them backend-agnostic:

- **PoolAlloc** (~12 lines) - Calls `memory.allocate_pool()`, stores handle in register
- **PoolFree** (~11 lines) - Reads handle from register, calls `memory.free_pool()`
- **PoolLoad** (~70 lines) - Reads handle+offset from registers, calls `memory.copy_from_pool()`, writes to register
- **PoolStore** (~70 lines) - Reads handle+offset+value from registers, calls `memory.copy_to_pool()`

**Why Shareable:**
- All use `MemoryStorage` trait methods (already common)
- Register read/write logic is identical across backends
- Bytemuck serialization is standard

**Slight Difference:**
- GPU might optimize with async memory ops, but semantics identical

---

### ⚠️ **90% Shareable - Memory Operations** (~185 lines)

Memory load/store instructions are *mostly* shareable:

- **LDG** - Load from global memory (~66 lines)
- **STG** - Store to global memory (~67 lines)
- **LDS** - Load from shared memory (~56 lines)
- **STS** - Store to shared memory (~58 lines)

**Current Implementation:**
```rust
fn execute_ldg(state: &mut ExecutionState, ty: Type, dst: Register, addr: &Address) -> Result<()> {
    let (handle, offset) = resolve_address(addr)?;  // ✅ Common
    let value_bytes = {
        let memory = state.memory.read();
        load_bytes_from_storage(&*memory, handle, offset, ty.size_bytes())?  // ✅ Common
    };
    // Match on type, deserialize, write to register
    match ty { ... }  // ✅ 100% shareable pattern
}
```

**Why 90% Shareable:**
- Address resolution: ✅ Already common (`resolve_address`)
- Memory access: ✅ Already common (`load_bytes_from_storage`, `store_bytes_to_storage`)
- Serialization: ✅ Uses `bytemuck` (standard)
- Register I/O: ✅ Backend-agnostic

**Slight Difference:**
- GPU might want separate LDS/STS implementations for actual shared memory vs global
- CPU treats LDS=LDG, STS=STG
- Could use trait method or conditional compilation

---

### ❌ **Backend-Specific - Cannot Share** (~80 lines)

These instructions are fundamentally different per backend:

#### Synchronization (2 instructions, ~8 lines)
- **BarSync** - Barrier synchronization
  - **CPU:** No-op (single-threaded)
  - **GPU:** `__syncthreads()` or equivalent
  - **TPU:** Custom barrier primitives
- **MemFence** - Memory fence
  - **CPU:** No-op
  - **GPU:** `__threadfence()` or memory ordering
  - **TPU:** Memory consistency primitives

**Why Backend-Specific:** Synchronization is inherently tied to execution model

#### Main Execution Loop (~72 lines)
- **execute()** function - Program execution orchestration
  - **CPU:** Sequential block iteration, sequential lane iteration
  - **GPU:** Launch kernel, SIMT execution with warp divergence
  - **TPU:** Dataflow scheduling
  - **FPGA:** Pipelined execution

**Why Backend-Specific:** Execution model fundamentally differs

---

## Recommended Architecture

### Create `backends/common/instruction_ops.rs`

Move all 100% and 95% shareable instructions (~1,635 lines):

```rust
// backends/common/instruction_ops.rs

use super::{ExecutionState, MemoryStorage};
use crate::error::Result;
use crate::isa::*;

// Data Movement Operations
pub fn execute_mov<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register
) -> Result<()> {
    // 100% shareable implementation
}

pub fn execute_cvt<M: MemoryStorage>(...) -> Result<()> { ... }

// Arithmetic Operations
pub fn execute_add<M: MemoryStorage>(...) -> Result<()> { ... }
pub fn execute_sub<M: MemoryStorage>(...) -> Result<()> { ... }
// ... all arithmetic ops

// Bitwise Operations
pub fn execute_and<M: MemoryStorage>(...) -> Result<()> { ... }
// ... all bitwise ops

// Control Flow
pub fn execute_bra<M: MemoryStorage>(...) -> Result<()> { ... }
pub fn execute_call<M: MemoryStorage>(...) -> Result<()> { ... }
pub fn execute_ret<M: MemoryStorage>(...) -> Result<()> { ... }
// ... all control flow

// Math Functions
pub fn execute_sin<M: MemoryStorage>(...) -> Result<()> { ... }
// ... all 11 math functions

// Reductions
pub fn execute_reduce_add<M: MemoryStorage>(...) -> Result<()> { ... }
// ... all 4 reductions

// Pool Operations
pub fn execute_pool_alloc<M: MemoryStorage>(...) -> Result<()> { ... }
// ... all 4 pool ops

// Selection
pub fn execute_sel<M: MemoryStorage>(...) -> Result<()> { ... }
```

### Keep Backend-Specific

Each backend keeps its own:

1. **Synchronization:** `execute_bar_sync()`, `execute_memfence()`
2. **Execution Loop:** `execute()` function
3. **Memory Ops (optional):** Backends can override LDS/STS if needed

### CPU Backend After Migration

```rust
// backends/cpu/executor.rs (after migration)

use crate::backends::common::{instruction_ops, atlas_ops, ExecutionState};

fn execute_instruction(state: &mut ExecutionState, instruction: &Instruction) -> Result<()> {
    match instruction {
        // Data Movement - use common
        Instruction::LDG { ty, dst, addr } => execute_ldg(state, *ty, *dst, addr),
        Instruction::STG { ty, src, addr } => execute_stg(state, *ty, *src, addr),
        Instruction::LDS { ty, dst, addr } => execute_lds(state, *ty, *dst, addr),
        Instruction::STS { ty, src, addr } => execute_sts(state, *ty, *src, addr),
        Instruction::MOV { ty, dst, src } => instruction_ops::execute_mov(state, *ty, *dst, *src),
        Instruction::CVT { src_ty, dst_ty, dst, src } => {
            instruction_ops::execute_cvt(state, *src_ty, *dst_ty, *dst, *src)
        }

        // Arithmetic - use common
        Instruction::ADD { ty, dst, src1, src2 } => {
            instruction_ops::execute_add(state, *ty, *dst, *src1, *src2)
        }
        // ... all other arithmetic via instruction_ops::

        // Bitwise - use common
        Instruction::AND { ty, dst, src1, src2 } => {
            instruction_ops::execute_and(state, *ty, *dst, *src1, *src2)
        }
        // ... all other bitwise via instruction_ops::

        // Control Flow - use common
        Instruction::BRA { pred, target } => instruction_ops::execute_bra(state, *pred, target),
        Instruction::CALL { target } => instruction_ops::execute_call(state, target),
        Instruction::RET => instruction_ops::execute_ret(state),
        // ... all other control flow via instruction_ops::

        // Math - use common
        Instruction::SIN { ty, dst, src } => instruction_ops::execute_sin(state, *ty, *dst, *src),
        // ... all other math via instruction_ops::

        // Reductions - use common
        Instruction::ReduceAdd { ty, dst, src_base, count } => {
            instruction_ops::execute_reduce_add(state, *ty, *dst, *src_base, *count)
        }
        // ... all other reductions via instruction_ops::

        // Pool - use common
        Instruction::PoolAlloc { size, dst } => instruction_ops::execute_pool_alloc(state, *size, *dst),
        // ... all other pool ops via instruction_ops::

        // Selection - use common
        Instruction::SEL { ty, dst, pred, src_true, src_false } => {
            instruction_ops::execute_sel(state, *ty, *dst, *pred, *src_true, *src_false)
        }

        // Synchronization - CPU-specific (keep local)
        Instruction::BarSync { id } => execute_bar_sync(state, *id),
        Instruction::MemFence { scope } => execute_memfence(state, *scope),

        // Atlas - already common
        Instruction::ClsGet { dst } => atlas_ops::execute_cls_get(state, *dst),
        // ... etc
    }
}

// CPU-specific implementations (~80 lines)
fn execute_bar_sync(_state: &mut ExecutionState, _id: u8) -> Result<()> {
    // No-op for CPU
    Ok(())
}

fn execute_memfence(_state: &mut ExecutionState, _scope: MemoryScope) -> Result<()> {
    // No-op for CPU
    Ok(())
}

// Keep memory ops local for now (can be moved later if needed)
fn execute_ldg(...) { ... }
fn execute_stg(...) { ... }
fn execute_lds(...) { ... }
fn execute_sts(...) { ... }

// Main execution loop - CPU-specific
pub fn execute(program: &Program, config: &LaunchConfig, memory: &Arc<RwLock<MemoryManager>>) -> Result<()> {
    // Sequential block/lane execution
}
```

**Result:** CPU executor.rs shrinks from 2,275 lines → ~450 lines (~80% reduction!)

---

## Benefits of This Approach

### 1. **Massive Code Reuse**
- **1,635+ lines** shared across all backends
- CPU: 80% reduction (2,275 → 450 lines)
- GPU backend: Start with ~400 lines instead of 2,000+
- TPU backend: Similar savings

### 2. **Consistency & Correctness**
- **Single source of truth** for instruction semantics
- Bug fixes benefit all backends automatically
- Type conversion logic identical everywhere
- Arithmetic overflow behavior consistent

### 3. **Easier Testing**
- Test instruction implementations once
- Backend tests only need to verify execution model
- Reduces test duplication by 80%

### 4. **Faster Backend Development**
- GPU backend only needs to implement:
  - Synchronization (~20 lines)
  - Execution loop (~100 lines)
  - Optionally: LDS/STS overrides (~100 lines)
  - **Total: ~220 lines** vs 2,000+ lines from scratch

### 5. **Maintenance**
- Adding new instructions: Implement once in common
- Modifying instruction semantics: Change once
- Register file changes propagate automatically

---

## Memory Operations Decision

**Option 1: Keep Memory Ops Backend-Specific (Current)**
- Pros: Flexibility for GPU to optimize shared memory
- Cons: ~185 lines duplicated per backend

**Option 2: Move to Common with Override**
- Provide default implementation in common
- Backends can override LDS/STS if needed
- Best of both worlds

**Recommendation:** Move to common with override capability
```rust
// Common provides default (treats LDS=LDG)
pub fn execute_lds<M: MemoryStorage>(...) -> Result<()> {
    execute_ldg(...)  // Default: same as global load
}

// GPU backend overrides
fn execute_lds(...) -> Result<()> {
    // Use actual shared memory
}
```

---

## Implementation Checklist

- [ ] Create `backends/common/instruction_ops.rs` (~1,635 lines)
  - [ ] Data movement: MOV, CVT
  - [ ] Arithmetic: ADD, SUB, MUL, DIV, MAD, FMA, MIN, MAX, ABS, NEG
  - [ ] Bitwise: AND, OR, XOR, NOT, SHL, SHR
  - [ ] Comparison: SETcc
  - [ ] Control flow: BRA, CALL, RET, LOOP, EXIT
  - [ ] Math: SIN, COS, TAN, TANH, SIGMOID, EXP, LOG, LOG2, LOG10, SQRT, RSQRT
  - [ ] Reductions: ReduceAdd, ReduceMin, ReduceMax, ReduceMul
  - [ ] Pool ops: PoolAlloc, PoolFree, PoolLoad, PoolStore
  - [ ] Selection: SEL

- [ ] Add comprehensive tests for instruction_ops (~500 lines)
  - [ ] Unit tests for each instruction
  - [ ] Edge cases (overflow, underflow, NaN, infinity)
  - [ ] Type conversion correctness
  - [ ] Control flow (branches, calls, returns)

- [ ] Update CPU backend to use common instruction_ops
  - [ ] Update execute_instruction dispatcher
  - [ ] Remove local instruction implementations
  - [ ] Keep synchronization ops local
  - [ ] Keep execution loop local

- [ ] Update documentation
  - [ ] Update SHARED_BACKEND_COMPONENTS.md
  - [ ] Document instruction_ops API
  - [ ] Add examples for GPU backend usage

- [ ] Run full test suite
  - [ ] Verify CPU backend still passes all tests
  - [ ] Verify no performance regression

---

## Estimated Impact

### Code Sharing Summary

| Component | Lines | Shareability | Shared? |
|-----------|-------|--------------|---------|
| RegisterFile | 650 | 100% | ✅ Yes |
| ExecutionState | 100 | 85% | ✅ Yes |
| Atlas Operations | 200 | 95% | ✅ Yes |
| Address Resolution | 40 | 100% | ✅ Yes |
| Memory Helpers | 45 | 100% | ✅ Yes |
| Memory Trait | 87 | 90% | ✅ Yes |
| **Instruction Ops** | **1,635** | **95-100%** | ❌ **Not Yet** |
| Memory Ops (LDG/STG/LDS/STS) | 185 | 90% | ❌ No |
| Synchronization | 8 | 0% | ❌ No |
| Execution Loop | 72 | 0% | ❌ No |
| **TOTAL** | **3,022** | | |

**Current State:**
- Shared: 1,122 lines (37%)
- Not shared: 1,900 lines (63%)

**After Moving Instruction Ops:**
- Shared: 2,757 lines (91%)
- Not shared: 265 lines (9%)

**Net Result:**
- CPU backend: 2,756 lines → ~450 lines (84% reduction)
- Future backends start with ~90% of work done
- Single source of truth for instruction semantics

---

## Conclusion

Moving instruction implementations to `backends/common/instruction_ops.rs` would:

1. **Reduce CPU backend from 2,756 → 450 lines** (84% reduction)
2. **Share 2,757 lines (91%) across all backends**
3. **Enable rapid development of GPU/TPU/FPGA backends**
4. **Ensure consistency in instruction semantics**
5. **Simplify testing and maintenance**

This is the **largest remaining opportunity** for code sharing in the backends architecture. The instruction implementations are purely functional transformations on registers and memory, making them ideal candidates for generification over the `MemoryStorage` trait.

**Recommendation: High Priority** - This migration would have the biggest impact on backend development velocity and code maintainability.
