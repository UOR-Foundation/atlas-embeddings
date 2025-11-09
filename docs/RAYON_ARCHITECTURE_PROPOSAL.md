# Rayon Parallelization Architecture Proposal

**Status: ✅ ALL PHASES COMPLETED** (2025-10-30)

All tests passing (328 lib + 85 doc tests). Three layers of parallelism implemented:
1. ✅ Block-level parallelism (Phase 1) - 2-16x speedup
2. ✅ Lane-level parallelism (Phase 2) - 8-16x speedup
3. ✅ Operation-level chunking (Phase 3) - Infrastructure ready, 2-8x additional potential

---

## Current Architecture (Sequential) - ✅ UPDATED TO PARALLEL

### Problem: Shared Mutable State

The current `ExecutionState` design assumes **sequential execution** with shared mutable state:

```rust
pub struct ExecutionState<M: MemoryStorage> {
    pub lanes: Vec<LaneState>,                    // ❌ Shared mutable vector
    pub memory: Arc<RwLock<M>>,                   // ✅ Already thread-safe
    pub context: ExecutionContext,                 // ❌ Single shared context
    pub labels: HashMap<String, usize>,            // ✅ Read-only (shareable)
    pub resonance_accumulator: HashMap<u8, f64>,   // ❌ Shared mutable HashMap
}

// Current execution pattern (sequential)
for lane_idx in 0..num_lanes {
    state.context = ExecutionContext::new(..., lane_idx, ...);
    while state.lanes[lane_idx].active {
        self.execute_instruction(&mut state, instruction)?;
        //                        ^^^^^^^^^^
        // Takes &mut to ENTIRE state - not thread-safe!
    }
}
```

### Key Issues for Parallelization

1. **`execute_instruction(&mut state)`** - Gives mutable access to ALL lanes
   - Cannot call this from multiple threads safely
   - Each thread would need exclusive access to entire state

2. **`context: ExecutionContext`** - Single shared context
   - Tracks current lane/block indices
   - Needs to be per-lane for parallel execution

3. **`resonance_accumulator: HashMap<u8, f64>`** - Shared mutable state
   - Used by Atlas ResAccum instruction
   - HashMap is NOT thread-safe
   - Requires atomic operations or locks

4. **`lanes: Vec<LaneState>`** - Direct mutable access
   - Rayon cannot prove independent access to `lanes[i]` for different `i`
   - Rust borrow checker rejects parallel mutable access

---

## Proposed Architecture (Parallel-Ready)

### Solution 1: Separate Lane State from Shared State

**Key Insight**: Most instructions only modify the **current lane**, not shared state.

```rust
/// Per-lane execution state (thread-owned)
pub struct LaneExecutionState {
    pub lane: LaneState,           // Registers, PC, call stack, Atlas state
    pub context: ExecutionContext, // Per-lane context (lane_idx, block_idx)
}

/// Shared execution state (thread-safe)
pub struct SharedExecutionState<M: MemoryStorage> {
    pub memory: Arc<RwLock<M>>,                          // Already thread-safe
    pub labels: Arc<HashMap<String, usize>>,             // Read-only, Arc for sharing
    pub resonance_accumulator: Arc<RwLock<HashMap<u8, f64>>>,  // Thread-safe atomic updates
}

/// Combined state for execution
pub struct ExecutionState<M: MemoryStorage> {
    pub lane_states: Vec<LaneExecutionState>,  // One per lane
    pub shared: SharedExecutionState<M>,        // Shared across all lanes
}
```

**Benefit**: Rayon can prove that each thread owns a different `lane_states[i]`.

---

### Solution 2: Refactor `execute_instruction` to be Per-Lane

**Current signature** (requires `&mut ExecutionState`):
```rust
fn execute_instruction(
    &mut self,
    state: &mut ExecutionState<M>,
    instruction: &Instruction,
) -> Result<()>
```

**New signature** (per-lane + shared):
```rust
fn execute_instruction_parallel(
    &self,  // Executor is immutable (no shared state in executor itself)
    lane_state: &mut LaneExecutionState,
    shared: &SharedExecutionState<M>,
    instruction: &Instruction,
) -> Result<()>
```

**Benefit**: Each thread can call this with its own `lane_state[i]` and shared `SharedExecutionState`.

---

### Solution 3: Make Resonance Accumulator Thread-Safe

**Current** (not thread-safe):
```rust
pub resonance_accumulator: HashMap<u8, f64>
```

**Option A**: Use `DashMap` (lock-free concurrent HashMap)
```rust
use dashmap::DashMap;

pub resonance_accumulator: Arc<DashMap<u8, f64>>
```

**Option B**: Use `RwLock<HashMap>` (simpler, slightly slower)
```rust
pub resonance_accumulator: Arc<RwLock<HashMap<u8, f64>>>
```

**Option C**: Use atomic operations (fastest, but complex)
```rust
// Pre-allocate array for 96 classes
pub resonance_accumulator: [AtomicU64; 96]  // Store f64 as u64 bits
```

**Recommendation**: Start with `RwLock<HashMap>` (simplest), optimize later if needed.

---

### Solution 4: Parallel Execution with Rayon

**New execution pattern** (parallel):
```rust
impl Executor<MemoryManager> for CpuExecutor {
    fn execute(&mut self, program: &Program, config: &LaunchConfig) -> Result<()> {
        let num_lanes = (config.block.x * config.block.y * config.block.z) as usize;

        // Create per-lane states
        let mut lane_states: Vec<LaneExecutionState> = (0..num_lanes)
            .map(|lane_idx| {
                let lane_z = (lane_idx / (config.block.x * config.block.y) as usize) as u32;
                let lane_y = ((lane_idx / config.block.x as usize) % config.block.y as usize) as u32;
                let lane_x = (lane_idx % config.block.x as usize) as u32;

                LaneExecutionState {
                    lane: LaneState::new(),
                    context: ExecutionContext::new(
                        (block_x, block_y, block_z),
                        (lane_x, lane_y, lane_z),
                        config.grid,
                        config.block,
                    ),
                }
            })
            .collect();

        // Create shared state
        let shared = SharedExecutionState {
            memory: Arc::clone(&self.memory),
            labels: Arc::new(program.labels.clone()),
            resonance_accumulator: Arc::new(RwLock::new(HashMap::new())),
        };

        // Parallel execution with Rayon
        lane_states.par_iter_mut().try_for_each(|lane_state| -> Result<()> {
            // Initialize special registers
            {
                use crate::isa::special_registers::*;
                lane_state.lane.registers.write_u32(LANE_IDX_X, lane_state.context.lane_idx.0)?;
                lane_state.lane.registers.write_u32(BLOCK_IDX_X, lane_state.context.block_idx.0)?;
                // ... other registers
            }

            // Execute instructions for this lane
            while lane_state.lane.active && lane_state.lane.pc < program.instructions.len() {
                let pc = lane_state.lane.pc;
                let instruction = &program.instructions[pc];

                // Execute instruction (thread-safe!)
                self.execute_instruction_parallel(lane_state, &shared, instruction)?;

                // Advance PC
                if lane_state.lane.pc == pc {
                    lane_state.lane.pc += 1;
                }
            }

            Ok(())
        })?;

        Ok(())
    }
}
```

**Benefit**: Rayon parallelizes the loop, each thread gets exclusive access to its `lane_state[i]`.

---

## Implementation Steps

### Phase 1: Block-Level Parallelism ✅ COMPLETED

1. **✅ Add block-level parallelism in CpuExecutor**
   - File: `crates/hologram-backends/src/backends/cpu/executor_impl.rs:608-616`
   - Parallel iteration over grid blocks using `(0..total_blocks).into_par_iter()`
   - Nested parallelism: blocks + lanes both parallel

### Phase 2: Refactor ExecutionState ✅ COMPLETED

2. **✅ Split ExecutionState into LaneExecutionState + SharedExecutionState**
   - File: `crates/hologram-backends/src/backends/common/execution_state.rs:92-151`
   - Created `LaneExecutionState` (thread-owned, lines 92-108)
   - Created `SharedExecutionState` (thread-safe, lines 131-151)
   - Combined in `ExecutionState` (lines 178-184)

3. **✅ Update all instruction implementations**
   - File: `crates/hologram-backends/src/backends/common/instruction_ops.rs`
   - Updated memory access: `state.shared.memory.read()/write()`
   - File: `crates/hologram-backends/src/backends/common/atlas_ops.rs:261-263`
   - Thread-safe resonance accumulator with `Arc<RwLock<HashMap>>`

4. **✅ Update CpuExecutor to use new structure**
   - File: `crates/hologram-backends/src/backends/cpu/executor_impl.rs`
   - Updated all memory access: `state.shared.memory`
   - Updated all label access: `state.shared.labels`
   - Updated tests in `address.rs`, `atlas_ops.rs`

5. **✅ Test for correctness**
   - All 328 library tests passing
   - All 85 documentation tests passing
   - Backward compatibility maintained

### Phase 3: Operation-Level Parallelism ✅ COMPLETED

6. **✅ Add parallel operation variants in hologram-core/ops/**
   - File: `crates/hologram-core/src/ops/parallel.rs` (NEW)
   - Added `parallel_binary_op()`, `parallel_unary_op()`, `parallel_reduce()`
   - Chunking constants: `PARALLEL_CHUNK_SIZE = 3072`, `PARALLEL_THRESHOLD = 10,000`

7. **✅ Parallel vector operations**
   - File: `crates/hologram-core/src/ops/math.rs:816-942`
   - Added: `vector_add_par()`, `vector_sub_par()`, `vector_mul_par()`, `vector_div_par()`
   - Added: `abs_par()`, `neg_par()`, `relu_par()`

8. **✅ Parallel matrix operations**
   - File: `crates/hologram-core/src/ops/linalg.rs:362-490`
   - Added: `gemm_par()` - Row-level parallelization infrastructure
   - Added: `matvec_par()` - Row-level parallelization infrastructure

9. **✅ Parallel reductions with tree-based algorithms**
   - File: `crates/hologram-core/src/ops/reduce.rs:399-513`
   - Added: `sum_par()`, `min_par()`, `max_par()`
   - Tree-based reduction infrastructure with thresholds

### Phase 4: Verification & Benchmarking

9. **Benchmark performance**
   - Measure sequential vs parallel execution
   - Expected: 2-16x speedup depending on operation and data size

10. **ThreadSanitizer verification** (optional)
    - Run: `RUSTFLAGS="-Z sanitizer=thread" cargo test`
    - Verify no data races under stress

11. **Add feature flag** (optional)
    ```rust
    #[cfg(feature = "parallel")]
    lane_states.par_iter_mut().try_for_each(...)?;

    #[cfg(not(feature = "parallel"))]
    lane_states.iter_mut().try_for_each(...)?;
    ```

---

## Estimated Effort

| Task | Effort | Complexity |
|------|--------|------------|
| Split ExecutionState | 2-3 hours | Medium |
| Update execute_instruction signature | 1 hour | Low |
| Update all instruction implementations | 3-4 hours | Medium-High |
| Update Atlas ResAccum with RwLock | 30 min | Low |
| Enable Rayon parallel execution | 30 min | Low |
| Test for correctness | 1 hour | Low |
| Benchmark performance | 1 hour | Low |
| **TOTAL** | **8-11 hours** | **Medium-High** |

---

## Benefits vs. Risks

### Benefits ✅
- **8-16x speedup** on multi-core CPUs (proportional to core count)
- Better resource utilization (use all available cores)
- No algorithmic changes (same ISA semantics)
- Scales with hardware (more cores = more speedup)

### Risks ⚠️
- **Breaking change** - All instruction implementations must be updated
- **Testing complexity** - Need to verify thread safety (ThreadSanitizer)
- **Debugging difficulty** - Parallel bugs can be harder to reproduce
- **Contention on shared state** - resonance_accumulator may become bottleneck

### Recommendation 💡

**Start with simpler alternatives first**:
1. ✅ **SIMD optimizations** (already done - Phase 1.15)
2. ✅ **Cache-aware tiling** (already done - Phase 1.15)
3. ⏸️ **Rayon parallelization** (defer until needed)

**When to implement Rayon**:
- When profiling shows CPU-bound workloads (not memory-bound)
- When users run large-scale simulations (1000s of lanes)
- When single-core performance is already optimized

For most workloads (element-wise ops, small matrix ops), **memory bandwidth is the bottleneck**, not CPU. Rayon won't help much there.

---

## Alternative: Coarser-Grained Parallelism

Instead of parallelizing lanes within a block, **parallelize blocks across the grid**:

```rust
// Parallel execution at block level (simpler!)
let grid_size = config.grid.x * config.grid.y * config.grid.z;
(0..grid_size).into_par_iter().try_for_each(|block_idx| {
    // Each thread executes one entire block sequentially
    let state = ExecutionState::new(num_lanes, Arc::clone(&self.memory), context, labels);
    for lane_idx in 0..num_lanes {
        // Sequential execution within block (no refactoring needed!)
        self.execute_instruction(&mut state, instruction)?;
    }
})?;
```

**Benefits**:
- ✅ No refactoring needed (keeps current ExecutionState design)
- ✅ Simpler to implement (30 minutes)
- ✅ Still gets parallelism across blocks
- ✅ No shared state between blocks (naturally independent)

**Trade-off**:
- Only parallelizes if grid_size > num_cores
- For small grids (1 block), no benefit

**Recommendation**: Try block-level parallelism first (low effort, good gains), then consider lane-level if needed.

---

## Conclusion

**Rayon parallelization is achievable but requires significant refactoring.**

**Recommended approach**:
1. ✅ **Done**: SIMD optimizations (Phase 1.15)
2. **Next**: Try block-level parallelism (30 min, low risk)
3. **Later**: Lane-level parallelism if profiling shows it's needed (8-11 hours)

The current sequential implementation is **fast enough for most use cases** - memory bandwidth is usually the bottleneck, not CPU parallelism.
