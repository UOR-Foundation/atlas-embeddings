# Backend Architecture Design

## Overview

This document describes the architectural design decisions for the hologram-backends crate, explaining how backend implementations share code while maintaining flexibility and performance.

## Architecture Layers

```text
┌─────────────────────────────────────────────────────────────┐
│                    Application Layer                          │
│  (hologram-core, hologram-ffi, user code)                    │
└────────────────────────────┬──────────────────────────────────┘
                             │
                             │ uses
                             ▼
┌─────────────────────────────────────────────────────────────┐
│              Backend Trait (Public API)                       │
│  src/backend/traits.rs                                       │
│                                                              │
│  pub trait Backend {                                         │
│      fn allocate_buffer(&mut self, size: usize) -> Result   │
│      fn free_buffer(&mut self, handle: BufferHandle)         │
│      fn allocate_pool(&mut self, size: usize) -> Result     │
│      fn execute_program(&mut self, ...) -> Result           │
│  }                                                           │
└────────────────────────────┬──────────────────────────────────┘
                             │
                             │ delegates to
                             ▼
┌─────────────────────────────────────────────────────────────┐
│           Executor Trait (Execution Engine)                  │
│  src/backends/common/executor_trait.rs                       │
│                                                              │
│  pub trait Executor<M: MemoryStorage> {                     │
│      fn execute(&mut self, ...) -> Result                   │
│      fn execute_instruction(&mut self, ...) -> Result       │
│      fn execute_barrier_sync(&mut self, ...) -> Result      │
│      fn execute_memory_fence(&mut self, ...) -> Result      │
│  }                                                           │
│                                                              │
│  ✓ Only 4 methods (backend-specific operations)             │
│  ✓ Clean, focused interface                                 │
│  ✓ Must be implemented for each backend                     │
└────────────────────────────┬──────────────────────────────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
     ┌──────────────┐ ┌──────────────┐ ┌──────────────┐
     │ CpuExecutor  │ │ GpuExecutor  │ │ TpuExecutor  │
     │              │ │   (future)   │ │   (future)   │
     │ impl         │ │              │ │              │
     │ Executor<T>  │ │ impl         │ │ impl         │
     │              │ │ Executor<T>  │ │ Executor<T>  │
     └──────────────┘ └──────────────┘ └──────────────┘
              │              │              │
              └──────────────┼──────────────┘
                             │
                             │ calls
                             ▼
┌─────────────────────────────────────────────────────────────┐
│         Shared Instruction Operations (Free Functions)       │
│  src/backends/common/instruction_ops.rs (1,753 lines)        │
│                                                              │
│  pub fn execute_add<M>(...) -> Result                       │
│  pub fn execute_mul<M>(...) -> Result                       │
│  pub fn execute_sin<M>(...) -> Result                       │
│  pub fn execute_exp<M>(...) -> Result                       │
│  ... 39 shared instruction implementations                  │
│                                                              │
│  ✓ Direct function calls (zero overhead)                    │
│  ✓ Cannot be overridden (consistent semantics)              │
│  ✓ Easy to test in isolation                                │
└─────────────────────────────────────────────────────────────┘
```

## Key Design Decision: Free Functions vs Trait Methods

### Current Design: Free Functions (Optimal)

Shared instruction operations are implemented as **free functions** in `instruction_ops.rs`, not as trait methods.

```rust
// instruction_ops.rs - FREE FUNCTIONS
pub fn execute_add<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src1: Register,
    src2: Register,
) -> Result<()> {
    // Implementation identical for all backends
}

// executor_impl.rs - USAGE
impl Executor<MemoryManager> for CpuExecutor {
    fn execute_instruction(&mut self, state: &mut ExecutionState<M>, instruction: &Instruction) -> Result<()> {
        match instruction {
            Instruction::ADD { ty, dst, src1, src2 } => {
                instruction_ops::execute_add(state, *ty, *dst, *src1, *src2)
            }
            // ... more instructions
        }
    }
}
```

### Why Free Functions Are Better

#### 1. Zero Overhead ✅

**Free functions**: Direct calls, no indirection
```rust
instruction_ops::execute_add(state, ty, dst, src1, src2)?;
// Compiles to: call _ZN17instruction_ops11execute_add...
```

**Trait methods**: Potential for virtual dispatch
```rust
self.execute_add(state, ty, dst, src1, src2)?;
// May compile to: call via vtable lookup (if trait object used)
```

Even with monomorphization, free functions make the optimizer's job easier.

#### 2. Smaller Trait Surface ✅

**Current**: 4 methods in `Executor` trait (backend-specific)
```rust
trait Executor<M: MemoryStorage> {
    fn execute(&mut self, program: &Program, config: &LaunchConfig) -> Result<()>;
    fn execute_instruction(&mut self, state: &mut ExecutionState<M>, instr: &Instruction) -> Result<()>;
    fn execute_barrier_sync(&mut self, state: &mut ExecutionState<M>, id: u8) -> Result<()>;
    fn execute_memory_fence(&mut self, state: &mut ExecutionState<M>, scope: MemoryScope) -> Result<()>;
}
```

**Alternative**: 43 methods (unwieldy, error-prone)
```rust
trait Executor<M: MemoryStorage> {
    fn execute(...);
    fn execute_instruction(...);
    fn execute_barrier_sync(...);
    fn execute_memory_fence(...);
    fn execute_add(...);        // + 39 shared operations
    fn execute_sub(...);
    fn execute_mul(...);
    // ... etc - trait becomes massive
}
```

#### 3. Clear Separation of Concerns ✅

**Backend-Specific** (Trait Methods):
- **Memory Operations**: `LDG`, `STG`, `LDS`, `STS`
  - CPU: Direct memory access via pointers
  - GPU: Device memory transfers, coalesced access
  - TPU: DMA, HBM access patterns

- **Control Flow**: `BRA`, `CALL`, `RET`, `LOOP`, `EXIT`
  - CPU: PC manipulation, call stack
  - GPU: Warp divergence, predication
  - TPU: Vector masking

- **Synchronization**: `BarSync`, `MemFence`
  - CPU: Atomic fences, no-op barriers (single-threaded)
  - GPU: `__syncthreads()`, memory visibility
  - TPU: Hardware synchronization primitives

**Shared Operations** (Free Functions):
- **Arithmetic**: `ADD`, `SUB`, `MUL`, `DIV`, `MAD`, `FMA`, `MIN`, `MAX`, `ABS`, `NEG`
  - Semantics identical across all backends
  - Operates on register state only

- **Bitwise**: `AND`, `OR`, `XOR`, `NOT`, `SHL`, `SHR`
  - Pure register operations

- **Transcendentals**: `SIN`, `COS`, `TAN`, `TANH`, `SIGMOID`, `EXP`, `LOG`, `SQRT`, `RSQRT`
  - Standard library calls

- **Atlas Operations**: `ClsGet`, `MIRROR`, `UnityTest`, `NbrCount`, `NbrGet`, `ResAccum`, `PhaseGet`, `PhaseAdv`, `BoundMap`
  - Uses atlas-core library functions
  - Same computation on all backends

#### 4. Prevents Accidental Override ✅

**Free functions cannot be overridden**, ensuring **consistent ISA semantics**:

```rust
// ✅ GOOD: ADD has identical semantics everywhere
instruction_ops::execute_add(state, Type::I32, r0, r1, r2)?;
// CPU: 5 + 3 = 8
// GPU: 5 + 3 = 8
// TPU: 5 + 3 = 8

// ❌ BAD: If trait methods, could diverge
impl Executor for GpuExecutor {
    fn execute_add(&mut self, ...) {
        // Oops! Someone "optimized" this differently
        // Now GPU ADD behaves differently than CPU ADD
        // ISA semantics broken!
    }
}
```

This is critical for **ISA compliance** - the instruction set must be **portable**.

#### 5. Easier Testing ✅

Free functions can be tested **without creating executor instances**:

```rust
#[test]
fn test_add_i32() {
    let memory = Arc::new(RwLock::new(MemoryManager::new()));
    let context = ExecutionContext::new(...);
    let mut state = ExecutionState::new(1, memory, context, HashMap::new());

    // Direct test - no executor needed!
    state.current_lane_mut().registers.write_i32(Register(1), 5)?;
    state.current_lane_mut().registers.write_i32(Register(2), 3)?;

    instruction_ops::execute_add(&mut state, Type::I32, Register(0), Register(1), Register(2))?;

    let result = state.current_lane().registers.read_i32(Register(0))?;
    assert_eq!(result, 8);
}
```

Compare to trait method approach:
```rust
#[test]
fn test_add_i32() {
    // Need to create full executor + memory + context + state
    let executor = CpuExecutor::new(...);  // Heavy setup
    let mut state = ...;

    executor.execute_add(&mut state, ...)?;  // Couples test to specific backend
}
```

#### 6. Better Code Organization ✅

```
backends/
├── common/
│   ├── instruction_ops.rs       # 39 shared operations (1,753 lines)
│   ├── atlas_ops.rs             # 9 Atlas-specific operations
│   ├── executor_trait.rs        # 4-method trait (focused)
│   ├── execution_state.rs       # Execution context
│   └── registers.rs             # Register file
│
├── cpu/
│   ├── executor_impl.rs         # CPU-specific execution (624 lines)
│   ├── memory.rs                # CPU memory management
│   └── mod.rs                   # CPU backend trait impl
│
├── gpu/  (future)
│   ├── executor_impl.rs         # GPU-specific execution
│   ├── memory.rs                # Device memory, transfers
│   └── mod.rs
│
└── tpu/  (future)
    ├── executor_impl.rs         # TPU-specific execution
    ├── memory.rs                # HBM, DMA
    └── mod.rs
```

**Clear modules**:
- `instruction_ops`: What's shared
- `executor_impl`: What's backend-specific

## Performance Analysis

### Benchmark: Free Function vs Trait Method

```rust
// Free function
pub fn execute_add_free(state: &mut State, a: i32, b: i32) -> i32 {
    a + b
}

// Trait method with default impl
pub trait Executor {
    fn execute_add(&self, state: &mut State, a: i32, b: i32) -> i32 {
        a + b
    }
}
```

**With optimizations enabled** (`cargo build --release`):
- Both compile to **identical assembly** due to monomorphization + inlining
- **Zero overhead** for both approaches in release builds

**However**:
- Free functions are **clearer to the optimizer**
- Free functions **guarantee** no virtual dispatch
- Free functions don't rely on optimizer doing the right thing

### Real-World Usage

In `executor_impl.rs`, the CPU executor calls `instruction_ops::` **39 times**:

```rust
fn execute_instruction(&mut self, state: &mut ExecutionState<M>, instruction: &Instruction) -> Result<()> {
    match instruction {
        // Backend-specific (methods)
        Instruction::LDG { .. } => self.execute_ldg(state, ...),
        Instruction::STG { .. } => self.execute_stg(state, ...),
        Instruction::BRA { .. } => self.execute_bra(state, ...),
        Instruction::BarSync { id } => self.execute_barrier_sync(state, *id),

        // Shared operations (free functions)
        Instruction::ADD { ty, dst, src1, src2 } =>
            instruction_ops::execute_add(state, *ty, *dst, *src1, *src2),
        Instruction::MUL { ty, dst, src1, src2 } =>
            instruction_ops::execute_mul(state, *ty, *dst, *src1, *src2),
        Instruction::SIN { ty, dst, src } =>
            instruction_ops::execute_sin(state, *ty, *dst, *src),
        // ... 36 more shared operations
    }
}
```

## Alternative Considered: Trait Methods

### What It Would Look Like

```rust
pub trait Executor<M: MemoryStorage> {
    // Backend-specific (required)
    fn execute(&mut self, program: &Program, config: &LaunchConfig) -> Result<()>;
    fn execute_barrier_sync(&mut self, state: &mut ExecutionState<M>, id: u8) -> Result<()>;
    fn execute_memory_fence(&mut self, state: &mut ExecutionState<M>, scope: MemoryScope) -> Result<()>;

    // Shared operations (default implementations)
    fn execute_add(&mut self, state: &mut ExecutionState<M>, ty: Type, dst: Register, src1: Register, src2: Register) -> Result<()> {
        // Default implementation
    }

    fn execute_mul(&mut self, ...) -> Result<()> { /* ... */ }
    fn execute_sin(&mut self, ...) -> Result<()> { /* ... */ }
    // ... 36 more default methods
}
```

### Why We Rejected This

1. **Trait becomes massive**: 43 methods instead of 4
2. **Risk of accidental override**: Backend could override shared operations
3. **Harder to maintain**: Changes require updating trait definition
4. **Coupling**: Shared operations coupled to trait, not standalone
5. **Testing friction**: Requires executor instance to test shared ops
6. **No performance benefit**: Identical performance to free functions

## Guidelines for Future Backend Implementations

### When Implementing a New Backend (GPU, TPU, FPGA)

#### Step 1: Implement Backend Trait

```rust
// backends/gpu/mod.rs
pub struct GpuBackend {
    device: CudaDevice,
    memory: Arc<RwLock<GpuMemoryManager>>,
}

impl Backend for GpuBackend {
    fn allocate_buffer(&mut self, size: usize) -> Result<BufferHandle> {
        // GPU-specific buffer allocation
    }

    fn execute_program(&mut self, program: &Program, config: &LaunchConfig) -> Result<()> {
        let mut executor = GpuExecutor::new(Arc::clone(&self.memory));
        executor.execute(program, config)
    }
}
```

#### Step 2: Implement Executor Trait

```rust
// backends/gpu/executor_impl.rs
pub struct GpuExecutor {
    memory: Arc<RwLock<GpuMemoryManager>>,
    device: CudaDevice,
}

impl Executor<GpuMemoryManager> for GpuExecutor {
    fn execute(&mut self, program: &Program, config: &LaunchConfig) -> Result<()> {
        // GPU-specific: Launch kernel, manage warps, etc.
    }

    fn execute_instruction(&mut self, state: &mut ExecutionState<M>, instr: &Instruction) -> Result<()> {
        match instr {
            // GPU-specific memory operations
            Instruction::LDG { .. } => self.execute_ldg_gpu(state, ...),
            Instruction::STG { .. } => self.execute_stg_gpu(state, ...),

            // GPU-specific synchronization
            Instruction::BarSync { id } => self.execute_barrier_sync(state, *id),  // __syncthreads()

            // Shared operations - USE FREE FUNCTIONS!
            Instruction::ADD { ty, dst, src1, src2 } =>
                instruction_ops::execute_add(state, *ty, *dst, *src1, *src2),

            // ... etc
        }
    }

    fn execute_barrier_sync(&mut self, state: &mut ExecutionState<M>, id: u8) -> Result<()> {
        // GPU-specific: __syncthreads() or similar
    }

    fn execute_memory_fence(&mut self, state: &mut ExecutionState<M>, scope: MemoryScope) -> Result<()> {
        // GPU-specific: __threadfence_block(), __threadfence(), __threadfence_system()
    }
}
```

#### Step 3: Implement Backend-Specific Operations

```rust
impl GpuExecutor {
    fn execute_ldg_gpu(&mut self, state: &mut ExecutionState<GpuMemoryManager>, ...) -> Result<()> {
        // GPU-specific: Device memory access, coalescing, etc.
    }

    fn execute_stg_gpu(&mut self, ...) -> Result<()> {
        // GPU-specific: Write to device memory
    }
}
```

#### Step 4: DO NOT Override Shared Operations

**❌ WRONG:**
```rust
impl Executor<GpuMemoryManager> for GpuExecutor {
    // DON'T DO THIS!
    fn execute_add(&mut self, ...) -> Result<()> {
        // Custom GPU implementation - BREAKS ISA PORTABILITY!
    }
}
```

**✅ CORRECT:**
```rust
impl Executor<GpuMemoryManager> for GpuExecutor {
    fn execute_instruction(&mut self, state: &mut ExecutionState<M>, instr: &Instruction) -> Result<()> {
        match instr {
            // Always delegate to shared operations
            Instruction::ADD { .. } => instruction_ops::execute_add(state, ...),
        }
    }
}
```

## When to Add New Functions

### Add to `instruction_ops` (Free Function) If:

- ✅ Semantics are **identical across all backends**
- ✅ Operates primarily on **register state**
- ✅ No backend-specific optimizations needed
- ✅ Part of the **ISA specification**

Examples: `ADD`, `MUL`, `SIN`, `EXP`, `SQRT`, `ClsGet`, `MIRROR`

### Add to `Executor` Trait (Method) If:

- ✅ Implementation **differs significantly** per backend
- ✅ Requires **backend-specific resources** (memory manager, device handles)
- ✅ Involves **hardware-specific operations** (memory transfers, synchronization)

Examples: `LDG`, `STG`, `BarSync`, `MemFence`, control flow operations

## Testing Strategy

### Shared Operations (instruction_ops)

Test **once** with generic memory storage:

```rust
#[test]
fn test_add_i32() {
    let memory = Arc::new(RwLock::new(MemoryManager::new()));
    let mut state = ExecutionState::new(1, memory, ...);

    // Test applies to ALL backends
    instruction_ops::execute_add(&mut state, Type::I32, ...)?;
}
```

Located in: `backends/common/instruction_ops_test.rs`

### Backend-Specific Operations

Test **per backend** with backend-specific setup:

```rust
#[test]
fn test_cpu_ldg() {
    let memory = Arc::new(RwLock::new(MemoryManager::new()));
    let mut executor = CpuExecutor::new(memory);

    // Test CPU-specific memory loading
    executor.execute_ldg(&mut state, ...)?;
}
```

Located in: `backends/cpu/executor_impl.rs` (tests module)

## Summary

The current architecture achieves **optimal separation**:

| Concern | Implementation | Location |
|---------|---------------|----------|
| **Public API** | `Backend` trait | `backend/traits.rs` |
| **Execution Engine** | `Executor` trait (4 methods) | `backends/common/executor_trait.rs` |
| **Shared Instructions** | Free functions (39 functions) | `backends/common/instruction_ops.rs` |
| **Atlas Operations** | Free functions (9 functions) | `backends/common/atlas_ops.rs` |
| **Backend-Specific** | Private methods in executor impl | `backends/*/executor_impl.rs` |

**This design ensures**:
- ✅ **Performance**: Zero overhead, direct calls
- ✅ **Maintainability**: Clear separation, small focused trait
- ✅ **Correctness**: Shared operations cannot diverge
- ✅ **Testability**: Easy to test in isolation
- ✅ **ISA Compliance**: Guaranteed portable semantics

**Do not change this architecture without careful consideration and team consensus.**

## References

- [Executor Trait Definition](../crates/hologram-backends/src/backends/common/executor_trait.rs)
- [Instruction Operations](../crates/hologram-backends/src/backends/common/instruction_ops.rs)
- [CPU Executor Implementation](../crates/hologram-backends/src/backends/cpu/executor_impl.rs)
- [Backend Trait Architecture](./BACKEND_TRAIT_ARCHITECTURE.md)
- [ISA Specification](../crates/hologram-backends/src/isa/)
