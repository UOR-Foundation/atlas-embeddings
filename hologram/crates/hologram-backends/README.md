# hologram-backends

Backend implementations for hologram kernel execution with Atlas ISA.

## Overview

This crate provides:

1. **Atlas ISA Specification** - Complete instruction set architecture for hologram kernels
2. **Backend Trait** - Pluggable backend interface for different execution targets
3. **CPU Backend** - Reference implementation for CPU execution
4. **Linear Pool Storage** - O(1) space streaming computation

## Architecture

### ISA (Instruction Set Architecture)

The Atlas ISA provides a complete instruction set for kernel execution:

- **Data Movement**: LDG, STG, LDS, STS, MOV, CVT
- **Arithmetic**: ADD, SUB, MUL, DIV, MAD, FMA, MIN, MAX, ABS, NEG
- **Logic**: AND, OR, XOR, NOT, SHL, SHR, SETcc, SEL
- **Control Flow**: BRA, CALL, RET, LOOP, EXIT
- **Synchronization**: BarSync, MemFence
- **Atlas-Specific**: ClsGet, MIRROR, UnityTest, NBR*, ResAccum, Phase*, BoundMap
- **Reductions**: ReduceAdd, ReduceMin, ReduceMax, ReduceMul
- **Transcendentals**: EXP, LOG, SQRT, SIN, COS, TANH, SIGMOID
- **Pool Storage**: PoolAlloc, PoolFree, PoolLoad, PoolStore

### Backend Trait

Backends implement a common interface for kernel execution:

```rust
pub trait Backend {
    fn execute_program(&mut self, program: &Program, config: &LaunchConfig) -> Result<()>;
    fn allocate_buffer(&mut self, size: usize) -> Result<BufferHandle>;
    fn free_buffer(&mut self, handle: BufferHandle) -> Result<()>;
    fn copy_to_buffer(&mut self, handle: BufferHandle, data: &[u8]) -> Result<()>;
    fn copy_from_buffer(&mut self, handle: BufferHandle, data: &mut [u8]) -> Result<()>;
    fn allocate_pool(&mut self, size: usize) -> Result<PoolHandle>;
    fn free_pool(&mut self, handle: PoolHandle) -> Result<()>;
}
```

### CPU Backend

Reference implementation that executes kernels on the CPU:

- **Execution Model**: Grid → parallel tasks (rayon), Block → work chunk, Lane → scalar
- **Memory**: HashMap-based buffers and pools
- **Register File**: 256 general-purpose + 16 predicate registers
- **Full ISA Coverage**: All 50+ instructions implemented

### Linear Pool Storage

Enables O(1) space complexity for arbitrary input sizes:

```rust
// Allocate fixed pool
let pool = backend.allocate_pool(4096)?;

// Stream data through pool in chunks
for chunk in data.chunks(1024) {
    // Load chunk into pool
    backend.pool_store(pool, 0, chunk)?;

    // Execute operations on pool data
    backend.execute_program(&program, &config)?;

    // Read results from pool
    backend.pool_load(pool, 0, &mut results)?;
}

// Pool reused for arbitrary input sizes
backend.free_pool(pool)?;
```

## Usage

### Basic Example

```rust
use hologram_backends::{CpuBackend, Backend, Program, Instruction, Register, Type};

// Create CPU backend
let mut backend = CpuBackend::new();

// Create program
let mut program = Program::new();
program.instructions.push(Instruction::ADD {
    ty: Type::F32,
    dst: Register::new(0),
    src1: Register::new(1),
    src2: Register::new(2),
});

// Execute program
let config = LaunchConfig::default();
backend.execute_program(&program, &config)?;
```

### Pool Storage Example

```rust
use hologram_backends::{CpuBackend, Backend};

let mut backend = CpuBackend::new();

// Allocate pool (fixed size)
let pool = backend.allocate_pool(12288)?; // 96 classes × 48 pages × 256 bytes

// Stream large input through fixed pool
for chunk in large_data.chunks(1024) {
    // Load chunk
    backend.copy_to_pool(pool, 0, bytemuck::cast_slice(chunk))?;

    // Execute on pool
    backend.execute_program(&add_program, &config)?;

    // Read results
    backend.copy_from_pool(pool, 0, bytemuck::cast_slice_mut(&mut results))?;
}

backend.free_pool(pool)?;
```

## Design Principles

### 1. No CPU Fallbacks

All operations MUST be implemented using ISA instructions. If primitives are missing, extend the ISA itself - never fall back to CPU implementations.

### 2. Circuit-as-Index Model

The circuit defines the memory pool structure, not the data size:

```
Circuit (SRAM):       "merge@c00[c01,c02]"  ← Fixed instruction
                             ↓ indexes
Memory Pool (DRAM):   {c00, c01, c02}       ← Fixed addresses
                             ↓ contains
Data (streaming):     chunk_0, ..., chunk_N ← Arbitrary size
```

### 3. O(1) Space, O(n) Time

Linear pool storage enables constant memory usage with linear time scaling:

- Pool size: 36 KB (fixed)
- Input size: 1 MB to 100 MB (arbitrary)
- Memory amplification: 2,844× at 100 MB
- Throughput: Constant across all sizes

### 4. Backend Agnostic

The ISA abstracts computation across diverse physical substrates:

- **Classical**: CPU, GPU, TPU, FPGA, ASIC
- **Analog**: Memristor arrays, analog compute memory
- **Quantum**: Superconducting qubits, trapped ions, photonic

## Testing

```bash
# Run all tests
cargo test --package hologram-backends

# Run benchmarks
cargo bench --package hologram-backends

# Run specific benchmark
cargo bench --package hologram-backends --bench instruction_throughput
```

## Performance

CPU backend performance (reference implementation):

- **Instruction Throughput**: ~10 ns/instruction
- **Pool Load/Store**: ~11 GB/s bandwidth
- **Memory Amplification**: 2,844× (100 MB / 36 KB pool)
- **Parallel Scaling**: Linear with core count

## License

MIT OR Apache-2.0
