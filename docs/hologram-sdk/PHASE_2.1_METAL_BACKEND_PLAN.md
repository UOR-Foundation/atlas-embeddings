# Phase 2.1: Metal Backend Implementation Plan

**Date:** 2025-10-30
**Status:** 🚧 In Progress
**Target:** Apple Silicon (M-series chips)

---

## Overview

Implement Metal compute backend for hologram on Apple Silicon, enabling GPU acceleration for operations.

---

## Architecture

### Metal Backend Stack

```
hologram-core::Executor
    ↓
hologram-backends::MetalBackend
    ↓
Metal Compute Shaders (MSL)
    ↓
Apple Silicon GPU
```

### Components

1. **MetalBackend** - Implements Backend trait
2. **MetalMemoryManager** - GPU memory management
3. **MetalExecutor** - Implements Executor trait for Metal
4. **Metal Compute Shaders** - MSL kernels for operations
5. **Atlas ISA → Metal Compiler** - Translate ISA to Metal Shading Language

---

## Implementation Steps

### Step 1: Add Metal Dependencies

**File:** `crates/hologram-backends/Cargo.toml`

```toml
[dependencies]
metal = { version = "0.27", optional = true }
objc = { version = "0.2", optional = true }

[features]
metal = ["dep:metal", "dep:objc"]
```

---

### Step 2: Create Metal Backend Module

**Directory Structure:**
```
crates/hologram-backends/src/backends/metal/
├── mod.rs              # Module exports
├── backend.rs          # MetalBackend implementation
├── memory.rs           # MetalMemoryManager
├── executor.rs         # MetalExecutor
├── shaders/            # Metal Shading Language files
│   ├── math.metal     # Math operations
│   ├── activation.metal  # Activations
│   ├── reduce.metal   # Reductions
│   └── linalg.metal   # Linear algebra
└── compiler.rs         # Atlas ISA → MSL compiler
```

---

### Step 3: Implement MetalBackend

**File:** `backend.rs`

```rust
use metal::{Device, CommandQueue, MTLResourceOptions};
use std::sync::{Arc, RwLock};

pub struct MetalBackend {
    device: Device,
    command_queue: CommandQueue,
    memory: Arc<RwLock<MetalMemoryManager>>,
    compute_pipeline_cache: HashMap<String, ComputePipelineState>,
}

impl MetalBackend {
    pub fn new() -> Result<Self> {
        // Get default Metal device
        let device = Device::system_default()
            .ok_or_else(|| Error::BackendNotAvailable("Metal device not found"))?;

        // Create command queue
        let command_queue = device.new_command_queue();

        // Initialize memory manager
        let memory = Arc::new(RwLock::new(MetalMemoryManager::new(device.clone())));

        Ok(Self {
            device,
            command_queue,
            memory,
            compute_pipeline_cache: HashMap::new(),
        })
    }

    pub fn is_available() -> bool {
        Device::system_default().is_some()
    }
}

impl Backend for MetalBackend {
    fn allocate_buffer(&mut self, size: usize) -> Result<BufferHandle> {
        let mut memory = self.memory.write();
        memory.allocate_buffer(size)
    }

    fn free_buffer(&mut self, handle: BufferHandle) -> Result<()> {
        let mut memory = self.memory.write();
        memory.free_buffer(handle)
    }

    fn copy_to_buffer(&mut self, handle: BufferHandle, data: &[u8]) -> Result<()> {
        let memory = self.memory.read();
        memory.copy_to_buffer(handle, data)
    }

    fn copy_from_buffer(&mut self, handle: BufferHandle, data: &mut [u8]) -> Result<()> {
        let memory = self.memory.read();
        memory.copy_from_buffer(handle, data)
    }

    fn execute_program(&mut self, program: &Program, config: &LaunchConfig) -> Result<()> {
        // Compile and execute Metal compute shader
        self.execute_metal_program(program, config)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}
```

---

### Step 4: Implement MetalMemoryManager

**File:** `memory.rs`

```rust
pub struct MetalMemoryManager {
    device: Device,
    buffers: HashMap<BufferHandle, metal::Buffer>,
    next_handle: u64,
}

impl MetalMemoryManager {
    pub fn new(device: Device) -> Self {
        Self {
            device,
            buffers: HashMap::new(),
            next_handle: 1,
        }
    }

    pub fn allocate_buffer(&mut self, size: usize) -> Result<BufferHandle> {
        // Create Metal buffer
        let metal_buffer = self.device.new_buffer(
            size as u64,
            MTLResourceOptions::StorageModeShared // Shared between CPU and GPU
        );

        let handle = BufferHandle(self.next_handle);
        self.next_handle += 1;

        self.buffers.insert(handle, metal_buffer);

        Ok(handle)
    }

    pub fn free_buffer(&mut self, handle: BufferHandle) -> Result<()> {
        self.buffers.remove(&handle)
            .ok_or(Error::InvalidBuffer)?;
        Ok(())
    }

    pub fn get_buffer(&self, handle: BufferHandle) -> Result<&metal::Buffer> {
        self.buffers.get(&handle)
            .ok_or(Error::InvalidBuffer)
    }

    pub fn copy_to_buffer(&self, handle: BufferHandle, data: &[u8]) -> Result<()> {
        let buffer = self.get_buffer(handle)?;

        // Copy data to Metal buffer
        let contents = buffer.contents();
        unsafe {
            std::ptr::copy_nonoverlapping(
                data.as_ptr(),
                contents as *mut u8,
                data.len()
            );
        }

        Ok(())
    }

    pub fn copy_from_buffer(&self, handle: BufferHandle, data: &mut [u8]) -> Result<()> {
        let buffer = self.get_buffer(handle)?;

        // Copy from Metal buffer
        let contents = buffer.contents();
        unsafe {
            std::ptr::copy_nonoverlapping(
                contents as *const u8,
                data.as_mut_ptr(),
                data.len()
            );
        }

        Ok(())
    }
}
```

---

### Step 5: Create Metal Compute Shaders

**File:** `shaders/math.metal`

```metal
#include <metal_stdlib>
using namespace metal;

// Vector addition kernel
kernel void vector_add(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    uint id [[thread_position_in_grid]])
{
    c[id] = a[id] + b[id];
}

// Vector multiplication kernel
kernel void vector_mul(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    uint id [[thread_position_in_grid]])
{
    c[id] = a[id] * b[id];
}

// ReLU activation kernel
kernel void relu(
    device const float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    uint id [[thread_position_in_grid]])
{
    output[id] = max(input[id], 0.0f);
}

// Sigmoid activation kernel
kernel void sigmoid(
    device const float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    uint id [[thread_position_in_grid]])
{
    output[id] = 1.0f / (1.0f + exp(-input[id]));
}
```

---

### Step 6: Compile and Execute Shaders

**File:** `backend.rs` (additional methods)

```rust
impl MetalBackend {
    fn execute_metal_program(&mut self, program: &Program, config: &LaunchConfig) -> Result<()> {
        // Get or compile shader
        let pipeline = self.get_or_compile_shader(program)?;

        // Create command buffer
        let command_buffer = self.command_queue.new_command_buffer();

        // Create compute command encoder
        let encoder = command_buffer.new_compute_command_encoder();

        // Set pipeline
        encoder.set_compute_pipeline_state(&pipeline);

        // Bind buffers
        for (index, buffer_handle) in program.buffers.iter().enumerate() {
            let memory = self.memory.read();
            let buffer = memory.get_buffer(*buffer_handle)?;
            encoder.set_buffer(index as u64, Some(buffer), 0);
        }

        // Calculate thread groups
        let threads_per_grid = MTLSize {
            width: config.grid.x as u64,
            height: config.grid.y as u64,
            depth: config.grid.z as u64,
        };

        let threads_per_threadgroup = MTLSize {
            width: config.block.x as u64,
            height: config.block.y as u64,
            depth: config.block.z as u64,
        };

        // Dispatch compute
        encoder.dispatch_threads(threads_per_grid, threads_per_threadgroup);

        // End encoding
        encoder.end_encoding();

        // Commit and wait
        command_buffer.commit();
        command_buffer.wait_until_completed();

        Ok(())
    }

    fn get_or_compile_shader(&mut self, program: &Program) -> Result<ComputePipelineState> {
        let shader_name = program.name.clone();

        // Check cache
        if let Some(pipeline) = self.compute_pipeline_cache.get(&shader_name) {
            return Ok(pipeline.clone());
        }

        // Compile shader
        let library = self.device.new_library_with_source(
            program.metal_source,
            &CompileOptions::new()
        )?;

        let function = library.get_function(&shader_name, None)?;

        let pipeline = self.device.new_compute_pipeline_state_with_function(&function)?;

        // Cache it
        self.compute_pipeline_cache.insert(shader_name, pipeline.clone());

        Ok(pipeline)
    }
}
```

---

### Step 7: Integrate with hologram-core

**File:** `crates/hologram-core/src/executor.rs`

```rust
impl Executor {
    pub fn new_with_backend(backend_type: BackendType) -> Result<Self> {
        let backend: Box<dyn Backend + Send + Sync> = match backend_type {
            BackendType::Cpu => Box::new(CpuBackend::new()),

            BackendType::Metal => {
                #[cfg(feature = "metal")]
                {
                    Box::new(MetalBackend::new()?)
                }
                #[cfg(not(feature = "metal"))]
                {
                    return Err(Error::InvalidOperation(
                        "Metal backend not enabled. Compile with --features metal".into()
                    ));
                }
            }

            BackendType::Cuda => {
                return Err(Error::InvalidOperation(
                    "CUDA backend not yet implemented. Coming in Phase 2.2!".into()
                ));
            }
        };

        Ok(Self {
            backend: Arc::new(RwLock::new(backend)),
            buffer_mappings: [None; 96],
            next_class: 0,
            is_boundary_pool: [false; 96],
        })
    }
}
```

---

## Testing Plan

### Unit Tests

**File:** `crates/hologram-backends/src/backends/metal/tests.rs`

```rust
#[cfg(test)]
#[cfg(feature = "metal")]
mod tests {
    use super::*;

    #[test]
    fn test_metal_availability() {
        assert!(MetalBackend::is_available());
    }

    #[test]
    fn test_metal_buffer_allocation() {
        let mut backend = MetalBackend::new().unwrap();
        let handle = backend.allocate_buffer(1024).unwrap();
        backend.free_buffer(handle).unwrap();
    }

    #[test]
    fn test_metal_buffer_copy() {
        let mut backend = MetalBackend::new().unwrap();
        let handle = backend.allocate_buffer(16).unwrap();

        let data = vec![1.0f32; 4];
        let bytes = unsafe {
            std::slice::from_raw_parts(
                data.as_ptr() as *const u8,
                data.len() * 4
            )
        };

        backend.copy_to_buffer(handle, bytes).unwrap();

        let mut result = vec![0u8; 16];
        backend.copy_from_buffer(handle, &mut result).unwrap();

        backend.free_buffer(handle).unwrap();
    }
}
```

### Integration Tests

Test Metal backend with real operations in Python SDK.

---

## Performance Targets

### Expected Speedup (vs CPU)

| Operation | Size | CPU Time | Metal Time | Target Speedup |
|-----------|------|----------|------------|----------------|
| Vector Add | 10K | 12 μs | 3 μs | 4x |
| Vector Mul | 10K | 15 μs | 4 μs | 3.75x |
| ReLU | 10K | 9 μs | 2 μs | 4.5x |
| GEMM (256×256) | - | 850 μs | 200 μs | 4.25x |

### Memory Bandwidth

- **Target:** 80% of theoretical Metal bandwidth
- **Apple M1/M2:** ~200 GB/s theoretical
- **Expected:** ~160 GB/s achieved

---

## Challenges & Solutions

### Challenge 1: Atlas ISA → Metal Compilation

**Problem:** Need to translate Atlas ISA instructions to Metal Shading Language

**Solution Options:**
1. **Direct kernel mapping** - Map each ISA instruction to pre-written Metal kernel
2. **Runtime code generation** - Generate MSL from ISA at runtime
3. **Ahead-of-time compilation** - Compile ISA to MSL at build time

**Chosen:** Option 1 (direct kernel mapping) for Phase 2.1, Option 2 for future

### Challenge 2: Memory Management

**Problem:** GPU memory is separate from CPU memory

**Solution:** Use `MTLResourceOptions::StorageModeShared` for unified memory on Apple Silicon

### Challenge 3: Synchronization

**Problem:** Need to wait for GPU operations to complete

**Solution:** Use `command_buffer.wait_until_completed()` for simplicity in Phase 2.1

---

## Timeline

**Estimated Time:** 3-5 hours

1. ✅ Planning (30 min)
2. 🚧 Setup dependencies and structure (30 min)
3. 🚧 Implement MetalBackend and memory manager (1 hour)
4. 🚧 Create Metal compute shaders (1 hour)
5. 🚧 Integrate with hologram-core (30 min)
6. 🚧 Test on Apple Silicon (1 hour)
7. 🚧 Benchmark and optimize (30 min)

---

## Success Criteria

- ✅ MetalBackend implements Backend trait
- ✅ Can allocate GPU buffers
- ✅ Can copy data to/from GPU
- ✅ Can execute Metal compute shaders
- ✅ Vector operations work correctly
- ✅ Performance is 3-5x faster than CPU
- ✅ Integration tests pass
- ✅ Python SDK can use `backend='metal'`

---

## Next Document

After Phase 2.1 completion:
- `/workspace/docs/hologram-sdk/PHASE_2.1_COMPLETE.md`

---

**Status:** 🚧 Ready to implement
**Started:** 2025-10-30
