//! CPU backend implementation
//!
//! Reference implementation of the Backend trait for CPU execution.
//! Provides sequential and parallel execution of Atlas ISA programs.
//!
//! # Architecture
//!
//! ```text
//! CpuBackend
//! ├── RegisterFile   - 256 registers + 16 predicates
//! ├── MemoryManager  - Buffers + pools + shared memory
//! ├── Executor       - Instruction dispatch and execution
//! └── Parallel       - Rayon-based grid/block execution
//! ```
//!
//! # Usage
//!
//! ```rust
//! use hologram_backends::{CpuBackend, Backend, Program};
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! let mut backend = CpuBackend::new();
//!
//! // Allocate buffer
//! let buffer = backend.allocate_buffer(1024)?;
//!
//! // Execute program
//! let program = Program::new();
//! let config = Default::default();
//! backend.execute_program(&program, &config)?;
//!
//! backend.free_buffer(buffer)?;
//! # Ok(())
//! # }
//! ```

mod boundary_pool;
mod executor_impl;
pub(crate) mod memory;

use crate::backend::{Backend, BufferHandle, LaunchConfig, PoolHandle};
use crate::backends::common::executor_trait::Executor;
pub use crate::backends::common::RegisterFile;
use crate::error::Result;
use crate::isa::Program;
use executor_impl::CpuExecutor;
use memory::MemoryManager;
use parking_lot::RwLock;
use std::sync::Arc;

/// CPU backend for executing Atlas ISA programs
///
/// This is the reference implementation of the Backend trait.
/// It executes programs on the CPU using:
/// - Sequential instruction execution per lane
/// - Rayon-based parallel execution across blocks
/// - HashMap-based buffer and pool management
#[derive(Clone)]
pub struct CpuBackend {
    /// Memory manager (buffers, pools, shared memory)
    memory: Arc<RwLock<MemoryManager>>,
}

impl CpuBackend {
    /// Create a new CPU backend
    ///
    /// # Example
    ///
    /// ```rust
    /// use hologram_backends::CpuBackend;
    ///
    /// let backend = CpuBackend::new();
    /// ```
    pub fn new() -> Self {
        Self {
            memory: Arc::new(RwLock::new(MemoryManager::new())),
        }
    }
}

impl Default for CpuBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for CpuBackend {
    fn execute_program(&mut self, program: &Program, config: &LaunchConfig) -> Result<()> {
        // Create executor and delegate execution
        let executor = CpuExecutor::new(Arc::clone(&self.memory));
        executor.execute(program, config)
    }

    fn allocate_buffer(&mut self, size: usize) -> Result<BufferHandle> {
        self.memory.write().allocate_buffer(size)
    }

    fn free_buffer(&mut self, handle: BufferHandle) -> Result<()> {
        self.memory.write().free_buffer(handle)
    }

    fn copy_to_buffer(&mut self, handle: BufferHandle, data: &[u8]) -> Result<()> {
        self.memory.write().copy_to_buffer(handle, data)
    }

    fn copy_from_buffer(&mut self, handle: BufferHandle, data: &mut [u8]) -> Result<()> {
        self.memory.read().copy_from_buffer(handle, data)
    }

    fn buffer_size(&self, handle: BufferHandle) -> Result<usize> {
        self.memory.read().buffer_size(handle)
    }

    fn allocate_pool(&mut self, size: usize) -> Result<PoolHandle> {
        self.memory.write().allocate_pool(size)
    }

    fn free_pool(&mut self, handle: PoolHandle) -> Result<()> {
        self.memory.write().free_pool(handle)
    }

    fn copy_to_pool(&mut self, handle: PoolHandle, offset: usize, data: &[u8]) -> Result<()> {
        self.memory.write().copy_to_pool(handle, offset, data)
    }

    fn copy_from_pool(&mut self, handle: PoolHandle, offset: usize, data: &mut [u8]) -> Result<()> {
        self.memory.read().copy_from_pool(handle, offset, data)
    }

    fn pool_size(&self, handle: PoolHandle) -> Result<usize> {
        self.memory.read().pool_size(handle)
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

impl CpuBackend {
    /// Get raw const pointer to buffer memory (for inline SIMD kernels)
    ///
    /// # Safety
    ///
    /// The returned pointer is valid as long as:
    /// - The buffer handle is valid
    /// - No mutable operations occur on the buffer
    /// - The backend/memory manager is not dropped
    pub fn get_buffer_ptr(&self, handle: BufferHandle) -> Result<*const u8> {
        self.memory.read().buffer_as_ptr(handle)
    }

    /// Get raw mutable pointer to buffer memory (for inline SIMD kernels)
    ///
    /// # Safety
    ///
    /// The returned pointer is valid as long as:
    /// - The buffer handle is valid
    /// - No concurrent access occurs
    /// - The backend/memory manager is not dropped
    pub fn get_buffer_mut_ptr(&mut self, handle: BufferHandle) -> Result<*mut u8> {
        self.memory.write().buffer_as_mut_ptr(handle)
    }

    /// Get raw const pointer to boundary pool class data (for inline SIMD kernels)
    ///
    /// # Arguments
    ///
    /// * `class` - Class index (0-95)
    ///
    /// # Returns
    ///
    /// Const pointer to the start of the class data (12,288 bytes)
    pub fn get_boundary_class_ptr(&self, class: u8) -> Result<*const u8> {
        self.memory.read().boundary_class_ptr(class)
    }

    /// Get raw mutable pointer to boundary pool class data (for inline SIMD kernels)
    ///
    /// # Arguments
    ///
    /// * `class` - Class index (0-95)
    ///
    /// # Returns
    ///
    /// Mutable pointer to the start of the class data (12,288 bytes)
    pub fn get_boundary_class_mut_ptr(&mut self, class: u8) -> Result<*mut u8> {
        self.memory.write().boundary_class_ptr_mut(class)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cpu_backend_creation() {
        let backend = CpuBackend::new();
        assert!(Arc::strong_count(&backend.memory) == 1);
    }

    #[test]
    fn test_cpu_backend_default() {
        let backend: CpuBackend = Default::default();
        assert!(Arc::strong_count(&backend.memory) == 1);
    }

    #[test]
    fn test_cpu_backend_buffer_allocation() {
        let mut backend = CpuBackend::new();

        let buffer = backend.allocate_buffer(1024).unwrap();
        assert_eq!(backend.buffer_size(buffer).unwrap(), 1024);

        backend.free_buffer(buffer).unwrap();
    }

    #[test]
    fn test_cpu_backend_pool_allocation() {
        let mut backend = CpuBackend::new();

        let pool = backend.allocate_pool(4096).unwrap();
        assert_eq!(backend.pool_size(pool).unwrap(), 4096);

        backend.free_pool(pool).unwrap();
    }

    #[test]
    fn test_cpu_backend_buffer_copy() {
        let mut backend = CpuBackend::new();

        let buffer = backend.allocate_buffer(16).unwrap();

        let data = b"Hello, World!";
        backend.copy_to_buffer(buffer, data).unwrap();

        let mut result = vec![0u8; data.len()];
        backend.copy_from_buffer(buffer, &mut result).unwrap();

        assert_eq!(result, data);

        backend.free_buffer(buffer).unwrap();
    }

    #[test]
    fn test_cpu_backend_pool_copy() {
        let mut backend = CpuBackend::new();

        let pool = backend.allocate_pool(1024).unwrap();

        let data = [1.0f32, 2.0, 3.0, 4.0];
        let bytes = bytemuck::cast_slice(&data);
        backend.copy_to_pool(pool, 0, bytes).unwrap();

        let mut result = [0.0f32; 4];
        let result_bytes = bytemuck::cast_slice_mut(&mut result);
        backend.copy_from_pool(pool, 0, result_bytes).unwrap();

        assert_eq!(result, data);

        backend.free_pool(pool).unwrap();
    }
}
