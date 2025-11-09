//! Metal backend implementation for Apple Silicon
//!
//! GPU-accelerated execution of Atlas ISA programs on Apple Silicon (M-series chips).
//! Uses Metal compute shaders for high-performance execution.
//!
//! # Architecture
//!
//! ```text
//! MetalBackend
//! ├── Device          - Metal GPU device
//! ├── CommandQueue    - Command submission queue
//! ├── MemoryManager   - GPU buffers + pools
//! └── PipelineCache   - Compiled compute pipelines
//! ```
//!
//! # Usage
//!
//! ```rust,ignore
//! use hologram_backends::{MetalBackend, Backend, Program};
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! let mut backend = MetalBackend::new()?;
//!
//! // Allocate GPU buffer
//! let buffer = backend.allocate_buffer(1024)?;
//!
//! // Execute program on GPU
//! let program = Program::new();
//! let config = Default::default();
//! backend.execute_program(&program, &config)?;
//!
//! backend.free_buffer(buffer)?;
//! # Ok(())
//! # }
//! ```

mod executor;
mod memory;
mod pipeline;

use crate::error::{BackendError, Result};

#[cfg(target_vendor = "apple")]
use metal::{CommandQueue, Device};

#[cfg(target_vendor = "apple")]
use executor::MetalExecutor;

#[cfg(target_vendor = "apple")]
use memory::MetalMemoryManager;

#[cfg(target_vendor = "apple")]
use pipeline::PipelineCache;

/// Metal backend for executing Atlas ISA programs on Apple Silicon
///
/// Provides GPU-accelerated execution using Metal compute shaders.
/// Significantly faster than CPU backend for large-scale operations.
#[cfg(target_vendor = "apple")]
pub struct MetalBackend {
    /// Metal device (GPU)
    device: Device,

    /// Command queue for GPU work submission
    command_queue: CommandQueue,

    /// Memory manager (GPU buffers and pools)
    memory: Arc<RwLock<MetalMemoryManager>>,

    /// Pipeline cache for compiled compute kernels
    pipeline_cache: Arc<RwLock<PipelineCache>>,
}

#[cfg(target_vendor = "apple")]
impl MetalBackend {
    /// Create a new Metal backend
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use hologram_backends::MetalBackend;
    ///
    /// let backend = MetalBackend::new()?;
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - No Metal device is available
    /// - Failed to create command queue
    pub fn new() -> Result<Self> {
        // Get default Metal device (Apple Silicon GPU)
        let device = Device::system_default().ok_or_else(|| BackendError::Other("Metal device not found".into()))?;

        // Create command queue for submitting GPU work
        let command_queue = device.new_command_queue();

        // Initialize memory manager with device
        let memory = Arc::new(RwLock::new(MetalMemoryManager::new(device.clone())));

        // Compile shaders and initialize pipeline cache
        let pipeline_cache = Arc::new(RwLock::new(PipelineCache::new(device.clone())?));

        Ok(Self {
            device,
            command_queue,
            memory,
            pipeline_cache,
        })
    }

    /// Check if Metal is available on this system
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// use hologram_backends::MetalBackend;
    ///
    /// if MetalBackend::is_available() {
    ///     let backend = MetalBackend::new()?;
    /// }
    /// ```
    pub fn is_available() -> bool {
        Device::system_default().is_some()
    }
}

#[cfg(target_vendor = "apple")]
impl Backend for MetalBackend {
    fn execute_program(&mut self, program: &Program, config: &LaunchConfig) -> Result<()> {
        // Create executor and delegate execution
        let executor = MetalExecutor::new(
            self.command_queue.clone(),
            Arc::clone(&self.memory),
            Arc::clone(&self.pipeline_cache),
        );

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

// Stub implementation for non-Apple platforms
#[cfg(not(target_vendor = "apple"))]
pub struct MetalBackend;

#[cfg(not(target_vendor = "apple"))]
impl MetalBackend {
    pub fn new() -> Result<Self> {
        Err(BackendError::UnsupportedOperation(
            "Metal backend only available on Apple platforms".into(),
        ))
    }

    pub fn is_available() -> bool {
        false
    }
}

#[cfg(test)]
#[cfg(target_vendor = "apple")]
mod tests {
    use super::*;

    #[test]
    fn test_metal_availability() {
        // Should be available on Apple Silicon
        assert!(MetalBackend::is_available());
    }

    #[test]
    fn test_metal_backend_creation() {
        let backend = MetalBackend::new().unwrap();
        assert!(Arc::strong_count(&backend.memory) == 1);
    }

    #[test]
    fn test_metal_buffer_allocation() {
        let mut backend = MetalBackend::new().unwrap();

        let buffer = backend.allocate_buffer(1024).unwrap();
        assert_eq!(backend.buffer_size(buffer).unwrap(), 1024);

        backend.free_buffer(buffer).unwrap();
    }

    #[test]
    fn test_metal_buffer_copy() {
        let mut backend = MetalBackend::new().unwrap();

        let buffer = backend.allocate_buffer(16).unwrap();

        let data = b"Hello, Metal!";
        backend.copy_to_buffer(buffer, data).unwrap();

        let mut result = vec![0u8; data.len()];
        backend.copy_from_buffer(buffer, &mut result).unwrap();

        assert_eq!(result, data);

        backend.free_buffer(buffer).unwrap();
    }

    #[test]
    fn test_metal_pool_allocation() {
        let mut backend = MetalBackend::new().unwrap();

        let pool = backend.allocate_pool(4096).unwrap();
        assert_eq!(backend.pool_size(pool).unwrap(), 4096);

        backend.free_pool(pool).unwrap();
    }

    #[test]
    fn test_metal_pool_copy() {
        let mut backend = MetalBackend::new().unwrap();

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
