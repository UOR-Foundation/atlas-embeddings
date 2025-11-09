//! Executor for managing backend execution
//!
//! The `Executor` wraps a `hologram-backends::Backend` and provides high-level APIs for
//! buffer allocation and operation execution.
//!
//! ## Architecture
//!
//! ```text
//! hologram-core::Executor
//!   ↓ delegates to
//! hologram-backends::Backend (CpuBackend, GpuBackend, etc.)
//!   ↓ executes
//! ISA Program (precompiled at build-time)
//! ```
//!
//! ## Zero-Copy Design
//!
//! - Buffers are backend-managed (no intermediate copying)
//! - Direct memory access via backend handles
//! - Reference-based APIs to avoid unnecessary allocations
//!
//! ## Performance
//!
//! - Zero runtime compilation (all operations precompiled)
//! - Direct ISA execution via backend (~10-20ns overhead)
//! - Rayon parallelization in backend execution loops
//! - <200ns total overhead per operation

use crate::buffer::{Buffer, MemoryPool};
use crate::error::{Error, Result};
use hologram_backends::backend::{BlockDim, GridDim, SharedMemoryConfig};
use hologram_backends::{Backend, BufferHandle, CpuBackend, LaunchConfig};
use parking_lot::RwLock;
use std::sync::Arc;

#[cfg(target_vendor = "apple")]
use hologram_backends::MetalBackend;

#[cfg(feature = "cuda")]
use hologram_backends::CudaBackend;

/// Backend type for executor initialization
///
/// Specifies which backend to use for computation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BackendType {
    /// CPU backend (always available)
    Cpu,
    /// Metal backend (Apple Silicon, macOS only)
    Metal,
    /// CUDA backend (NVIDIA GPUs)
    Cuda,
}

/// Executor for backend execution
///
/// The executor wraps a `hologram-backends::Backend` and provides:
/// - Buffer allocation mapped to backend handles
/// - Zero-copy memory management
/// - Direct ISA program execution
/// - Rayon-parallelized execution loops
///
/// # Example
///
/// ```text
/// use hologram_core::Executor;
///
/// let mut exec = Executor::new()?;
/// let buf = exec.allocate::<f32>(3072)?; // One class worth of f32 elements
///
/// // Operations execute precompiled ISA Programs
/// // No runtime compilation overhead
/// ```
pub struct Executor {
    pub(crate) backend: Arc<RwLock<Box<dyn Backend + Send + Sync>>>,
    buffer_mappings: [Option<BufferHandle>; 96], // Class → Backend buffer handle (direct array indexing)
    next_class: u8,                              // Track next available class for allocation
    is_boundary_pool: [bool; 96],                // Track which classes use boundary pool (PoolHandle(0))
}

impl Executor {
    /// Create a new executor with CPU backend
    ///
    /// This initializes:
    /// - CpuBackend with rayon parallelization
    /// - Empty buffer/pool mappings
    /// - Class allocation counter starting at 0
    ///
    /// This is equivalent to `Executor::new_with_backend(BackendType::Cpu)`.
    #[tracing::instrument]
    pub fn new() -> Result<Self> {
        Self::new_with_backend(BackendType::Cpu)
    }

    /// Create a new executor with specified backend
    ///
    /// # Arguments
    ///
    /// * `backend_type` - The backend to use (Cpu, Metal, or Cuda)
    ///
    /// # Returns
    ///
    /// Returns `Err` if the specified backend is not available or not yet implemented.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use hologram_core::{Executor, BackendType};
    ///
    /// // Create CPU executor (always available)
    /// let cpu_exec = Executor::new_with_backend(BackendType::Cpu)?;
    ///
    /// // Create Metal executor (Apple Silicon only)
    /// let metal_exec = Executor::new_with_backend(BackendType::Metal)?;
    ///
    /// // Create CUDA executor (NVIDIA GPUs only)
    /// let cuda_exec = Executor::new_with_backend(BackendType::Cuda)?;
    /// # Ok::<(), hologram_core::Error>(())
    /// ```
    #[tracing::instrument]
    pub fn new_with_backend(backend_type: BackendType) -> Result<Self> {
        let start = std::time::Instant::now();

        let backend: Box<dyn Backend + Send + Sync> = match backend_type {
            BackendType::Cpu => Box::new(CpuBackend::new()),
            BackendType::Metal => {
                // Metal backend only available on Apple platforms
                #[cfg(target_vendor = "apple")]
                {
                    match MetalBackend::new() {
                        Ok(backend) => Box::new(backend),
                        Err(e) => {
                            return Err(Error::InvalidOperation(format!(
                                "Failed to create Metal backend: {}",
                                e
                            )));
                        }
                    }
                }
                #[cfg(not(target_vendor = "apple"))]
                {
                    return Err(Error::InvalidOperation(
                        "Metal backend only available on Apple platforms".into(),
                    ));
                }
            }
            BackendType::Cuda => {
                // CUDA backend for NVIDIA GPUs (requires 'cuda' feature)
                #[cfg(feature = "cuda")]
                {
                    match CudaBackend::new() {
                        Ok(backend) => Box::new(backend),
                        Err(e) => {
                            return Err(Error::InvalidOperation(format!("Failed to create CUDA backend: {}", e)));
                        }
                    }
                }
                #[cfg(not(feature = "cuda"))]
                {
                    return Err(Error::InvalidOperation(
                        "CUDA backend requires 'cuda' feature to be enabled".into(),
                    ));
                }
            }
        };

        let duration_us = start.elapsed().as_micros() as u64;
        tracing::debug!(
            duration_us = duration_us,
            backend = ?backend_type,
            "executor_created"
        );

        Ok(Self {
            backend: Arc::new(RwLock::new(backend)),
            buffer_mappings: [None; 96],
            next_class: 0,
            is_boundary_pool: [false; 96],
        })
    }

    /// Create a new executor with automatic backend detection
    ///
    /// Automatically selects the best available backend in this order:
    /// 1. Metal (if on Apple Silicon)
    /// 2. CUDA (if NVIDIA GPU available)
    /// 3. CPU (fallback, always available)
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_core::Executor;
    ///
    /// // Automatically select best backend
    /// let exec = Executor::new_auto()?;
    /// # Ok::<(), hologram_core::Error>(())
    /// ```
    #[tracing::instrument]
    pub fn new_auto() -> Result<Self> {
        // Try Metal first (Apple Silicon)
        if cfg!(target_os = "macos") && cfg!(target_arch = "aarch64") {
            if let Ok(exec) = Self::new_with_backend(BackendType::Metal) {
                tracing::info!("Auto-selected Metal backend (Apple Silicon detected)");
                return Ok(exec);
            }
        }

        // Try CUDA (NVIDIA GPU)
        // Will succeed if CUDA feature is enabled and NVIDIA GPU is available
        if let Ok(exec) = Self::new_with_backend(BackendType::Cuda) {
            tracing::info!("Auto-selected CUDA backend (NVIDIA GPU detected)");
            return Ok(exec);
        }

        // Fallback to CPU (always available)
        tracing::info!("Auto-selected CPU backend (fallback)");
        Self::new_with_backend(BackendType::Cpu)
    }

    /// Get shared reference to backend (for read operations)
    pub fn backend(&self) -> Arc<RwLock<Box<dyn Backend + Send + Sync>>> {
        Arc::clone(&self.backend)
    }

    /// Allocate a linear buffer of `len` elements
    ///
    /// Allocates a buffer managed by the backend and maps it to the next available class.
    ///
    /// # Type Requirements
    ///
    /// `T` must implement `bytemuck::Pod` for safe zero-copy semantics.
    ///
    /// # Example
    ///
    /// ```text
    /// let buf: Buffer<f32> = exec.allocate(3072)?; // One class worth of f32s
    /// ```
    #[tracing::instrument(skip(self), fields(
        len = len,
        elem_size = std::mem::size_of::<T>(),
        type_name = std::any::type_name::<T>()
    ))]
    pub fn allocate<T: bytemuck::Pod>(&mut self, len: usize) -> Result<Buffer<T>> {
        let start = std::time::Instant::now();

        // Check if we have available classes
        if self.next_class >= 96 {
            return Err(Error::InvalidOperation(
                "No more classes available for allocation (all 96 classes used)".into(),
            ));
        }

        let class = self.next_class;
        self.next_class += 1;

        let size_bytes = len * std::mem::size_of::<T>();

        // Allocate buffer via backend
        let handle = self
            .backend
            .write()
            .allocate_buffer(size_bytes)
            .map_err(|e| Error::InvalidOperation(format!("Backend buffer allocation failed: {}", e)))?;

        // Map class to backend handle (direct array indexing)
        self.buffer_mappings[class as usize] = Some(handle);

        let duration_us = start.elapsed().as_micros() as u64;
        tracing::debug!(
            duration_us = duration_us,
            class = class,
            size_bytes = size_bytes,
            size_kb = size_bytes as f64 / 1024.0,
            pool = "Linear",
            "buffer_allocated"
        );

        Ok(Buffer::new(class, len, MemoryPool::Linear))
    }

    /// Allocate a boundary-addressed buffer
    ///
    /// This creates a buffer that directly maps to a specific class
    /// in the 96-class system.
    ///
    /// # Arguments
    ///
    /// * `class` - Class index [0, 96)
    /// * `width` - Width in pages [0, 48) (for compatibility)
    /// * `height` - Height in bytes per page [0, 256) (for compatibility)
    ///
    /// # Example
    ///
    /// ```text
    /// let buf: Buffer<f32> = exec.allocate_boundary(0, 48, 256)?;
    /// ```
    #[tracing::instrument(skip(self), fields(
        class = class,
        width = width,
        height = height,
        elem_size = std::mem::size_of::<T>(),
        type_name = std::any::type_name::<T>()
    ))]
    pub fn allocate_boundary<T: bytemuck::Pod>(&mut self, class: u8, width: usize, height: usize) -> Result<Buffer<T>> {
        let start = std::time::Instant::now();

        // Validate class
        if class >= 96 {
            return Err(Error::InvalidOperation(format!("class {} >= 96", class)));
        }
        if width > 48 {
            return Err(Error::InvalidOperation(format!("width {} > 48", width)));
        }
        if height > 256 {
            return Err(Error::InvalidOperation(format!("height {} > 256", height)));
        }

        // Boundary buffers: width × height bytes per class
        let size_bytes = width * height; // Typically: 48 × 256 = 12,288 bytes
        let len = size_bytes / std::mem::size_of::<T>(); // e.g., 3,072 for f32

        // Mark this class as using boundary pool (PoolHandle(0))
        // No BufferHandle allocation needed - boundary pool uses PoolHandle(0) directly
        // The backend will lazily initialize the actual boundary pool on first access
        self.is_boundary_pool[class as usize] = true;
        self.buffer_mappings[class as usize] = None; // No BufferHandle for boundary pool classes

        let duration_us = start.elapsed().as_micros() as u64;
        tracing::debug!(
            duration_us = duration_us,
            class = class,
            size_bytes = size_bytes,
            size_kb = size_bytes as f64 / 1024.0,
            pool = "Boundary",
            "boundary_buffer_allocated"
        );

        Ok(Buffer::new(class, len, MemoryPool::Boundary))
    }

    /// Write data to a buffer (zero-copy via backend)
    ///
    /// # Arguments
    ///
    /// * `class` - The class index [0, 96)
    /// * `data` - Slice of data to write
    ///
    /// # Zero-Copy Design
    ///
    /// Data is written directly to backend-managed memory without intermediate copies.
    pub(crate) fn write_buffer_data<T: bytemuck::Pod>(&mut self, class: u8, data: &[T]) -> Result<()> {
        let bytes = bytemuck::cast_slice(data);

        // Check if this class uses boundary pool (PoolHandle(0))
        if self.is_boundary_pool[class as usize] {
            use hologram_backends::backend::PoolHandle;

            // Calculate offset for this class (class * 12,288 bytes)
            const BYTES_PER_CLASS: usize = 12_288;
            let offset = class as usize * BYTES_PER_CLASS;

            // Write to pool at offset (uses efficient pool storage)
            self.backend
                .write()
                .copy_to_pool(PoolHandle::new(0), offset, bytes)
                .map_err(|e| Error::InvalidOperation(format!("Backend write failed: {}", e)))?;
        } else {
            // Regular buffer write
            let handle = self.buffer_mappings[class as usize]
                .ok_or_else(|| Error::InvalidOperation(format!("No buffer mapped to class {}", class)))?;

            self.backend
                .write()
                .copy_to_buffer(handle, bytes)
                .map_err(|e| Error::InvalidOperation(format!("Backend write failed: {}", e)))?;
        }

        Ok(())
    }

    /// Read data from a buffer (zero-copy via backend)
    ///
    /// # Arguments
    ///
    /// * `class` - The class index [0, 96)
    /// * `len` - Number of elements to read
    ///
    /// # Zero-Copy Design
    ///
    /// Data is read directly from backend-managed memory without intermediate copies.
    pub(crate) fn read_buffer_data<T: bytemuck::Pod>(&self, class: u8, len: usize) -> Result<Vec<T>> {
        let mut bytes = vec![0u8; len * std::mem::size_of::<T>()];

        // Check if this class uses boundary pool (PoolHandle(0))
        if self.is_boundary_pool[class as usize] {
            use hologram_backends::backend::PoolHandle;

            // Calculate offset for this class (class * 12,288 bytes)
            const BYTES_PER_CLASS: usize = 12_288;
            let offset = class as usize * BYTES_PER_CLASS;

            // Read from pool at offset (uses efficient pool storage)
            self.backend
                .write()
                .copy_from_pool(PoolHandle::new(0), offset, &mut bytes)
                .map_err(|e| Error::InvalidOperation(format!("Backend read failed: {}", e)))?;
        } else {
            // Regular buffer read
            let handle = self.buffer_mappings[class as usize]
                .ok_or_else(|| Error::InvalidOperation(format!("No buffer mapped to class {}", class)))?;

            self.backend
                .write()
                .copy_from_buffer(handle, &mut bytes)
                .map_err(|e| Error::InvalidOperation(format!("Backend read failed: {}", e)))?;
        }

        Ok(bytemuck::cast_slice(&bytes).to_vec())
    }

    /// Get buffer handle for a class (used by operations)
    pub(crate) fn get_buffer_handle(&self, class: u8) -> Result<BufferHandle> {
        // Check if this is a boundary pool buffer
        if self.is_boundary_pool[class as usize] {
            // Encode class index in buffer handle ID for boundary pool buffers
            // Use high range (u64::MAX - 95 to u64::MAX) to avoid conflicts with regular buffers
            // Handle ID = BOUNDARY_POOL_HANDLE_BASE + class
            // The backend will recognize these and compute offset = class * 12,288 + element_offset
            // See load_bytes_from_storage() and store_bytes_to_storage() in hologram-backends
            const BOUNDARY_POOL_HANDLE_BASE: u64 = u64::MAX - 95;
            return Ok(BufferHandle::new(BOUNDARY_POOL_HANDLE_BASE + class as u64));
        }

        // Regular buffer - look up handle in mappings
        self.buffer_mappings[class as usize]
            .ok_or_else(|| Error::InvalidOperation(format!("No buffer mapped to class {}", class)))
    }

    /// Get raw const pointer to buffer memory (for inline SIMD kernels)
    ///
    /// # Safety
    ///
    /// This is intended ONLY for inline SIMD kernel fast paths.
    /// The returned pointer is valid as long as:
    /// - The buffer is valid
    /// - No mutable operations occur on the buffer
    /// - The executor/backend is not dropped
    ///
    /// # Returns
    ///
    /// Returns `Err` if the backend is not CPU or the buffer is invalid.
    pub fn get_buffer_ptr<T: bytemuck::Pod>(&self, buffer: &Buffer<T>) -> Result<*const T> {
        // CPU backend only - get raw pointer from MemoryManager
        let backend = self.backend.read();
        let cpu_backend = backend
            .as_any()
            .downcast_ref::<CpuBackend>()
            .ok_or_else(|| Error::InvalidOperation("Inline kernels only supported on CPU backend".into()))?;

        let byte_ptr = if self.is_boundary_pool[buffer.class_index() as usize] {
            // Boundary pool buffer - get pointer to class data
            cpu_backend
                .get_boundary_class_ptr(buffer.class_index())
                .map_err(|e| Error::InvalidOperation(format!("Failed to get boundary class pointer: {}", e)))?
        } else {
            // Regular buffer - get pointer via buffer handle
            let handle = self.get_buffer_handle(buffer.class_index())?;
            cpu_backend
                .get_buffer_ptr(handle)
                .map_err(|e| Error::InvalidOperation(format!("Failed to get buffer pointer: {}", e)))?
        };

        // Cast u8 pointer to T pointer (bytemuck::Pod ensures this is safe)
        Ok(byte_ptr as *const T)
    }

    /// Get raw mutable pointer to buffer memory (for inline SIMD kernels)
    ///
    /// # Safety
    ///
    /// This is intended ONLY for inline SIMD kernel fast paths.
    /// The returned pointer is valid as long as:
    /// - The buffer is valid
    /// - No concurrent access occurs
    /// - The executor/backend is not dropped
    ///
    /// # Returns
    ///
    /// Returns `Err` if the backend is not CPU or the buffer is invalid.
    pub fn get_buffer_mut_ptr<T: bytemuck::Pod>(&mut self, buffer: &Buffer<T>) -> Result<*mut T> {
        // CPU backend only - get raw pointer from MemoryManager
        let mut backend = self.backend.write();
        let cpu_backend = backend
            .as_any_mut()
            .downcast_mut::<CpuBackend>()
            .ok_or_else(|| Error::InvalidOperation("Inline kernels only supported on CPU backend".into()))?;

        let byte_ptr = if self.is_boundary_pool[buffer.class_index() as usize] {
            // Boundary pool buffer - get mutable pointer to class data
            cpu_backend
                .get_boundary_class_mut_ptr(buffer.class_index())
                .map_err(|e| Error::InvalidOperation(format!("Failed to get boundary class mut pointer: {}", e)))?
        } else {
            // Regular buffer - get mutable pointer via buffer handle
            let handle = self.get_buffer_handle(buffer.class_index())?;
            cpu_backend
                .get_buffer_mut_ptr(handle)
                .map_err(|e| Error::InvalidOperation(format!("Failed to get buffer mut pointer: {}", e)))?
        };

        // Cast u8 pointer to T pointer (bytemuck::Pod ensures this is safe)
        Ok(byte_ptr as *mut T)
    }

    /// Get default launch configuration for N elements
    ///
    /// Uses rayon-compatible parallelization strategy:
    /// - Grid: 1 block
    /// - Block: N lanes (threads)
    /// - Shared memory: default
    pub fn default_launch_config(n: usize) -> LaunchConfig {
        LaunchConfig {
            grid: GridDim { x: 1, y: 1, z: 1 },
            block: BlockDim {
                x: n as u32,
                y: 1,
                z: 1,
            },
            shared_memory: SharedMemoryConfig::default(),
        }
    }
}

impl Default for Executor {
    fn default() -> Self {
        Self::new().expect("Failed to create default executor")
    }
}

impl Drop for Executor {
    fn drop(&mut self) {
        tracing::debug!("Executor dropped");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_executor_creation() {
        let exec = Executor::new().unwrap();
        assert_eq!(exec.next_class, 0);
    }

    #[test]
    fn test_allocate_linear() {
        let mut exec = Executor::new().unwrap();
        let buf: Buffer<f32> = exec.allocate(1024).unwrap();
        assert_eq!(buf.len(), 1024);
        assert_eq!(buf.pool(), MemoryPool::Linear);
    }

    #[test]
    fn test_allocate_boundary() {
        let mut exec = Executor::new().unwrap();
        let buf: Buffer<f32> = exec.allocate_boundary(0, 48, 256).unwrap();
        // 48 × 256 bytes = 12,288 bytes / 4 bytes per f32 = 3,072 f32 elements
        assert_eq!(buf.len(), 3072);
        assert_eq!(buf.pool(), MemoryPool::Boundary);
    }

    #[test]
    fn test_allocate_boundary_invalid_class() {
        let mut exec = Executor::new().unwrap();
        let result: Result<Buffer<f32>> = exec.allocate_boundary(96, 48, 256);
        assert!(result.is_err());
    }

    #[test]
    fn test_buffer_read_write() {
        let mut exec = Executor::new().unwrap();
        let mut buf: Buffer<f32> = exec.allocate(10).unwrap();

        // Write data
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0];
        buf.copy_from_slice(&mut exec, &data).unwrap();

        // Read data back
        let result = buf.to_vec(&exec).unwrap();
        assert_eq!(result, data);
    }

    #[test]
    fn test_multiple_allocations() {
        let mut exec = Executor::new().unwrap();

        // Allocate multiple buffers
        let buf1: Buffer<f32> = exec.allocate(100).unwrap();
        let buf2: Buffer<f32> = exec.allocate(200).unwrap();
        let buf3: Buffer<f32> = exec.allocate(300).unwrap();

        // Each should get a different class
        assert_eq!(buf1.class(), 0);
        assert_eq!(buf2.class(), 1);
        assert_eq!(buf3.class(), 2);
    }

    #[test]
    fn test_launch_config_creation() {
        let config = Executor::default_launch_config(1024);
        assert_eq!(config.grid.x, 1);
        assert_eq!(config.block.x, 1024);
    }
}
