//! Memory management trait and utilities shared across backends
//!
//! Provides a common interface for memory management that can be implemented
//! by different backends with their own storage mechanisms:
//! - CPU: Vec<u8>
//! - GPU: CUDA/Vulkan/Metal device memory
//! - TPU: HBM memory
//! - FPGA: On-chip memory

use crate::backend::{BufferHandle, PoolHandle};
use crate::error::Result;

// ================================================================================================
// Memory Storage Trait
// ================================================================================================

/// Memory storage trait that must be implemented by all backends
///
/// This trait abstracts over the underlying storage mechanism, allowing
/// different backends to use different memory types:
/// - CPU backend uses `Vec<u8>`
/// - GPU backend uses device memory pointers
/// - TPU backend uses HBM memory
/// - FPGA backend uses on-chip RAM
///
/// # Buffer Management
///
/// Buffers are general-purpose linear memory allocations accessed via:
/// - `LDG`/`STG` instructions (global memory)
/// - `LDS`/`STS` instructions (shared memory, treated as global on CPU)
///
/// # Pool Management
///
/// Pools are fixed-size streaming buffers accessed via:
/// - `PoolLoad`/`PoolStore` instructions
/// - Enable O(1) space computation on arbitrary input sizes
///
/// # Thread Safety
///
/// Implementations must be thread-safe when wrapped in `Arc<RwLock<_>>`.
/// The common execution state uses `Arc<RwLock<M>>` to share memory across lanes.
pub trait MemoryStorage: Send + Sync {
    // ============================================================================================
    // Buffer Management
    // ============================================================================================

    /// Allocate a buffer of the given size in bytes
    ///
    /// Returns a handle to the allocated buffer.
    fn allocate_buffer(&mut self, size: usize) -> Result<BufferHandle>;

    /// Free a previously allocated buffer
    ///
    /// # Errors
    ///
    /// Returns an error if the buffer handle is invalid.
    fn free_buffer(&mut self, handle: BufferHandle) -> Result<()>;

    /// Copy data from host to buffer
    ///
    /// # Arguments
    ///
    /// * `handle` - Buffer handle
    /// * `data` - Data to copy
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Buffer handle is invalid
    /// - Data size exceeds buffer size
    fn copy_to_buffer(&mut self, handle: BufferHandle, data: &[u8]) -> Result<()>;

    /// Copy data from buffer to host
    ///
    /// # Arguments
    ///
    /// * `handle` - Buffer handle
    /// * `data` - Destination buffer
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Buffer handle is invalid
    /// - Data size exceeds buffer size
    fn copy_from_buffer(&self, handle: BufferHandle, data: &mut [u8]) -> Result<()>;

    /// Get buffer size in bytes
    ///
    /// # Errors
    ///
    /// Returns an error if the buffer handle is invalid.
    fn buffer_size(&self, handle: BufferHandle) -> Result<usize>;

    // ============================================================================================
    // Pool Storage Management
    // ============================================================================================

    /// Allocate a pool of the given size in bytes
    ///
    /// Pools enable O(1) space streaming computation.
    fn allocate_pool(&mut self, size: usize) -> Result<PoolHandle>;

    /// Free a previously allocated pool
    ///
    /// # Errors
    ///
    /// Returns an error if the pool handle is invalid.
    fn free_pool(&mut self, handle: PoolHandle) -> Result<()>;

    /// Copy data to pool at given offset
    ///
    /// # Arguments
    ///
    /// * `handle` - Pool handle
    /// * `offset` - Byte offset within pool
    /// * `data` - Data to copy
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Pool handle is invalid
    /// - Offset + data size exceeds pool size
    fn copy_to_pool(&mut self, handle: PoolHandle, offset: usize, data: &[u8]) -> Result<()>;

    /// Copy data from pool at given offset
    ///
    /// # Arguments
    ///
    /// * `handle` - Pool handle
    /// * `offset` - Byte offset within pool
    /// * `data` - Destination buffer
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Pool handle is invalid
    /// - Offset + data size exceeds pool size
    fn copy_from_pool(&self, handle: PoolHandle, offset: usize, data: &mut [u8]) -> Result<()>;

    /// Get pool size in bytes
    ///
    /// # Errors
    ///
    /// Returns an error if the pool handle is invalid.
    fn pool_size(&self, handle: PoolHandle) -> Result<usize>;
}

// ================================================================================================
// Generic Memory Manager
// ================================================================================================

/// Generic memory manager wrapping any MemoryStorage implementation
///
/// This struct provides the common memory management pattern (handle generation,
/// HashMap storage) that can be used with any underlying storage type.
///
/// # Type Parameter
///
/// - `S`: The storage implementation (must implement MemoryStorage)
///
/// # Usage
///
/// ```text
/// // For CPU backend
/// type CpuMemoryManager = MemoryManager<CpuStorage>;
///
/// // For GPU backend
/// type GpuMemoryManager = MemoryManager<GpuStorage>;
/// ```
pub struct MemoryManager<S: MemoryStorage> {
    storage: S,
}

impl<S: MemoryStorage> MemoryManager<S> {
    /// Create a new memory manager with the given storage implementation
    pub fn new(storage: S) -> Self {
        Self { storage }
    }

    /// Get a reference to the underlying storage
    pub fn storage(&self) -> &S {
        &self.storage
    }

    /// Get a mutable reference to the underlying storage
    pub fn storage_mut(&mut self) -> &mut S {
        &mut self.storage
    }
}

impl<S: MemoryStorage> MemoryStorage for MemoryManager<S> {
    fn allocate_buffer(&mut self, size: usize) -> Result<BufferHandle> {
        self.storage.allocate_buffer(size)
    }

    fn free_buffer(&mut self, handle: BufferHandle) -> Result<()> {
        self.storage.free_buffer(handle)
    }

    fn copy_to_buffer(&mut self, handle: BufferHandle, data: &[u8]) -> Result<()> {
        self.storage.copy_to_buffer(handle, data)
    }

    fn copy_from_buffer(&self, handle: BufferHandle, data: &mut [u8]) -> Result<()> {
        self.storage.copy_from_buffer(handle, data)
    }

    fn buffer_size(&self, handle: BufferHandle) -> Result<usize> {
        self.storage.buffer_size(handle)
    }

    fn allocate_pool(&mut self, size: usize) -> Result<PoolHandle> {
        self.storage.allocate_pool(size)
    }

    fn free_pool(&mut self, handle: PoolHandle) -> Result<()> {
        self.storage.free_pool(handle)
    }

    fn copy_to_pool(&mut self, handle: PoolHandle, offset: usize, data: &[u8]) -> Result<()> {
        self.storage.copy_to_pool(handle, offset, data)
    }

    fn copy_from_pool(&self, handle: PoolHandle, offset: usize, data: &mut [u8]) -> Result<()> {
        self.storage.copy_from_pool(handle, offset, data)
    }

    fn pool_size(&self, handle: PoolHandle) -> Result<usize> {
        self.storage.pool_size(handle)
    }
}

// ================================================================================================
// Helper Functions
// ================================================================================================

/// Load bytes from memory storage
///
/// This is a shared helper function used by LDG/LDS instruction implementations.
///
/// # Arguments
///
/// * `storage` - Memory storage implementation
/// * `handle` - Buffer handle
/// * `offset` - Byte offset within buffer
/// * `size` - Number of bytes to load
///
/// # Returns
///
/// Vector containing the loaded bytes
///
/// # Errors
///
/// Returns an error if the buffer handle is invalid or the access is out of bounds.
pub fn load_bytes_from_storage<S: MemoryStorage>(
    storage: &S,
    handle: BufferHandle,
    offset: usize,
    size: usize,
) -> Result<Vec<u8>> {
    let buffer_size = storage.buffer_size(handle)?;

    if offset + size > buffer_size {
        return Err(crate::error::BackendError::BufferOutOfBounds {
            offset,
            size,
            buffer_size,
        });
    }

    // Special handling for boundary pool access
    // Two patterns supported:
    // 1. BufferHandle(0): PhiCoordinate addressing with full offset (class * 12,288 + position)
    // 2. BufferHandle(BOUNDARY_POOL_HANDLE_BASE + class): Class-specific with element offset
    const BOUNDARY_POOL_HANDLE_BASE: u64 = u64::MAX - 95;
    if handle.id() == 0 || handle.id() >= BOUNDARY_POOL_HANDLE_BASE {
        let actual_offset = if handle.id() == 0 {
            // PhiCoordinate: offset already includes class base
            offset
        } else {
            // Class-specific: compute full offset
            let class = (handle.id() - BOUNDARY_POOL_HANDLE_BASE) as u8;
            let class_base_offset = (class as usize) * 12_288; // BYTES_PER_CLASS = 12,288
            class_base_offset + offset
        };

        let mut result = vec![0u8; size];
        storage.copy_from_pool(PoolHandle::new(0), actual_offset, &mut result)?;
        return Ok(result);
    }

    // Read entire buffer (since MemoryStorage trait doesn't support offset parameter)
    let mut buffer = vec![0u8; buffer_size];
    storage.copy_from_buffer(handle, &mut buffer)?;

    // Return the requested slice
    Ok(buffer[offset..offset + size].to_vec())
}

/// Store bytes to memory storage
///
/// This is a shared helper function used by STG/STS instruction implementations.
///
/// # Arguments
///
/// * `storage` - Memory storage implementation
/// * `handle` - Buffer handle
/// * `offset` - Byte offset within buffer
/// * `bytes` - Bytes to store
///
/// # Errors
///
/// Returns an error if the buffer handle is invalid or the access is out of bounds.
pub fn store_bytes_to_storage<S: MemoryStorage>(
    storage: &mut S,
    handle: BufferHandle,
    offset: usize,
    bytes: &[u8],
) -> Result<()> {
    let buffer_size = storage.buffer_size(handle)?;

    if offset + bytes.len() > buffer_size {
        return Err(crate::error::BackendError::BufferOutOfBounds {
            offset,
            size: bytes.len(),
            buffer_size,
        });
    }

    // Special handling for boundary pool access
    // Two patterns supported:
    // 1. BufferHandle(0): PhiCoordinate addressing with full offset (class * 12,288 + position)
    // 2. BufferHandle(BOUNDARY_POOL_HANDLE_BASE + class): Class-specific with element offset
    const BOUNDARY_POOL_HANDLE_BASE: u64 = u64::MAX - 95;
    if handle.id() == 0 || handle.id() >= BOUNDARY_POOL_HANDLE_BASE {
        let actual_offset = if handle.id() == 0 {
            // PhiCoordinate: offset already includes class base
            offset
        } else {
            // Class-specific: compute full offset
            let class = (handle.id() - BOUNDARY_POOL_HANDLE_BASE) as u8;
            let class_base_offset = (class as usize) * 12_288; // BYTES_PER_CLASS = 12,288
            class_base_offset + offset
        };

        storage.copy_to_pool(PoolHandle::new(0), actual_offset, bytes)?;
        return Ok(());
    }

    // Read existing buffer (since MemoryStorage trait doesn't support offset parameter)
    let mut buffer = vec![0u8; buffer_size];
    storage.copy_from_buffer(handle, &mut buffer)?;

    // Update bytes at offset
    buffer[offset..offset + bytes.len()].copy_from_slice(bytes);

    // Write back entire buffer
    storage.copy_to_buffer(handle, &buffer)
}
