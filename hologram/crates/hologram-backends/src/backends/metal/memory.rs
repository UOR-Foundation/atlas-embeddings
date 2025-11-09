//! Metal memory management for GPU buffers and pools
//!
//! Manages Metal buffers with unified memory (shared between CPU and GPU on Apple Silicon).

#[cfg(target_vendor = "apple")]
use metal::{Buffer as MetalBuffer, Device, MTLResourceOptions};

#[cfg(target_vendor = "apple")]
use std::collections::HashMap;

/// Memory manager for Metal GPU buffers and pools
#[cfg(target_vendor = "apple")]
pub struct MetalMemoryManager {
    /// Metal device for buffer allocation
    device: Device,

    /// Allocated buffers (handle -> Metal buffer)
    buffers: HashMap<u64, MetalBuffer>,

    /// Allocated pools (handle -> Metal buffer)
    pools: HashMap<u64, MetalBuffer>,

    /// Next buffer handle
    next_buffer_handle: u64,

    /// Next pool handle
    next_pool_handle: u64,
}

#[cfg(target_vendor = "apple")]
impl MetalMemoryManager {
    /// Create a new Metal memory manager
    ///
    /// # Arguments
    ///
    /// * `device` - Metal device for buffer allocation
    pub fn new(device: Device) -> Self {
        Self {
            device,
            buffers: HashMap::new(),
            pools: HashMap::new(),
            next_buffer_handle: 1,
            next_pool_handle: 1,
        }
    }

    // ============================================================================================
    // Buffer Management
    // ============================================================================================

    /// Allocate a Metal buffer
    ///
    /// Uses MTLResourceOptions::StorageModeShared for unified memory on Apple Silicon.
    /// This allows zero-copy access from both CPU and GPU.
    pub fn allocate_buffer(&mut self, size: usize) -> Result<BufferHandle> {
        // Create Metal buffer with shared storage mode (unified memory)
        let metal_buffer = self.device.new_buffer(
            size as u64,
            MTLResourceOptions::StorageModeShared, // CPU and GPU can both access
        );

        let handle = BufferHandle::new(self.next_buffer_handle);
        self.next_buffer_handle += 1;

        self.buffers.insert(handle.id(), metal_buffer);

        Ok(handle)
    }

    /// Free a Metal buffer
    pub fn free_buffer(&mut self, handle: BufferHandle) -> Result<()> {
        self.buffers
            .remove(&handle.id())
            .ok_or(BackendError::InvalidBufferHandle(handle.id()))?;
        Ok(())
    }

    /// Copy data from CPU to Metal buffer
    pub fn copy_to_buffer(&mut self, handle: BufferHandle, data: &[u8]) -> Result<()> {
        let buffer = self
            .buffers
            .get(&handle.id())
            .ok_or(BackendError::InvalidBufferHandle(handle.id()))?;

        // Ensure data fits in buffer
        if data.len() > buffer.length() as usize {
            return Err(BackendError::BufferOutOfBounds {
                offset: 0,
                size: data.len(),
                buffer_size: buffer.length() as usize,
            });
        }

        // Copy data to Metal buffer
        unsafe {
            let contents = buffer.contents() as *mut u8;
            std::ptr::copy_nonoverlapping(data.as_ptr(), contents, data.len());
        }

        Ok(())
    }

    /// Copy data from Metal buffer to CPU
    pub fn copy_from_buffer(&self, handle: BufferHandle, data: &mut [u8]) -> Result<()> {
        let buffer = self
            .buffers
            .get(&handle.id())
            .ok_or(BackendError::InvalidBufferHandle(handle.id()))?;

        // Ensure destination can hold buffer contents
        if data.len() > buffer.length() as usize {
            return Err(BackendError::BufferOutOfBounds {
                offset: 0,
                size: data.len(),
                buffer_size: buffer.length() as usize,
            });
        }

        // Copy from Metal buffer
        unsafe {
            let contents = buffer.contents() as *const u8;
            std::ptr::copy_nonoverlapping(contents, data.as_mut_ptr(), data.len());
        }

        Ok(())
    }

    /// Get buffer size in bytes
    pub fn buffer_size(&self, handle: BufferHandle) -> Result<usize> {
        let buffer = self
            .buffers
            .get(&handle.id())
            .ok_or(BackendError::InvalidBufferHandle(handle.id()))?;
        Ok(buffer.length() as usize)
    }

    /// Get Metal buffer for GPU operations
    pub fn get_buffer(&self, handle: BufferHandle) -> Result<&MetalBuffer> {
        self.buffers
            .get(&handle.id())
            .ok_or(BackendError::InvalidBufferHandle(handle.id()))
    }

    // ============================================================================================
    // Pool Management
    // ============================================================================================

    /// Allocate a Metal pool
    pub fn allocate_pool(&mut self, size: usize) -> Result<PoolHandle> {
        // Create Metal buffer with shared storage mode
        let metal_buffer = self
            .device
            .new_buffer(size as u64, MTLResourceOptions::StorageModeShared);

        let handle = PoolHandle::new(self.next_pool_handle);
        self.next_pool_handle += 1;

        self.pools.insert(handle.id(), metal_buffer);

        Ok(handle)
    }

    /// Free a Metal pool
    pub fn free_pool(&mut self, handle: PoolHandle) -> Result<()> {
        self.pools
            .remove(&handle.id())
            .ok_or(BackendError::InvalidPoolHandle(handle.id()))?;
        Ok(())
    }

    /// Copy data from CPU to Metal pool
    pub fn copy_to_pool(&mut self, handle: PoolHandle, offset: usize, data: &[u8]) -> Result<()> {
        let pool = self
            .pools
            .get(&handle.id())
            .ok_or(BackendError::InvalidPoolHandle(handle.id()))?;

        // Ensure data fits in pool
        if offset + data.len() > pool.length() as usize {
            return Err(BackendError::PoolOutOfBounds {
                offset,
                size: data.len(),
                pool_size: pool.length() as usize,
            });
        }

        // Copy data to Metal pool
        unsafe {
            let contents = (pool.contents() as *mut u8).add(offset);
            std::ptr::copy_nonoverlapping(data.as_ptr(), contents, data.len());
        }

        Ok(())
    }

    /// Copy data from Metal pool to CPU
    pub fn copy_from_pool(&self, handle: PoolHandle, offset: usize, data: &mut [u8]) -> Result<()> {
        let pool = self
            .pools
            .get(&handle.id())
            .ok_or(BackendError::InvalidPoolHandle(handle.id()))?;

        // Ensure read is within pool bounds
        if offset + data.len() > pool.length() as usize {
            return Err(BackendError::PoolOutOfBounds {
                offset,
                size: data.len(),
                pool_size: pool.length() as usize,
            });
        }

        // Copy from Metal pool
        unsafe {
            let contents = (pool.contents() as *const u8).add(offset);
            std::ptr::copy_nonoverlapping(contents, data.as_mut_ptr(), data.len());
        }

        Ok(())
    }

    /// Get pool size in bytes
    pub fn pool_size(&self, handle: PoolHandle) -> Result<usize> {
        let pool = self
            .pools
            .get(&handle.id())
            .ok_or(BackendError::InvalidPoolHandle(handle.id()))?;
        Ok(pool.length() as usize)
    }

    /// Get Metal pool for GPU operations
    pub fn get_pool(&self, handle: PoolHandle) -> Result<&MetalBuffer> {
        self.pools
            .get(&handle.id())
            .ok_or(BackendError::InvalidPoolHandle(handle.id()))
    }
}

#[cfg(test)]
#[cfg(target_vendor = "apple")]
mod tests {
    use super::*;
    use metal::Device;

    #[test]
    fn test_metal_memory_manager_creation() {
        let device = Device::system_default().unwrap();
        let _manager = MetalMemoryManager::new(device);
    }

    #[test]
    fn test_buffer_allocation_and_free() {
        let device = Device::system_default().unwrap();
        let mut manager = MetalMemoryManager::new(device);

        let handle = manager.allocate_buffer(1024).unwrap();
        assert_eq!(manager.buffer_size(handle).unwrap(), 1024);

        manager.free_buffer(handle).unwrap();
        assert!(manager.buffer_size(handle).is_err());
    }

    #[test]
    fn test_buffer_copy_roundtrip() {
        let device = Device::system_default().unwrap();
        let mut manager = MetalMemoryManager::new(device);

        let handle = manager.allocate_buffer(64).unwrap();

        // Write data
        let data = b"Hello, Metal memory manager!";
        manager.copy_to_buffer(handle, data).unwrap();

        // Read data back
        let mut result = vec![0u8; data.len()];
        manager.copy_from_buffer(handle, &mut result).unwrap();

        assert_eq!(result, data);

        manager.free_buffer(handle).unwrap();
    }

    #[test]
    fn test_pool_allocation_and_free() {
        let device = Device::system_default().unwrap();
        let mut manager = MetalMemoryManager::new(device);

        let handle = manager.allocate_pool(4096).unwrap();
        assert_eq!(manager.pool_size(handle).unwrap(), 4096);

        manager.free_pool(handle).unwrap();
        assert!(manager.pool_size(handle).is_err());
    }

    #[test]
    fn test_pool_copy_with_offset() {
        let device = Device::system_default().unwrap();
        let mut manager = MetalMemoryManager::new(device);

        let handle = manager.allocate_pool(1024).unwrap();

        // Write at offset 100
        let data = [1.0f32, 2.0, 3.0, 4.0];
        let bytes = bytemuck::cast_slice(&data);
        manager.copy_to_pool(handle, 100, bytes).unwrap();

        // Read back from offset 100
        let mut result = [0.0f32; 4];
        let result_bytes = bytemuck::cast_slice_mut(&mut result);
        manager.copy_from_pool(handle, 100, result_bytes).unwrap();

        assert_eq!(result, data);

        manager.free_pool(handle).unwrap();
    }

    #[test]
    fn test_buffer_size_validation() {
        let device = Device::system_default().unwrap();
        let mut manager = MetalMemoryManager::new(device);

        let handle = manager.allocate_buffer(16).unwrap();

        // Try to write more than buffer can hold
        let too_much_data = vec![0u8; 32];
        assert!(manager.copy_to_buffer(handle, &too_much_data).is_err());

        manager.free_buffer(handle).unwrap();
    }
}
