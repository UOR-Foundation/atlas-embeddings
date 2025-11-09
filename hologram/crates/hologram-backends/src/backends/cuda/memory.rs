//! CUDA memory management for GPU buffers and pools
//!
//! Manages CUDA device memory with support for unified memory.

#[cfg(feature = "cuda")]
use crate::backend::{BufferHandle, PoolHandle};
#[cfg(feature = "cuda")]
use crate::error::{BackendError, Result};

#[cfg(feature = "cuda")]
use cudarc::driver::{CudaDevice, CudaSlice};

#[cfg(feature = "cuda")]
use std::collections::HashMap;

#[cfg(feature = "cuda")]
use std::sync::Arc;

/// Memory manager for CUDA GPU buffers and pools
#[cfg(feature = "cuda")]
pub struct CudaMemoryManager {
    /// CUDA device
    device: Arc<CudaDevice>,

    /// Allocated buffers (handle -> CUDA device pointer + size)
    buffers: HashMap<u64, (CudaSlice<u8>, usize)>,

    /// Allocated pools (handle -> CUDA device pointer + size)
    pools: HashMap<u64, (CudaSlice<u8>, usize)>,

    /// Next buffer handle
    next_buffer_handle: u64,

    /// Next pool handle
    next_pool_handle: u64,
}

#[cfg(feature = "cuda")]
impl CudaMemoryManager {
    /// Create a new CUDA memory manager
    ///
    /// # Arguments
    ///
    /// * `device` - CUDA device for buffer allocation
    pub fn new(device: Arc<CudaDevice>) -> Self {
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

    /// Allocate a CUDA buffer
    ///
    /// Allocates device memory on the GPU.
    pub fn allocate_buffer(&mut self, size: usize) -> Result<BufferHandle> {
        // Allocate CUDA device memory
        let device_ptr = self
            .device
            .alloc_zeros::<u8>(size)
            .map_err(|e| BackendError::Other(format!("CUDA buffer allocation failed: {}", e)))?;

        let handle = BufferHandle::new(self.next_buffer_handle);
        self.next_buffer_handle += 1;

        self.buffers.insert(handle.id(), (device_ptr.clone(), size));

        Ok(handle)
    }

    /// Free a CUDA buffer
    pub fn free_buffer(&mut self, handle: BufferHandle) -> Result<()> {
        self.buffers
            .remove(&handle.id())
            .ok_or(BackendError::InvalidBufferHandle(handle.id()))?;
        // CUDA memory is automatically freed when DevicePtr is dropped
        Ok(())
    }

    /// Copy data from CPU to CUDA buffer
    pub fn copy_to_buffer(&mut self, handle: BufferHandle, data: &[u8]) -> Result<()> {
        let (device_ptr, size) = self
            .buffers
            .get_mut(&handle.id())
            .ok_or(BackendError::InvalidBufferHandle(handle.id()))?;

        // Ensure data fits in buffer
        if data.len() > *size {
            return Err(BackendError::BufferOutOfBounds {
                offset: 0,
                size: data.len(),
                buffer_size: *size,
            });
        }

        // Copy data to CUDA device memory
        self.device
            .htod_sync_copy_into(data, device_ptr)
            .map_err(|e| BackendError::Other(format!("CUDA host-to-device copy failed: {}", e)))?;

        Ok(())
    }

    /// Copy data from CUDA buffer to CPU
    pub fn copy_from_buffer(&self, handle: BufferHandle, data: &mut [u8]) -> Result<()> {
        let (device_ptr, size) = self
            .buffers
            .get(&handle.id())
            .ok_or(BackendError::InvalidBufferHandle(handle.id()))?;

        // Ensure destination can hold buffer contents
        if data.len() > *size {
            return Err(BackendError::BufferOutOfBounds {
                offset: 0,
                size: data.len(),
                buffer_size: *size,
            });
        }

        // Copy from CUDA device memory
        self.device
            .dtoh_sync_copy_into(device_ptr, data)
            .map_err(|e| BackendError::Other(format!("CUDA device-to-host copy failed: {}", e)))?;

        Ok(())
    }

    /// Get buffer size in bytes
    pub fn buffer_size(&self, handle: BufferHandle) -> Result<usize> {
        let (_device_ptr, size) = self
            .buffers
            .get(&handle.id())
            .ok_or(BackendError::InvalidBufferHandle(handle.id()))?;
        Ok(*size)
    }

    /// Get CUDA device pointer for GPU operations
    /// Used for kernel execution (not yet implemented)
    #[allow(dead_code)]
    pub fn get_buffer(&self, handle: BufferHandle) -> Result<&CudaSlice<u8>> {
        let (device_slice, _size) = self
            .buffers
            .get(&handle.id())
            .ok_or(BackendError::InvalidBufferHandle(handle.id()))?;
        Ok(device_slice)
    }

    // ============================================================================================
    // Pool Management
    // ============================================================================================

    /// Allocate a CUDA pool
    pub fn allocate_pool(&mut self, size: usize) -> Result<PoolHandle> {
        // Allocate CUDA device memory
        let device_ptr = self
            .device
            .alloc_zeros::<u8>(size)
            .map_err(|e| BackendError::Other(format!("CUDA pool allocation failed: {}", e)))?;

        let handle = PoolHandle::new(self.next_pool_handle);
        self.next_pool_handle += 1;

        self.pools.insert(handle.id(), (device_ptr.clone(), size));

        Ok(handle)
    }

    /// Free a CUDA pool
    pub fn free_pool(&mut self, handle: PoolHandle) -> Result<()> {
        self.pools
            .remove(&handle.id())
            .ok_or(BackendError::InvalidPoolHandle(handle.id()))?;
        // CUDA memory is automatically freed when DevicePtr is dropped
        Ok(())
    }

    /// Copy data from CPU to CUDA pool
    pub fn copy_to_pool(&mut self, handle: PoolHandle, offset: usize, data: &[u8]) -> Result<()> {
        // Get mutable reference to device pointer and size
        let (device_ptr, size) = self
            .pools
            .get_mut(&handle.id())
            .ok_or(BackendError::InvalidPoolHandle(handle.id()))?;

        // Ensure data fits in pool
        if offset + data.len() > *size {
            return Err(BackendError::PoolOutOfBounds {
                offset,
                size: data.len(),
                pool_size: *size,
            });
        }

        // TODO: Implement offset copying for cudarc 0.12
        // For now, only support offset=0
        if offset != 0 {
            return Err(BackendError::Other(
                "CUDA pool offset copying not yet implemented for cudarc 0.12".to_string(),
            ));
        }

        // Copy data to CUDA pool
        self.device
            .htod_sync_copy_into(data, device_ptr)
            .map_err(|e| BackendError::Other(format!("CUDA host-to-device copy failed: {}", e)))?;

        Ok(())
    }

    /// Copy data from CUDA pool to CPU
    pub fn copy_from_pool(&self, handle: PoolHandle, offset: usize, data: &mut [u8]) -> Result<()> {
        let (device_ptr, size) = self
            .pools
            .get(&handle.id())
            .ok_or(BackendError::InvalidPoolHandle(handle.id()))?;

        // Ensure read is within pool bounds
        if offset + data.len() > *size {
            return Err(BackendError::PoolOutOfBounds {
                offset,
                size: data.len(),
                pool_size: *size,
            });
        }

        // TODO: Implement offset copying for cudarc 0.12
        // For now, only support offset=0
        if offset != 0 {
            return Err(BackendError::Other(
                "CUDA pool offset copying not yet implemented for cudarc 0.12".to_string(),
            ));
        }

        // Copy from CUDA pool
        self.device
            .dtoh_sync_copy_into(device_ptr, data)
            .map_err(|e| BackendError::Other(format!("CUDA device-to-host copy failed: {}", e)))?;

        Ok(())
    }

    /// Get pool size in bytes
    pub fn pool_size(&self, handle: PoolHandle) -> Result<usize> {
        let (_device_ptr, size) = self
            .pools
            .get(&handle.id())
            .ok_or(BackendError::InvalidPoolHandle(handle.id()))?;
        Ok(*size)
    }

    /// Get CUDA pool device pointer for GPU operations
    /// Used for kernel execution (not yet implemented)
    #[allow(dead_code)]
    pub fn get_pool(&self, handle: PoolHandle) -> Result<&CudaSlice<u8>> {
        let (device_slice, _size) = self
            .pools
            .get(&handle.id())
            .ok_or(BackendError::InvalidPoolHandle(handle.id()))?;
        Ok(device_slice)
    }
}

#[cfg(test)]
#[cfg(feature = "cuda")]
mod tests {
    use super::*;
    use cudarc::driver::CudaDevice;

    fn try_get_device() -> Option<Arc<CudaDevice>> {
        CudaDevice::new(0).ok()
    }

    #[test]
    fn test_cuda_memory_manager_creation() {
        if let Some(device) = try_get_device() {
            let _manager = CudaMemoryManager::new(device);
        }
    }

    #[test]
    fn test_buffer_allocation_and_free() {
        if let Some(device) = try_get_device() {
            let mut manager = CudaMemoryManager::new(device);

            let handle = manager.allocate_buffer(1024).unwrap();
            assert_eq!(manager.buffer_size(handle).unwrap(), 1024);

            manager.free_buffer(handle).unwrap();
            assert!(manager.buffer_size(handle).is_err());
        }
    }

    #[test]
    fn test_buffer_copy_roundtrip() {
        if let Some(device) = try_get_device() {
            let mut manager = CudaMemoryManager::new(device);

            let handle = manager.allocate_buffer(64).unwrap();

            // Write data
            let data = b"Hello, CUDA memory manager!";
            manager.copy_to_buffer(handle, data).unwrap();

            // Read data back
            let mut result = vec![0u8; data.len()];
            manager.copy_from_buffer(handle, &mut result).unwrap();

            assert_eq!(result, data);

            manager.free_buffer(handle).unwrap();
        }
    }

    #[test]
    fn test_pool_allocation_and_free() {
        if let Some(device) = try_get_device() {
            let mut manager = CudaMemoryManager::new(device);

            let handle = manager.allocate_pool(4096).unwrap();
            assert_eq!(manager.pool_size(handle).unwrap(), 4096);

            manager.free_pool(handle).unwrap();
            assert!(manager.pool_size(handle).is_err());
        }
    }

    #[test]
    fn test_pool_copy_with_offset() {
        if let Some(device) = try_get_device() {
            let mut manager = CudaMemoryManager::new(device);

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
    }

    #[test]
    fn test_buffer_size_validation() {
        if let Some(device) = try_get_device() {
            let mut manager = CudaMemoryManager::new(device);

            let handle = manager.allocate_buffer(16).unwrap();

            // Try to write more than buffer can hold
            let too_much_data = vec![0u8; 32];
            assert!(manager.copy_to_buffer(handle, &too_much_data).is_err());

            manager.free_buffer(handle).unwrap();
        }
    }
}
