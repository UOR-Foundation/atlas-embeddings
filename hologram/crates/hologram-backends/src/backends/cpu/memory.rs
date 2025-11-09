//! Memory manager for CPU backend
//!
//! Manages buffers, pools, and shared memory for the CPU backend.
//! Implements the MemoryStorage trait from the common backend infrastructure.
//!
//! # Cache-Aware Architecture
//!
//! The memory manager implements a tiered caching strategy:
//!
//! ```text
//! L1 Cache (32 KB)  - HotClassPool (8 hot classes)
//!     ↓ miss
//! L2/L3 Cache (1.125 MB) - BoundaryPool (96 classes)
//!     ↓ miss
//! DRAM - Heap buffers (arbitrary size)
//! ```
//!
//! Access pattern:
//! 1. Check hot class pool (L1 resident)
//! 2. If miss, check boundary pool (L2/L3 resident)
//! 3. If miss, fallback to heap buffers (DRAM)

use crate::backend::{BufferHandle, PoolHandle};
use crate::backends::common::memory::MemoryStorage;
use crate::backends::cpu::boundary_pool::{BoundaryPool, HotClassPool, CLASS_COUNT};
use crate::error::{BackendError, Result};
use crate::pool::LinearPool;
use std::collections::HashMap;

/// Access threshold for hot class promotion (from streaming experiments)
#[allow(dead_code)]
const HOT_CLASS_PROMOTION_THRESHOLD: u64 = 100;

/// Memory manager for CPU backend with cache-aware boundary pools
///
/// # Tiered Memory Architecture
///
/// 1. **HotClassPool (L1 Cache, 32 KB)**:
///    - 8 hot classes × 4 KB
///    - Memory-locked, prefetched to L1
///    - LRU eviction on overflow
///
/// 2. **BoundaryPool (L2/L3 Cache, 1.125 MB)**:
///    - 96 classes × 12,288 bytes
///    - Memory-locked, cache-line aligned
///    - Serves as backing store for hot pool
///
/// 3. **Heap Buffers (DRAM)**:
///    - HashMap-based storage for arbitrary sizes
///    - Fallback for non-boundary pool allocations
///
/// # Access Tracking
///
/// - Tracks access count per class (0-95)
/// - Promotes to hot pool when count reaches threshold (100)
/// - Batched promotion check (every 128 accesses)
pub struct MemoryManager {
    /// Hot class pool (L1 cache, 32 KB, 8 classes)
    hot_pool: Option<HotClassPool>,

    /// Boundary pool (L2/L3 cache, 1.125 MB, 96 classes)
    boundary_pool: Option<BoundaryPool>,

    /// Access counts per class (for hot promotion)
    #[allow(dead_code)]
    class_access_counts: [u64; CLASS_COUNT],

    /// Total accesses (for batched promotion check)
    #[allow(dead_code)]
    total_accesses: u64,

    /// Buffers storage (heap-allocated, DRAM)
    buffers: HashMap<u64, Vec<u8>>,

    /// Pools storage (linear pools)
    pools: HashMap<u64, LinearPool>,

    /// Next buffer handle ID
    next_buffer_id: u64,

    /// Next pool handle ID
    next_pool_id: u64,
}

impl MemoryManager {
    /// Create a new memory manager with lazy-initialized boundary pools
    ///
    /// Pools are created on first PhiCoordinate access to avoid initialization
    /// overhead when they're not needed (e.g., when operations use BufferOffset addressing).
    ///
    /// This design ensures zero overhead for non-PhiCoordinate workloads while
    /// enabling cache-resident performance for class-based addressing.
    pub fn new() -> Self {
        Self {
            hot_pool: None,
            boundary_pool: None,
            class_access_counts: [0; CLASS_COUNT],
            total_accesses: 0,
            buffers: HashMap::new(),
            pools: HashMap::new(),
            next_buffer_id: 1,
            next_pool_id: 1,
        }
    }

    /// Initialize boundary pools (lazy initialization on first PhiCoordinate access)
    ///
    /// Attempts to create:
    /// 1. BoundaryPool (1.125 MB, memory-locked)
    /// 2. HotClassPool (32 KB, memory-locked)
    ///
    /// If pool creation fails (insufficient privileges/memory), logs warning
    /// and returns false. Caller should fall back to error or alternate path.
    fn ensure_boundary_pools_initialized(&mut self) -> bool {
        // Already initialized?
        if self.boundary_pool.is_some() {
            return true;
        }

        // Attempt to create cache-resident pools
        let boundary_pool = match BoundaryPool::new() {
            Ok(pool) => {
                eprintln!(
                    "✓ BoundaryPool initialized: {} bytes, locked: {}",
                    pool.size(),
                    pool.is_locked()
                );
                Some(pool)
            }
            Err(e) => {
                eprintln!(
                    "Warning: Failed to create BoundaryPool: {}. \
                     PhiCoordinate addressing will not be available.",
                    e
                );
                return false;
            }
        };

        let hot_pool = match HotClassPool::new() {
            Ok(pool) => {
                eprintln!("✓ HotClassPool initialized: locked: {}", pool.is_locked());
                Some(pool)
            }
            Err(e) => {
                eprintln!(
                    "Warning: Failed to create HotClassPool: {}. \
                     Falling back to boundary pool only.",
                    e
                );
                None
            }
        };

        self.boundary_pool = boundary_pool;
        self.hot_pool = hot_pool;
        true
    }

    /// Record class access and check for hot promotion
    ///
    /// # Strategy
    ///
    /// - Increment access count for class
    /// - Every 128 accesses, check for promotion candidates
    /// - Promote classes with count ≥ 100 to hot pool
    #[allow(dead_code)]
    fn record_class_access(&mut self, class: u8) {
        if class >= CLASS_COUNT as u8 {
            return;
        }

        self.class_access_counts[class as usize] += 1;
        self.total_accesses += 1;

        // Batched promotion check (every 128 accesses)
        if self.total_accesses.is_multiple_of(128) {
            self.check_hot_promotion();
        }
    }

    /// Check for hot class promotion candidates
    #[allow(dead_code)]
    fn check_hot_promotion(&mut self) {
        // Need both pools for promotion
        let (Some(ref mut hot_pool), Some(boundary_pool)) = (self.hot_pool.as_mut(), self.boundary_pool.as_ref())
        else {
            return;
        };

        // Find classes exceeding promotion threshold
        for (class, &count) in self.class_access_counts.iter().enumerate() {
            if count >= HOT_CLASS_PROMOTION_THRESHOLD && !hot_pool.contains(class as u8) {
                // Promote to hot pool (may evict LRU)
                if let Err(e) = hot_pool.promote(class as u8, boundary_pool) {
                    eprintln!("Warning: Failed to promote class {} to hot pool: {}", class, e);
                }
            }
        }
    }

    /// Load from boundary class (tiered: hot pool → boundary pool)
    ///
    /// # Tiered Access Strategy
    ///
    /// 1. Lazy-initialize pools on first access
    /// 2. Check hot pool (L1 cache)
    /// 3. If miss, check boundary pool (L2/L3 cache)
    /// 4. Record access for promotion tracking
    #[allow(dead_code)]
    pub fn load_boundary_class(&mut self, class: u8, offset: usize, dest: &mut [u8]) -> Result<()> {
        // Lazy initialization on first PhiCoordinate access
        if !self.ensure_boundary_pools_initialized() {
            return Err(BackendError::ExecutionError(
                "Boundary pools could not be initialized".to_string(),
            ));
        }

        // Record access for hot promotion
        self.record_class_access(class);

        // Tier 1: Try hot pool (L1 cache)
        if let Some(ref mut hot_pool) = self.hot_pool {
            if hot_pool.contains(class) {
                hot_pool.record_access(class);
                return hot_pool.load(class, offset, dest);
            }
        }

        // Tier 2: Try boundary pool (L2/L3 cache)
        if let Some(ref boundary_pool) = self.boundary_pool {
            return boundary_pool.load(class, offset, dest);
        }

        // This should never happen (pools were just initialized)
        Err(BackendError::ExecutionError(
            "Boundary pools not available after initialization".to_string(),
        ))
    }

    /// Store to boundary class (boundary pool only, hot pool is read-only cache)
    pub fn store_boundary_class(&mut self, class: u8, offset: usize, src: &[u8]) -> Result<()> {
        // Lazy initialization on first PhiCoordinate access
        if !self.ensure_boundary_pools_initialized() {
            return Err(BackendError::ExecutionError(
                "Boundary pools could not be initialized".to_string(),
            ));
        }

        // Store to boundary pool (source of truth)
        if let Some(ref mut boundary_pool) = self.boundary_pool {
            boundary_pool.store(class, offset, src)?;

            // Invalidate hot pool entry if present (write-through would require more logic)
            // For now, hot pool is read-only cache - writes go to boundary pool
            // Hot pool will be refreshed on next promotion

            Ok(())
        } else {
            // This should never happen (pools were just initialized)
            Err(BackendError::ExecutionError(
                "Boundary pool not available after initialization".to_string(),
            ))
        }
    }

    // ============================================================================================
    // Buffer Management
    // ============================================================================================

    /// Allocate a buffer
    pub fn allocate_buffer(&mut self, size: usize) -> Result<BufferHandle> {
        let id = self.next_buffer_id;
        self.next_buffer_id += 1;

        self.buffers.insert(id, vec![0u8; size]);

        Ok(BufferHandle::new(id))
    }

    /// Free a buffer
    pub fn free_buffer(&mut self, handle: BufferHandle) -> Result<()> {
        if self.buffers.remove(&handle.id()).is_none() {
            return Err(BackendError::InvalidBufferHandle(handle.id()));
        }
        Ok(())
    }

    /// Copy data to buffer
    ///
    /// # Special Handling for Boundary Pool
    ///
    /// BufferHandle IDs in range [u64::MAX - 95, u64::MAX] are reserved for boundary pool class indices.
    /// This method writes to the specific class (12,288 bytes).
    pub fn copy_to_buffer(&mut self, handle: BufferHandle, data: &[u8]) -> Result<()> {
        // Special handling for boundary pool classes
        const BOUNDARY_POOL_HANDLE_BASE: u64 = u64::MAX - 95;
        if handle.id() >= BOUNDARY_POOL_HANDLE_BASE {
            use crate::backends::cpu::boundary_pool::BYTES_PER_CLASS;

            let class = (handle.id() - BOUNDARY_POOL_HANDLE_BASE) as u8;
            if data.len() != BYTES_PER_CLASS {
                return Err(BackendError::BufferOutOfBounds {
                    offset: 0,
                    size: data.len(),
                    buffer_size: BYTES_PER_CLASS,
                });
            }

            // Ensure boundary pools are initialized
            if !self.ensure_boundary_pools_initialized() {
                return Err(BackendError::ExecutionError(format!(
                    "Boundary pools could not be initialized for class {}",
                    class
                )));
            }

            // Write to specific class in boundary pool
            self.store_boundary_class(class, 0, data)?;
            return Ok(());
        }

        let buffer = self
            .buffers
            .get_mut(&handle.id())
            .ok_or_else(|| BackendError::InvalidBufferHandle(handle.id()))?;

        if data.len() > buffer.len() {
            return Err(BackendError::BufferOutOfBounds {
                offset: 0,
                size: data.len(),
                buffer_size: buffer.len(),
            });
        }

        buffer[..data.len()].copy_from_slice(data);
        Ok(())
    }

    /// Copy data from buffer
    ///
    /// # Special Handling for Boundary Pool
    ///
    /// BufferHandle IDs in range [u64::MAX - 95, u64::MAX] are reserved for boundary pool class indices.
    /// This method reads from the specific class (12,288 bytes).
    ///
    /// **Boundary Pool Initialization**: The boundary pools must be pre-initialized before
    /// calling this method. This happens automatically on the first boundary pool access.
    pub fn copy_from_buffer(&self, handle: BufferHandle, data: &mut [u8]) -> Result<()> {
        // Special handling for boundary pool classes
        const BOUNDARY_POOL_HANDLE_BASE: u64 = u64::MAX - 95;
        if handle.id() >= BOUNDARY_POOL_HANDLE_BASE {
            use crate::backends::cpu::boundary_pool::BYTES_PER_CLASS;

            let class = (handle.id() - BOUNDARY_POOL_HANDLE_BASE) as u8;
            if data.len() != BYTES_PER_CLASS {
                return Err(BackendError::BufferOutOfBounds {
                    offset: 0,
                    size: data.len(),
                    buffer_size: BYTES_PER_CLASS,
                });
            }

            // Check that boundary pools are initialized
            if self.boundary_pool.is_none() {
                // Pools not yet initialized - return zeros (will be initialized on first write)
                data.fill(0);
                return Ok(());
            }

            // Read specific class from boundary pool
            let boundary_pool = self.boundary_pool.as_ref().unwrap();
            boundary_pool.load(class, 0, data)?;

            return Ok(());
        }

        let buffer = self
            .buffers
            .get(&handle.id())
            .ok_or_else(|| BackendError::InvalidBufferHandle(handle.id()))?;

        if data.len() > buffer.len() {
            return Err(BackendError::BufferOutOfBounds {
                offset: 0,
                size: data.len(),
                buffer_size: buffer.len(),
            });
        }

        data.copy_from_slice(&buffer[..data.len()]);
        Ok(())
    }

    /// Get buffer size
    ///
    /// # Special Handling for Boundary Pool
    ///
    /// - BufferHandle(0): Entire boundary pool (96 classes × 12,288 bytes = 1,179,648 bytes)
    /// - BufferHandle(BOUNDARY_POOL_HANDLE_BASE + class): Single class (12,288 bytes)
    pub fn buffer_size(&self, handle: BufferHandle) -> Result<usize> {
        // Special handling for boundary pool
        use crate::backends::cpu::boundary_pool::{BYTES_PER_CLASS, CLASS_COUNT};

        if handle.id() == 0 {
            // BufferHandle(0): entire boundary pool for PhiCoordinate addressing
            return Ok(CLASS_COUNT * BYTES_PER_CLASS);
        }

        const BOUNDARY_POOL_HANDLE_BASE: u64 = u64::MAX - 95;
        if handle.id() >= BOUNDARY_POOL_HANDLE_BASE {
            // Class-specific handle: single class
            return Ok(BYTES_PER_CLASS);
        }

        self.buffers
            .get(&handle.id())
            .map(|b| b.len())
            .ok_or_else(|| BackendError::InvalidBufferHandle(handle.id()))
    }

    /// Get raw const pointer to buffer memory
    ///
    /// # Safety
    ///
    /// The returned pointer is valid as long as:
    /// - The buffer handle is valid
    /// - No mutable operations occur on the buffer
    /// - The MemoryManager is not dropped
    ///
    /// This is intended for inline SIMD kernel fast paths.
    pub fn buffer_as_ptr(&self, handle: BufferHandle) -> Result<*const u8> {
        let buffer = self
            .buffers
            .get(&handle.id())
            .ok_or_else(|| BackendError::InvalidBufferHandle(handle.id()))?;

        Ok(buffer.as_ptr())
    }

    /// Get raw mutable pointer to buffer memory
    ///
    /// # Safety
    ///
    /// The returned pointer is valid as long as:
    /// - The buffer handle is valid
    /// - No concurrent access occurs
    /// - The MemoryManager is not dropped
    ///
    /// This is intended for inline SIMD kernel fast paths.
    pub fn buffer_as_mut_ptr(&mut self, handle: BufferHandle) -> Result<*mut u8> {
        let buffer = self
            .buffers
            .get_mut(&handle.id())
            .ok_or_else(|| BackendError::InvalidBufferHandle(handle.id()))?;

        Ok(buffer.as_mut_ptr())
    }

    /// Get raw const pointer to boundary pool class data
    ///
    /// # Arguments
    ///
    /// * `class` - Class index (0-95)
    ///
    /// # Returns
    ///
    /// Const pointer to the start of the class data (12,288 bytes)
    pub fn boundary_class_ptr(&self, class: u8) -> Result<*const u8> {
        self.boundary_pool
            .as_ref()
            .ok_or_else(|| BackendError::ExecutionError("Boundary pool not initialized".to_string()))?
            .class_ptr(class)
    }

    /// Get raw mutable pointer to boundary pool class data
    ///
    /// # Arguments
    ///
    /// * `class` - Class index (0-95)
    ///
    /// # Returns
    ///
    /// Mutable pointer to the start of the class data (12,288 bytes)
    pub fn boundary_class_ptr_mut(&mut self, class: u8) -> Result<*mut u8> {
        self.boundary_pool
            .as_mut()
            .ok_or_else(|| BackendError::ExecutionError("Boundary pool not initialized".to_string()))?
            .class_ptr_mut(class)
    }

    // ============================================================================================
    // Pool Management
    // ============================================================================================

    /// Allocate a pool
    pub fn allocate_pool(&mut self, size: usize) -> Result<PoolHandle> {
        let id = self.next_pool_id;
        self.next_pool_id += 1;

        self.pools.insert(id, LinearPool::new(size));

        Ok(PoolHandle::new(id))
    }

    /// Free a pool
    pub fn free_pool(&mut self, handle: PoolHandle) -> Result<()> {
        if self.pools.remove(&handle.id()).is_none() {
            return Err(BackendError::InvalidPoolHandle(handle.id()));
        }
        Ok(())
    }

    /// Copy data to pool
    ///
    /// # Special Handling for PoolHandle(0)
    ///
    /// PoolHandle(0) is reserved for the boundary pool (PhiCoordinate space).
    /// This method lazily initializes the boundary pool on first access.
    pub fn copy_to_pool(&mut self, handle: PoolHandle, offset: usize, data: &[u8]) -> Result<()> {
        // Special handling for boundary pool (PoolHandle(0) = PhiCoordinate space)
        if handle.id() == 0 {
            // Ensure boundary pools are initialized
            if !self.ensure_boundary_pools_initialized() {
                return Err(BackendError::ExecutionError(
                    "Boundary pools could not be initialized for PoolHandle(0) access".to_string(),
                ));
            }

            // Calculate which class the offset falls into
            use crate::backends::cpu::boundary_pool::BYTES_PER_CLASS;
            let class = (offset / BYTES_PER_CLASS) as u8;
            let offset_in_class = offset % BYTES_PER_CLASS;

            // Store to boundary pool
            if let Some(ref mut boundary_pool) = self.boundary_pool {
                return boundary_pool.store(class, offset_in_class, data);
            }

            return Err(BackendError::ExecutionError(
                "Boundary pool not initialized".to_string(),
            ));
        }

        let pool = self
            .pools
            .get_mut(&handle.id())
            .ok_or_else(|| BackendError::InvalidPoolHandle(handle.id()))?;

        pool.store_bytes(offset, data)
    }

    /// Copy data from pool
    ///
    /// # Special Handling for PoolHandle(0)
    ///
    /// PoolHandle(0) is reserved for the boundary pool (PhiCoordinate space).
    /// If the boundary pool is not initialized, returns zeros.
    pub fn copy_from_pool(&self, handle: PoolHandle, offset: usize, data: &mut [u8]) -> Result<()> {
        // Special handling for boundary pool (PoolHandle(0) = PhiCoordinate space)
        if handle.id() == 0 {
            // If boundary pool not initialized, return zeros
            if self.boundary_pool.is_none() {
                data.fill(0);
                return Ok(());
            }

            // Calculate which class the offset falls into
            use crate::backends::cpu::boundary_pool::BYTES_PER_CLASS;
            let class = (offset / BYTES_PER_CLASS) as u8;
            let offset_in_class = offset % BYTES_PER_CLASS;

            // Load from boundary pool
            if let Some(ref boundary_pool) = self.boundary_pool {
                return boundary_pool.load(class, offset_in_class, data);
            }

            // Fallback to zeros if something goes wrong
            data.fill(0);
            return Ok(());
        }

        let pool = self
            .pools
            .get(&handle.id())
            .ok_or_else(|| BackendError::InvalidPoolHandle(handle.id()))?;

        pool.load_bytes(offset, data)
    }

    /// Get pool size
    ///
    /// # Special Handling for PoolHandle(0)
    ///
    /// PoolHandle(0) is reserved for the boundary pool (PhiCoordinate space).
    /// Returns the total boundary pool size: 96 classes × 12,288 bytes = 1,179,648 bytes.
    pub fn pool_size(&self, handle: PoolHandle) -> Result<usize> {
        // Special handling for boundary pool (PoolHandle(0) = PhiCoordinate space)
        if handle.id() == 0 {
            use crate::backends::cpu::boundary_pool::{BYTES_PER_CLASS, CLASS_COUNT};
            return Ok(CLASS_COUNT * BYTES_PER_CLASS);
        }

        self.pools
            .get(&handle.id())
            .map(|p| p.capacity())
            .ok_or_else(|| BackendError::InvalidPoolHandle(handle.id()))
    }
}

impl Default for MemoryManager {
    fn default() -> Self {
        Self::new()
    }
}

// Implement MemoryStorage trait to integrate with common backend infrastructure
impl MemoryStorage for MemoryManager {
    fn allocate_buffer(&mut self, size: usize) -> Result<BufferHandle> {
        MemoryManager::allocate_buffer(self, size)
    }

    fn free_buffer(&mut self, handle: BufferHandle) -> Result<()> {
        MemoryManager::free_buffer(self, handle)
    }

    fn copy_to_buffer(&mut self, handle: BufferHandle, data: &[u8]) -> Result<()> {
        MemoryManager::copy_to_buffer(self, handle, data)
    }

    fn copy_from_buffer(&self, handle: BufferHandle, data: &mut [u8]) -> Result<()> {
        MemoryManager::copy_from_buffer(self, handle, data)
    }

    fn buffer_size(&self, handle: BufferHandle) -> Result<usize> {
        MemoryManager::buffer_size(self, handle)
    }

    fn allocate_pool(&mut self, size: usize) -> Result<PoolHandle> {
        MemoryManager::allocate_pool(self, size)
    }

    fn free_pool(&mut self, handle: PoolHandle) -> Result<()> {
        MemoryManager::free_pool(self, handle)
    }

    fn copy_to_pool(&mut self, handle: PoolHandle, offset: usize, data: &[u8]) -> Result<()> {
        MemoryManager::copy_to_pool(self, handle, offset, data)
    }

    fn copy_from_pool(&self, handle: PoolHandle, offset: usize, data: &mut [u8]) -> Result<()> {
        MemoryManager::copy_from_pool(self, handle, offset, data)
    }

    fn pool_size(&self, handle: PoolHandle) -> Result<usize> {
        MemoryManager::pool_size(self, handle)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_manager_buffer_allocation() {
        let mut manager = MemoryManager::new();

        let buffer = manager.allocate_buffer(1024).unwrap();
        assert_eq!(manager.buffer_size(buffer).unwrap(), 1024);

        manager.free_buffer(buffer).unwrap();

        // Should fail after free
        assert!(manager.buffer_size(buffer).is_err());
    }

    #[test]
    fn test_memory_manager_pool_allocation() {
        let mut manager = MemoryManager::new();

        let pool = manager.allocate_pool(4096).unwrap();
        assert_eq!(manager.pool_size(pool).unwrap(), 4096);

        manager.free_pool(pool).unwrap();

        // Should fail after free
        assert!(manager.pool_size(pool).is_err());
    }

    #[test]
    fn test_memory_manager_buffer_copy() {
        let mut manager = MemoryManager::new();

        let buffer = manager.allocate_buffer(16).unwrap();

        let data = b"Hello, World!";
        manager.copy_to_buffer(buffer, data).unwrap();

        let mut result = vec![0u8; data.len()];
        manager.copy_from_buffer(buffer, &mut result).unwrap();

        assert_eq!(result.as_slice(), data);

        manager.free_buffer(buffer).unwrap();
    }

    #[test]
    fn test_memory_manager_pool_copy() {
        let mut manager = MemoryManager::new();

        let pool = manager.allocate_pool(1024).unwrap();

        let data = [1.0f32, 2.0, 3.0, 4.0];
        let bytes = bytemuck::cast_slice(&data);
        manager.copy_to_pool(pool, 0, bytes).unwrap();

        let mut result = [0.0f32; 4];
        let result_bytes = bytemuck::cast_slice_mut(&mut result);
        manager.copy_from_pool(pool, 0, result_bytes).unwrap();

        assert_eq!(result, data);

        manager.free_pool(pool).unwrap();
    }
}
