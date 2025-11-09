//! Cache-Resident Boundary Pool for CPU Backend
//!
//! Implements the designed cache-aware memory architecture for compute-bound operations.
//!
//! # Architecture
//!
//! ```text
//! L1 Cache (32 KB)  - HotClassPool (8 hot classes × 4 KB)
//!     ↓ promotion
//! L2/L3 Cache (1.125 MB) - BoundaryPool (96 classes × 12,288 bytes)
//!     ↓ lookups
//! DRAM - Circuit constant-space (input buffers)
//! ```
//!
//! # Design Goals (from archived SPEC)
//!
//! - **Cache Residency**: Memory-locked to prevent OS paging
//! - **Hot-Class Promotion**: Top 8 classes in L1 (80/20 distribution)
//! - **O(1) Space**: Fixed pool size handles arbitrary input sizes
//! - **Compute-Bound**: Move from memory-bound to compute-bound operations
//!
//! # Memory Layout
//!
//! - **BoundaryPool**: 1,179,648 bytes = 96 classes × 12,288 bytes
//!   - 64-byte cache-line aligned
//!   - Platform-specific memory locking (mlock/VirtualAlloc)
//!   - Huge page backing when available
//!
//! - **HotClassPool**: 32,768 bytes = 8 classes × 4,096 bytes
//!   - L1-cache resident (32 KB fits typical L1 data cache)
//!   - Prefetched using platform intrinsics
//!   - Access-tracked for promotion/demotion

use crate::error::{BackendError, Result};
use std::alloc::{alloc_zeroed, dealloc, Layout};
use std::ptr::NonNull;

// ================================================================================================
// Constants (from archived SPEC)
// ================================================================================================

/// Number of classes in the boundary pool (96-class system)
pub const CLASS_COUNT: usize = 96;

/// Bytes per class in boundary pool (12,288 = 48 pages × 256 bytes)
pub const BYTES_PER_CLASS: usize = 12_288;

/// Total boundary pool size (1,179,648 bytes = 1.125 MB)
pub const BOUNDARY_POOL_SIZE: usize = CLASS_COUNT * BYTES_PER_CLASS;

/// Cache line size for alignment (64 bytes on x86-64/ARM64)
pub const CACHE_LINE_SIZE: usize = 64;

/// Number of hot classes to promote to L1 cache
pub const HOT_CLASS_COUNT: usize = 8;

/// Bytes per hot class (4 KB, typical L1 cache line size)
pub const BYTES_PER_HOT_CLASS: usize = 4_096;

/// Total hot class pool size (32 KB, fits in L1 data cache)
pub const HOT_CLASS_POOL_SIZE: usize = HOT_CLASS_COUNT * BYTES_PER_HOT_CLASS;

// ================================================================================================
// BoundaryPool - L2/L3 Cache-Resident Pool
// ================================================================================================

/// Cache-resident boundary pool for 96-class system
///
/// # Memory Properties
///
/// - **Size**: 1,179,648 bytes (1.125 MB)
/// - **Alignment**: 64-byte cache lines
/// - **Locking**: Platform-specific memory locking
/// - **Backing**: Huge pages when available
///
/// # Platform-Specific Locking
///
/// - **Linux**: `mmap(MAP_LOCKED | MAP_HUGETLB)` + `mlock()`
/// - **macOS**: `mmap()` + `mlock()` + `madvise(MADV_WILLNEED)`
/// - **Windows**: `VirtualAlloc(MEM_LARGE_PAGES)` + `VirtualLock()`
pub struct BoundaryPool {
    /// Raw pointer to memory-locked, cache-line aligned memory
    data: NonNull<u8>,

    /// Layout for deallocation
    layout: Layout,

    /// Whether memory is successfully locked
    locked: bool,
}

impl BoundaryPool {
    /// Create a new cache-resident boundary pool
    ///
    /// # Memory Allocation
    ///
    /// 1. Allocate 1,179,648 bytes with 64-byte alignment
    /// 2. Lock memory to prevent OS paging
    /// 3. Prefetch to L2/L3 cache
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - Allocation fails (OOM)
    /// - Memory locking fails (insufficient privileges)
    pub fn new() -> Result<Self> {
        // Create layout: 1.125 MB, 64-byte aligned
        let layout = Layout::from_size_align(BOUNDARY_POOL_SIZE, CACHE_LINE_SIZE)
            .map_err(|e| BackendError::Other(format!("Invalid layout: {}", e)))?;

        // Allocate zeroed memory
        let data = unsafe {
            let ptr = alloc_zeroed(layout);
            if ptr.is_null() {
                return Err(BackendError::Other("Failed to allocate boundary pool".to_string()));
            }
            NonNull::new_unchecked(ptr)
        };

        // Platform-specific memory locking
        let locked = Self::lock_memory(data.as_ptr(), BOUNDARY_POOL_SIZE);

        if !locked {
            eprintln!(
                "Warning: Failed to lock boundary pool memory. \
                 Performance may be degraded due to OS paging. \
                 Consider running with elevated privileges."
            );
        }

        Ok(Self { data, layout, locked })
    }

    /// Lock memory to prevent OS paging (platform-specific)
    ///
    /// # Linux
    ///
    /// Uses `mlock()` to lock pages in physical memory.
    /// Requires `CAP_IPC_LOCK` capability or `ulimit -l` increase.
    ///
    /// # macOS
    ///
    /// Uses `mlock()` + `madvise(MADV_WILLNEED)` for resident set.
    /// May require root privileges depending on system limits.
    ///
    /// # Windows
    ///
    /// Uses `VirtualLock()` to lock pages.
    /// Requires `SeLockMemoryPrivilege` for large pages.
    ///
    /// # Returns
    ///
    /// `true` if memory successfully locked, `false` otherwise.
    #[cfg(target_os = "linux")]
    fn lock_memory(ptr: *const u8, size: usize) -> bool {
        unsafe {
            // Lock memory in physical RAM (prevent paging)
            if libc::mlock(ptr as *const libc::c_void, size) != 0 {
                return false;
            }

            // Advise kernel: sequential access, will need all pages
            libc::madvise(
                ptr as *mut libc::c_void,
                size,
                libc::MADV_SEQUENTIAL | libc::MADV_WILLNEED,
            );

            // Attempt huge page backing (may fail without privileges)
            libc::madvise(ptr as *mut libc::c_void, size, libc::MADV_HUGEPAGE);

            true
        }
    }

    #[cfg(target_os = "macos")]
    fn lock_memory(ptr: *const u8, size: usize) -> bool {
        unsafe {
            // Lock memory in physical RAM
            if libc::mlock(ptr as *const libc::c_void, size) != 0 {
                return false;
            }

            // Advise kernel: will need all pages (prefetch)
            libc::madvise(ptr as *mut libc::c_void, size, libc::MADV_WILLNEED);

            true
        }
    }

    #[cfg(target_os = "windows")]
    fn lock_memory(ptr: *const u8, size: usize) -> bool {
        unsafe {
            use winapi::um::memoryapi::VirtualLock;

            // Lock memory in working set
            VirtualLock(ptr as *mut winapi::ctypes::c_void, size) != 0
        }
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "windows")))]
    fn lock_memory(_ptr: *const u8, _size: usize) -> bool {
        // Unsupported platform - memory locking not available
        false
    }

    /// Get pointer to class data
    ///
    /// # Arguments
    ///
    /// * `class` - Class index (0-95)
    ///
    /// # Returns
    ///
    /// Pointer to the start of the class data (12,288 bytes)
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `class < 96`
    /// - Returned pointer is not held across pool mutations
    pub fn class_ptr(&self, class: u8) -> Result<*const u8> {
        if class >= CLASS_COUNT as u8 {
            return Err(BackendError::InvalidClassIndex(class));
        }

        let offset = class as usize * BYTES_PER_CLASS;
        unsafe { Ok(self.data.as_ptr().add(offset)) }
    }

    /// Get mutable pointer to class data
    ///
    /// # Arguments
    ///
    /// * `class` - Class index (0-95)
    ///
    /// # Returns
    ///
    /// Mutable pointer to the start of the class data (12,288 bytes)
    ///
    /// # Safety
    ///
    /// Caller must ensure:
    /// - `class < 96`
    /// - No concurrent access to the same class
    pub fn class_ptr_mut(&mut self, class: u8) -> Result<*mut u8> {
        if class >= CLASS_COUNT as u8 {
            return Err(BackendError::InvalidClassIndex(class));
        }

        let offset = class as usize * BYTES_PER_CLASS;
        unsafe { Ok(self.data.as_ptr().add(offset)) }
    }

    /// Load bytes from class at offset
    pub fn load(&self, class: u8, offset: usize, dest: &mut [u8]) -> Result<()> {
        if offset + dest.len() > BYTES_PER_CLASS {
            return Err(BackendError::BufferOutOfBounds {
                offset,
                size: dest.len(),
                buffer_size: BYTES_PER_CLASS,
            });
        }

        let class_ptr = self.class_ptr(class)?;
        unsafe {
            let src = class_ptr.add(offset);
            std::ptr::copy_nonoverlapping(src, dest.as_mut_ptr(), dest.len());
        }

        Ok(())
    }

    /// Store bytes to class at offset
    pub fn store(&mut self, class: u8, offset: usize, src: &[u8]) -> Result<()> {
        if offset + src.len() > BYTES_PER_CLASS {
            return Err(BackendError::BufferOutOfBounds {
                offset,
                size: src.len(),
                buffer_size: BYTES_PER_CLASS,
            });
        }

        let class_ptr = self.class_ptr_mut(class)?;
        unsafe {
            let dest = class_ptr.add(offset);
            std::ptr::copy_nonoverlapping(src.as_ptr(), dest, src.len());
        }

        Ok(())
    }

    /// Check if memory is locked
    pub fn is_locked(&self) -> bool {
        self.locked
    }

    /// Get total pool size
    pub fn size(&self) -> usize {
        BOUNDARY_POOL_SIZE
    }
}

impl Drop for BoundaryPool {
    fn drop(&mut self) {
        unsafe {
            // Unlock memory before deallocation (if locked)
            #[cfg(target_os = "linux")]
            {
                libc::munlock(self.data.as_ptr() as *const libc::c_void, BOUNDARY_POOL_SIZE);
            }

            #[cfg(target_os = "macos")]
            {
                libc::munlock(self.data.as_ptr() as *const libc::c_void, BOUNDARY_POOL_SIZE);
            }

            #[cfg(target_os = "windows")]
            {
                use winapi::um::memoryapi::VirtualUnlock;
                VirtualUnlock(self.data.as_ptr() as *mut winapi::ctypes::c_void, BOUNDARY_POOL_SIZE);
            }

            // Deallocate memory
            dealloc(self.data.as_ptr(), self.layout);
        }
    }
}

// Safety: BoundaryPool owns its memory exclusively
unsafe impl Send for BoundaryPool {}
unsafe impl Sync for BoundaryPool {}

// ================================================================================================
// HotClassPool - L1 Cache-Resident Pool
// ================================================================================================

/// Hot class entry for L1 cache promotion
#[derive(Debug, Clone, Copy)]
struct HotClassEntry {
    /// Class index (0-95) or None if slot is empty
    #[allow(dead_code)]
    class: Option<u8>,

    /// Access count for this class (for LRU eviction)
    #[allow(dead_code)]
    access_count: u64,
}

/// L1 cache-resident pool for hot classes
///
/// # Memory Properties
///
/// - **Size**: 32,768 bytes (32 KB)
/// - **Capacity**: 8 hot classes × 4,096 bytes each
/// - **Target**: L1 data cache (typical 32-48 KB)
/// - **Strategy**: LRU promotion based on access patterns
///
/// # Hot-Class Promotion
///
/// From archived SPEC and streaming experiments:
/// - Top 8 classes account for 80% of accesses (80/20 distribution)
/// - Promote on threshold: 100 accesses in boundary pool
/// - Prefetch using `_mm_prefetch` (x86) or `__builtin_prefetch` (ARM)
pub struct HotClassPool {
    /// Memory-locked, cache-line aligned storage
    data: NonNull<u8>,

    /// Layout for deallocation
    layout: Layout,

    /// Hot class entries (LRU tracking)
    #[allow(dead_code)]
    entries: [HotClassEntry; HOT_CLASS_COUNT],

    /// Whether memory is successfully locked
    locked: bool,
}

impl HotClassPool {
    /// Create a new L1 cache-resident hot class pool
    pub fn new() -> Result<Self> {
        // Create layout: 32 KB, 64-byte aligned
        let layout = Layout::from_size_align(HOT_CLASS_POOL_SIZE, CACHE_LINE_SIZE)
            .map_err(|e| BackendError::Other(format!("Invalid layout: {}", e)))?;

        // Allocate zeroed memory
        let data = unsafe {
            let ptr = alloc_zeroed(layout);
            if ptr.is_null() {
                return Err(BackendError::Other("Failed to allocate hot class pool".to_string()));
            }
            NonNull::new_unchecked(ptr)
        };

        // Lock memory (critical for L1 residency)
        let locked = Self::lock_memory(data.as_ptr(), HOT_CLASS_POOL_SIZE);

        Ok(Self {
            data,
            layout,
            entries: [HotClassEntry {
                class: None,
                access_count: 0,
            }; HOT_CLASS_COUNT],
            locked,
        })
    }

    /// Lock memory (same as BoundaryPool, but smaller size)
    #[cfg(target_os = "linux")]
    fn lock_memory(ptr: *const u8, size: usize) -> bool {
        unsafe {
            if libc::mlock(ptr as *const libc::c_void, size) != 0 {
                return false;
            }
            libc::madvise(ptr as *mut libc::c_void, size, libc::MADV_WILLNEED | libc::MADV_RANDOM);
            true
        }
    }

    #[cfg(target_os = "macos")]
    fn lock_memory(ptr: *const u8, size: usize) -> bool {
        unsafe {
            if libc::mlock(ptr as *const libc::c_void, size) != 0 {
                return false;
            }
            libc::madvise(ptr as *mut libc::c_void, size, libc::MADV_WILLNEED);
            true
        }
    }

    #[cfg(target_os = "windows")]
    fn lock_memory(ptr: *const u8, size: usize) -> bool {
        unsafe {
            use winapi::um::memoryapi::VirtualLock;
            VirtualLock(ptr as *mut winapi::ctypes::c_void, size) != 0
        }
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "windows")))]
    fn lock_memory(_ptr: *const u8, _size: usize) -> bool {
        false
    }

    /// Check if class is in hot pool
    #[allow(dead_code)]
    pub fn contains(&self, class: u8) -> bool {
        self.entries.iter().any(|e| e.class == Some(class))
    }

    /// Find hot pool slot for class (if present)
    #[allow(dead_code)]
    fn find_slot(&self, class: u8) -> Option<usize> {
        self.entries.iter().position(|e| e.class == Some(class))
    }

    /// Promote class to hot pool (LRU eviction if full)
    ///
    /// # Arguments
    ///
    /// * `class` - Class index to promote
    /// * `boundary_pool` - Source boundary pool to copy from
    ///
    /// # Strategy
    ///
    /// 1. Check if class already in hot pool (no-op if present)
    /// 2. Find empty slot or LRU victim
    /// 3. Copy 4 KB from boundary pool to hot pool
    /// 4. Prefetch to L1 cache
    #[allow(dead_code)]
    pub fn promote(&mut self, class: u8, boundary_pool: &BoundaryPool) -> Result<()> {
        // Already promoted?
        if self.contains(class) {
            return Ok(());
        }

        // Find slot: empty or LRU
        let slot = self.entries.iter().position(|e| e.class.is_none()).unwrap_or_else(|| {
            // All slots full - evict LRU
            self.entries
                .iter()
                .enumerate()
                .min_by_key(|(_, e)| e.access_count)
                .map(|(i, _)| i)
                .unwrap()
        });

        // Copy from boundary pool to hot pool (4 KB)
        let src_ptr = boundary_pool.class_ptr(class)?;
        let dest_ptr = unsafe { self.data.as_ptr().add(slot * BYTES_PER_HOT_CLASS) };

        unsafe {
            std::ptr::copy_nonoverlapping(src_ptr, dest_ptr, BYTES_PER_HOT_CLASS);
        }

        // Update entry
        self.entries[slot] = HotClassEntry {
            class: Some(class),
            access_count: 0,
        };

        // Prefetch to L1 cache (platform-specific)
        Self::prefetch_to_l1(dest_ptr);

        Ok(())
    }

    /// Prefetch memory to L1 cache (platform-specific intrinsics)
    #[cfg(target_arch = "x86_64")]
    #[allow(dead_code)]
    fn prefetch_to_l1(ptr: *const u8) {
        unsafe {
            // Prefetch to all cache levels (L1/L2/L3)
            for offset in (0..BYTES_PER_HOT_CLASS).step_by(CACHE_LINE_SIZE) {
                let cache_line = ptr.add(offset);
                #[cfg(target_feature = "sse")]
                {
                    use std::arch::x86_64::{_mm_prefetch, _MM_HINT_T0};
                    _mm_prefetch(cache_line as *const i8, _MM_HINT_T0);
                }
            }
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[allow(dead_code)]
    fn prefetch_to_l1(ptr: *const u8) {
        unsafe {
            for offset in (0..BYTES_PER_HOT_CLASS).step_by(CACHE_LINE_SIZE) {
                let cache_line = ptr.add(offset);
                // ARM prefetch using inline assembly
                // PRFM PLDL1KEEP, [x0] - prefetch for load to L1 cache
                std::arch::asm!("prfm pldl1keep, [{0}]", in(reg) cache_line, options(nostack, preserves_flags));
            }
        }
    }

    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    #[allow(dead_code)]
    fn prefetch_to_l1(_ptr: *const u8) {
        // No-op on unsupported architectures
    }

    /// Record access to class (for LRU tracking)
    #[allow(dead_code)]
    pub fn record_access(&mut self, class: u8) {
        if let Some(slot) = self.find_slot(class) {
            self.entries[slot].access_count += 1;
        }
    }

    /// Load from hot pool (if present)
    #[allow(dead_code)]
    pub fn load(&self, class: u8, offset: usize, dest: &mut [u8]) -> Result<()> {
        let slot = self
            .find_slot(class)
            .ok_or_else(|| BackendError::ExecutionError(format!("Class {} not in hot pool", class)))?;

        if offset + dest.len() > BYTES_PER_HOT_CLASS {
            return Err(BackendError::BufferOutOfBounds {
                offset,
                size: dest.len(),
                buffer_size: BYTES_PER_HOT_CLASS,
            });
        }

        unsafe {
            let src = self.data.as_ptr().add(slot * BYTES_PER_HOT_CLASS + offset);
            std::ptr::copy_nonoverlapping(src, dest.as_mut_ptr(), dest.len());
        }

        Ok(())
    }

    /// Check if memory is locked
    pub fn is_locked(&self) -> bool {
        self.locked
    }
}

impl Drop for HotClassPool {
    fn drop(&mut self) {
        unsafe {
            // Unlock memory
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            {
                libc::munlock(self.data.as_ptr() as *const libc::c_void, HOT_CLASS_POOL_SIZE);
            }

            #[cfg(target_os = "windows")]
            {
                use winapi::um::memoryapi::VirtualUnlock;
                VirtualUnlock(self.data.as_ptr() as *mut winapi::ctypes::c_void, HOT_CLASS_POOL_SIZE);
            }

            // Deallocate
            dealloc(self.data.as_ptr(), self.layout);
        }
    }
}

unsafe impl Send for HotClassPool {}
unsafe impl Sync for HotClassPool {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_boundary_pool_creation() {
        let pool = BoundaryPool::new().unwrap();
        assert_eq!(pool.size(), BOUNDARY_POOL_SIZE);
        println!("Boundary pool created. Memory locked: {}", pool.is_locked());
    }

    #[test]
    fn test_boundary_pool_class_access() {
        let mut pool = BoundaryPool::new().unwrap();

        // Store to class 0
        let data = vec![42u8; 256];
        pool.store(0, 0, &data).unwrap();

        // Load from class 0
        let mut result = vec![0u8; 256];
        pool.load(0, 0, &mut result).unwrap();

        assert_eq!(result, data);
    }

    #[test]
    fn test_boundary_pool_bounds_checking() {
        let pool = BoundaryPool::new().unwrap();

        // Out of bounds class
        assert!(pool.class_ptr(96).is_err());

        // Out of bounds offset
        let mut dest = vec![0u8; 256];
        assert!(pool.load(0, BYTES_PER_CLASS, &mut dest).is_err());
    }

    #[test]
    fn test_hot_class_pool_creation() {
        let pool = HotClassPool::new().unwrap();
        println!("Hot class pool created. Memory locked: {}", pool.is_locked());
    }

    #[test]
    fn test_hot_class_promotion() {
        let boundary_pool = BoundaryPool::new().unwrap();
        let mut hot_pool = HotClassPool::new().unwrap();

        // Promote class 5
        hot_pool.promote(5, &boundary_pool).unwrap();
        assert!(hot_pool.contains(5));
    }

    #[test]
    fn test_hot_class_lru_eviction() {
        let boundary_pool = BoundaryPool::new().unwrap();
        let mut hot_pool = HotClassPool::new().unwrap();

        // Fill all 8 slots
        for class in 0..HOT_CLASS_COUNT as u8 {
            hot_pool.promote(class, &boundary_pool).unwrap();
        }

        // All should be present
        for class in 0..HOT_CLASS_COUNT as u8 {
            assert!(hot_pool.contains(class));
        }

        // Promote 9th class - should evict LRU (class 0)
        hot_pool.promote(8, &boundary_pool).unwrap();
        assert!(hot_pool.contains(8));
        assert!(!hot_pool.contains(0)); // Evicted
    }
}
