//! Linear pool storage for O(1) space streaming computation
//!
//! Based on the streaming_computation experiment, which demonstrated:
//! - 2,844× memory amplification (100 MB input / 36 KB pool)
//! - Constant throughput across all input sizes
//! - O(1) space complexity with O(n) time complexity
//!
//! # Architecture
//!
//! ```text
//! Circuit (SRAM):       "merge@c00[c01,c02]"  ← Fixed instruction
//!                              ↓ indexes
//! Memory Pool (DRAM):   {c00, c01, c02}       ← Fixed addresses
//!                              ↓ contains
//! Data (streaming):     chunk_0, ..., chunk_N ← Arbitrary size
//! ```
//!
//! The pool provides a fixed-size memory region that can be reused for
//! arbitrary input sizes by loading data in chunks.

use crate::error::{BackendError, Result};

/// Linear pool storage with fixed capacity
///
/// Provides O(1) space streaming computation by reusing a fixed memory pool
/// for arbitrary input sizes.
///
/// # Usage
///
/// ```rust
/// use hologram_backends::LinearPool;
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// // Allocate fixed pool (36 KB)
/// let mut pool = LinearPool::new(36_864);
///
/// // Stream 100 MB through fixed pool
/// let large_data = vec![0.0f32; 25_000_000]; // 100 MB
/// for chunk in large_data.chunks(9_216) { // 36 KB / 4 bytes
///     // Load chunk into pool
///     pool.store_slice(0, chunk)?;
///
///     // Process data in pool
///     let mut results = vec![0.0f32; chunk.len()];
///     pool.load_slice(0, &mut results)?;
///
///     // Memory amplification: 2,844× at 100 MB
/// }
/// # Ok(())
/// # }
/// ```
///
/// # Properties
///
/// - **Fixed size**: Pool size independent of input size
/// - **Reusable**: Same pool handles 1 MB to 100 MB inputs
/// - **Type-safe**: Generic load/store with bytemuck Pod trait
/// - **Bounds-checked**: All accesses validated
#[derive(Debug, Clone)]
pub struct LinearPool {
    /// Pool data storage
    data: Vec<u8>,

    /// Total capacity in bytes
    capacity: usize,
}

impl LinearPool {
    /// Create a new linear pool with the given capacity
    ///
    /// # Arguments
    ///
    /// * `capacity` - Pool size in bytes
    ///
    /// # Example
    ///
    /// ```rust
    /// use hologram_backends::LinearPool;
    ///
    /// // 96 classes × 48 pages × 8 bytes = 36,864 bytes
    /// let pool = LinearPool::new(36_864);
    /// assert_eq!(pool.capacity(), 36_864);
    /// ```
    pub fn new(capacity: usize) -> Self {
        Self {
            data: vec![0; capacity],
            capacity,
        }
    }

    /// Get pool capacity in bytes
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Load a single typed value from the pool
    ///
    /// # Type Safety
    ///
    /// Uses `bytemuck::Pod` trait to ensure safe zero-copy casting.
    /// Only types that can be safely transmuted from bytes are allowed.
    ///
    /// # Arguments
    ///
    /// * `offset` - Byte offset within pool
    ///
    /// # Errors
    ///
    /// Returns `PoolOutOfBounds` if offset + sizeof(T) exceeds capacity.
    ///
    /// # Example
    ///
    /// ```rust
    /// use hologram_backends::LinearPool;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pool = LinearPool::new(1024);
    ///
    /// // Store value
    /// pool.store(0, 42.0f32)?;
    ///
    /// // Load value
    /// let value: f32 = pool.load(0)?;
    /// assert_eq!(value, 42.0);
    /// # Ok(())
    /// # }
    /// ```
    pub fn load<T: bytemuck::Pod>(&self, offset: usize) -> Result<T> {
        let size = std::mem::size_of::<T>();

        if offset + size > self.capacity {
            return Err(BackendError::PoolOutOfBounds {
                offset,
                size,
                pool_size: self.capacity,
            });
        }

        let bytes = &self.data[offset..offset + size];
        Ok(*bytemuck::from_bytes(bytes))
    }

    /// Store a single typed value to the pool
    ///
    /// # Type Safety
    ///
    /// Uses `bytemuck::Pod` trait to ensure safe zero-copy casting.
    ///
    /// # Arguments
    ///
    /// * `offset` - Byte offset within pool
    /// * `value` - Value to store
    ///
    /// # Errors
    ///
    /// Returns `PoolOutOfBounds` if offset + sizeof(T) exceeds capacity.
    ///
    /// # Example
    ///
    /// ```rust
    /// use hologram_backends::LinearPool;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pool = LinearPool::new(1024);
    ///
    /// pool.store(0, 123.45f32)?;
    /// pool.store(4, 678.90f32)?;
    ///
    /// assert_eq!(pool.load::<f32>(0)?, 123.45);
    /// assert_eq!(pool.load::<f32>(4)?, 678.90);
    /// # Ok(())
    /// # }
    /// ```
    pub fn store<T: bytemuck::Pod>(&mut self, offset: usize, value: T) -> Result<()> {
        let size = std::mem::size_of::<T>();

        if offset + size > self.capacity {
            return Err(BackendError::PoolOutOfBounds {
                offset,
                size,
                pool_size: self.capacity,
            });
        }

        let bytes = bytemuck::bytes_of(&value);
        self.data[offset..offset + size].copy_from_slice(bytes);

        Ok(())
    }

    /// Load a slice of typed values from the pool
    ///
    /// # Arguments
    ///
    /// * `offset` - Byte offset within pool
    /// * `dest` - Destination slice
    ///
    /// # Errors
    ///
    /// Returns `PoolOutOfBounds` if offset + slice size exceeds capacity.
    ///
    /// # Example
    ///
    /// ```rust
    /// use hologram_backends::LinearPool;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pool = LinearPool::new(1024);
    ///
    /// // Store data
    /// let data = [1.0f32, 2.0, 3.0, 4.0];
    /// pool.store_slice(0, &data)?;
    ///
    /// // Load data
    /// let mut results = [0.0f32; 4];
    /// pool.load_slice(0, &mut results)?;
    /// assert_eq!(results, data);
    /// # Ok(())
    /// # }
    /// ```
    pub fn load_slice<T: bytemuck::Pod>(&self, offset: usize, dest: &mut [T]) -> Result<()> {
        let size = std::mem::size_of_val(dest);

        if offset + size > self.capacity {
            return Err(BackendError::PoolOutOfBounds {
                offset,
                size,
                pool_size: self.capacity,
            });
        }

        let bytes = &self.data[offset..offset + size];
        dest.copy_from_slice(bytemuck::cast_slice(bytes));

        Ok(())
    }

    /// Store a slice of typed values to the pool
    ///
    /// # Arguments
    ///
    /// * `offset` - Byte offset within pool
    /// * `src` - Source slice
    ///
    /// # Errors
    ///
    /// Returns `PoolOutOfBounds` if offset + slice size exceeds capacity.
    ///
    /// # Example
    ///
    /// ```rust
    /// use hologram_backends::LinearPool;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pool = LinearPool::new(1024);
    ///
    /// let data = vec![1.0f32, 2.0, 3.0, 4.0, 5.0];
    /// pool.store_slice(0, &data)?;
    ///
    /// let mut chunk = [0.0f32; 3];
    /// pool.load_slice(0, &mut chunk)?;
    /// assert_eq!(chunk, [1.0, 2.0, 3.0]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn store_slice<T: bytemuck::Pod>(&mut self, offset: usize, src: &[T]) -> Result<()> {
        let size = std::mem::size_of_val(src);

        if offset + size > self.capacity {
            return Err(BackendError::PoolOutOfBounds {
                offset,
                size,
                pool_size: self.capacity,
            });
        }

        let bytes = bytemuck::cast_slice(src);
        self.data[offset..offset + size].copy_from_slice(bytes);

        Ok(())
    }

    /// Load raw bytes from the pool
    ///
    /// # Arguments
    ///
    /// * `offset` - Byte offset within pool
    /// * `dest` - Destination byte buffer
    ///
    /// # Errors
    ///
    /// Returns `PoolOutOfBounds` if offset + length exceeds capacity.
    pub fn load_bytes(&self, offset: usize, dest: &mut [u8]) -> Result<()> {
        let size = dest.len();

        if offset + size > self.capacity {
            return Err(BackendError::PoolOutOfBounds {
                offset,
                size,
                pool_size: self.capacity,
            });
        }

        dest.copy_from_slice(&self.data[offset..offset + size]);
        Ok(())
    }

    /// Store raw bytes to the pool
    ///
    /// # Arguments
    ///
    /// * `offset` - Byte offset within pool
    /// * `src` - Source byte buffer
    ///
    /// # Errors
    ///
    /// Returns `PoolOutOfBounds` if offset + length exceeds capacity.
    pub fn store_bytes(&mut self, offset: usize, src: &[u8]) -> Result<()> {
        let size = src.len();

        if offset + size > self.capacity {
            return Err(BackendError::PoolOutOfBounds {
                offset,
                size,
                pool_size: self.capacity,
            });
        }

        self.data[offset..offset + size].copy_from_slice(src);
        Ok(())
    }

    /// Clear the pool (fill with zeros)
    ///
    /// # Example
    ///
    /// ```rust
    /// use hologram_backends::LinearPool;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pool = LinearPool::new(1024);
    ///
    /// pool.store(0, 42.0f32)?;
    /// pool.clear();
    /// assert_eq!(pool.load::<f32>(0)?, 0.0);
    /// # Ok(())
    /// # }
    /// ```
    pub fn clear(&mut self) {
        self.data.fill(0);
    }

    /// Get a slice view of the pool data
    pub fn as_slice(&self) -> &[u8] {
        &self.data
    }

    /// Get a mutable slice view of the pool data
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.data
    }
}

// ================================================================================================
// Tests
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pool_creation() {
        let pool = LinearPool::new(1024);
        assert_eq!(pool.capacity(), 1024);
    }

    #[test]
    fn test_pool_load_store() {
        let mut pool = LinearPool::new(1024);

        // Store and load f32
        pool.store(0, 42.0f32).unwrap();
        assert_eq!(pool.load::<f32>(0).unwrap(), 42.0);

        // Store and load i32
        pool.store(4, 123i32).unwrap();
        assert_eq!(pool.load::<i32>(4).unwrap(), 123);

        // Store and load u64
        pool.store(8, 9876543210u64).unwrap();
        assert_eq!(pool.load::<u64>(8).unwrap(), 9876543210);
    }

    #[test]
    fn test_pool_slice_operations() {
        let mut pool = LinearPool::new(1024);

        let data = [1.0f32, 2.0, 3.0, 4.0, 5.0];
        pool.store_slice(0, &data).unwrap();

        let mut results = [0.0f32; 5];
        pool.load_slice(0, &mut results).unwrap();

        assert_eq!(results, data);
    }

    #[test]
    fn test_pool_out_of_bounds() {
        let mut pool = LinearPool::new(16);

        // Store beyond capacity
        let result = pool.store(15, 42.0f32);
        assert!(result.is_err());

        // Load beyond capacity
        let result = pool.load::<f32>(15);
        assert!(result.is_err());
    }

    #[test]
    fn test_pool_byte_operations() {
        let mut pool = LinearPool::new(1024);

        let bytes = b"Hello, World!";
        pool.store_bytes(0, bytes).unwrap();

        let mut dest = vec![0u8; bytes.len()];
        pool.load_bytes(0, &mut dest).unwrap();

        assert_eq!(dest, bytes);
    }

    #[test]
    fn test_pool_clear() {
        let mut pool = LinearPool::new(64);

        // Fill with data
        pool.store(0, 123.45f32).unwrap();
        pool.store(4, 67.89f32).unwrap();

        // Clear
        pool.clear();

        // Verify cleared
        assert_eq!(pool.load::<f32>(0).unwrap(), 0.0);
        assert_eq!(pool.load::<f32>(4).unwrap(), 0.0);
    }

    #[test]
    fn test_pool_streaming_pattern() {
        // Simulate streaming computation from experiment 3
        let mut pool = LinearPool::new(36_864); // 96 classes × 48 pages × 8 bytes

        // Simulate 100 MB input (25 million f32 values)
        let chunk_size = 9_216; // 36 KB / 4 bytes
        let total_chunks = 100;

        for chunk_idx in 0..total_chunks {
            // Simulate chunk data
            let chunk: Vec<f32> = (0..chunk_size).map(|i| (chunk_idx * chunk_size + i) as f32).collect();

            // Load chunk into pool
            pool.store_slice(0, &chunk).unwrap();

            // Verify chunk loaded correctly
            let mut results = vec![0.0f32; chunk_size];
            pool.load_slice(0, &mut results).unwrap();

            assert_eq!(results[0], (chunk_idx * chunk_size) as f32);

            // Pool is reused for next chunk (O(1) space)
        }

        // Memory amplification: input_size / pool_size
        // 9216 * 100 * 4 bytes = 3,686,400 bytes input
        // 36,864 bytes pool
        // 3,686,400 / 36,864 = 100×
        let input_size = chunk_size * total_chunks * std::mem::size_of::<f32>();
        let pool_size = pool.capacity();
        let amplification = input_size / pool_size;

        assert_eq!(amplification, 100);
    }

    #[test]
    fn test_pool_multiple_types() {
        let mut pool = LinearPool::new(1024);

        // Store different types at properly aligned offsets
        // u8: 1-byte alignment -> offset 0
        // u16: 2-byte alignment -> offset 2
        // u32: 4-byte alignment -> offset 4
        // u64: 8-byte alignment -> offset 8
        // f32: 4-byte alignment -> offset 16
        // f64: 8-byte alignment -> offset 24
        pool.store(0, 42u8).unwrap();
        pool.store(2, 1234u16).unwrap();
        pool.store(4, 567890u32).unwrap();
        pool.store(8, 9876543210u64).unwrap();
        pool.store(16, std::f32::consts::PI).unwrap();
        pool.store(24, std::f64::consts::E).unwrap();

        // Verify all values
        assert_eq!(pool.load::<u8>(0).unwrap(), 42);
        assert_eq!(pool.load::<u16>(2).unwrap(), 1234);
        assert_eq!(pool.load::<u32>(4).unwrap(), 567890);
        assert_eq!(pool.load::<u64>(8).unwrap(), 9876543210);
        assert!((pool.load::<f32>(16).unwrap() - std::f32::consts::PI).abs() < 0.00001);
        assert!((pool.load::<f64>(24).unwrap() - std::f64::consts::E).abs() < 0.00001);
    }
}
