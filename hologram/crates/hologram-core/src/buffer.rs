//! Typed buffer views over backend-managed memory
//!
//! Buffers provide safe, typed access to Sigmatics memory via backend abstraction.
//! There are two memory pools:
//!
//! - **Linear**: RAM-resident, unlimited capacity, simple offset addressing
//! - **Boundary**: L2-resident, 1.125 MiB fixed, Φ-based structured addressing

use crate::error::{Error, Result};
use std::marker::PhantomData;

/// Memory pool type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryPool {
    /// Linear addressing (simple offset-based)
    Linear,
    /// Boundary addressing (class-based structured)
    Boundary,
}

/// Typed buffer handle
///
/// A `Buffer<T>` wraps a backend handle and provides safe, typed access
/// to Sigmatics memory. Buffers are allocated through an Executor and their
/// lifecycle is tied to the executor's backend.
///
/// # Type Safety
///
/// `T` must be `bytemuck::Pod` to ensure safe zero-copy semantics.
///
/// # Examples
///
/// ```text
/// use hologram_core::{Executor, Buffer};
///
/// let exec = Executor::new()?;
/// let buf: Buffer<f32> = exec.allocate(1024)?;
///
/// // Buffer now wraps backend handle
/// let handle = buf.handle(); // BackendHandle
/// ```
pub struct Buffer<T> {
    /// Primary class index [0, 96)
    class_index: u8,
    /// Number of T elements
    len: usize,
    /// Memory pool type
    pool: MemoryPool,
    /// Type marker
    _phantom: PhantomData<T>,
}

impl<T: bytemuck::Pod> Buffer<T> {
    /// Create new buffer mapped to a class
    ///
    /// # Safety
    ///
    /// This is pub(crate) because:
    /// - class_index must be valid [0, 96)
    /// - len must match actual class capacity
    ///
    /// Only Executor should call this.
    pub(crate) fn new(class_index: u8, len: usize, pool: MemoryPool) -> Self {
        Self {
            class_index,
            len,
            pool,
            _phantom: PhantomData,
        }
    }

    /// Get primary class index
    ///
    /// Returns the class index [0, 96) that this buffer maps to
    pub fn class_index(&self) -> u8 {
        self.class_index
    }

    /// Get primary class index (alias for class_index)
    ///
    /// Returns the class index [0, 96) that this buffer maps to
    pub fn class(&self) -> u8 {
        self.class_index
    }

    /// Get number of elements
    pub fn len(&self) -> usize {
        self.len
    }

    /// Check if buffer is empty
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Get memory pool (Linear or Boundary)
    pub fn pool(&self) -> MemoryPool {
        self.pool
    }

    /// Check if this is a linear buffer
    pub fn is_linear(&self) -> bool {
        matches!(self.pool, MemoryPool::Linear)
    }

    /// Check if this is a boundary buffer
    pub fn is_boundary(&self) -> bool {
        matches!(self.pool, MemoryPool::Boundary)
    }

    /// Get element size in bytes
    pub fn element_size(&self) -> usize {
        std::mem::size_of::<T>()
    }

    /// Get total size in bytes
    pub fn size_bytes(&self) -> usize {
        self.len * self.element_size()
    }

    /// Copy data from host slice to buffer (H2D transfer)
    ///
    /// Writes data directly to the class memory in Sigmatics ClassMemory.
    ///
    /// # Arguments
    ///
    /// * `exec` - Executor for accessing class memory
    /// * `src` - Source data slice
    ///
    /// # Errors
    ///
    /// Returns error if slice length doesn't match buffer length
    #[tracing::instrument(skip(self, exec, src), fields(
        class = self.class_index,
        elements = src.len(),
        bytes = std::mem::size_of_val(src),
        type_name = std::any::type_name::<T>()
    ))]
    pub fn copy_from_slice(&mut self, exec: &mut crate::executor::Executor, src: &[T]) -> Result<()> {
        let start = std::time::Instant::now();

        if src.len() != self.len() {
            return Err(Error::BufferSizeMismatch {
                expected: self.len(),
                actual: src.len(),
            });
        }

        exec.write_buffer_data(self.class_index, src)?;

        let duration_us = start.elapsed().as_micros() as u64;
        let bytes_copied = std::mem::size_of_val(src);
        let bandwidth_mbps = if duration_us > 0 {
            (bytes_copied as f64 / duration_us as f64) * 1_000_000.0 / (1024.0 * 1024.0)
        } else {
            0.0
        };

        tracing::debug!(
            duration_us = duration_us,
            bytes = bytes_copied,
            kb = bytes_copied as f64 / 1024.0,
            bandwidth_mbps = bandwidth_mbps,
            direction = "H2D",
            pool = ?self.pool,
            "buffer_copy_from_slice"
        );

        Ok(())
    }

    /// Copy data from buffer to host slice (D2H transfer)
    ///
    /// Reads data directly from the class memory in Sigmatics ClassMemory
    /// and copies it to the provided mutable slice.
    ///
    /// # Arguments
    ///
    /// * `exec` - Executor to read class data from
    /// * `dst` - Destination slice to copy data into (must match buffer length)
    #[tracing::instrument(skip(self, exec, dst), fields(
        class = self.class_index,
        elements = self.len,
        bytes = self.len * std::mem::size_of::<T>(),
        type_name = std::any::type_name::<T>()
    ))]
    pub fn copy_to_slice(&self, exec: &crate::executor::Executor, dst: &mut [T]) -> Result<()> {
        if dst.len() != self.len() {
            return Err(Error::BufferSizeMismatch {
                expected: self.len(),
                actual: dst.len(),
            });
        }

        let start = std::time::Instant::now();

        let data = exec.read_buffer_data(self.class_index, self.len())?;
        dst.copy_from_slice(&data);

        let duration_us = start.elapsed().as_micros() as u64;
        let bytes_copied = self.len() * std::mem::size_of::<T>();
        let bandwidth_mbps = if duration_us > 0 {
            (bytes_copied as f64 / duration_us as f64) * 1_000_000.0 / (1024.0 * 1024.0)
        } else {
            0.0
        };

        tracing::debug!(
            duration_us = duration_us,
            bytes = bytes_copied,
            kb = bytes_copied as f64 / 1024.0,
            bandwidth_mbps = bandwidth_mbps,
            direction = "D2H",
            pool = ?self.pool,
            "buffer_copy_to_slice"
        );

        Ok(())
    }

    /// Copy buffer contents to a Vec (D2H transfer)
    ///
    /// Reads data directly from the class memory in Sigmatics ClassMemory.
    #[tracing::instrument(skip(self, exec), fields(
        class = self.class_index,
        elements = self.len,
        bytes = self.len * std::mem::size_of::<T>(),
        type_name = std::any::type_name::<T>()
    ))]
    pub fn to_vec(&self, exec: &crate::executor::Executor) -> Result<Vec<T>> {
        let start = std::time::Instant::now();

        let typed = exec.read_buffer_data(self.class_index, self.len())?;

        let duration_us = start.elapsed().as_micros() as u64;
        let bytes_copied = self.len() * std::mem::size_of::<T>();
        let bandwidth_mbps = if duration_us > 0 {
            (bytes_copied as f64 / duration_us as f64) * 1_000_000.0 / (1024.0 * 1024.0)
        } else {
            0.0
        };

        tracing::debug!(
            duration_us = duration_us,
            bytes = bytes_copied,
            kb = bytes_copied as f64 / 1024.0,
            bandwidth_mbps = bandwidth_mbps,
            direction = "D2H",
            pool = ?self.pool,
            "buffer_to_vec"
        );

        Ok(typed)
    }

    /// Get immutable slice view with zero-copy access
    ///
    /// Provides direct read-only access to the buffer's data in Sigmatics class memory.
    /// This is a zero-copy operation that reinterprets the class memory as a typed slice.
    ///
    /// # Arguments
    ///
    /// * `exec` - Executor to access class memory from
    ///
    /// # Returns
    ///
    /// Immutable slice of type `&[T]` with length equal to buffer length
    ///
    pub fn as_slice<'a>(&'a self, _exec: &'a crate::executor::Executor) -> Result<&'a [T]> {
        panic!("Buffer::as_slice() has been removed. ClassMemory no longer exists. Use to_vec() instead.")
    }

    /// Get mutable slice view with zero-copy access
    ///
    /// Provides direct read-write access to the buffer's data in Sigmatics class memory.
    /// This is a zero-copy operation that reinterprets the class memory as a mutable typed slice.
    ///
    /// # Arguments
    ///
    /// * `exec` - Executor to access class memory from
    ///
    /// # Returns
    ///
    /// Mutable slice of type `&mut [T]` with length equal to buffer length
    ///
    pub fn as_mut_slice<'a>(&'a mut self, _exec: &'a mut crate::executor::Executor) -> Result<&'a mut [T]> {
        panic!("Buffer::as_mut_slice() has been removed. ClassMemory no longer exists. Use copy_from_slice() instead.")
    }

    /// Copy data from host slice to buffer, canonicalizing all bytes (LSB=0)
    ///
    /// This method combines data transfer with canonicalization, ensuring
    /// all bytes in the buffer have their LSB cleared (canonical form).
    ///
    /// # Arguments
    ///
    /// * `exec` - Executor for backend access
    /// * `src` - Source data slice (will be canonicalized before writing)
    ///
    /// # Returns
    ///
    /// Ok(()) if successful, or an error if sizes don't match or write fails
    ///
    /// # Example
    ///
    /// ```text
    /// use hologram_core::Executor;
    ///
    /// let mut exec = Executor::new()?;
    /// let mut buf = exec.allocate::<f32>(1024)?;
    ///
    /// let data = vec![1.0f32; 1024];
    /// buf.copy_from_canonical_slice(&mut exec, &data)?;
    /// // All bytes in buffer now have LSB=0
    /// ```
    pub fn copy_from_canonical_slice(&mut self, exec: &mut crate::executor::Executor, src: &[T]) -> Result<()> {
        if src.len() != self.len() {
            return Err(Error::BufferSizeMismatch {
                expected: self.len(),
                actual: src.len(),
            });
        }

        // Canonicalize the data before writing (clear LSB)
        let mut canonical_data = src.to_vec();
        let bytes: &mut [u8] = bytemuck::cast_slice_mut(&mut canonical_data);
        for byte in bytes.iter_mut() {
            *byte &= 0xFE; // Clear LSB
        }

        // Write canonicalized data to buffer
        self.copy_from_slice(exec, &canonical_data)
    }

    /// Canonicalize all bytes in the buffer (clear all LSBs)
    ///
    /// This method reads the buffer data, canonicalizes it (clears all LSBs),
    /// and writes it back. This ensures all byte values are in canonical form.
    ///
    /// # Arguments
    ///
    /// * `exec` - Executor for backend access
    ///
    /// # Returns
    ///
    /// Ok(()) if successful, or an error if read/write fails
    ///
    /// # Example
    ///
    /// ```text
    /// use hologram_core::Executor;
    ///
    /// let mut exec = Executor::new()?;
    /// let mut buf = exec.allocate::<f32>(1024)?;
    ///
    /// // ... fill buffer with data ...
    ///
    /// buf.canonicalize_all(&mut exec)?;
    /// // All bytes now have LSB=0
    /// ```
    pub fn canonicalize_all(&mut self, exec: &mut crate::executor::Executor) -> Result<()> {
        // Read current data
        let mut data = self.to_vec(exec)?;

        // Canonicalize all bytes (clear LSB)
        let bytes: &mut [u8] = bytemuck::cast_slice_mut(&mut data);
        for byte in bytes.iter_mut() {
            *byte &= 0xFE; // Clear LSB
        }

        // Write back
        self.copy_from_slice(exec, &data)
    }

    /// Verify that all bytes in the buffer are in canonical form (LSB=0)
    ///
    /// This method reads the buffer and checks that all bytes have their
    /// least significant bit cleared.
    ///
    /// # Arguments
    ///
    /// * `exec` - Executor for backend access
    ///
    /// # Returns
    ///
    /// Ok(true) if all bytes are canonical, Ok(false) if any are not,
    /// or an error if read fails
    ///
    /// # Example
    ///
    /// ```text
    /// use hologram_core::Executor;
    ///
    /// let mut exec = Executor::new()?;
    /// let buf = exec.allocate::<f32>(1024)?;
    ///
    /// if buf.verify_canonical(&mut exec)? {
    ///     println!("All bytes are canonical");
    /// } else {
    ///     println!("Some bytes are not canonical");
    /// }
    /// ```
    pub fn verify_canonical(&self, exec: &mut crate::executor::Executor) -> Result<bool> {
        // Read data
        let data = self.to_vec(exec)?;

        // Check all bytes - canonical means LSB=0
        let bytes: &[u8] = bytemuck::cast_slice(&data);
        Ok(bytes.iter().all(|&byte| (byte & 1) == 0))
    }
}

impl<T: bytemuck::Pod> Clone for Buffer<T> {
    fn clone(&self) -> Self {
        Self {
            class_index: self.class_index,
            len: self.len,
            pool: self.pool,
            _phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_buffer_basic_properties() {
        let buf: Buffer<f32> = Buffer::new(0, 1024, MemoryPool::Linear);

        assert_eq!(buf.len(), 1024);
        assert!(!buf.is_empty());
        assert_eq!(buf.class_index(), 0);
        assert_eq!(buf.pool(), MemoryPool::Linear);
        assert!(buf.is_linear());
        assert!(!buf.is_boundary());
        assert_eq!(buf.element_size(), 4);
        assert_eq!(buf.size_bytes(), 4096);
    }

    #[test]
    fn test_buffer_boundary() {
        let buf: Buffer<f32> = Buffer::new(5, 4, MemoryPool::Boundary);

        assert_eq!(buf.len(), 4);
        assert_eq!(buf.class_index(), 5);
        assert_eq!(buf.pool(), MemoryPool::Boundary);
        assert!(buf.is_boundary());
        assert!(!buf.is_linear());
    }

    #[test]
    fn test_buffer_empty() {
        let buf: Buffer<f32> = Buffer::new(0, 0, MemoryPool::Linear);

        assert_eq!(buf.len(), 0);
        assert!(buf.is_empty());
    }

    #[test]
    fn test_buffer_class_index_accessor() {
        let buf: Buffer<u8> = Buffer::new(42, 256, MemoryPool::Linear);

        assert_eq!(buf.class_index(), 42);
    }

    #[test]
    fn test_buffer_clone() {
        let buf1: Buffer<f32> = Buffer::new(10, 128, MemoryPool::Linear);
        let buf2 = buf1.clone();

        assert_eq!(buf1.class_index(), buf2.class_index());
        assert_eq!(buf1.len(), buf2.len());
        assert_eq!(buf1.pool(), buf2.pool());
    }

    #[test]
    fn test_copy_from_slice_size_mismatch() {
        let mut exec = crate::executor::Executor::new().unwrap();
        let mut buf: Buffer<f32> = Buffer::new(0, 1024, MemoryPool::Linear);
        let data = vec![1.0f32; 512]; // Wrong size
        let result = buf.copy_from_slice(&mut exec, &data);
        assert!(result.is_err());

        match result {
            Err(Error::BufferSizeMismatch { expected, actual }) => {
                assert_eq!(expected, 1024);
                assert_eq!(actual, 512);
            }
            _ => panic!("Expected BufferSizeMismatch error"),
        }
    }

    #[test]
    fn test_copy_from_canonical_slice() {
        let mut exec = crate::executor::Executor::new().unwrap();

        // Properly allocate buffer through Executor
        let mut buf: Buffer<u8> = exec.allocate(16).unwrap();

        // Data with odd bytes (non-canonical)
        let data: Vec<u8> = vec![
            0x01, 0x03, 0x05, 0x07, 0x09, 0x0B, 0x0D, 0x0F, 0x11, 0x13, 0x15, 0x17, 0x19, 0x1B, 0x1D, 0x1F,
        ];

        // Copy with canonicalization
        buf.copy_from_canonical_slice(&mut exec, &data).unwrap();

        // Read back and verify all bytes are even (canonical)
        let result = buf.to_vec(&exec).unwrap();
        for &byte in &result {
            assert_eq!(byte & 1, 0, "byte {:#04x} is not canonical", byte);
        }
    }

    #[test]
    fn test_canonicalize_all() {
        let mut exec = crate::executor::Executor::new().unwrap();

        // Properly allocate buffer through Executor
        let mut buf: Buffer<u8> = exec.allocate(16).unwrap();

        // Fill with non-canonical data (odd bytes)
        let odd_data: Vec<u8> = (1..=16).map(|i| i * 2 + 1).collect();
        buf.copy_from_slice(&mut exec, &odd_data).unwrap();

        // Verify some bytes are non-canonical before
        let before = buf.to_vec(&exec).unwrap();
        assert!(before.iter().any(|&b| (b & 1) != 0));

        // Canonicalize all
        buf.canonicalize_all(&mut exec).unwrap();

        // Verify all bytes are canonical after
        let after = buf.to_vec(&exec).unwrap();
        for &byte in &after {
            assert_eq!(
                byte & 1,
                0,
                "byte {:#04x} is not canonical after canonicalize_all",
                byte
            );
        }
    }

    #[test]
    fn test_verify_canonical() {
        let mut exec = crate::executor::Executor::new().unwrap();

        // Properly allocate buffer through Executor
        let mut buf: Buffer<u8> = exec.allocate(16).unwrap();

        // Test 1: Non-canonical data should fail verification
        let odd_data: Vec<u8> = vec![0x01; 16]; // All odd bytes
        buf.copy_from_slice(&mut exec, &odd_data).unwrap();
        assert!(!buf.verify_canonical(&mut exec).unwrap());

        // Test 2: Canonical data should pass verification
        let even_data: Vec<u8> = vec![
            0x00, 0x02, 0x04, 0x06, 0x08, 0x0A, 0x0C, 0x0E, 0x10, 0x12, 0x14, 0x16, 0x18, 0x1A, 0x1C, 0x1E,
        ];
        buf.copy_from_slice(&mut exec, &even_data).unwrap();
        assert!(buf.verify_canonical(&mut exec).unwrap());

        // Test 3: Mixed data should fail verification
        let mixed_data: Vec<u8> = vec![
            0x00, 0x02, 0x04, 0x06, 0x08, 0x0A, 0x0C, 0x0E, 0x11, 0x12, 0x14, 0x16, 0x18, 0x1A, 0x1C, 0x1E,
        ]; // One odd byte
        buf.copy_from_slice(&mut exec, &mixed_data).unwrap();
        assert!(!buf.verify_canonical(&mut exec).unwrap());
    }

    #[test]
    fn test_buffer_copy_to_slice() {
        let mut exec = crate::executor::Executor::new().unwrap();
        let mut buf: Buffer<f32> = exec.allocate(16).unwrap();

        // Write test data to buffer
        let test_data: Vec<f32> = (0..16).map(|i| i as f32 * 2.5).collect();
        buf.copy_from_slice(&mut exec, &test_data).unwrap();

        // Copy data back to host slice
        let mut dst = vec![0.0f32; 16];
        buf.copy_to_slice(&exec, &mut dst).unwrap();

        // Verify data matches
        assert_eq!(dst, test_data);
    }

    #[test]
    fn test_buffer_copy_to_slice_size_mismatch() {
        let mut exec = crate::executor::Executor::new().unwrap();
        let buf: Buffer<f32> = exec.allocate(16).unwrap();

        // Try to copy to wrong-sized slice
        let mut dst = vec![0.0f32; 10];
        let result = buf.copy_to_slice(&exec, &mut dst);

        assert!(result.is_err());
        match result {
            Err(Error::BufferSizeMismatch { expected, actual }) => {
                assert_eq!(expected, 16);
                assert_eq!(actual, 10);
            }
            _ => panic!("Expected BufferSizeMismatch error"),
        }
    }

    #[test]
    fn test_buffer_copy_and_read() {
        // Tests the new Buffer API: copy_from_slice() and to_vec()
        // Replaces the old zero-copy slice API that was removed with ClassMemory
        let mut exec = crate::executor::Executor::new().unwrap();
        let mut buf: Buffer<f32> = exec.allocate(16).unwrap();

        // Write test data to buffer
        let test_data: Vec<f32> = (0..16).map(|i| i as f32 * 2.5).collect();
        buf.copy_from_slice(&mut exec, &test_data).unwrap();

        // Read data back using to_vec()
        let result = buf.to_vec(&exec).unwrap();

        // Verify data matches
        assert_eq!(result.len(), 16);
        assert_eq!(result[0], 0.0);
        assert_eq!(result[1], 2.5);
        assert_eq!(result[15], 37.5);

        // Verify all data matches
        for (i, &val) in result.iter().enumerate() {
            assert_eq!(val, test_data[i], "Mismatch at index {}", i);
        }
    }

    #[test]
    fn test_buffer_write_and_read() {
        // Tests buffer write and read operations
        let mut exec = crate::executor::Executor::new().unwrap();
        let mut buf: Buffer<f32> = exec.allocate(16).unwrap();

        // Initialize buffer with zeros
        let zeros = vec![0.0f32; 16];
        buf.copy_from_slice(&mut exec, &zeros).unwrap();

        // Write specific values
        let mut new_data = vec![0.0f32; 16];
        new_data[0] = 42.0;
        new_data[1] = 43.0;
        new_data[15] = 100.0;
        buf.copy_from_slice(&mut exec, &new_data).unwrap();

        // Verify modifications persisted
        let result = buf.to_vec(&exec).unwrap();
        assert_eq!(result[0], 42.0);
        assert_eq!(result[1], 43.0);
        assert_eq!(result[15], 100.0);
        assert_eq!(result[2], 0.0); // Unchanged
    }

    #[test]
    fn test_buffer_multiple_writes() {
        // Tests multiple write operations to the same buffer
        let mut exec = crate::executor::Executor::new().unwrap();
        let mut buf: Buffer<f32> = exec.allocate(8).unwrap();

        // Write initial data
        let data1 = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
        buf.copy_from_slice(&mut exec, &data1).unwrap();

        // Verify first write
        let result1 = buf.to_vec(&exec).unwrap();
        assert_eq!(result1[0], 1.0);

        // Write modified data
        let mut data2 = data1.clone();
        data2[0] = 99.0;
        buf.copy_from_slice(&mut exec, &data2).unwrap();

        // Verify second write
        let result2 = buf.to_vec(&exec).unwrap();
        assert_eq!(result2[0], 99.0);
        assert_eq!(result2[1], 2.0);
    }
}
