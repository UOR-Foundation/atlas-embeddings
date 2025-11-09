//! Zero-copy buffer operations for FFI
//!
//! Provides efficient data transfer using raw bytes instead of JSON serialization.
//! Compatible with Python's buffer protocol (memoryview) and NumPy arrays.

use crate::handles::{lock_registry, BUFFER_REGISTRY, EXECUTOR_REGISTRY};

/// Copy data from raw bytes to buffer (zero-copy)
///
/// This function accepts raw bytes that can be provided by Python's memoryview
/// or NumPy arrays, avoiding JSON serialization overhead.
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `buffer_handle` - Handle to the buffer
/// * `data_bytes` - Raw bytes (interpreted as f32 array)
///
/// # Example (Python)
///
/// ```python
/// import numpy as np
/// arr = np.array([1.0, 2.0, 3.0], dtype=np.float32)
/// hg.buffer_copy_from_bytes(exec, buf, bytes(memoryview(arr)))
/// ```
pub fn buffer_copy_from_bytes(executor_handle: u64, buffer_handle: u64, data_bytes: Vec<u8>) {
    // Get executor
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    // Get buffer
    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);
    let buffer = buf_registry
        .get_mut(&buffer_handle)
        .unwrap_or_else(|| panic!("Buffer handle {} not found", buffer_handle));

    // Validate size
    let expected_bytes = buffer.len() * std::mem::size_of::<f32>();
    if data_bytes.len() != expected_bytes {
        panic!(
            "Data size mismatch: expected {} bytes, got {}",
            expected_bytes,
            data_bytes.len()
        );
    }

    // Reinterpret bytes as f32 slice (zero-copy within Rust)
    let f32_slice = unsafe { std::slice::from_raw_parts(data_bytes.as_ptr() as *const f32, buffer.len()) };

    // Copy data to buffer
    buffer
        .copy_from_slice(executor, f32_slice)
        .expect("Failed to copy data to buffer");

    tracing::debug!(
        executor_handle = executor_handle,
        buffer_handle = buffer_handle,
        bytes = data_bytes.len(),
        elements = buffer.len(),
        "Zero-copy data transfer to buffer"
    );
}

/// Get buffer data as raw bytes (zero-copy compatible)
///
/// Returns raw bytes that can be efficiently converted to NumPy arrays
/// in Python without JSON serialization overhead.
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `buffer_handle` - Handle to the buffer
///
/// # Returns
///
/// Raw bytes (f32 array as bytes)
///
/// # Example (Python)
///
/// ```python
/// import numpy as np
/// data_bytes = hg.buffer_to_bytes(exec, buf)
/// arr = np.frombuffer(data_bytes, dtype=np.float32)
/// ```
pub fn buffer_to_bytes(executor_handle: u64, buffer_handle: u64) -> Vec<u8> {
    // Get executor
    let exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    // Get buffer
    let buf_registry = lock_registry(&BUFFER_REGISTRY);
    let buffer = buf_registry
        .get(&buffer_handle)
        .unwrap_or_else(|| panic!("Buffer handle {} not found", buffer_handle));

    // Read data from buffer
    let data = buffer.to_vec(executor).expect("Failed to read buffer data");

    // Convert Vec<f32> to Vec<u8> (zero-copy reinterpretation)
    let byte_slice =
        unsafe { std::slice::from_raw_parts(data.as_ptr() as *const u8, data.len() * std::mem::size_of::<f32>()) };

    tracing::debug!(
        executor_handle = executor_handle,
        buffer_handle = buffer_handle,
        bytes = byte_slice.len(),
        elements = data.len(),
        "Zero-copy data transfer from buffer"
    );

    byte_slice.to_vec()
}

/// Get raw pointer to buffer data (CPU backend only)
///
/// Returns the memory address of the buffer for direct pointer sharing.
/// Only works with CPU backend - will error for GPU backends.
///
/// # Safety
///
/// This exposes raw memory pointers. The caller must ensure:
/// - The buffer is not freed while the pointer is in use
/// - The executor stays alive while the pointer is in use
/// - No concurrent modifications occur
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `buffer_handle` - Handle to the buffer
///
/// # Returns
///
/// Memory address as u64 (0 if error)
///
/// # Example (Python)
///
/// ```python
/// import ctypes
/// ptr = hg.buffer_as_ptr(exec, buf)
/// # Use ctypes to access memory at ptr
/// ```
pub fn buffer_as_ptr(executor_handle: u64, buffer_handle: u64) -> u64 {
    // Get executor
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    // Get buffer
    let buf_registry = lock_registry(&BUFFER_REGISTRY);
    let buffer = buf_registry
        .get(&buffer_handle)
        .unwrap_or_else(|| panic!("Buffer handle {} not found", buffer_handle));

    // Try to get raw pointer (CPU backend only)
    match executor.get_buffer_ptr(buffer) {
        Ok(ptr) => {
            tracing::debug!(
                executor_handle = executor_handle,
                buffer_handle = buffer_handle,
                ptr = ptr as u64,
                "Got buffer pointer"
            );
            ptr as u64
        }
        Err(e) => {
            tracing::error!(
                executor_handle = executor_handle,
                buffer_handle = buffer_handle,
                error = ?e,
                "Failed to get buffer pointer (CPU backend required)"
            );
            0 // Return 0 on error
        }
    }
}

/// Get mutable raw pointer to buffer data (CPU backend only)
///
/// Returns the memory address of the buffer for direct pointer sharing.
/// Only works with CPU backend - will error for GPU backends.
///
/// # Safety
///
/// This exposes raw mutable memory pointers. The caller must ensure:
/// - The buffer is not freed while the pointer is in use
/// - The executor stays alive while the pointer is in use
/// - No concurrent modifications occur
/// - No aliasing violations (no other references to the buffer)
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `buffer_handle` - Handle to the buffer
///
/// # Returns
///
/// Memory address as u64 (0 if error)
pub fn buffer_as_mut_ptr(executor_handle: u64, buffer_handle: u64) -> u64 {
    // Get executor
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    // Get buffer
    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);
    let buffer = buf_registry
        .get_mut(&buffer_handle)
        .unwrap_or_else(|| panic!("Buffer handle {} not found", buffer_handle));

    // Try to get raw mutable pointer (CPU backend only)
    match executor.get_buffer_mut_ptr(buffer) {
        Ok(ptr) => {
            tracing::debug!(
                executor_handle = executor_handle,
                buffer_handle = buffer_handle,
                ptr = ptr as u64,
                "Got mutable buffer pointer"
            );
            ptr as u64
        }
        Err(e) => {
            tracing::error!(
                executor_handle = executor_handle,
                buffer_handle = buffer_handle,
                error = ?e,
                "Failed to get mutable buffer pointer (CPU backend required)"
            );
            0 // Return 0 on error
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::{executor_allocate_buffer, new_executor};
    use crate::handles::clear_all_registries;
    use serial_test::serial;

    #[test]
    #[serial]
    fn test_buffer_copy_from_bytes() {
        clear_all_registries();

        let exec = new_executor();
        let buf = executor_allocate_buffer(exec, 5);

        // Create test data as bytes
        let data: Vec<f32> = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let data_bytes: Vec<u8> =
            unsafe { std::slice::from_raw_parts(data.as_ptr() as *const u8, data.len() * std::mem::size_of::<f32>()) }
                .to_vec();

        // Copy using zero-copy function
        buffer_copy_from_bytes(exec, buf, data_bytes);

        // Read back using zero-copy
        let result_bytes = buffer_to_bytes(exec, buf);
        let result: Vec<f32> = unsafe {
            std::slice::from_raw_parts(
                result_bytes.as_ptr() as *const f32,
                result_bytes.len() / std::mem::size_of::<f32>(),
            )
        }
        .to_vec();

        assert_eq!(result, data);
    }

    #[test]
    #[serial]
    fn test_buffer_to_bytes() {
        clear_all_registries();

        let exec = new_executor();
        let buf = executor_allocate_buffer(exec, 3);

        // Fill buffer with known data using JSON (existing method)
        use crate::buffer::buffer_copy_from_slice;
        let data = vec![10.0, 20.0, 30.0];
        buffer_copy_from_slice(exec, buf, serde_json::to_string(&data).unwrap());

        // Read using zero-copy
        let result_bytes = buffer_to_bytes(exec, buf);
        let result: Vec<f32> = unsafe {
            std::slice::from_raw_parts(
                result_bytes.as_ptr() as *const f32,
                result_bytes.len() / std::mem::size_of::<f32>(),
            )
        }
        .to_vec();

        assert_eq!(result, data);
    }

    #[test]
    #[serial]
    fn test_buffer_as_ptr() {
        clear_all_registries();

        let exec = new_executor();
        let buf = executor_allocate_buffer(exec, 10);

        // Get pointer
        let ptr = buffer_as_ptr(exec, buf);

        // Should return non-zero pointer for CPU backend
        assert!(ptr > 0, "Expected non-zero pointer for CPU backend");
    }

    #[test]
    #[serial]
    fn test_buffer_as_mut_ptr() {
        clear_all_registries();

        let exec = new_executor();
        let buf = executor_allocate_buffer(exec, 10);

        // Get mutable pointer
        let ptr = buffer_as_mut_ptr(exec, buf);

        // Should return non-zero pointer for CPU backend
        assert!(ptr > 0, "Expected non-zero mutable pointer for CPU backend");
    }

    #[test]
    #[serial]
    fn test_roundtrip_bytes() {
        clear_all_registries();

        let exec = new_executor();
        let buf = executor_allocate_buffer(exec, 100);

        // Create test data
        let original: Vec<f32> = (0..100).map(|i| i as f32 * 0.5).collect();
        let original_bytes: Vec<u8> = unsafe {
            std::slice::from_raw_parts(
                original.as_ptr() as *const u8,
                original.len() * std::mem::size_of::<f32>(),
            )
        }
        .to_vec();

        // Write
        buffer_copy_from_bytes(exec, buf, original_bytes.clone());

        // Read
        let result_bytes = buffer_to_bytes(exec, buf);

        // Should match exactly
        assert_eq!(result_bytes, original_bytes);
    }
}
