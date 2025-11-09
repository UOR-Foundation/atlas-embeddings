//! Buffer management functions for FFI
//!
//! Provides handle-based API for buffer operations across FFI boundaries.

use crate::handles::{lock_registry, BUFFER_REGISTRY, EXECUTOR_REGISTRY};
use hologram_core::ops::memory;

/// Get buffer length
///
/// # Arguments
///
/// * `buffer_handle` - Handle to the buffer
///
/// # Returns
///
/// Number of elements in the buffer
pub fn buffer_length(buffer_handle: u64) -> u32 {
    let registry = lock_registry(&BUFFER_REGISTRY);
    let buffer = registry
        .get(&buffer_handle)
        .unwrap_or_else(|| panic!("Buffer handle {} not found", buffer_handle));

    buffer.len() as u32
}

/// Copy data from JSON-encoded slice to buffer
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `buffer_handle` - Handle to the buffer
/// * `data_json` - JSON-encoded array of f32 values
///
/// # Example JSON
///
/// ```json
/// [1.0, 2.0, 3.0, 4.0]
/// ```
pub fn buffer_copy_from_slice(executor_handle: u64, buffer_handle: u64, data_json: String) {
    // Parse JSON data
    let data: Vec<f32> = serde_json::from_str(&data_json).expect("Failed to parse JSON data");

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

    // Copy data
    buffer
        .copy_from_slice(executor, &data)
        .expect("Failed to copy data to buffer");

    tracing::debug!(
        executor_handle = executor_handle,
        buffer_handle = buffer_handle,
        elements = data.len(),
        "Data copied to buffer"
    );
}

/// Get buffer data as JSON-encoded string
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `buffer_handle` - Handle to the buffer
///
/// # Returns
///
/// JSON-encoded array of f32 values
pub fn buffer_to_vec(executor_handle: u64, buffer_handle: u64) -> String {
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

    // Read data
    let data = buffer.to_vec(executor).expect("Failed to read buffer data");

    // Convert to JSON
    serde_json::to_string(&data).expect("Failed to serialize data to JSON")
}

/// Fill buffer with a value
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `buffer_handle` - Handle to the buffer
/// * `value` - Value to fill with
/// * `len` - Number of elements to fill
pub fn buffer_fill(executor_handle: u64, buffer_handle: u64, value: f32, len: u32) {
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

    // Fill buffer using ops::memory::fill
    // Note: fill fills the entire buffer, ignoring the len parameter for now
    memory::fill(executor, buffer, value).expect("Failed to fill buffer");

    tracing::debug!(
        executor_handle = executor_handle,
        buffer_handle = buffer_handle,
        value = value,
        len = len,
        "Buffer filled"
    );
}

/// Copy from one buffer to another
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `src_handle` - Source buffer handle
/// * `dst_handle` - Destination buffer handle
/// * `len` - Number of elements to copy
pub fn buffer_copy(executor_handle: u64, src_handle: u64, dst_handle: u64, len: u32) {
    // Get executor
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    // Get buffers
    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    // Get source buffer (immutable)
    let src_ptr: *const hologram_core::Buffer<f32> = buf_registry
        .get(&src_handle)
        .unwrap_or_else(|| panic!("Source buffer handle {} not found", src_handle))
        as *const _;

    // Get destination buffer (mutable)
    let dst_ptr: *mut hologram_core::Buffer<f32> = buf_registry
        .get_mut(&dst_handle)
        .unwrap_or_else(|| panic!("Destination buffer handle {} not found", dst_handle))
        as *mut _;

    // Safety: We're using raw pointers to avoid borrow checker issues
    // The pointers are valid as long as we hold the registry lock
    unsafe {
        let src = &*src_ptr;
        let dst = &mut *dst_ptr;

        memory::copy(executor, src, dst).expect("Failed to copy buffer");
    }

    tracing::debug!(
        executor_handle = executor_handle,
        src_handle = src_handle,
        dst_handle = dst_handle,
        len = len,
        "Buffer copied"
    );
}

/// Copy data from buffer to host slice (JSON-encoded)
///
/// This is an alias for buffer_to_vec() for consistency with the hologram-core API.
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `buffer_handle` - Handle to the buffer
///
/// # Returns
///
/// JSON-encoded array of f32 values
pub fn buffer_copy_to_slice(executor_handle: u64, buffer_handle: u64) -> String {
    // Just call buffer_to_vec - same functionality
    buffer_to_vec(executor_handle, buffer_handle)
}

/// Copy data from JSON-encoded slice to buffer, canonicalizing all bytes (LSB=0)
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `buffer_handle` - Handle to the buffer
/// * `data_json` - JSON-encoded array of f32 values
pub fn buffer_copy_from_canonical_slice(executor_handle: u64, buffer_handle: u64, data_json: String) {
    // Parse JSON data
    let data: Vec<f32> = serde_json::from_str(&data_json).expect("Failed to parse JSON data");

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

    // Copy data with canonicalization
    buffer
        .copy_from_canonical_slice(executor, &data)
        .expect("Failed to copy canonical data to buffer");

    tracing::debug!(
        executor_handle = executor_handle,
        buffer_handle = buffer_handle,
        elements = data.len(),
        "Canonical data copied to buffer"
    );
}

/// Canonicalize all bytes in the buffer (clear all LSBs)
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `buffer_handle` - Handle to the buffer
pub fn buffer_canonicalize_all(executor_handle: u64, buffer_handle: u64) {
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

    // Canonicalize all bytes
    buffer
        .canonicalize_all(executor)
        .expect("Failed to canonicalize buffer");

    tracing::debug!(
        executor_handle = executor_handle,
        buffer_handle = buffer_handle,
        "Buffer canonicalized"
    );
}

/// Verify that all bytes in the buffer are in canonical form (LSB=0)
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `buffer_handle` - Handle to the buffer
///
/// # Returns
///
/// 1 if all bytes are canonical, 0 otherwise
pub fn buffer_verify_canonical(executor_handle: u64, buffer_handle: u64) -> u8 {
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

    // Verify canonical
    let is_canonical = buffer.verify_canonical(executor).expect("Failed to verify canonical");

    if is_canonical {
        1
    } else {
        0
    }
}

/// Cleanup buffer and free resources
///
/// # Arguments
///
/// * `buffer_handle` - Handle to the buffer to cleanup
pub fn buffer_cleanup(buffer_handle: u64) {
    tracing::debug!(buffer_handle = buffer_handle, "Cleaning up buffer");

    let mut registry = lock_registry(&BUFFER_REGISTRY);
    if registry.remove(&buffer_handle).is_some() {
        tracing::info!(buffer_handle = buffer_handle, "Buffer cleaned up successfully");
    } else {
        tracing::warn!(buffer_handle = buffer_handle, "Buffer handle not found during cleanup");
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
    fn test_buffer_length() {
        clear_all_registries();

        let exec = new_executor();
        let buf = executor_allocate_buffer(exec, 100);

        assert_eq!(buffer_length(buf), 100);
    }

    #[test]
    #[serial]
    fn test_buffer_fill_and_read() {
        clear_all_registries();

        let exec = new_executor();
        let buf = executor_allocate_buffer(exec, 10);

        buffer_fill(exec, buf, 42.0, 10);

        let data_json = buffer_to_vec(exec, buf);
        let data: Vec<f32> = serde_json::from_str(&data_json).unwrap();

        assert_eq!(data.len(), 10);
        assert_eq!(data[0], 42.0);
        assert_eq!(data[9], 42.0);
    }

    #[test]
    #[serial]
    fn test_buffer_copy_from_slice() {
        clear_all_registries();

        let exec = new_executor();
        let buf = executor_allocate_buffer(exec, 5);

        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let data_json = serde_json::to_string(&data).unwrap();

        buffer_copy_from_slice(exec, buf, data_json);

        let result_json = buffer_to_vec(exec, buf);
        let result: Vec<f32> = serde_json::from_str(&result_json).unwrap();

        assert_eq!(result, data);
    }

    #[test]
    #[serial]
    fn test_buffer_copy() {
        clear_all_registries();

        let exec = new_executor();
        let src = executor_allocate_buffer(exec, 5);
        let dst = executor_allocate_buffer(exec, 5);

        // Fill source
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        buffer_copy_from_slice(exec, src, serde_json::to_string(&data).unwrap());

        // Copy to dest
        buffer_copy(exec, src, dst, 5);

        // Verify
        let result_json = buffer_to_vec(exec, dst);
        let result: Vec<f32> = serde_json::from_str(&result_json).unwrap();

        assert_eq!(result, data);
    }
}
