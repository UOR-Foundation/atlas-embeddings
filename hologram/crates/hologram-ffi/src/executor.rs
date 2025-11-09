//! Executor management functions for FFI
//!
//! Provides handle-based API for creating and managing Sigmatics executors.

use crate::handles::{generate_handle, lock_registry, BUFFER_REGISTRY, EXECUTOR_REGISTRY};
use hologram_core::{BackendType, Executor as CoreExecutor};

/// Create a new executor with CPU backend (default)
///
/// The executor uses Sigmatics CircuitExecutor under the hood,
/// providing canonical circuit compilation for all operations.
///
/// This is equivalent to `new_executor_with_backend("cpu")`.
///
/// # Returns
///
/// Handle (u64) to the created executor. Use this handle for all
/// subsequent operations.
///
/// # Panics
///
/// Panics if executor creation fails (out of memory, etc.)
pub fn new_executor() -> u64 {
    let handle = generate_handle();

    tracing::debug!(handle = handle, "Creating new executor (CPU backend)");

    // Create Sigmatics executor with CPU backend
    let executor = CoreExecutor::new().expect("Failed to create executor");

    // Store in registry
    lock_registry(&EXECUTOR_REGISTRY).insert(handle, executor);

    tracing::info!(handle = handle, "Executor created successfully (CPU backend)");

    handle
}

/// Create a new executor with specified backend
///
/// # Arguments
///
/// * `backend` - Backend type as string: "cpu", "metal", or "cuda"
///
/// # Returns
///
/// Handle (u64) to the created executor, or 0 if backend is not available.
///
/// # Example backends
///
/// - "cpu" - Always available
/// - "metal" - Apple Silicon only (Coming in Phase 2.1)
/// - "cuda" - NVIDIA GPUs only (Coming in Phase 2.2)
pub fn new_executor_with_backend(backend: String) -> u64 {
    let handle = generate_handle();

    tracing::debug!(handle = handle, backend = %backend, "Creating executor with backend");

    // Parse backend type
    let backend_type = match backend.to_lowercase().as_str() {
        "cpu" => BackendType::Cpu,
        "metal" => BackendType::Metal,
        "cuda" => BackendType::Cuda,
        _ => {
            tracing::error!(backend = %backend, "Invalid backend type");
            return 0; // Return 0 to indicate error
        }
    };

    // Create executor with specified backend
    let executor = match CoreExecutor::new_with_backend(backend_type) {
        Ok(exec) => exec,
        Err(e) => {
            tracing::error!(
                backend = %backend,
                error = %e,
                "Failed to create executor with backend"
            );
            return 0; // Return 0 to indicate error
        }
    };

    // Store in registry
    lock_registry(&EXECUTOR_REGISTRY).insert(handle, executor);

    tracing::info!(
        handle = handle,
        backend = %backend,
        "Executor created successfully with backend"
    );

    handle
}

/// Create a new executor with automatic backend detection
///
/// Automatically selects the best available backend:
/// 1. Metal (if on Apple Silicon)
/// 2. CUDA (if NVIDIA GPU available)
/// 3. CPU (fallback, always available)
///
/// # Returns
///
/// Handle (u64) to the created executor.
///
/// # Panics
///
/// Panics if no backend is available (CPU should always be available).
pub fn new_executor_auto() -> u64 {
    let handle = generate_handle();

    tracing::debug!(handle = handle, "Creating executor with auto backend detection");

    // Create executor with auto detection
    let executor = CoreExecutor::new_auto().expect("Failed to create executor (auto detection)");

    // Store in registry
    lock_registry(&EXECUTOR_REGISTRY).insert(handle, executor);

    tracing::info!(handle = handle, "Executor created successfully (auto backend)");

    handle
}

/// Allocate a buffer using an executor
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `len` - Number of f32 elements to allocate
///
/// # Returns
///
/// Handle (u64) to the allocated buffer
///
/// # Panics
///
/// Panics if executor handle is invalid or buffer allocation fails
pub fn executor_allocate_buffer(executor_handle: u64, len: u32) -> u64 {
    let buffer_handle = generate_handle();

    tracing::debug!(
        executor_handle = executor_handle,
        buffer_handle = buffer_handle,
        len = len,
        "Allocating buffer"
    );

    // Get executor from registry
    let mut registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    // Allocate buffer
    let buffer = executor
        .allocate::<f32>(len as usize)
        .expect("Failed to allocate buffer");

    // Store buffer in registry
    lock_registry(&BUFFER_REGISTRY).insert(buffer_handle, buffer);

    tracing::info!(
        executor_handle = executor_handle,
        buffer_handle = buffer_handle,
        len = len,
        "Buffer allocated successfully"
    );

    buffer_handle
}

/// Cleanup executor and free resources
///
/// Removes executor from registry. All buffers allocated by this
/// executor will become invalid.
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor to cleanup
pub fn executor_cleanup(executor_handle: u64) {
    tracing::debug!(executor_handle = executor_handle, "Cleaning up executor");

    let mut registry = lock_registry(&EXECUTOR_REGISTRY);
    if registry.remove(&executor_handle).is_some() {
        tracing::info!(executor_handle = executor_handle, "Executor cleaned up successfully");
    } else {
        tracing::warn!(
            executor_handle = executor_handle,
            "Executor handle not found during cleanup"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::handles::clear_all_registries;
    use serial_test::serial;

    #[test]
    #[serial]
    fn test_create_executor() {
        clear_all_registries();

        let handle = new_executor();
        assert!(handle > 0);

        // Verify executor is in registry
        let registry = lock_registry(&EXECUTOR_REGISTRY);
        assert!(registry.contains_key(&handle));
    }

    #[test]
    #[serial]
    fn test_allocate_buffer() {
        clear_all_registries();

        let exec_handle = new_executor();
        let buf_handle = executor_allocate_buffer(exec_handle, 1024);

        assert!(buf_handle > 0);

        // Verify buffer is in registry
        let registry = lock_registry(&BUFFER_REGISTRY);
        assert!(registry.contains_key(&buf_handle));
    }

    #[test]
    #[serial]
    fn test_executor_cleanup() {
        clear_all_registries();

        let handle = new_executor();
        assert!(lock_registry(&EXECUTOR_REGISTRY).contains_key(&handle));

        executor_cleanup(handle);
        assert!(!lock_registry(&EXECUTOR_REGISTRY).contains_key(&handle));
    }
}
