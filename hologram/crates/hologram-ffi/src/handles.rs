//! Handle-based object management for FFI
//!
//! This module provides global registries for managing Executor, Buffer, and Tensor objects
//! across FFI boundaries using opaque u64 handles.
//!
//! ## Thread Safety
//!
//! All registries use `Arc<Mutex<HashMap>>` for thread-safe access.
//! Handle generation uses atomic operations.

use hologram_core::{Buffer as CoreBuffer, Executor as CoreExecutor, Tensor as CoreTensor};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};

// Global handle counter for unique handle generation
static HANDLE_COUNTER: AtomicU64 = AtomicU64::new(1);

// Global registries for object management
lazy_static::lazy_static! {
    /// Registry of all active executors
    pub(crate) static ref EXECUTOR_REGISTRY: Arc<Mutex<HashMap<u64, CoreExecutor>>> =
        Arc::new(Mutex::new(HashMap::new()));

    /// Registry of all active f32 buffers
    pub(crate) static ref BUFFER_REGISTRY: Arc<Mutex<HashMap<u64, CoreBuffer<f32>>>> =
        Arc::new(Mutex::new(HashMap::new()));

    /// Registry of all active f32 tensors
    pub(crate) static ref TENSOR_REGISTRY: Arc<Mutex<HashMap<u64, CoreTensor<f32>>>> =
        Arc::new(Mutex::new(HashMap::new()));
}

/// Generate a unique handle for object management
///
/// Uses atomic increment to ensure thread-safe handle generation.
/// Handles start at 1 (0 is reserved for invalid/null handles).
pub(crate) fn generate_handle() -> u64 {
    HANDLE_COUNTER.fetch_add(1, Ordering::SeqCst)
}

/// Helper function to lock a registry, handling poisoned mutexes gracefully
///
/// If the mutex is poisoned (due to a panic while holding the lock),
/// we recover the data anyway since it's still valid.
pub(crate) fn lock_registry<T>(mutex: &Arc<Mutex<T>>) -> MutexGuard<'_, T> {
    match mutex.lock() {
        Ok(guard) => guard,
        Err(poisoned) => {
            // Mutex poisoned due to panic, but data is still valid
            tracing::warn!("Registry mutex was poisoned, recovering data");
            poisoned.into_inner()
        }
    }
}

/// Clear all registries (for testing/debugging)
///
/// # Warning
///
/// This will invalidate all existing handles. Use only for testing.
pub fn clear_all_registries() {
    lock_registry(&EXECUTOR_REGISTRY).clear();
    lock_registry(&BUFFER_REGISTRY).clear();
    lock_registry(&TENSOR_REGISTRY).clear();
    tracing::info!("All registries cleared");
}

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;

    #[test]
    #[serial]
    fn test_handle_generation() {
        let h1 = generate_handle();
        let h2 = generate_handle();
        let h3 = generate_handle();

        assert!(h1 > 0);
        assert!(h2 > h1);
        assert!(h3 > h2);
    }

    #[test]
    #[serial]
    fn test_clear_registries() {
        // Start with clean slate
        clear_all_registries();

        // Add some dummy data
        lock_registry(&EXECUTOR_REGISTRY).insert(123, CoreExecutor::new().unwrap());

        assert_eq!(lock_registry(&EXECUTOR_REGISTRY).len(), 1);

        clear_all_registries();

        assert_eq!(lock_registry(&EXECUTOR_REGISTRY).len(), 0);
        assert_eq!(lock_registry(&BUFFER_REGISTRY).len(), 0);
        assert_eq!(lock_registry(&TENSOR_REGISTRY).len(), 0);
    }
}
