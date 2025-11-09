//! Extended executor operations for FFI
//!
//! Provides executor metadata and advanced operations.

use crate::handles::{lock_registry, EXECUTOR_REGISTRY};

/// Allocate a boundary buffer from executor
/// Maps directly to a specific class in the 96-class system
pub fn executor_allocate_boundary_buffer(executor_handle: u64, class: u8, width: u32, height: u32) -> u64 {
    use crate::handles::{generate_handle, BUFFER_REGISTRY};

    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    // Allocate boundary buffer
    let buffer = executor
        .allocate_boundary::<f32>(class, width as usize, height as usize)
        .expect("Failed to allocate boundary buffer");

    // Generate handle and register buffer
    let handle = generate_handle();
    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);
    buf_registry.insert(handle, buffer);

    handle
}
