//! Extended buffer operations for FFI
//!
//! Provides additional buffer query functions not in the main UDL.

use crate::handles::{lock_registry, BUFFER_REGISTRY};

/// Check if buffer is empty
pub fn buffer_is_empty(buffer_handle: u64) -> u8 {
    let registry = lock_registry(&BUFFER_REGISTRY);
    let buffer = registry
        .get(&buffer_handle)
        .unwrap_or_else(|| panic!("Buffer handle {} not found", buffer_handle));

    if buffer.is_empty() {
        1
    } else {
        0
    }
}

/// Check if buffer is in linear pool
pub fn buffer_is_linear(buffer_handle: u64) -> u8 {
    let registry = lock_registry(&BUFFER_REGISTRY);
    let buffer = registry
        .get(&buffer_handle)
        .unwrap_or_else(|| panic!("Buffer handle {} not found", buffer_handle));

    if buffer.is_linear() {
        1
    } else {
        0
    }
}

/// Check if buffer is in boundary pool
pub fn buffer_is_boundary(buffer_handle: u64) -> u8 {
    let registry = lock_registry(&BUFFER_REGISTRY);
    let buffer = registry
        .get(&buffer_handle)
        .unwrap_or_else(|| panic!("Buffer handle {} not found", buffer_handle));

    if buffer.is_boundary() {
        1
    } else {
        0
    }
}

/// Get buffer pool type
/// Returns: "linear" or "boundary"
pub fn buffer_pool(buffer_handle: u64) -> String {
    let registry = lock_registry(&BUFFER_REGISTRY);
    let buffer = registry
        .get(&buffer_handle)
        .unwrap_or_else(|| panic!("Buffer handle {} not found", buffer_handle));

    match buffer.pool() {
        hologram_core::buffer::MemoryPool::Linear => "linear".to_string(),
        hologram_core::buffer::MemoryPool::Boundary => "boundary".to_string(),
    }
}

/// Get buffer element size in bytes
pub fn buffer_element_size(buffer_handle: u64) -> u32 {
    let registry = lock_registry(&BUFFER_REGISTRY);
    let buffer = registry
        .get(&buffer_handle)
        .unwrap_or_else(|| panic!("Buffer handle {} not found", buffer_handle));

    buffer.element_size() as u32
}

/// Get buffer total size in bytes
pub fn buffer_size_bytes(buffer_handle: u64) -> u32 {
    let registry = lock_registry(&BUFFER_REGISTRY);
    let buffer = registry
        .get(&buffer_handle)
        .unwrap_or_else(|| panic!("Buffer handle {} not found", buffer_handle));

    buffer.size_bytes() as u32
}

/// Get buffer class index [0, 96)
pub fn buffer_class_index(buffer_handle: u64) -> u8 {
    let registry = lock_registry(&BUFFER_REGISTRY);
    let buffer = registry
        .get(&buffer_handle)
        .unwrap_or_else(|| panic!("Buffer handle {} not found", buffer_handle));

    buffer.class_index()
}
