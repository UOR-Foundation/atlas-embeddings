//! Kernel execution with hybrid approach
//!
//! This module provides both inline kernels (compiled into binary) and dynamic kernels
//! (loaded from .so/.dylib files) for maximum performance and flexibility.

pub mod inline;

use crate::buffer::Buffer;
use crate::error::{Error, Result};
use crate::executor::Executor;
use std::collections::HashMap;
use std::path::Path;
use std::sync::{Arc, Mutex};

/// Type alias for kernel handles
pub type KernelHandle = usize;

/// Loaded kernel information
#[derive(Debug, Clone)]
pub struct LoadedKernel {
    pub name: String,
    pub abi_version: u32,
}

/// Kernel loader and registry
#[derive(Debug)]
pub struct KernelLoader {
    kernels: Arc<Mutex<HashMap<String, LoadedKernel>>>,
}

impl KernelLoader {
    /// Create a new kernel loader
    pub fn new() -> Self {
        Self {
            kernels: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Load kernels from a directory
    pub fn load_from_directory(&self, path: impl AsRef<Path>) -> Result<()> {
        let path = path.as_ref();

        if !path.exists() {
            return Err(Error::InvalidOperation(format!(
                "Kernel directory does not exist: {}",
                path.display()
            )));
        }

        let entries =
            std::fs::read_dir(path).map_err(|e| Error::InvalidOperation(format!("Failed to read directory: {}", e)))?;
        let mut loaded = Vec::new();

        for entry in entries {
            let entry = entry.map_err(|e| Error::InvalidOperation(format!("Failed to read directory entry: {}", e)))?;
            let file_path = entry.path();

            if let Some(ext) = file_path.extension() {
                let ext_str = ext.to_string_lossy();
                if ext_str == "so" || ext_str == "dylib" || ext_str == "dll" {
                    if let Some(stem) = file_path.file_stem() {
                        let kernel_name = stem.to_string_lossy().to_string();

                        // Load the library to validate it and get ABI version
                        unsafe {
                            match libloading::Library::new(&file_path) {
                                Ok(library) => {
                                    // Try to get ABI version
                                    let abi_version = match library
                                        .get::<unsafe extern "C" fn() -> u32>(b"atlas_kernel_abi_version")
                                    {
                                        Ok(func) => func(),
                                        Err(_) => 1, // Default to version 1
                                    };

                                    // Register with global hologram-codegen registry once
                                    static REGISTERED: std::sync::Once = std::sync::Once::new();
                                    REGISTERED.call_once(|| {
                                        use hologram_codegen::register_all_kernels_from_directory;
                                        let _ = register_all_kernels_from_directory(path);
                                    });

                                    loaded.push((kernel_name.clone(), abi_version));
                                }
                                Err(e) => {
                                    tracing::warn!("Failed to load kernel {}: {}", kernel_name, e);
                                }
                            }
                        }
                    }
                }
            }
        }

        // Register loaded kernels
        let mut kernels = self.kernels.lock().unwrap();
        for (name, abi_version) in loaded {
            kernels.insert(
                name.clone(),
                LoadedKernel {
                    name: name.clone(),
                    abi_version,
                },
            );
            tracing::info!("Registered kernel: {} (ABI v{})", name, abi_version);
        }

        Ok(())
    }

    /// Get a loaded kernel by name
    pub fn get_kernel(&self, name: &str) -> Option<LoadedKernel> {
        self.kernels.lock().unwrap().get(name).cloned()
    }

    /// List all loaded kernels
    pub fn list_kernels(&self) -> Vec<String> {
        self.kernels.lock().unwrap().keys().cloned().collect()
    }

    /// Check if a kernel is loaded
    pub fn has_kernel(&self, name: &str) -> bool {
        self.kernels.lock().unwrap().contains_key(name)
    }
}

impl Default for KernelLoader {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Kernel-Enabled Operations
// ============================================================================

/// Vector addition with automatic kernel dispatch (f32 only)
///
/// This function attempts to use a loaded kernel if available.
///
/// Uses zero-copy access via `as_slice()` to avoid memory transfers.
#[tracing::instrument(skip(exec, a, b, c))]
pub fn vector_add_kernel(
    exec: &mut Executor,
    a: &Buffer<f32>,
    b: &Buffer<f32>,
    c: &mut Buffer<f32>,
    n: usize,
) -> Result<()> {
    use hologram_codegen::{execute_kernel, get_kernel, marshal_kernel_params};

    // Try to use kernel if available
    let handle =
        get_kernel("vector_add").map_err(|e| Error::InvalidOperation(format!("Kernel not available: {}", e)))?;

    tracing::debug!("Using vector_add kernel");

    // Get zero-copy slices directly from class memory
    // This bypasses the expensive to_vec/copy_from_slice transfers
    // We need separate scopes to handle borrow checker constraints

    // Get immutable pointers first
    let (a_ptr, b_ptr) = {
        let data_a = a.as_slice(exec)?;
        let data_b = b.as_slice(exec)?;
        (data_a.as_ptr() as u64, data_b.as_ptr() as u64)
    };

    // Then get mutable pointer
    let c_ptr = {
        let data_c = c.as_mut_slice(exec)?;
        data_c.as_mut_ptr() as u64
    };

    let params = marshal_kernel_params(&[a_ptr, b_ptr, c_ptr], &[n as u32]);

    // Execute kernel (operates directly on class memory)
    unsafe {
        execute_kernel(handle, &params)
            .map_err(|e| Error::InvalidOperation(format!("Kernel execution failed: {}", e)))?;
    }

    tracing::debug!("Kernel execution complete");
    Ok(())
}

// Removed PodZero trait - no longer needed

// Re-export for convenience
pub use crate::ops::math::vector_add;
