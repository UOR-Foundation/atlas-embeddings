//! Hologram Code Generator
//!
//! Generates Rust code from JSON kernel schemas and manages dynamic library loading.
//! Supports codegen for kernel execution and dynamic library compilation.

pub mod dylib_codegen;
pub mod error;
pub mod inline_kernels;
pub mod json_schema;
pub mod schema;

pub use dylib_codegen::DylibCodegen;
pub use error::CodegenError;
pub use error::Result as CodegenResult;
pub use inline_kernels::{generate_inline_kernel, generate_kernels_module};
pub use json_schema::{Expression, FunctionDef, JsonSchema, ParamDef, Statement, Type};

use hologram_tracing::debug;
use libloading::Library;
use std::collections::HashMap;
use std::path::Path;
use std::sync::{LazyLock, Mutex};

/// Type alias for kernel handles
pub type KernelHandle = usize;

/// Loaded kernel library with FFI function pointers
pub struct KernelLibrary {
    pub library: Library,
    pub name: String,
}

/// Type-safe FFI function pointer for kernel execution
type KernelExecuteFn = unsafe extern "C" fn(
    config: *const std::os::raw::c_void,
    params: *const u8,
    params_len: usize,
    error_msg: *mut *mut std::os::raw::c_char,
) -> u32;

/// Kernel registry - manages all loaded kernels
pub struct KernelRegistry {
    kernels: HashMap<String, KernelHandle>,
    libraries: HashMap<KernelHandle, KernelLibrary>,
    /// Cached function pointers (loaded at startup, no resolution overhead)
    execute_functions: HashMap<KernelHandle, KernelExecuteFn>,
}

impl Default for KernelRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl KernelRegistry {
    pub fn new() -> Self {
        Self {
            kernels: HashMap::new(),
            libraries: HashMap::new(),
            execute_functions: HashMap::new(),
        }
    }

    pub fn load_from_directory(
        path: impl AsRef<Path>,
    ) -> Result<Vec<(String, KernelHandle)>, Box<dyn std::error::Error>> {
        let path = path.as_ref();
        let mut loaded = Vec::new();
        let mut libraries = HashMap::new();

        // Find all .so/.dylib/.dll files in directory
        let entries = std::fs::read_dir(path)?;

        for entry in entries {
            let entry = entry?;
            let file_path = entry.path();

            if let Some(ext) = file_path.extension() {
                let ext_str = ext.to_string_lossy();
                // On macOS, prefer .dylib; on Linux, prefer .so
                #[cfg(target_os = "macos")]
                let valid_ext = ext_str == "dylib";
                #[cfg(target_os = "linux")]
                let valid_ext = ext_str == "so";
                #[cfg(target_os = "windows")]
                let valid_ext = ext_str == "dll";
                #[cfg(not(any(target_os = "macos", target_os = "linux", target_os = "windows")))]
                let valid_ext = ext_str == "so" || ext_str == "dylib" || ext_str == "dll";

                if valid_ext {
                    // Extract kernel name from filename (e.g., "vector_add.dylib" -> "vector_add")
                    if let Some(stem) = file_path.file_stem() {
                        let kernel_name = stem.to_string_lossy().to_string();

                        // Load the library
                        unsafe {
                            let library = Library::new(&file_path)?;

                            // Register kernel with handle
                            let handle = loaded.len();
                            loaded.push((kernel_name.clone(), handle));

                            // Store the library in registry
                            libraries.insert(
                                handle,
                                KernelLibrary {
                                    library,
                                    name: kernel_name.clone(),
                                },
                            );

                            debug!("✅ Loaded kernel: {} from {}", kernel_name, file_path.display());
                        }
                    }
                }
            }
        }

        // Store all kernels and libraries in the global registry
        let mut registry = KERNEL_REGISTRY.lock().unwrap();
        for (name, handle) in &loaded {
            registry.kernels.insert(name.clone(), *handle);
        }
        for (handle, lib) in libraries {
            registry.libraries.insert(handle, lib);

            // Cache the execute function at startup (eliminate Symbol resolution overhead)
            let kernel_name = loaded
                .iter()
                .find(|(_, h)| *h == handle)
                .map(|(n, _)| n.clone())
                .unwrap_or_default();
            if let Err(e) = registry.cache_execute_fn(handle, &kernel_name) {
                debug!("⚠️  Could not cache execute function for handle {}: {}", handle, e);
            }
        }

        Ok(loaded)
    }

    pub fn register(&mut self, name: String) -> KernelHandle {
        let handle = self.kernels.len();
        self.kernels.insert(name, handle);
        handle
    }

    pub fn get(&self, name: &str) -> Option<KernelHandle> {
        self.kernels.get(name).copied()
    }

    pub fn get_library(&self, handle: KernelHandle) -> Option<&KernelLibrary> {
        self.libraries.get(&handle)
    }

    /// Get cached execute function for a kernel (zero overhead)
    pub fn get_execute_fn(&self, handle: KernelHandle) -> Option<KernelExecuteFn> {
        self.execute_functions.get(&handle).copied()
    }

    /// Cache execute function at startup
    pub fn cache_execute_fn(
        &mut self,
        handle: KernelHandle,
        _kernel_name: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let library = self.libraries.get(&handle).ok_or("Library not found")?;

        unsafe {
            // Use standard "atlas_kernel_execute" symbol (generated by macros)
            let symbol: libloading::Symbol<KernelExecuteFn> = library
                .library
                .get(b"atlas_kernel_execute")
                .map_err(|_| "Failed to get atlas_kernel_execute symbol")?;

            let fn_ptr = *symbol;
            self.execute_functions.insert(handle, fn_ptr);
        }

        Ok(())
    }
}

/// Global kernel registry
static KERNEL_REGISTRY: LazyLock<Mutex<KernelRegistry>> = LazyLock::new(|| Mutex::new(KernelRegistry::new()));

/// Get a kernel handle by name
pub fn get_kernel(name: &str) -> Result<KernelHandle, String> {
    let registry = KERNEL_REGISTRY.lock().unwrap();
    registry.get(name).ok_or_else(|| format!("Kernel not found: {}", name))
}

/// Marshal vector pointers and scalars into a parameter buffer
pub fn marshal_kernel_params(
    buffers: &[u64], // Device array pointers
    scalars: &[u32], // Scalar values (u32 values)
) -> Vec<u8> {
    let mut buf = Vec::new();

    // Marshal device array pointers (each 8 bytes on 64-bit systems)
    for &ptr in buffers {
        buf.extend_from_slice(&ptr.to_le_bytes());
    }

    // Marshal scalar values (each 4 bytes for u32)
    for &val in scalars {
        buf.extend_from_slice(&val.to_le_bytes());
    }

    buf
}

/// Execute a kernel with given parameters
///
/// # Safety
///
/// This function is unsafe because it calls FFI functions.
/// The caller must ensure that:
/// - The kernel handle is valid
/// - The parameters are properly marshalled
/// - The buffers are properly allocated and sized
pub unsafe fn execute_kernel(handle: KernelHandle, params: &[u8]) -> Result<(), String> {
    let registry = KERNEL_REGISTRY.lock().unwrap();

    // Get cached function pointer (NO Symbol resolution overhead)
    let execute_fn = registry
        .get_execute_fn(handle)
        .ok_or_else(|| format!("Kernel handle {} not found or not cached", handle))?;

    // Direct FFI call with cached function pointer
    let config = std::ptr::null();
    let params_ptr = params.as_ptr();
    let params_len = params.len();
    let error_msg = std::ptr::null_mut();

    let result = execute_fn(config, params_ptr, params_len, error_msg);

    if result == 0 {
        Ok(())
    } else {
        Err(format!("Kernel execution failed with error code: {}", result))
    }
}

/// Load all kernels from directory at startup
pub fn register_all_kernels_from_directory(
    kernel_dir: impl AsRef<Path>,
) -> Result<Vec<(String, KernelHandle)>, Box<dyn std::error::Error>> {
    println!("🔍 Scanning for kernels in: {}", kernel_dir.as_ref().display());

    // Load kernels and update global registry in one operation
    let loaded = KernelRegistry::load_from_directory(&kernel_dir)?;

    Ok(loaded)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kernel_registry() {
        // Try to load kernels from the target/kernel-libs directory
        if let Ok(_loaded) = register_all_kernels_from_directory("../../target/kernel-libs") {
            // If kernels were loaded, test that we can retrieve them
            let handle = get_kernel("vector_add");
            if handle.is_ok() {
                println!("✅ Successfully retrieved vector_add kernel handle");
            } else {
                println!("ℹ️  No vector_add kernel loaded yet (this is OK if kernels haven't been compiled)");
            }
        } else {
            println!("ℹ️  No kernel directory found (this is OK if kernels haven't been compiled)");
        }
    }
}
