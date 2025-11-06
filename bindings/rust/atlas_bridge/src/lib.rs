//! Atlas Bridge Context API v0.5 - Rust Bindings
//!
//! This crate provides safe Rust bindings to the Atlas Bridge Context API.
//!
//! # v0.5 Features
//! - BLAS-accelerated matrix-vector operations
//! - Real artifact integration (lift_forms.hex, P_299_matrix.bin, co1_gates.txt)
//! - Safe Rust API wrapping the C library
//!
//! # Example
//! ```no_run
//! use atlas_bridge::{AtlasContext, AtlasConfig};
//!
//! let config = AtlasConfig::default();
//! let ctx = AtlasContext::new(config).expect("Failed to create context");
//! 
//! // Load artifacts
//! ctx.load_lift_forms("lift_forms.hex").ok();
//! ctx.load_p299_matrix("P_299_matrix.bin").ok();
//! ctx.load_co1_gates("co1_gates.txt").ok();
//!
//! // Perform operations
//! let mut state = vec![0.0; ctx.block_size()];
//! ctx.apply_p_class(&mut state).expect("Failed to apply P_class");
//! ```
//!
//! # Legacy API
//! ⚠️ The legacy non-context API has been deprecated in v0.5 and will be removed in v0.6.
//! Please migrate all code to use the context-based API.

use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_double, c_int, c_uint};
use std::path::Path;
use std::ptr;

mod ffi;
pub use ffi::*;

/// Atlas Bridge Context (opaque handle)
pub struct AtlasContext {
    ctx: *mut AtlasBridgeContext,
}

/// Configuration for Atlas Bridge Context
#[derive(Debug, Clone)]
pub struct AtlasConfig {
    pub flags: u32,
    pub block_size: u32,
    pub n_qubits: u32,
    pub twirl_gens: u32,
    pub epsilon: f64,
    pub n_qbits: u32,
}

impl Default for AtlasConfig {
    fn default() -> Self {
        Self {
            flags: 0,
            block_size: 12288,
            n_qubits: 8,
            twirl_gens: 16,
            epsilon: 1e-10,
            n_qbits: 8,
        }
    }
}

impl AtlasContext {
    /// Create a new Atlas Bridge context with the given configuration
    pub fn new(config: AtlasConfig) -> Result<Self, String> {
        let cfg = AtlasContextConfig {
            flags: config.flags,
            block_size: config.block_size,
            n_qubits: config.n_qubits,
            twirl_gens: config.twirl_gens,
            epsilon: config.epsilon,
            n_qbits: config.n_qbits,
        };

        unsafe {
            let ctx = atlas_ctx_new(&cfg as *const _);
            if ctx.is_null() {
                Err("Failed to create Atlas context".to_string())
            } else {
                Ok(Self { ctx })
            }
        }
    }

    /// Create a new context with default configuration
    pub fn new_default() -> Result<Self, String> {
        Self::new(AtlasConfig::default())
    }

    /// Load lift forms from hex file
    pub fn load_lift_forms<P: AsRef<Path>>(&self, path: P) -> Result<(), String> {
        let path_str = path
            .as_ref()
            .to_str()
            .ok_or_else(|| "Invalid path".to_string())?;
        let c_path = CString::new(path_str).map_err(|_| "Invalid path string".to_string())?;

        unsafe {
            let result = atlas_ctx_load_lift_forms(self.ctx, c_path.as_ptr());
            if result == 0 {
                Ok(())
            } else {
                Err("Failed to load lift forms".to_string())
            }
        }
    }

    /// Load P_299 matrix from binary file (optional)
    pub fn load_p299_matrix<P: AsRef<Path>>(&self, path: P) -> Result<(), String> {
        let path_str = path
            .as_ref()
            .to_str()
            .ok_or_else(|| "Invalid path".to_string())?;
        let c_path = CString::new(path_str).map_err(|_| "Invalid path string".to_string())?;

        unsafe {
            let result = atlas_ctx_load_p299_matrix(self.ctx, c_path.as_ptr());
            if result == 0 {
                Ok(())
            } else {
                Err("Failed to load P_299 matrix (will use fallback)".to_string())
            }
        }
    }

    /// Load Co1 gates from text file (optional)
    pub fn load_co1_gates<P: AsRef<Path>>(&self, path: P) -> Result<(), String> {
        let path_str = path
            .as_ref()
            .to_str()
            .ok_or_else(|| "Invalid path".to_string())?;
        let c_path = CString::new(path_str).map_err(|_| "Invalid path string".to_string())?;

        unsafe {
            let result = atlas_ctx_load_co1_gates(self.ctx, c_path.as_ptr());
            if result == 0 {
                Ok(())
            } else {
                Err("Failed to load Co1 gates".to_string())
            }
        }
    }

    /// Apply P_class projector
    pub fn apply_p_class(&self, state: &mut [f64]) -> Result<(), String> {
        if state.len() != self.block_size() {
            return Err(format!(
                "State vector size mismatch: expected {}, got {}",
                self.block_size(),
                state.len()
            ));
        }

        unsafe {
            let result = atlas_ctx_apply_p_class(self.ctx, state.as_mut_ptr());
            if result == 0 {
                Ok(())
            } else {
                Err("Failed to apply P_class".to_string())
            }
        }
    }

    /// Apply P_299 projector
    pub fn apply_p_299(&self, state: &mut [f64]) -> Result<(), String> {
        if state.len() != self.block_size() {
            return Err(format!(
                "State vector size mismatch: expected {}, got {}",
                self.block_size(),
                state.len()
            ));
        }

        unsafe {
            let result = atlas_ctx_apply_p_299(self.ctx, state.as_mut_ptr());
            if result == 0 {
                Ok(())
            } else {
                Err("Failed to apply P_299".to_string())
            }
        }
    }

    /// Get block size for this context
    pub fn block_size(&self) -> usize {
        unsafe { atlas_ctx_get_block_size(self.ctx) as usize }
    }

    /// Get number of qubits for this context
    pub fn n_qubits(&self) -> usize {
        unsafe { atlas_ctx_get_n_qubits(self.ctx) as usize }
    }

    /// Emit JSON certificate to file
    pub fn emit_certificate<P: AsRef<Path>>(&self, path: P, mode: &str) -> Result<(), String> {
        let path_str = path
            .as_ref()
            .to_str()
            .ok_or_else(|| "Invalid path".to_string())?;
        let c_path = CString::new(path_str).map_err(|_| "Invalid path string".to_string())?;
        let c_mode = CString::new(mode).map_err(|_| "Invalid mode string".to_string())?;

        unsafe {
            let result = atlas_ctx_emit_certificate(self.ctx, c_path.as_ptr(), c_mode.as_ptr());
            if result == 0 {
                Ok(())
            } else {
                Err("Failed to emit certificate".to_string())
            }
        }
    }

    /// Get library version
    pub fn version() -> &'static str {
        unsafe {
            let c_str = atlas_ctx_version();
            CStr::from_ptr(c_str).to_str().unwrap_or("unknown")
        }
    }
}

impl Drop for AtlasContext {
    fn drop(&mut self) {
        unsafe {
            atlas_ctx_free(self.ctx);
        }
    }
}

// Ensure AtlasContext is Send (not Sync, as the C library may not be thread-safe)
unsafe impl Send for AtlasContext {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_context() {
        let ctx = AtlasContext::new_default();
        assert!(ctx.is_ok());
    }

    #[test]
    fn test_version() {
        let version = AtlasContext::version();
        assert!(version.starts_with("0."));
    }
}
