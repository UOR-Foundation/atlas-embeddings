//! Utility functions for Hologram FFI
//!
//! This module contains utility functions that provide information about the library
//! and help with configuration and debugging.

use crate::{FfiError, FfiResult};
use hologram_core::ops;
use tracing::{info, Level};

/// Get the version of the hologram-ffi library
pub fn get_version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

/// Get the phase of a default executor (for testing)
pub fn get_executor_phase() -> u16 {
    // Create a temporary executor to test the functionality
    match hologram_core::Executor::new() {
        Ok(executor) => executor.phase(),
        Err(_) => 0, // Return 0 if executor creation fails
    }
}

/// Advance the phase of a default executor (for testing)
pub fn advance_executor_phase(delta: u16) {
    // Create a temporary executor to test the functionality
    if let Ok(mut executor) = hologram_core::Executor::new() {
        let _ = executor.advance_phase(delta);
    }
}

// ============================================================================
// Mathematical Operations
// ============================================================================

/// Vector addition operation
pub fn vector_add_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(b) = exec.allocate::<f32>(len as usize) {
                if let Ok(mut c) = exec.allocate::<f32>(len as usize) {
                    let _ = ops::math::vector_add(&mut exec, &a, &b, &mut c, len as usize);
                }
            }
        }
    }
}

/// Vector subtraction operation
pub fn vector_sub_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(b) = exec.allocate::<f32>(len as usize) {
                if let Ok(mut c) = exec.allocate::<f32>(len as usize) {
                    let _ = ops::math::vector_sub(&mut exec, &a, &b, &mut c, len as usize);
                }
            }
        }
    }
}

/// Vector multiplication operation
pub fn vector_mul_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(b) = exec.allocate::<f32>(len as usize) {
                if let Ok(mut c) = exec.allocate::<f32>(len as usize) {
                    let _ = ops::math::vector_mul(&mut exec, &a, &b, &mut c, len as usize);
                }
            }
        }
    }
}

/// Vector division operation
pub fn vector_div_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(b) = exec.allocate::<f32>(len as usize) {
                if let Ok(mut c) = exec.allocate::<f32>(len as usize) {
                    let _ = ops::math::vector_div(&mut exec, &a, &b, &mut c, len as usize);
                }
            }
        }
    }
}

/// Vector absolute value operation
pub fn vector_abs_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(mut b) = exec.allocate::<f32>(len as usize) {
                let _ = ops::math::abs(&mut exec, &a, &mut b, len as usize);
            }
        }
    }
}

/// Vector negation operation
pub fn vector_neg_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(mut b) = exec.allocate::<f32>(len as usize) {
                let _ = ops::math::neg(&mut exec, &a, &mut b, len as usize);
            }
        }
    }
}

/// ReLU activation operation
pub fn vector_relu_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(mut b) = exec.allocate::<f32>(len as usize) {
                let _ = ops::math::relu(&mut exec, &a, &mut b, len as usize);
            }
        }
    }
}

// ============================================================================
// Reduction Operations
// ============================================================================

/// Sum reduction operation
pub fn reduce_sum_f32(len: u32) -> f32 {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(mut output) = exec.allocate::<f32>(1) {
                if ops::reduce::sum(&mut exec, &a, &mut output, len as usize).is_ok() {
                    // For now, return 0.0 since we can't easily extract the result
                    // In a real implementation, we'd need to copy from the output buffer
                    return 0.0;
                }
            }
        }
    }
    0.0
}

/// Maximum reduction operation
pub fn reduce_max_f32(len: u32) -> f32 {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(mut output) = exec.allocate::<f32>(1) {
                if ops::reduce::max(&mut exec, &a, &mut output, len as usize).is_ok() {
                    // For now, return 0.0 since we can't easily extract the result
                    return 0.0;
                }
            }
        }
    }
    0.0
}

/// Minimum reduction operation
pub fn reduce_min_f32(len: u32) -> f32 {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(mut output) = exec.allocate::<f32>(1) {
                if ops::reduce::min(&mut exec, &a, &mut output, len as usize).is_ok() {
                    // For now, return 0.0 since we can't easily extract the result
                    return 0.0;
                }
            }
        }
    }
    0.0
}

// ============================================================================
// Activation Functions
// ============================================================================

/// Sigmoid activation operation
pub fn sigmoid_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(mut b) = exec.allocate::<f32>(len as usize) {
                let _ = ops::activation::sigmoid(&mut exec, &a, &mut b, len as usize);
            }
        }
    }
}

/// Tanh activation operation
pub fn tanh_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(mut b) = exec.allocate::<f32>(len as usize) {
                let _ = ops::activation::tanh(&mut exec, &a, &mut b, len as usize);
            }
        }
    }
}

/// Softmax activation operation
pub fn softmax_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(mut b) = exec.allocate::<f32>(len as usize) {
                let _ = ops::activation::softmax(&mut exec, &a, &mut b, len as usize);
            }
        }
    }
}

/// Set the logging level for the library
#[uniffi::export]
pub fn set_log_level(level: &str) -> FfiResult<()> {
    let log_level = match level.to_lowercase().as_str() {
        "trace" => Level::TRACE,
        "debug" => Level::DEBUG,
        "info" => Level::INFO,
        "warn" => Level::WARN,
        "error" => Level::ERROR,
        _ => {
            return Err(FfiError::InvalidParameter {
                message: format!(
                    "Invalid log level: {}. Valid levels are: trace, debug, info, warn, error",
                    level
                ),
            });
        }
    };

    // Initialize tracing with the specified level
    tracing_subscriber::fmt().with_max_level(log_level).init();

    info!("Log level set to: {}", level);
    Ok(())
}

/// Check if Atlas runtime is available
#[uniffi::export]
pub fn is_atlas_available() -> FfiResult<bool> {
    // Try to create an executor to test Atlas availability
    match hologram_core::Executor::new() {
        Ok(_) => Ok(true),
        Err(_) => Ok(false),
    }
}
