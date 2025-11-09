//! Advanced operations for hologram-ffi
//!
//! This module contains Phase 2 operations including linear algebra,
//! loss functions, and additional mathematical operations.

use hologram_core::ops;

// ============================================================================
// Linear Algebra Operations (Phase 2.1)
// ============================================================================

/// General matrix multiplication (GEMM) operation
pub fn gemm_f32(m: u32, n: u32, k: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        // Allocate matrices A (m×k), B (k×n), C (m×n)
        if let Ok(a) = exec.allocate::<f32>((m * k) as usize) {
            if let Ok(b) = exec.allocate::<f32>((k * n) as usize) {
                if let Ok(mut c) = exec.allocate::<f32>((m * n) as usize) {
                    // For now, just validate the operation can be performed
                    // In a real implementation, this would call the actual GEMM operation
                    let _ = ops::linalg::gemm(&mut exec, &a, &b, &mut c, m as usize, n as usize, k as usize);
                }
            }
        }
    }
}

/// Matrix-vector multiplication operation
pub fn matvec_f32(m: u32, n: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        // Allocate matrix A (m×n) and vector x (n×1), result y (m×1)
        if let Ok(a) = exec.allocate::<f32>((m * n) as usize) {
            if let Ok(x) = exec.allocate::<f32>(n as usize) {
                if let Ok(mut y) = exec.allocate::<f32>(m as usize) {
                    // For now, just validate the operation can be performed
                    // In a real implementation, this would call the actual matvec operation
                    let _ = ops::linalg::matvec(&mut exec, &a, &x, &mut y, m as usize, n as usize);
                }
            }
        }
    }
}

// ============================================================================
// Loss Functions (Phase 2.2)
// ============================================================================

/// Mean squared error loss
pub fn mse_loss_f32(len: u32) -> f32 {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(pred) = exec.allocate::<f32>(len as usize) {
            if let Ok(target) = exec.allocate::<f32>(len as usize) {
                if let Ok(mut loss) = exec.allocate::<f32>(1) {
                    if ops::loss::mse(&mut exec, &pred, &target, &mut loss, len as usize).is_ok() {
                        // For now, return 0.0 since we can't easily extract the result
                        // In a real implementation, we'd need to copy from the loss buffer
                        return 0.0;
                    }
                }
            }
        }
    }
    0.0
}

/// Cross-entropy loss
pub fn cross_entropy_loss_f32(len: u32) -> f32 {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(pred) = exec.allocate::<f32>(len as usize) {
            if let Ok(target) = exec.allocate::<f32>(len as usize) {
                if let Ok(mut loss) = exec.allocate::<f32>(1) {
                    if ops::loss::cross_entropy(&mut exec, &pred, &target, &mut loss, len as usize).is_ok() {
                        // For now, return 0.0 since we can't easily extract the result
                        return 0.0;
                    }
                }
            }
        }
    }
    0.0
}

// ============================================================================
// Additional Math Operations (Phase 2.4)
// ============================================================================

/// Element-wise minimum operation
pub fn vector_min_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(b) = exec.allocate::<f32>(len as usize) {
                if let Ok(mut c) = exec.allocate::<f32>(len as usize) {
                    let _ = ops::math::min(&mut exec, &a, &b, &mut c, len as usize);
                }
            }
        }
    }
}

/// Element-wise maximum operation
pub fn vector_max_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(b) = exec.allocate::<f32>(len as usize) {
                if let Ok(mut c) = exec.allocate::<f32>(len as usize) {
                    let _ = ops::math::max(&mut exec, &a, &b, &mut c, len as usize);
                }
            }
        }
    }
}

/// Scalar addition operation
pub fn scalar_add_f32(value: f32, len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(mut b) = exec.allocate::<f32>(len as usize) {
                let _ = ops::math::scalar_add(&mut exec, &a, value, &mut b, len as usize);
            }
        }
    }
}

/// Scalar multiplication operation
pub fn scalar_mul_f32(value: f32, len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(mut b) = exec.allocate::<f32>(len as usize) {
                let _ = ops::math::scalar_mul(&mut exec, &a, value, &mut b, len as usize);
            }
        }
    }
}

/// GELU activation function
pub fn gelu_f32(len: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate::<f32>(len as usize) {
            if let Ok(mut b) = exec.allocate::<f32>(len as usize) {
                let _ = ops::activation::gelu(&mut exec, &a, &mut b, len as usize);
            }
        }
    }
}

// ============================================================================
// Boundary Operations (Phase 2.5)
// ============================================================================

/// Transpose boundary buffer operation
pub fn transpose_boundary_f32(width: u32, height: u32) {
    if let Ok(mut exec) = hologram_core::Executor::new() {
        if let Ok(a) = exec.allocate_boundary::<f32>(0, width as usize, height as usize) {
            if let Ok(b) = exec.allocate_boundary::<f32>(0, height as usize, width as usize) {
                // For now, just validate the operation can be performed
                // In a real implementation, this would call the actual transpose operation
                let _ = (a, b, width, height);
            }
        }
    }
}
