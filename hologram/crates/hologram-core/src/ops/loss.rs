//! Loss Functions (Not Yet Implemented)
//!
//! This module will provide loss functions for neural network training.
//! These require complex ISA Program composition and are not yet implemented.
//!
//! # Planned Functions
//!
//! - **MSE** - Mean Squared Error: `(1/N) * Σ (pred[i] - target[i])²`
//! - **Cross Entropy** - `-( 1/N) * Σ target[i] * log(pred[i])`
//! - **Binary Cross Entropy** - `-(1/N) * Σ [target * log(pred) + (1-target) * log(1-pred)]`
//!
//! # Example (when implemented)
//!
//! ```text
//! use hologram_core::{Executor, ops::loss};
//!
//! let mut exec = Executor::new()?;
//! let predictions = exec.allocate::<f32>(100)?;
//! let targets = exec.allocate::<f32>(100)?;
//! let mut loss = exec.allocate::<f32>(3)?; // Need 3 elements for temporaries
//!
//! loss::mse(&mut exec, &predictions, &targets, &mut loss, 100)?;
//! println!("Loss: {}", loss.to_vec(&exec)?[0]);
//! ```

use crate::buffer::Buffer;
use crate::error::{Error, Result};
use crate::executor::Executor;
use hologram_backends::program_cache::{ProgramCache, ProgramKey};

// ============================================================================
// Program Caches (Thread-Safe, Lock-Free After First Access)
// ============================================================================

static MSE_DIV_CACHE: ProgramCache = ProgramCache::new();
static CROSS_ENTROPY_LOG_CACHE: ProgramCache = ProgramCache::new();
static CROSS_ENTROPY_FINAL_CACHE: ProgramCache = ProgramCache::new();
static BCE_LOG_PRED_CACHE: ProgramCache = ProgramCache::new();
static BCE_SUB_FROM_ONE_PRED_CACHE: ProgramCache = ProgramCache::new();
static BCE_LOG_ONE_MINUS_PRED_CACHE: ProgramCache = ProgramCache::new();
static BCE_SUB_FROM_ONE_TARGET_CACHE: ProgramCache = ProgramCache::new();
static BCE_FINAL_CACHE: ProgramCache = ProgramCache::new();

// ============================================================================
// Loss Functions (Not Yet Implemented)
// ============================================================================

/// Mean Squared Error: loss = (1/N) * Σ (pred[i] - target[i])²
///
/// **Status**: Not yet implemented. Requires ISA Program composition.
///
/// # Implementation Plan
///
/// Requires chaining these operations in an ISA Program:
/// 1. Element-wise subtraction: `diff[i] = pred[i] - target[i]`
/// 2. Element-wise multiplication: `squared[i] = diff[i] * diff[i]`
/// 3. Reduction sum: `sum = Σ squared[i]`
/// 4. Scalar division: `mse = sum / N`
///
/// # Arguments
///
/// * `exec` - Executor for program execution
/// * `predictions` - Predicted values buffer with N elements
/// * `targets` - Target values buffer with N elements
/// * `output` - Output buffer (needs at least 3 elements for temporaries)
/// * `n` - Number of elements to process
///
/// # Returns
///
/// Will store loss value in `output[0]` when implemented
pub fn mse<T: bytemuck::Pod>(
    exec: &mut Executor,
    predictions: &Buffer<T>,
    targets: &Buffer<T>,
    output: &mut Buffer<T>,
    n: usize,
) -> Result<()> {
    // Validate inputs
    if predictions.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Predictions buffer too small: len={}, need={}",
            predictions.len(),
            n
        )));
    }
    if targets.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Targets buffer too small: len={}, need={}",
            targets.len(),
            n
        )));
    }
    if output.len() < 3 {
        return Err(Error::InvalidOperation(
            "Output buffer needs at least 3 elements for temporaries".into(),
        ));
    }

    // Allocate temporary buffers for intermediate results
    let mut diff = exec.allocate::<T>(n)?;
    let mut squared = exec.allocate::<T>(n)?;

    // Step 1: diff[i] = predictions[i] - targets[i]
    crate::ops::math::vector_sub(exec, predictions, targets, &mut diff, n)?;

    // Step 2: squared[i] = diff[i] * diff[i]
    crate::ops::math::vector_mul(exec, &diff, &diff, &mut squared, n)?;

    // Step 3: sum = Σ squared[i]
    crate::ops::reduce::sum(exec, &squared, output, n)?;

    // Step 4: mse = sum / N
    // Use scalar division via ISA program
    let class_output = output.class_index();
    let handle_output = exec.get_buffer_handle(class_output)?.id();

    let ty = crate::isa_builder::type_from_rust_type::<T>();

    // Load N value as immediate
    let n_bits = if std::any::type_name::<T>() == "f32" {
        (n as f32).to_bits() as u64
    } else if std::any::type_name::<T>() == "f64" {
        (n as f64).to_bits()
    } else {
        return Err(Error::InvalidOperation("MSE only supports f32 and f64 types".into()));
    };

    // Build cache key
    let cache_key = ProgramKey::new("mse_div", vec![handle_output, n as u64, ty as u64, n_bits]);

    // Get or create cached program
    let program = MSE_DIV_CACHE.get_or_create(&cache_key, || {
        let mut prog = hologram_backends::Program::new();

        // Load sum value (already in output[0])
        prog.instructions.push(hologram_backends::Instruction::LDG {
            ty,
            dst: hologram_backends::Register::new(1),
            addr: hologram_backends::Address::BufferOffset {
                handle: handle_output,
                offset: 0,
            },
        });

        // Load N value as immediate
        prog.instructions.push(hologram_backends::Instruction::MOV_IMM {
            ty,
            dst: hologram_backends::Register::new(2),
            value: n_bits,
        });

        // Divide: r3 = r1 / r2
        prog.instructions.push(hologram_backends::Instruction::DIV {
            ty,
            dst: hologram_backends::Register::new(3),
            src1: hologram_backends::Register::new(1),
            src2: hologram_backends::Register::new(2),
        });

        // Store result back to output[0]
        prog.instructions.push(hologram_backends::Instruction::STG {
            ty,
            src: hologram_backends::Register::new(3),
            addr: hologram_backends::Address::BufferOffset {
                handle: handle_output,
                offset: 0,
            },
        });

        prog
    });

    let config = hologram_backends::LaunchConfig::default();
    exec.backend
        .write()
        .execute_program(&program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    Ok(())
}

/// Cross Entropy Loss: loss = -(1/N) * Σ target[i] * log(pred[i])
///
/// **Status**: Not yet implemented. Requires ISA Program composition.
///
/// # Implementation Plan
///
/// Requires chaining these operations in an ISA Program:
/// 1. Element-wise log: `log_pred[i] = log(pred[i])`
/// 2. Element-wise multiplication: `product[i] = target[i] * log_pred[i]`
/// 3. Reduction sum: `sum = Σ product[i]`
/// 4. Scalar negation and division: `ce = -sum / N`
///
/// # Arguments
///
/// * `exec` - Executor for program execution
/// * `predictions` - Predicted probabilities buffer with N elements
/// * `targets` - Target labels buffer with N elements
/// * `output` - Output buffer (needs at least 3 elements for temporaries)
/// * `n` - Number of elements to process
///
/// # Returns
///
/// Will store loss value in `output[0]` when implemented
pub fn cross_entropy<T: bytemuck::Pod>(
    exec: &mut Executor,
    predictions: &Buffer<T>,
    targets: &Buffer<T>,
    output: &mut Buffer<T>,
    n: usize,
) -> Result<()> {
    // Validate inputs
    if predictions.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Predictions buffer too small: len={}, need={}",
            predictions.len(),
            n
        )));
    }
    if targets.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Targets buffer too small: len={}, need={}",
            targets.len(),
            n
        )));
    }
    if output.len() < 3 {
        return Err(Error::InvalidOperation(
            "Output buffer needs at least 3 elements for temporaries".into(),
        ));
    }

    // Allocate temporary buffers
    let log_pred = exec.allocate::<T>(n)?;
    let mut product = exec.allocate::<T>(n)?;

    // Step 1: log_pred[i] = log(predictions[i])
    let class_pred = predictions.class_index();
    let class_log_pred = log_pred.class_index();
    let handle_pred = exec.get_buffer_handle(class_pred)?.id();
    let handle_log_pred = exec.get_buffer_handle(class_log_pred)?.id();
    let ty = crate::isa_builder::type_from_rust_type::<T>();

    // Build cache key for log operation
    let cache_key = ProgramKey::new(
        "cross_entropy_log",
        vec![handle_pred, handle_log_pred, n as u64, ty as u64],
    );

    // Get or create cached program
    let log_program = CROSS_ENTROPY_LOG_CACHE.get_or_create(&cache_key, || {
        crate::isa_builder::build_elementwise_unary_op(handle_pred, handle_log_pred, n, ty, |dst, src| {
            hologram_backends::Instruction::LOG { ty, dst, src }
        })
        .expect("Failed to build cross entropy log program")
    });

    let config = hologram_backends::LaunchConfig::default();
    exec.backend
        .write()
        .execute_program(&log_program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    // Step 2: product[i] = targets[i] * log_pred[i]
    crate::ops::math::vector_mul(exec, targets, &log_pred, &mut product, n)?;

    // Step 3: sum = Σ product[i]
    crate::ops::reduce::sum(exec, &product, output, n)?;

    // Step 4: ce = -sum / N
    let class_output = output.class_index();
    let handle_output = exec.get_buffer_handle(class_output)?.id();

    // Load N as immediate
    let n_bits = if std::any::type_name::<T>() == "f32" {
        (n as f32).to_bits() as u64
    } else if std::any::type_name::<T>() == "f64" {
        (n as f64).to_bits()
    } else {
        return Err(Error::InvalidOperation(
            "Cross entropy only supports f32 and f64 types".into(),
        ));
    };

    // Build cache key
    let cache_key = ProgramKey::new("cross_entropy_final", vec![handle_output, n as u64, ty as u64, n_bits]);

    // Get or create cached program
    let program = CROSS_ENTROPY_FINAL_CACHE.get_or_create(&cache_key, || {
        let mut prog = hologram_backends::Program::new();

        // Load sum
        prog.instructions.push(hologram_backends::Instruction::LDG {
            ty,
            dst: hologram_backends::Register::new(1),
            addr: hologram_backends::Address::BufferOffset {
                handle: handle_output,
                offset: 0,
            },
        });

        // Load N as immediate
        prog.instructions.push(hologram_backends::Instruction::MOV_IMM {
            ty,
            dst: hologram_backends::Register::new(2),
            value: n_bits,
        });

        // Divide: r3 = r1 / r2
        prog.instructions.push(hologram_backends::Instruction::DIV {
            ty,
            dst: hologram_backends::Register::new(3),
            src1: hologram_backends::Register::new(1),
            src2: hologram_backends::Register::new(2),
        });

        // Negate: r4 = -r3
        prog.instructions.push(hologram_backends::Instruction::NEG {
            ty,
            dst: hologram_backends::Register::new(4),
            src: hologram_backends::Register::new(3),
        });

        // Store result
        prog.instructions.push(hologram_backends::Instruction::STG {
            ty,
            src: hologram_backends::Register::new(4),
            addr: hologram_backends::Address::BufferOffset {
                handle: handle_output,
                offset: 0,
            },
        });

        prog
    });

    exec.backend
        .write()
        .execute_program(&program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    Ok(())
}

/// Binary Cross Entropy Loss: loss = -(1/N) * Σ [target * log(pred) + (1-target) * log(1-pred)]
///
/// **Status**: Not yet implemented. Requires ISA Program composition.
///
/// # Implementation Plan
///
/// Requires chaining these operations in an ISA Program:
/// 1. Element-wise log: `log_pred[i] = log(pred[i])`
/// 2. Element-wise multiplication: `term1[i] = target[i] * log_pred[i]`
/// 3. Element-wise subtraction: `one_minus_pred[i] = 1 - pred[i]`
/// 4. Element-wise log: `log_one_minus_pred[i] = log(one_minus_pred[i])`
/// 5. Element-wise subtraction: `one_minus_target[i] = 1 - target[i]`
/// 6. Element-wise multiplication: `term2[i] = one_minus_target[i] * log_one_minus_pred[i]`
/// 7. Element-wise addition: `sum_terms[i] = term1[i] + term2[i]`
/// 8. Reduction sum: `sum = Σ sum_terms[i]`
/// 9. Scalar negation and division: `bce = -sum / N`
///
/// # Arguments
///
/// * `exec` - Executor for program execution
/// * `predictions` - Predicted probabilities buffer with N elements
/// * `targets` - Target binary labels buffer with N elements (0 or 1)
/// * `output` - Output buffer (needs at least 3 elements for temporaries)
/// * `n` - Number of elements to process
///
/// # Returns
///
/// Will store loss value in `output[0]` when implemented
pub fn binary_cross_entropy<T: bytemuck::Pod>(
    exec: &mut Executor,
    predictions: &Buffer<T>,
    targets: &Buffer<T>,
    output: &mut Buffer<T>,
    n: usize,
) -> Result<()> {
    // Validate inputs
    if predictions.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Predictions buffer too small: len={}, need={}",
            predictions.len(),
            n
        )));
    }
    if targets.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Targets buffer too small: len={}, need={}",
            targets.len(),
            n
        )));
    }
    if output.len() < 3 {
        return Err(Error::InvalidOperation(
            "Output buffer needs at least 3 elements for temporaries".into(),
        ));
    }

    // Allocate temporary buffers
    let log_pred = exec.allocate::<T>(n)?;
    let mut term1 = exec.allocate::<T>(n)?;
    let one_minus_pred = exec.allocate::<T>(n)?;
    let log_one_minus_pred = exec.allocate::<T>(n)?;
    let one_minus_target = exec.allocate::<T>(n)?;
    let mut term2 = exec.allocate::<T>(n)?;
    let mut sum_terms = exec.allocate::<T>(n)?;

    let ty = crate::isa_builder::type_from_rust_type::<T>();
    let config = hologram_backends::LaunchConfig::default();

    // Step 1: log_pred[i] = log(pred[i])
    let class_pred = predictions.class_index();
    let class_log_pred = log_pred.class_index();
    let handle_pred = exec.get_buffer_handle(class_pred)?.id();
    let handle_log_pred = exec.get_buffer_handle(class_log_pred)?.id();

    // Build cache key for log(pred)
    let cache_key = ProgramKey::new("bce_log_pred", vec![handle_pred, handle_log_pred, n as u64, ty as u64]);

    // Get or create cached program
    let log_program = BCE_LOG_PRED_CACHE.get_or_create(&cache_key, || {
        crate::isa_builder::build_elementwise_unary_op(handle_pred, handle_log_pred, n, ty, |dst, src| {
            hologram_backends::Instruction::LOG { ty, dst, src }
        })
        .expect("Failed to build BCE log_pred program")
    });

    exec.backend
        .write()
        .execute_program(&log_program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    // Step 2: term1[i] = target[i] * log_pred[i]
    crate::ops::math::vector_mul(exec, targets, &log_pred, &mut term1, n)?;

    // Step 3: one_minus_pred[i] = 1 - pred[i]
    let class_pred2 = predictions.class_index();
    let class_one_minus_pred = one_minus_pred.class_index();
    let handle_pred2 = exec.get_buffer_handle(class_pred2)?.id();
    let handle_one_minus_pred = exec.get_buffer_handle(class_one_minus_pred)?.id();

    let elem_size = ty.size_bytes();
    let one_bits = if std::any::type_name::<T>() == "f32" {
        1.0f32.to_bits() as u64
    } else {
        1.0f64.to_bits()
    };

    // Build cache key for 1 - pred
    let cache_key = ProgramKey::new(
        "bce_sub_from_one_pred",
        vec![handle_pred2, handle_one_minus_pred, n as u64, ty as u64, one_bits],
    );

    // Get or create cached program
    let sub_from_one_program = BCE_SUB_FROM_ONE_PRED_CACHE.get_or_create(&cache_key, || {
        let mut prog = hologram_backends::Program::new();
        for i in 0..n {
            let offset = i * elem_size;

            // Load 1.0 into r1
            prog.instructions.push(hologram_backends::Instruction::MOV_IMM {
                ty,
                dst: hologram_backends::Register::new(1),
                value: one_bits,
            });

            // Load pred[i] into r2
            prog.instructions.push(hologram_backends::Instruction::LDG {
                ty,
                dst: hologram_backends::Register::new(2),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_pred2,
                    offset,
                },
            });

            // Subtract: r3 = r1 - r2 (1 - pred[i])
            prog.instructions.push(hologram_backends::Instruction::SUB {
                ty,
                dst: hologram_backends::Register::new(3),
                src1: hologram_backends::Register::new(1),
                src2: hologram_backends::Register::new(2),
            });

            // Store to one_minus_pred[i]
            prog.instructions.push(hologram_backends::Instruction::STG {
                ty,
                src: hologram_backends::Register::new(3),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_one_minus_pred,
                    offset,
                },
            });
        }
        prog
    });

    exec.backend
        .write()
        .execute_program(&sub_from_one_program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    // Step 4: log_one_minus_pred[i] = log(one_minus_pred[i])
    let class_log_one_minus_pred = log_one_minus_pred.class_index();
    let handle_log_one_minus_pred = exec.get_buffer_handle(class_log_one_minus_pred)?.id();

    // Build cache key for log(1-pred)
    let cache_key = ProgramKey::new(
        "bce_log_one_minus_pred",
        vec![handle_one_minus_pred, handle_log_one_minus_pred, n as u64, ty as u64],
    );

    // Get or create cached program
    let log2_program = BCE_LOG_ONE_MINUS_PRED_CACHE.get_or_create(&cache_key, || {
        crate::isa_builder::build_elementwise_unary_op(
            handle_one_minus_pred,
            handle_log_one_minus_pred,
            n,
            ty,
            |dst, src| hologram_backends::Instruction::LOG { ty, dst, src },
        )
        .expect("Failed to build BCE log_one_minus_pred program")
    });

    exec.backend
        .write()
        .execute_program(&log2_program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    // Step 5: one_minus_target[i] = 1 - target[i]
    let class_target = targets.class_index();
    let class_one_minus_target = one_minus_target.class_index();
    let handle_target = exec.get_buffer_handle(class_target)?.id();
    let handle_one_minus_target = exec.get_buffer_handle(class_one_minus_target)?.id();

    // Build cache key for 1 - target
    let cache_key = ProgramKey::new(
        "bce_sub_from_one_target",
        vec![handle_target, handle_one_minus_target, n as u64, ty as u64, one_bits],
    );

    // Get or create cached program
    let sub_from_one_target_program = BCE_SUB_FROM_ONE_TARGET_CACHE.get_or_create(&cache_key, || {
        let mut prog = hologram_backends::Program::new();
        for i in 0..n {
            let offset = i * elem_size;

            // Load 1.0 into r1
            prog.instructions.push(hologram_backends::Instruction::MOV_IMM {
                ty,
                dst: hologram_backends::Register::new(1),
                value: one_bits,
            });

            // Load target[i] into r2
            prog.instructions.push(hologram_backends::Instruction::LDG {
                ty,
                dst: hologram_backends::Register::new(2),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_target,
                    offset,
                },
            });

            // Subtract: r3 = r1 - r2 (1 - target[i])
            prog.instructions.push(hologram_backends::Instruction::SUB {
                ty,
                dst: hologram_backends::Register::new(3),
                src1: hologram_backends::Register::new(1),
                src2: hologram_backends::Register::new(2),
            });

            // Store to one_minus_target[i]
            prog.instructions.push(hologram_backends::Instruction::STG {
                ty,
                src: hologram_backends::Register::new(3),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_one_minus_target,
                    offset,
                },
            });
        }
        prog
    });

    exec.backend
        .write()
        .execute_program(&sub_from_one_target_program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    // Step 6: term2[i] = one_minus_target[i] * log_one_minus_pred[i]
    crate::ops::math::vector_mul(exec, &one_minus_target, &log_one_minus_pred, &mut term2, n)?;

    // Step 7: sum_terms[i] = term1[i] + term2[i]
    crate::ops::math::vector_add(exec, &term1, &term2, &mut sum_terms, n)?;

    // Step 8: sum = Σ sum_terms[i]
    crate::ops::reduce::sum(exec, &sum_terms, output, n)?;

    // Step 9: bce = -sum / N
    let class_output = output.class_index();
    let handle_output = exec.get_buffer_handle(class_output)?.id();

    // Load N as immediate
    let n_bits = if std::any::type_name::<T>() == "f32" {
        (n as f32).to_bits() as u64
    } else if std::any::type_name::<T>() == "f64" {
        (n as f64).to_bits()
    } else {
        return Err(Error::InvalidOperation(
            "Binary cross entropy only supports f32 and f64 types".into(),
        ));
    };

    // Build cache key
    let cache_key = ProgramKey::new("bce_final", vec![handle_output, n as u64, ty as u64, n_bits]);

    // Get or create cached program
    let final_program = BCE_FINAL_CACHE.get_or_create(&cache_key, || {
        let mut prog = hologram_backends::Program::new();

        // Load sum
        prog.instructions.push(hologram_backends::Instruction::LDG {
            ty,
            dst: hologram_backends::Register::new(1),
            addr: hologram_backends::Address::BufferOffset {
                handle: handle_output,
                offset: 0,
            },
        });

        // Load N as immediate
        prog.instructions.push(hologram_backends::Instruction::MOV_IMM {
            ty,
            dst: hologram_backends::Register::new(2),
            value: n_bits,
        });

        // Divide: r3 = r1 / r2
        prog.instructions.push(hologram_backends::Instruction::DIV {
            ty,
            dst: hologram_backends::Register::new(3),
            src1: hologram_backends::Register::new(1),
            src2: hologram_backends::Register::new(2),
        });

        // Negate: r4 = -r3
        prog.instructions.push(hologram_backends::Instruction::NEG {
            ty,
            dst: hologram_backends::Register::new(4),
            src: hologram_backends::Register::new(3),
        });

        // Store result
        prog.instructions.push(hologram_backends::Instruction::STG {
            ty,
            src: hologram_backends::Register::new(4),
            addr: hologram_backends::Address::BufferOffset {
                handle: handle_output,
                offset: 0,
            },
        });

        prog
    });

    exec.backend
        .write()
        .execute_program(&final_program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mse() -> Result<()> {
        let mut exec = Executor::new()?;

        let mut predictions = exec.allocate::<f32>(100)?;
        let mut targets = exec.allocate::<f32>(100)?;
        let mut loss = exec.allocate::<f32>(3)?;

        // Setup: pred = 2.0, target = 1.0
        let pred_data = vec![2.0f32; 100];
        let target_data = vec![1.0f32; 100];

        predictions.copy_from_slice(&mut exec, &pred_data)?;
        targets.copy_from_slice(&mut exec, &target_data)?;

        mse(&mut exec, &predictions, &targets, &mut loss, 100)?;

        let result = loss.to_vec(&exec)?;
        // Expected: (2.0 - 1.0)² = 1.0
        assert!((result[0] - 1.0).abs() < 0.001);

        Ok(())
    }

    #[test]
    fn test_cross_entropy() -> Result<()> {
        let mut exec = Executor::new()?;

        let mut predictions = exec.allocate::<f32>(100)?;
        let mut targets = exec.allocate::<f32>(100)?;
        let mut loss = exec.allocate::<f32>(3)?;

        // Setup test data
        let pred_data = vec![0.7f32; 100];
        let target_data = vec![1.0f32; 100];

        predictions.copy_from_slice(&mut exec, &pred_data)?;
        targets.copy_from_slice(&mut exec, &target_data)?;

        cross_entropy(&mut exec, &predictions, &targets, &mut loss, 100)?;

        let result = loss.to_vec(&exec)?;
        // Expected: -1.0 * log(0.7) ≈ 0.357
        assert!(result[0] > 0.0);

        Ok(())
    }

    #[test]
    fn test_binary_cross_entropy() -> Result<()> {
        let mut exec = Executor::new()?;

        let mut predictions = exec.allocate::<f32>(100)?;
        let mut targets = exec.allocate::<f32>(100)?;
        let mut loss = exec.allocate::<f32>(3)?;

        // Setup test data
        let pred_data = vec![0.7f32; 100];
        let target_data = vec![1.0f32; 100];

        predictions.copy_from_slice(&mut exec, &pred_data)?;
        targets.copy_from_slice(&mut exec, &target_data)?;

        binary_cross_entropy(&mut exec, &predictions, &targets, &mut loss, 100)?;

        let result = loss.to_vec(&exec)?;
        assert!(result[0] > 0.0);

        Ok(())
    }
}
