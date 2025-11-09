//! Loss function wrappers for FFI
//!
//! Provides handle-based API for loss functions.
//! Note: Output buffers must have at least 3 elements for internal temporaries.

use crate::handles::{lock_registry, BUFFER_REGISTRY, EXECUTOR_REGISTRY};
use hologram_core::ops::loss;

/// Mean Squared Error loss
///
/// Computes MSE = mean((pred - target)²)
///
/// # Important
///
/// The output buffer must have at least 3 elements for internal temporaries.
/// The result will be in output[0].
///
/// # Returns
///
/// The MSE loss value (also stored in output[0])
pub fn mse_loss_f32(executor_handle: u64, pred_handle: u64, target_handle: u64, output_handle: u64, len: u32) -> f32 {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let pred_ptr = buf_registry
        .get(&pred_handle)
        .unwrap_or_else(|| panic!("Prediction buffer not found")) as *const _;
    let target_ptr = buf_registry
        .get(&target_handle)
        .unwrap_or_else(|| panic!("Target buffer not found")) as *const _;
    let output_ptr = buf_registry
        .get_mut(&output_handle)
        .unwrap_or_else(|| panic!("Output buffer not found")) as *mut _;

    unsafe {
        let pred = &*pred_ptr;
        let target = &*target_ptr;
        let output = &mut *output_ptr;

        loss::mse(executor, pred, target, output, len as usize).expect("mse_loss failed");

        // Read result from output[0]
        let result_vec = output.to_vec(executor).expect("Failed to read result");
        result_vec[0]
    }
}

/// Cross Entropy loss
///
/// Computes CE = -mean(target * log(pred))
///
/// # Important
///
/// The output buffer must have at least 3 elements for internal temporaries.
/// The result will be in output[0].
///
/// # Returns
///
/// The cross entropy loss value (also stored in output[0])
pub fn cross_entropy_loss_f32(
    executor_handle: u64,
    pred_handle: u64,
    target_handle: u64,
    output_handle: u64,
    len: u32,
) -> f32 {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let pred_ptr = buf_registry
        .get(&pred_handle)
        .unwrap_or_else(|| panic!("Prediction buffer not found")) as *const _;
    let target_ptr = buf_registry
        .get(&target_handle)
        .unwrap_or_else(|| panic!("Target buffer not found")) as *const _;
    let output_ptr = buf_registry
        .get_mut(&output_handle)
        .unwrap_or_else(|| panic!("Output buffer not found")) as *mut _;

    unsafe {
        let pred = &*pred_ptr;
        let target = &*target_ptr;
        let output = &mut *output_ptr;

        loss::cross_entropy(executor, pred, target, output, len as usize).expect("cross_entropy_loss failed");

        // Read result from output[0]
        let result_vec = output.to_vec(executor).expect("Failed to read result");
        result_vec[0]
    }
}

/// Binary Cross Entropy loss
///
/// Computes BCE = -mean(target * log(pred) + (1 - target) * log(1 - pred))
///
/// # Important
///
/// The output buffer must have at least 3 elements for internal temporaries.
/// The result will be in output[0].
///
/// # Returns
///
/// The binary cross entropy loss value (also stored in output[0])
pub fn binary_cross_entropy_loss_f32(
    executor_handle: u64,
    pred_handle: u64,
    target_handle: u64,
    output_handle: u64,
    len: u32,
) -> f32 {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let pred_ptr = buf_registry
        .get(&pred_handle)
        .unwrap_or_else(|| panic!("Prediction buffer not found")) as *const _;
    let target_ptr = buf_registry
        .get(&target_handle)
        .unwrap_or_else(|| panic!("Target buffer not found")) as *const _;
    let output_ptr = buf_registry
        .get_mut(&output_handle)
        .unwrap_or_else(|| panic!("Output buffer not found")) as *mut _;

    unsafe {
        let pred = &*pred_ptr;
        let target = &*target_ptr;
        let output = &mut *output_ptr;

        loss::binary_cross_entropy(executor, pred, target, output, len as usize)
            .expect("binary_cross_entropy_loss failed");

        // Read result from output[0]
        let result_vec = output.to_vec(executor).expect("Failed to read result");
        result_vec[0]
    }
}
