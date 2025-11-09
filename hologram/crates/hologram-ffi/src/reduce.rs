//! Reduction operation wrappers for FFI
//!
//! Provides handle-based API for reduction operations.
//! Note: Output buffers must have at least 3 elements for internal temporaries.

use crate::handles::{lock_registry, BUFFER_REGISTRY, EXECUTOR_REGISTRY};
use hologram_core::ops::reduce;

/// Sum reduction: output[0] = sum(input)
///
/// # Important
///
/// The output buffer must have at least 3 elements for internal temporaries.
/// The result will be in output[0].
///
/// # Returns
///
/// The sum value (also stored in output[0])
pub fn reduce_sum_f32(executor_handle: u64, input_handle: u64, output_handle: u64, len: u32) -> f32 {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let input_ptr = buf_registry
        .get(&input_handle)
        .unwrap_or_else(|| panic!("Input buffer not found")) as *const _;
    let output_ptr = buf_registry
        .get_mut(&output_handle)
        .unwrap_or_else(|| panic!("Output buffer not found")) as *mut _;

    unsafe {
        let input = &*input_ptr;
        let output = &mut *output_ptr;

        reduce::sum(executor, input, output, len as usize).expect("reduce_sum failed");

        // Read result from output[0]
        let result_vec = output.to_vec(executor).expect("Failed to read result");
        result_vec[0]
    }
}

/// Min reduction: output[0] = min(input)
///
/// # Important
///
/// The output buffer must have at least 3 elements for internal temporaries.
/// The result will be in output[0].
///
/// # Returns
///
/// The minimum value (also stored in output[0])
pub fn reduce_min_f32(executor_handle: u64, input_handle: u64, output_handle: u64, len: u32) -> f32 {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let input_ptr = buf_registry
        .get(&input_handle)
        .unwrap_or_else(|| panic!("Input buffer not found")) as *const _;
    let output_ptr = buf_registry
        .get_mut(&output_handle)
        .unwrap_or_else(|| panic!("Output buffer not found")) as *mut _;

    unsafe {
        let input = &*input_ptr;
        let output = &mut *output_ptr;

        reduce::min(executor, input, output, len as usize).expect("reduce_min failed");

        // Read result from output[0]
        let result_vec = output.to_vec(executor).expect("Failed to read result");
        result_vec[0]
    }
}

/// Max reduction: output[0] = max(input)
///
/// # Important
///
/// The output buffer must have at least 3 elements for internal temporaries.
/// The result will be in output[0].
///
/// # Returns
///
/// The maximum value (also stored in output[0])
pub fn reduce_max_f32(executor_handle: u64, input_handle: u64, output_handle: u64, len: u32) -> f32 {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let input_ptr = buf_registry
        .get(&input_handle)
        .unwrap_or_else(|| panic!("Input buffer not found")) as *const _;
    let output_ptr = buf_registry
        .get_mut(&output_handle)
        .unwrap_or_else(|| panic!("Output buffer not found")) as *mut _;

    unsafe {
        let input = &*input_ptr;
        let output = &mut *output_ptr;

        reduce::max(executor, input, output, len as usize).expect("reduce_max failed");

        // Read result from output[0]
        let result_vec = output.to_vec(executor).expect("Failed to read result");
        result_vec[0]
    }
}
