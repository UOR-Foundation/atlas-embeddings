//! Activation function wrappers for FFI
//!
//! Provides handle-based API for neural network activation functions.

use crate::handles::{lock_registry, BUFFER_REGISTRY, EXECUTOR_REGISTRY};
use hologram_core::ops::activation;

/// Sigmoid activation: output = 1 / (1 + exp(-input))
pub fn sigmoid_f32(executor_handle: u64, input_handle: u64, output_handle: u64, len: u32) {
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

        activation::sigmoid(executor, input, output, len as usize).expect("sigmoid failed");
    }
}

/// Hyperbolic tangent activation: output = tanh(input)
pub fn tanh_f32(executor_handle: u64, input_handle: u64, output_handle: u64, len: u32) {
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

        activation::tanh(executor, input, output, len as usize).expect("tanh failed");
    }
}

/// GELU activation: output = x * 0.5 * (1 + tanh(sqrt(2/π) * (x + 0.044715 * x³)))
pub fn gelu_f32(executor_handle: u64, input_handle: u64, output_handle: u64, len: u32) {
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

        activation::gelu(executor, input, output, len as usize).expect("gelu failed");
    }
}

/// Softmax activation: output[i] = exp(input[i]) / sum(exp(input))
pub fn softmax_f32(executor_handle: u64, input_handle: u64, output_handle: u64, len: u32) {
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

        activation::softmax(executor, input, output, len as usize).expect("softmax failed");
    }
}
