//! Math operation wrappers for FFI
//!
//! Provides handle-based API for element-wise math operations.
//! All operations compile to canonical Sigmatics circuits under the hood.

use crate::handles::{lock_registry, BUFFER_REGISTRY, EXECUTOR_REGISTRY};
use hologram_core::ops::math;

/// Element-wise addition: c = a + b
pub fn vector_add_f32(executor_handle: u64, a_handle: u64, b_handle: u64, c_handle: u64, len: u32) {
    // Get executor
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    // Get buffers
    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Buffer A not found")) as *const _;
    let b_ptr = buf_registry
        .get(&b_handle)
        .unwrap_or_else(|| panic!("Buffer B not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Buffer C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let b = &*b_ptr;
        let c = &mut *c_ptr;

        math::vector_add(executor, a, b, c, len as usize).expect("vector_add failed");
    }
}

/// Element-wise subtraction: c = a - b
pub fn vector_sub_f32(executor_handle: u64, a_handle: u64, b_handle: u64, c_handle: u64, len: u32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Buffer A not found")) as *const _;
    let b_ptr = buf_registry
        .get(&b_handle)
        .unwrap_or_else(|| panic!("Buffer B not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Buffer C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let b = &*b_ptr;
        let c = &mut *c_ptr;

        math::vector_sub(executor, a, b, c, len as usize).expect("vector_sub failed");
    }
}

/// Element-wise multiplication: c = a * b
pub fn vector_mul_f32(executor_handle: u64, a_handle: u64, b_handle: u64, c_handle: u64, len: u32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Buffer A not found")) as *const _;
    let b_ptr = buf_registry
        .get(&b_handle)
        .unwrap_or_else(|| panic!("Buffer B not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Buffer C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let b = &*b_ptr;
        let c = &mut *c_ptr;

        math::vector_mul(executor, a, b, c, len as usize).expect("vector_mul failed");
    }
}

/// Element-wise division: c = a / b
pub fn vector_div_f32(executor_handle: u64, a_handle: u64, b_handle: u64, c_handle: u64, len: u32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Buffer A not found")) as *const _;
    let b_ptr = buf_registry
        .get(&b_handle)
        .unwrap_or_else(|| panic!("Buffer B not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Buffer C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let b = &*b_ptr;
        let c = &mut *c_ptr;

        math::vector_div(executor, a, b, c, len as usize).expect("vector_div failed");
    }
}

/// Element-wise minimum: c = min(a, b)
pub fn vector_min_f32(executor_handle: u64, a_handle: u64, b_handle: u64, c_handle: u64, len: u32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Buffer A not found")) as *const _;
    let b_ptr = buf_registry
        .get(&b_handle)
        .unwrap_or_else(|| panic!("Buffer B not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Buffer C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let b = &*b_ptr;
        let c = &mut *c_ptr;

        math::min(executor, a, b, c, len as usize).expect("min failed");
    }
}

/// Element-wise maximum: c = max(a, b)
pub fn vector_max_f32(executor_handle: u64, a_handle: u64, b_handle: u64, c_handle: u64, len: u32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Buffer A not found")) as *const _;
    let b_ptr = buf_registry
        .get(&b_handle)
        .unwrap_or_else(|| panic!("Buffer B not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Buffer C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let b = &*b_ptr;
        let c = &mut *c_ptr;

        math::max(executor, a, b, c, len as usize).expect("max failed");
    }
}

/// Element-wise absolute value: c = |a|
pub fn vector_abs_f32(executor_handle: u64, a_handle: u64, c_handle: u64, len: u32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Buffer A not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Buffer C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let c = &mut *c_ptr;

        math::abs(executor, a, c, len as usize).expect("abs failed");
    }
}

/// Element-wise negation: c = -a
pub fn vector_neg_f32(executor_handle: u64, a_handle: u64, c_handle: u64, len: u32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Buffer A not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Buffer C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let c = &mut *c_ptr;

        math::neg(executor, a, c, len as usize).expect("neg failed");
    }
}

/// Element-wise ReLU: c = max(0, a)
pub fn vector_relu_f32(executor_handle: u64, a_handle: u64, c_handle: u64, len: u32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Buffer A not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Buffer C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let c = &mut *c_ptr;

        math::relu(executor, a, c, len as usize).expect("relu failed");
    }
}

/// Clip values to range [min_val, max_val]: c = clip(a, min_val, max_val)
pub fn vector_clip_f32(executor_handle: u64, a_handle: u64, c_handle: u64, len: u32, min_val: f32, max_val: f32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Buffer A not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Buffer C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let c = &mut *c_ptr;

        math::clip(executor, a, c, min_val, max_val, len as usize).expect("clip failed");
    }
}

/// Add scalar to vector: c = a + scalar
pub fn scalar_add_f32(executor_handle: u64, a_handle: u64, c_handle: u64, len: u32, scalar: f32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Buffer A not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Buffer C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let c = &mut *c_ptr;

        math::scalar_add(executor, a, c, scalar, len as usize).expect("scalar_add failed");
    }
}

/// Multiply vector by scalar: c = a * scalar
pub fn scalar_mul_f32(executor_handle: u64, a_handle: u64, c_handle: u64, len: u32, scalar: f32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Buffer A not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Buffer C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let c = &mut *c_ptr;

        math::scalar_mul(executor, a, c, scalar, len as usize).expect("scalar_mul failed");
    }
}
