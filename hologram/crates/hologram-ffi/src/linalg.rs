//! Linear algebra operation wrappers for FFI
//!
//! Provides handle-based API for linear algebra operations.

use crate::handles::{lock_registry, BUFFER_REGISTRY, EXECUTOR_REGISTRY};
use hologram_core::ops::linalg;

/// General Matrix Multiplication: C = A * B
///
/// Computes matrix multiplication where:
/// - A is m×k matrix
/// - B is k×n matrix
/// - C is m×n matrix (output)
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `a_handle` - Handle to matrix A (m×k elements)
/// * `b_handle` - Handle to matrix B (k×n elements)
/// * `c_handle` - Handle to matrix C (m×n elements, output)
/// * `m` - Number of rows in A and C
/// * `n` - Number of columns in B and C
/// * `k` - Number of columns in A, rows in B
pub fn gemm_f32(executor_handle: u64, a_handle: u64, b_handle: u64, c_handle: u64, m: u32, n: u32, k: u32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Matrix A not found")) as *const _;
    let b_ptr = buf_registry
        .get(&b_handle)
        .unwrap_or_else(|| panic!("Matrix B not found")) as *const _;
    let c_ptr = buf_registry
        .get_mut(&c_handle)
        .unwrap_or_else(|| panic!("Matrix C not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let b = &*b_ptr;
        let c = &mut *c_ptr;

        linalg::gemm(executor, a, b, c, m as usize, n as usize, k as usize).expect("gemm failed");
    }
}

/// Matrix-Vector Multiplication: y = A * x
///
/// Computes matrix-vector product where:
/// - A is m×n matrix
/// - x is n-element vector
/// - y is m-element vector (output)
///
/// # Arguments
///
/// * `executor_handle` - Handle to the executor
/// * `a_handle` - Handle to matrix A (m×n elements)
/// * `x_handle` - Handle to vector x (n elements)
/// * `y_handle` - Handle to vector y (m elements, output)
/// * `m` - Number of rows in A, size of y
/// * `n` - Number of columns in A, size of x
pub fn matvec_f32(executor_handle: u64, a_handle: u64, x_handle: u64, y_handle: u64, m: u32, n: u32) {
    let mut exec_registry = lock_registry(&EXECUTOR_REGISTRY);
    let executor = exec_registry
        .get_mut(&executor_handle)
        .unwrap_or_else(|| panic!("Executor handle {} not found", executor_handle));

    let mut buf_registry = lock_registry(&BUFFER_REGISTRY);

    let a_ptr = buf_registry
        .get(&a_handle)
        .unwrap_or_else(|| panic!("Matrix A not found")) as *const _;
    let x_ptr = buf_registry
        .get(&x_handle)
        .unwrap_or_else(|| panic!("Vector x not found")) as *const _;
    let y_ptr = buf_registry
        .get_mut(&y_handle)
        .unwrap_or_else(|| panic!("Vector y not found")) as *mut _;

    unsafe {
        let a = &*a_ptr;
        let x = &*x_ptr;
        let y = &mut *y_ptr;

        linalg::matvec(executor, a, x, y, m as usize, n as usize).expect("matvec failed");
    }
}
