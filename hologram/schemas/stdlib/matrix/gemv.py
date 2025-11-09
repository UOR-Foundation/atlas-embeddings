"""
General Matrix-Vector Multiply (GEMV) - BLAS Level 2

Operation: y = alpha * A * x + beta * y

Matrix-vector multiplication.
Computes y = αAx + βy where A is m×n, x is n×1, y is m×1.
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id

def gemv_f32(
    A: DeviceArray[f32],      # m × n matrix
    x: DeviceArray[f32],      # n × 1 vector
    y: DeviceArray[f32],      # m × 1 vector (result)
    m: u32,                   # Rows of A
    n: u32,                   # Columns of A
    lda: u32,                 # Leading dimension of A
):
    """Matrix-vector multiply: y = A × x"""
    thread_id = get_global_id()
    
    if thread_id < m:
        # Compute row i of result
        sum_val = 0.0
        for j in range(n):
            sum_val += A[thread_id * lda + j] * x[j]
        
        y[thread_id] = sum_val

