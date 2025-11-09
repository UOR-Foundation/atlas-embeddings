"""
General Matrix Multiply (GEMM) - BLAS Level 3

Operation: C = alpha * A * B + beta * C

Standard general matrix multiply from BLAS.
Computes C = αAB + βC where A is m×k, B is k×n, C is m×n.
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id

def gemm_f32(
    A: DeviceArray[f32],      # m × k matrix
    B: DeviceArray[f32],      # k × n matrix
    C: DeviceArray[f32],      # m × n matrix (result)
    m: u32,                   # Rows of A and C
    n: u32,                   # Columns of B and C
    k: u32,                   # Columns of A, rows of B
    lda: u32,                 # Leading dimension of A
    ldb: u32,                 # Leading dimension of B
    ldc: u32,                 # Leading dimension of C
):
    """General matrix multiply: C = A × B"""
    thread_id = get_global_id()
    total_elements = m * n
    
    if thread_id < total_elements:
        # Compute row and column
        i = thread_id // n  # Row in C
        j = thread_id % n   # Column in C
        
        # Compute dot product
        sum_val = 0.0
        for k_idx in range(k):
            sum_val += A[i * lda + k_idx] * B[k_idx * ldb + j]
        
        C[i * ldc + j] = sum_val

