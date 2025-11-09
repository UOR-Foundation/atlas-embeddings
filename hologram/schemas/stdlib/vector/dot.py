"""
Dot Product - Inner product of two vectors

Operation: result = Σ(a[i] * b[i])

BLAS Level 1 reduction operation that computes dot product.
Requires atomic addition for reduction.
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id, atomic_add_f32

def vector_dot(a: DeviceArray[f32], b: DeviceArray[f32], result: DeviceArray[f32], n: u32):
    """Compute dot product: result = Σ(a[i] * b[i])"""
    idx = get_global_id()
    if idx < n:
        product = a[idx] * b[idx]
        atomic_add_f32(result, product)

