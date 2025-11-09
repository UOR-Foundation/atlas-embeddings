"""
Vector Sum Reduction

Operation: result = Σ(a[i])

Computes the sum of all elements in the vector using atomic reduction.
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id, atomic_add_f32

def vector_sum(a: DeviceArray[f32], result: DeviceArray[f32], n: u32):
    """Compute sum reduction: result = Σ(a[i])"""
    idx = get_global_id()
    if idx < n:
        atomic_add_f32(result, a[idx])

