"""
Exponential Function

Operation: b[i] = exp(a[i])

Element-wise exponential computation.
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id

def exp(a: DeviceArray[f32], b: DeviceArray[f32], n: u32):
    """Compute exponential: b = exp(a)"""
    idx = get_global_id()
    if idx < n:
        b[idx] = expf(a[idx])  # Use standard library expf()

