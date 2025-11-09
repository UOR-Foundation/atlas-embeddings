"""
Sine Function

Operation: b[i] = sin(a[i])

Element-wise sine computation.
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id

def sin(a: DeviceArray[f32], b: DeviceArray[f32], n: u32):
    """Compute sine: b = sin(a)"""
    idx = get_global_id()
    if idx < n:
        b[idx] = sinf(a[idx])  # Use standard library sinf()

