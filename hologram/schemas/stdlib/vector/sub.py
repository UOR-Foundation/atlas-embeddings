"""
Vector Subtraction - Element-wise subtraction of two vectors

Operation: c[i] = a[i] - b[i]

Subtracts vector b from vector a element-wise.
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id

def vector_sub(a: DeviceArray[f32], b: DeviceArray[f32], c: DeviceArray[f32], n: u32):
    """Subtract two vectors: c = a - b"""
    idx = get_global_id()
    if idx < n:
        c[idx] = a[idx] - b[idx]

