"""
Vector Multiplication (Hadamard) - Element-wise multiplication

Operation: c[i] = a[i] * b[i]

Performs element-wise (Hadamard) product of two vectors.
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id

def vector_mul(a: DeviceArray[f32], b: DeviceArray[f32], c: DeviceArray[f32], n: u32):
    """Multiply two vectors element-wise: c = a * b"""
    idx = get_global_id()
    if idx < n:
        c[idx] = a[idx] * b[idx]

