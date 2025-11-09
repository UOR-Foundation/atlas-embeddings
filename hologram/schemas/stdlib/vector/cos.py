"""
Cosine Function

Operation: b[i] = cos(a[i])

Element-wise cosine computation.
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id

def cos(a: DeviceArray[f32], b: DeviceArray[f32], n: u32):
    """Compute cosine: b = cos(a)"""
    idx = get_global_id()
    if idx < n:
        b[idx] = cosf(a[idx])  # Use standard library cosf()

