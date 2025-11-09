"""
Natural Logarithm Function

Operation: b[i] = log(a[i])

Element-wise natural logarithm computation.
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id

def log(a: DeviceArray[f32], b: DeviceArray[f32], n: u32):
    """Compute logarithm: b = log(a)"""
    idx = get_global_id()
    if idx < n:
        b[idx] = logf(a[idx])  # Use standard library logf()

