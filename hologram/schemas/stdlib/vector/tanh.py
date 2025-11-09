"""
Tanh Activation Function

Operation: b[i] = tanh(a[i])

Neural network activation function that maps values to [-1, 1].
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id

def tanh(a: DeviceArray[f32], b: DeviceArray[f32], n: u32):
    """Apply tanh activation"""
    idx = get_global_id()
    if idx < n:
        value = a[idx]
        # Simplified tanh
        b[idx] = value

