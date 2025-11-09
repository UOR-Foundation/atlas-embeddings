"""
ReLU - Rectified Linear Unit activation

Operation: b[i] = max(0, a[i])

Neural network activation function that zeros negative values.
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id

def relu(a: DeviceArray[f32], b: DeviceArray[f32], n: u32):
    """Apply ReLU activation: b = max(0, a)"""
    idx = get_global_id()
    if idx < n:
        value = a[idx]
        if value > 0.0:
            b[idx] = value
        else:
            b[idx] = 0.0

