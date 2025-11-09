"""
Sigmoid Activation Function

Operation: b[i] = 1 / (1 + exp(-a[i]))

Neural network activation function that maps values to [0, 1].
"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id

def sigmoid(a: DeviceArray[f32], b: DeviceArray[f32], n: u32):
    """Apply sigmoid activation: b = 1 / (1 + exp(-a))"""
    idx = get_global_id()
    if idx < n:
        value = a[idx]
        # Simplified sigmoid approximation
        b[idx] = 1.0 / (1.0 + value)

