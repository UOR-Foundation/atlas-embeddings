"""
Atlas Kernel Primitives

Common functions and types for Atlas kernel schemas.
Kernel schemas should import from this module.

Example usage:
    from atlas_kernel import DeviceArray, f32, u32, get_global_id
    
    def my_kernel(a: DeviceArray[f32], n: u32):
        idx = get_global_id()
        if idx < n:
            # kernel logic
"""

# Type aliases for Atlas kernel interface
class DeviceArray:
    """Device array type annotation for Atlas vGPU memory"""
    def __class_getitem__(cls, item):
        return cls

f32 = float  # 32-bit floating point
i32 = int    # 32-bit signed integer
u32 = int    # 32-bit unsigned integer
f64 = float  # 64-bit floating point
usize = int  # Pointer-sized unsigned integer

def get_global_id() -> int:
    """
    Get global thread ID - replaced during compilation
    
    Returns the unique thread index in the parallel execution.
    This function is replaced by the kernel code generator with actual
    thread ID calculation based on grid/block dimensions.
    """
    pass


def atomic_add_f32(addr, value: f32):
    """
    Atomic addition for reduction operations
    
    Atomically adds value to the memory location pointed to by addr.
    This intrinsic is replaced by the kernel code generator with the
    appropriate atomic instruction (CPU or GPU).
    """
    pass


def atomic_add_u32(addr, value: u32):
    """Atomic add for u32 - replaced during compilation"""
    pass


def atomic_add_i32(addr, value: i32):
    """Atomic add for i32 - replaced during compilation"""
    pass


def atomic_add(addr: DeviceArray[u32], index: u32, value: u32) -> u32:
    """
    Atomic addition with return value

    Atomically adds value to addr[index] and returns the old value.
    This intrinsic is replaced by the kernel code generator with the
    appropriate atomic instruction.
    """
    pass


def atomic_min(addr: DeviceArray[f32], index: u32, value: f32):
    """
    Atomic minimum for optimization operations

    Atomically compares and stores the minimum value at addr[index].
    This intrinsic is replaced by the kernel code generator with the
    appropriate atomic compare-and-swap instruction.
    """
    pass


def expf(x: f32) -> f32:
    """Standard library exponential"""
    pass

def logf(x: f32) -> f32:
    """Standard library logarithm"""
    pass

def sinf(x: f32) -> f32:
    """Standard library sine"""
    pass

def cosf(x: f32) -> f32:
    """Standard library cosine"""
    pass

def sqrtf(x: f32) -> f32:
    """Standard library square root"""
    pass

def exp(x: f32) -> f32:
    """Exponential function"""
    pass

