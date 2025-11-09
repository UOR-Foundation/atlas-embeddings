"""
Hologram FFI - Python bindings for the Hologram Atlas runtime

This package provides Python bindings for the Hologram Atlas computational interface,
enabling high-performance numerical computations across diverse hardware substrates.
"""

from .hologram_ffi import *
from .version import __version__

__all__ = [
    # Core functions
    "get_version",
    "get_executor_phase",
    "advance_executor_phase",
    
    # Executor Management (Phase 1.1)
    "new_executor",
    "executor_with_backend",
    "executor_allocate_buffer",
    "executor_allocate_boundary_buffer",
    "executor_phase",
    "executor_advance_phase",
    "executor_resonance_at",
    "executor_resonance_snapshot",
    "executor_mirror",
    "executor_neighbors",
    "executor_cleanup",
    "buffer_cleanup",
    
    # Buffer Operations (Phase 1.2)
    "buffer_length",
    "buffer_copy",
    "buffer_fill",
    "buffer_to_vec",
    
    # Additional Buffer Operations (Phase 2)
    "buffer_backend_handle",
    "buffer_topology",
    "buffer_is_empty",
    "buffer_pool",
    "buffer_is_linear",
    "buffer_is_boundary",
    "buffer_element_size",
    "buffer_size_bytes",
    "buffer_copy_from_slice",
    
    # Linear Algebra Operations (Phase 2.1)
    "gemm_f32",
    "matvec_f32",
    
    # Loss Functions (Phase 2.2)
    "mse_loss_f32",
    "cross_entropy_loss_f32",
    
    # Additional Math Operations (Phase 2.4)
    "vector_min_f32",
    "vector_max_f32",
    "scalar_add_f32",
    "scalar_mul_f32",
    "gelu_f32",
    
    # Boundary Operations (Phase 2.5)
    "transpose_boundary_f32",
    
    # Tensor Support (Phase 3.1)
    "tensor_from_buffer",
    "tensor_from_buffer_with_strides",
    "tensor_shape",
    "tensor_strides",
    "tensor_offset",
    "tensor_ndim",
    "tensor_numel",
    "tensor_buffer",
    "tensor_is_contiguous",
    "tensor_cleanup",
    
    # Tensor Operations (Phase 3.2)
    "tensor_reshape",
    "tensor_transpose",
    "tensor_permute",
    "tensor_view_1d",
    "tensor_matmul",
    "tensor_is_broadcast_compatible",
    "tensor_broadcast_shape",
    "tensor_select",
    "tensor_narrow",
    "tensor_slice",
    "tensor_buffer_mut",
    
    # Compiler Infrastructure (Phase 4)
    "program_builder_new",
    "register_allocator_new",
    "address_builder_direct",
    
    # Atlas State Management (Phase 4.2)
    "atlas_phase",
    "atlas_advance_phase",
    "atlas_resonance_at",
    "atlas_resonance_snapshot",
    
    # Mathematical Operations (Simplified)
    "vector_add_f32",
    "vector_sub_f32",
    "vector_mul_f32",
    "vector_div_f32",
    "vector_abs_f32",
    "vector_neg_f32",
    "vector_relu_f32",
    
    # Reduction Operations
    "reduce_sum_f32",
    "reduce_max_f32",
    "reduce_min_f32",
    
    # Activation Functions
    "sigmoid_f32",
    "tanh_f32",
    "softmax_f32",
]
