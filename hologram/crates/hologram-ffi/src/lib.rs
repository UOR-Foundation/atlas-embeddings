//! # Hologram FFI
//!
//! Cross-language Foreign Function Interface for Hologram
//!
//! This crate provides a unified FFI interface using UniFFI to expose Hologram
//! Sigmatics-based compute functionality across multiple programming languages
//! including Python, TypeScript, Swift, Kotlin, and WebAssembly.
//!
//! ## Architecture
//!
//! The FFI uses handle-based object management to safely expose Rust objects
//! across language boundaries:
//!
//! - **Executor** - Sigmatics circuit executor (u64 handle)
//! - **Buffer<T>** - Typed memory buffers (u64 handle)
//! - **Tensor<T>** - Multi-dimensional arrays (u64 handle)
//!
//! All operations compile to canonical Sigmatics circuits under the hood,
//! providing lowest-latency execution through pattern-based canonicalization.

// Allow clippy warnings in generated UniFFI code
#![allow(clippy::empty_line_after_doc_comments)]

// Module declarations
mod activation;
mod buffer;
mod buffer_ext;
mod buffer_zerocopy;
mod executor;
mod executor_ext;
mod handles;
mod linalg;
mod loss;
mod math;
mod reduce;
mod tensor;

// Re-export all public functions for UniFFI
pub use activation::{gelu_f32, sigmoid_f32, softmax_f32, tanh_f32};
pub use buffer::{
    buffer_canonicalize_all, buffer_cleanup, buffer_copy, buffer_copy_from_canonical_slice, buffer_copy_from_slice,
    buffer_copy_to_slice, buffer_fill, buffer_length, buffer_to_vec, buffer_verify_canonical,
};
pub use buffer_ext::{
    buffer_class_index, buffer_element_size, buffer_is_boundary, buffer_is_empty, buffer_is_linear, buffer_pool,
    buffer_size_bytes,
};
pub use buffer_zerocopy::{buffer_as_mut_ptr, buffer_as_ptr, buffer_copy_from_bytes, buffer_to_bytes};
pub use executor::{
    executor_allocate_buffer, executor_cleanup, new_executor, new_executor_auto, new_executor_with_backend,
};
pub use executor_ext::executor_allocate_boundary_buffer;
pub use handles::clear_all_registries;
pub use linalg::{gemm_f32, matvec_f32};
pub use loss::{binary_cross_entropy_loss_f32, cross_entropy_loss_f32, mse_loss_f32};
pub use math::{
    scalar_add_f32, scalar_mul_f32, vector_abs_f32, vector_add_f32, vector_clip_f32, vector_div_f32, vector_max_f32,
    vector_min_f32, vector_mul_f32, vector_neg_f32, vector_relu_f32, vector_sub_f32,
};
pub use reduce::{reduce_max_f32, reduce_min_f32, reduce_sum_f32};
pub use tensor::{
    tensor_broadcast_shapes, tensor_buffer, tensor_cleanup, tensor_contiguous, tensor_from_buffer,
    tensor_from_buffer_with_strides, tensor_is_broadcast_compatible_with, tensor_is_contiguous, tensor_matmul,
    tensor_narrow, tensor_ndim, tensor_numel, tensor_offset, tensor_permute, tensor_reshape, tensor_select,
    tensor_shape, tensor_slice, tensor_strides, tensor_transpose, tensor_view_1d,
};

/// Get the version of the hologram-ffi library
pub fn get_version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

// Include the UDL file for UniFFI scaffolding
uniffi::include_scaffolding!("hologram_ffi");
