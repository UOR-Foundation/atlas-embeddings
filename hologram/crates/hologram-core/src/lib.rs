//! # hologram-core - Canonical Compute Operations
//!
//! High-performance compute library using precompiled ISA operations via hologram-backends.
//!
//! ## Architecture
//!
//! hologram-core provides composable operations that execute precompiled ISA Programs.
//! **All operations are compiled at build-time** through Sigmatics canonicalization,
//! enabling lowest-latency execution with zero runtime overhead.
//!
//! ### Build-Time Compilation
//!
//! Operations are compiled from Python schemas → Sigmatics → ISA at build time:
//! - **Pattern Rewriting**: H²=I, X²=I, Z²=I, HXH=Z, S²=Z, I·I=I (Sigmatics)
//! - **Operation Reduction**: Typical 75% reduction in operation count
//! - **ISA Translation**: Generator sequences → backend instructions
//! - **Zero Runtime Compilation**: All operations precompiled as const Programs
//!
//! ### Runtime Execution
//!
//! - **Backend Execution**: Operations execute via hologram-backends (CPU, GPU, etc.)
//! - **96-Class System**: Logical addressing mapped to backend buffers
//! - **Zero-Copy**: Direct backend memory access, no intermediate copies
//! - **<200ns Overhead**: Direct ISA execution, no compilation
//!
//! ## Key Principles
//!
//! 1. **Compile-Time Optimization**: All canonicalization at build time (Sigmatics)
//! 2. **Runtime Efficiency**: Zero compilation overhead, direct ISA execution
//! 3. **Lowest Latency**: Precompiled + minimal instructions = fastest execution
//! 4. **Universal Compute**: General-purpose acceleration, not domain-specific
//!
//! ## Example
//!
//! ```text
//! use hologram_core::{Executor, ops};
//!
//! // Create executor
//! let mut exec = Executor::new()?;
//!
//! // Allocate buffers (each buffer maps to a class index)
//! let mut a = exec.allocate::<f32>(3072)?;  // 3072 elements = 12,288 bytes
//! let mut b = exec.allocate::<f32>(3072)?;
//! let mut c = exec.allocate::<f32>(3072)?;
//!
//! // Copy data to buffers
//! let data_a = vec![1.0f32; 3072];
//! let data_b = vec![2.0f32; 3072];
//! a.copy_from_slice(&mut exec, &data_a)?;
//! b.copy_from_slice(&mut exec, &data_b)?;
//!
//! // Execute operation (compiles to canonical circuit)
//! ops::math::vector_add(&mut exec, &a, &b, &mut c, 3072)?;
//!
//! // Read results
//! let result = c.to_vec(&exec)?;
//! assert_eq!(result[0], 3.0);
//! ```
//!
//! ## Operation Modules
//!
//! - [`ops::math`] - Element-wise arithmetic (add, sub, mul, div, min, max, abs, neg, relu)
//! - [`ops::reduce`] - Reductions (sum, min, max)
//! - [`ops::activation`] - Neural network activations (sigmoid, tanh, gelu, softmax)
//! - [`ops::loss`] - Loss functions (mse, cross_entropy, binary_cross_entropy)
//! - [`ops::linalg`] - Linear algebra (gemm, matvec)
//! - [`ops::memory`] - Memory operations (copy, fill)

pub mod address_mapping;
pub mod buffer;
pub mod compiler;
pub mod error;
pub mod executor;
pub mod instrumentation;
pub mod isa_builder;
pub mod kernel;
pub mod ops;
pub mod tensor;

// Re-export primary types
pub use address_mapping::{
    fits_in_class, max_elements_per_class, offset_to_phi_coordinate, phi_coordinate_to_offset, BYTES_PER_CLASS,
    BYTES_PER_PAGE, PAGES_PER_CLASS,
};
pub use buffer::Buffer;
// Note: Sigmatics types no longer exported (build-time only)
pub use error::{Error, Result};
pub use executor::{BackendType, Executor};
pub use instrumentation::{
    AggregateStatistics, CompilationMetrics, ExecutionMetrics, GeneratorMetrics, OptimizationMetrics,
};
pub use kernel::KernelLoader;
pub use tensor::Tensor;
