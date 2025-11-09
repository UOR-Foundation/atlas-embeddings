//! High-level operations for Sigmatics execution
//!
//! All operations compile to Sigmatics generator sequences and execute
//! via the 96-class memory system. No host-side computation.
//!
//! ## Modules
//!
//! - `activation` - Neural network activation functions (sigmoid, tanh, gelu, softmax)
//! - `linalg` - Linear algebra operations (GEMM, matrix-vector multiply)
//! - `loss` - Loss functions for training (MSE, cross-entropy)
//! - `math` - Basic mathematical operations (add, mul, etc.)
//! - `memory` - Memory operations (copy, fill, etc.)
//! - `parallel` - Parallel execution utilities for large-scale operations
//! - `reduce` - Reduction operations (sum, max, min, etc.)
//! - `traits` - Operation trait interfaces (MathOp, LinAlgOp, ActivationOp, etc.)

pub mod activation;
pub mod linalg;
pub mod loss;
pub mod math;
pub mod memory;
pub mod parallel;
pub mod reduce;
pub mod traits;
