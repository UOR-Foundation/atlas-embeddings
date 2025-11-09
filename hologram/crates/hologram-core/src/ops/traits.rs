//! NOTE: All operations in this file are temporarily stubbed during Phase 0 migration.
//! They will be implemented with ISA Programs in Phase 1.

//! Operation Trait Interfaces with Interface Segregation
//!
//! This module defines segregated traits for different operation categories.
//! Each trait represents a specific domain of operations that compile to
//! generator sequences.
//!
//! ## Interface Segregation Principle
//!
//! Rather than a monolithic "Operation" trait, we separate concerns:
//! - **MathOperation**: Arithmetic operations (add, sub, mul, div, min, max, abs, neg)
//! - **LinearAlgebraOperation**: Matrix/vector operations (gemm, matvec, outer)
//! - **ActivationOperation**: Neural network activations (relu, sigmoid, tanh, softmax)
//! - **ReductionOperation**: Aggregations (sum, min, max, mean)
//! - **LossOperation**: Loss functions (mse, cross_entropy, binary_cross_entropy)
//!
//! All traits extend `GeneratorOperationCompiler` to ensure they compile to
//! generator sequences for execution.
//!
//! ## Example
//!
//! ```text
//! use hologram_core::ops::traits::MathOperation;
//!
//! struct VectorAdd {
//!     src_a_class: u8,
//!     src_b_class: u8,
//!     dst_class: u8,
//! }
//!
//! impl GeneratorOperationCompiler for VectorAdd {
//!     fn compile(&self) -> Result<GeneratorSequence> {
//!         let mut seq = GeneratorSequence::new();
//!         seq.merge(self.src_a_class, self.dst_class, self.src_b_class);
//!         Ok(seq.finalize())
//!     }
//! }
//!
//! impl MathOperation for VectorAdd {
//!     fn operation_name(&self) -> &'static str {
//!         "vector_add"
//!     }
//! }
//! ```

// NOTE: These traits are deprecated in favor of direct sigmatics usage.
// See ops::math, ops::activation, etc. for current implementations.

/// Placeholder trait for backward compatibility
pub trait GeneratorOperationCompiler {
    /// Compile to a circuit (deprecated)
    fn compile(&self) -> crate::error::Result<String> {
        Ok(String::new())
    }
}

/// Math operations: element-wise arithmetic
///
/// This trait represents operations that perform arithmetic on vectors/tensors:
/// - Binary: add, sub, mul, div, min, max
/// - Unary: abs, neg, relu
///
/// All math operations compile to generator sequences using Merge, Copy, or Mark.
pub trait MathOperation: GeneratorOperationCompiler {
    /// Get the operation name for debugging/instrumentation
    fn operation_name(&self) -> &'static str;

    /// Whether this operation is element-wise (true for most math ops)
    fn is_elementwise(&self) -> bool {
        true
    }

    /// Whether this operation is commutative (e.g., add, mul, min, max)
    fn is_commutative(&self) -> bool {
        false
    }
}

/// Linear algebra operations: matrix/vector operations
///
/// This trait represents operations that perform linear algebra:
/// - Matrix multiplication (GEMM): C = A @ B
/// - Matrix-vector multiplication (GEMV): y = A @ x
/// - Outer product: C = x ⊗ y
/// - Vector dot product: scalar = x · y
///
/// These operations compile to nested generator sequences with blocking
/// for cache optimization.
pub trait LinearAlgebraOperation: GeneratorOperationCompiler {
    /// Get the operation name for debugging/instrumentation
    fn operation_name(&self) -> &'static str;

    /// Get the complexity class (e.g., O(n²) for matvec, O(n³) for gemm)
    fn complexity(&self) -> Complexity;
}

/// Activation operations: neural network activation functions
///
/// This trait represents operations that apply activation functions:
/// - ReLU: y = max(0, x)
/// - Sigmoid: y = 1 / (1 + exp(-x))
/// - Tanh: y = tanh(x)
/// - Softmax: y_i = exp(x_i) / sum(exp(x_j))
/// - GELU: y = x * Φ(x)
///
/// These operations compile to generator sequences using Copy, Merge,
/// and conditional operations.
pub trait ActivationOperation: GeneratorOperationCompiler {
    /// Get the operation name for debugging/instrumentation
    fn operation_name(&self) -> &'static str;

    /// Whether this activation is differentiable everywhere
    fn is_differentiable(&self) -> bool {
        true
    }

    /// Whether this activation has bounded output range
    fn is_bounded(&self) -> bool {
        false
    }
}

/// Reduction operations: aggregations
///
/// This trait represents operations that reduce tensors to scalars or lower dimensions:
/// - Sum: scalar = Σ x_i
/// - Min: scalar = min(x_i)
/// - Max: scalar = max(x_i)
/// - Mean: scalar = (1/n) Σ x_i
///
/// These operations compile to tree-based generator sequences using Merge
/// for parallel reduction.
pub trait ReductionOperation: GeneratorOperationCompiler {
    /// Get the operation name for debugging/instrumentation
    fn operation_name(&self) -> &'static str;

    /// Get the reduction strategy (tree, sequential, etc.)
    fn strategy(&self) -> ReductionStrategy;
}

/// Loss operations: loss functions for training
///
/// This trait represents operations that compute loss metrics:
/// - Mean Squared Error: L = (1/n) Σ (pred - target)²
/// - Cross Entropy: L = -Σ target * log(pred)
/// - Binary Cross Entropy: L = -Σ [target*log(pred) + (1-target)*log(1-pred)]
///
/// These operations compile to compositions of math, reduction, and activation
/// generator sequences.
pub trait LossOperation: GeneratorOperationCompiler {
    /// Get the operation name for debugging/instrumentation
    fn operation_name(&self) -> &'static str;

    /// Whether this loss requires numerical stability measures (e.g., log-sum-exp trick)
    fn requires_stability(&self) -> bool {
        false
    }
}

/// Complexity classification for operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Complexity {
    /// O(1) - Constant time
    Constant,
    /// O(n) - Linear time
    Linear,
    /// O(n log n) - Log-linear time
    LogLinear,
    /// O(n²) - Quadratic time
    Quadratic,
    /// O(n³) - Cubic time
    Cubic,
    /// O(2ⁿ) - Exponential time
    Exponential,
}

/// Reduction strategy for aggregation operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReductionStrategy {
    /// Tree-based parallel reduction (O(log n) depth)
    Tree,
    /// Sequential reduction (O(n) depth, simpler)
    Sequential,
    /// Blocked reduction (cache-aware)
    Blocked,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_complexity_enum() {
        assert_eq!(Complexity::Linear, Complexity::Linear);
        assert_ne!(Complexity::Linear, Complexity::Quadratic);
    }

    #[test]
    fn test_reduction_strategy_enum() {
        assert_eq!(ReductionStrategy::Tree, ReductionStrategy::Tree);
        assert_ne!(ReductionStrategy::Tree, ReductionStrategy::Sequential);
    }
}
