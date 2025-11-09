//! High-Level Circuit Construction API
//!
//! Provides user-friendly interfaces for constructing Sigmatics circuits
//! that represent common vector operations.

use crate::compiler::CompiledCircuit;
use crate::SigmaticsCompiler;

/// A high-level circuit builder for common operations
pub struct CircuitBuilder {
    operations: Vec<String>,
}

impl CircuitBuilder {
    /// Create a new circuit builder
    pub fn new() -> Self {
        Self { operations: Vec::new() }
    }

    /// Add a mark operation at a class
    pub fn mark(mut self, class: u8) -> Self {
        self.operations.push(format!("mark@c{:02}", class));
        self
    }

    /// Add a copy operation from one class to another
    pub fn copy(mut self, src_class: u8, dst_class: u8) -> Self {
        self.operations
            .push(format!("copy@c{:02}->c{:02}", src_class, dst_class));
        self
    }

    /// Add a swap operation between two classes
    pub fn swap(mut self, class_a: u8, class_b: u8) -> Self {
        self.operations.push(format!("swap@c{:02}<->c{:02}", class_a, class_b));
        self
    }

    /// Add a merge operation (addition)
    pub fn merge(mut self, src: u8, context: u8, dst: u8) -> Self {
        self.operations
            .push(format!("merge@c{:02}[c{:02},c{:02}]", src, context, dst));
        self
    }

    /// Add a split operation (subtraction)
    pub fn split(mut self, src: u8, context: u8, dst: u8) -> Self {
        self.operations
            .push(format!("split@c{:02}[c{:02},c{:02}]", src, context, dst));
        self
    }

    /// Build the circuit string
    pub fn build(self) -> String {
        self.operations.join(" . ")
    }

    /// Build and compile the circuit
    pub fn compile(self) -> Result<CompiledCircuit, String> {
        let circuit = self.build();
        SigmaticsCompiler::compile(&circuit)
    }
}

impl Default for CircuitBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Pre-defined circuits for common vector operations
pub struct VectorCircuits;

impl VectorCircuits {
    /// Circuit for vector addition: output = a + b
    ///
    /// Uses classes:
    /// - 0: input A
    /// - 1: input B
    /// - 2: output
    ///
    /// # Example
    ///
    /// ```text
    /// use hologram_compiler::circuit::VectorCircuits;
    ///
    /// let circuit = VectorCircuits::add();
    /// let compiled = SigmaticsCompiler::compile(&circuit).unwrap();
    /// ```
    pub fn add() -> String {
        "merge@c00[c01,c02]".to_string()
    }

    /// Circuit for vector subtraction: output = a - b
    pub fn sub() -> String {
        "split@c00[c01,c02]".to_string()
    }

    /// Circuit for vector multiplication: output = a * b
    pub fn mul() -> String {
        "merge@c00[c01,c02]".to_string() // Uses MergeVariant::Mul
    }

    /// Circuit for vector negation: output = -a
    pub fn neg() -> String {
        "mark@c00".to_string() // Mark for negation
    }

    /// Circuit for identity: output = a
    pub fn identity() -> String {
        "copy@c00->c01".to_string()
    }

    /// Circuit demonstrating H² = I canonicalization
    ///
    /// This circuit contains redundant operations that will be optimized
    /// away by Sigmatics canonicalization.
    pub fn h_squared() -> String {
        "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21".to_string()
    }

    /// Circuit demonstrating X² = I canonicalization
    pub fn x_squared() -> String {
        "mark@c21 . mark@c21".to_string()
    }

    /// Circuit demonstrating HXH = Z conjugation
    ///
    /// This is the key quantum gate identity that reduces 5 operations to 1.
    pub fn hxh_conjugation() -> String {
        "copy@c05->c06 . mark@c21 . mark@c21 . copy@c05->c06 . mark@c21".to_string()
    }
}

/// Compiled vector operation that can be executed
pub struct VectorOperation {
    /// The compiled circuit
    pub compiled: CompiledCircuit,
    /// Human-readable name
    pub name: String,
}

impl VectorOperation {
    /// Create a new vector operation from a circuit
    pub fn new(name: impl Into<String>, circuit: &str) -> Result<Self, String> {
        let compiled = SigmaticsCompiler::compile(circuit)?;
        Ok(Self {
            compiled,
            name: name.into(),
        })
    }

    /// Get the optimization ratio (original ops / canonical ops)
    pub fn optimization_ratio(&self) -> f64 {
        if self.compiled.canonical_ops > 0 {
            self.compiled.original_ops as f64 / self.compiled.canonical_ops as f64
        } else {
            1.0
        }
    }

    /// Get the reduction percentage
    pub fn reduction_pct(&self) -> f64 {
        self.compiled.reduction_pct
    }

    /// Get the number of generator calls that will be executed
    pub fn num_calls(&self) -> usize {
        self.compiled.calls.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_circuit_builder() {
        let circuit = CircuitBuilder::new().mark(21).mark(42).build();

        assert_eq!(circuit, "mark@c21 . mark@c42");
    }

    #[test]
    fn test_vector_add_circuit() {
        let circuit = VectorCircuits::add();
        let compiled = SigmaticsCompiler::compile(&circuit).unwrap();
        assert!(!compiled.calls.is_empty());
    }

    #[test]
    fn test_h_squared_optimization() {
        let op = VectorOperation::new("H²", &VectorCircuits::h_squared()).unwrap();

        // H² should be optimized
        assert_eq!(op.compiled.original_ops, 4);
        assert!(
            op.compiled.canonical_ops < op.compiled.original_ops,
            "Expected canonicalization to reduce operations"
        );
        assert!(op.reduction_pct() > 0.0);
    }

    #[test]
    fn test_hxh_conjugation_optimization() {
        let op = VectorOperation::new("HXH", &VectorCircuits::hxh_conjugation()).unwrap();

        // HXH = Z should reduce 5 operations significantly
        assert_eq!(op.compiled.original_ops, 5);
        assert!(
            op.reduction_pct() >= 75.0,
            "Expected at least 75% reduction, got {}%",
            op.reduction_pct()
        );
    }

    #[test]
    fn test_optimization_ratio() {
        let op = VectorOperation::new("H²", &VectorCircuits::h_squared()).unwrap();
        let ratio = op.optimization_ratio();

        // Should be greater than 1 (original > canonical)
        assert!(ratio > 1.0, "Expected optimization ratio > 1.0, got {}", ratio);
    }
}
