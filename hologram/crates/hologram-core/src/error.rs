//! Error types for hologram-core operations

/// Result type for hologram-core operations
pub type Result<T> = std::result::Result<T, Error>;

/// Errors that can occur in hologram-core operations
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Sigmatics circuit compilation error
    #[error("Circuit compilation error: {0}")]
    CircuitCompilation(String),

    /// Sigmatics execution error
    #[error("Circuit execution error: {0}")]
    CircuitExecution(String),

    /// Buffer size mismatch
    #[error("Buffer size mismatch: expected {expected}, got {actual}")]
    BufferSizeMismatch { expected: usize, actual: usize },

    /// Invalid buffer view
    #[error("Invalid buffer view: {0}")]
    InvalidView(String),

    /// Type mismatch
    #[error("Type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },

    /// Out of memory
    #[error("Out of memory: requested {requested} bytes")]
    OutOfMemory { requested: usize },

    /// Invalid operation
    #[error("Invalid operation: {0}")]
    InvalidOperation(String),

    /// Class index out of bounds
    #[error("Class index out of bounds: {index} >= 96")]
    ClassIndexOutOfBounds { index: u8 },

    /// Invalid tensor shape
    #[error("Invalid tensor shape: {0}")]
    InvalidShape(String),
}
