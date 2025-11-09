//! Error types for backend operations

use std::fmt;

/// Result type for backend operations
pub type Result<T> = std::result::Result<T, BackendError>;

/// Errors that can occur during backend execution
#[derive(Debug, thiserror::Error)]
pub enum BackendError {
    /// Invalid buffer handle
    #[error("invalid buffer handle: {0}")]
    InvalidBufferHandle(u64),

    /// Invalid pool handle
    #[error("invalid pool handle: {0}")]
    InvalidPoolHandle(u64),

    /// Buffer access out of bounds
    #[error("buffer access out of bounds: offset {offset} + size {size} > buffer size {buffer_size}")]
    BufferOutOfBounds {
        offset: usize,
        size: usize,
        buffer_size: usize,
    },

    /// Pool access out of bounds
    #[error("pool access out of bounds: offset {offset} + size {size} > pool size {pool_size}")]
    PoolOutOfBounds {
        offset: usize,
        size: usize,
        pool_size: usize,
    },

    /// Invalid register index
    #[error("invalid register index: {0}")]
    InvalidRegister(u8),

    /// Invalid predicate index
    #[error("invalid predicate index: {0}")]
    InvalidPredicate(u8),

    /// Type mismatch
    #[error("type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },

    /// Uninitialized register
    #[error("uninitialized register: r{0}")]
    UninitializedRegister(u8),

    /// Uninitialized predicate
    #[error("uninitialized predicate: p{0}")]
    UninitializedPredicate(u8),

    /// Division by zero
    #[error("division by zero")]
    DivisionByZero,

    /// Invalid memory address
    #[error("invalid memory address: {0:#x}")]
    InvalidMemoryAddress(u64),

    /// Program error
    #[error("program error: {0}")]
    ProgramError(#[from] crate::isa::ProgramError),

    /// Label not found
    #[error("label not found: {0}")]
    LabelNotFound(String),

    /// Call stack overflow
    #[error("call stack overflow (max depth: {0})")]
    CallStackOverflow(usize),

    /// Call stack underflow
    #[error("call stack underflow: attempted return with empty call stack")]
    CallStackUnderflow,

    /// Invalid class index
    #[error("invalid class index: {0} (must be < 96)")]
    InvalidClassIndex(u8),

    /// Invalid boundary coordinates
    #[error("invalid boundary coordinates: page={page} (must be < 48), byte={byte} (must be < 256)")]
    InvalidBoundaryCoordinates { page: u8, byte: u8 },

    /// Execution error
    #[error("execution error: {0}")]
    ExecutionError(String),

    /// Unsupported operation
    #[error("unsupported operation: {0}")]
    UnsupportedOperation(String),

    /// Unsupported instruction
    #[error("unsupported instruction: {0}")]
    UnsupportedInstruction(String),

    /// Invalid launch configuration
    #[error("invalid launch configuration: {0}")]
    InvalidLaunchConfig(String),

    /// Shared memory allocation failed
    #[error("shared memory allocation failed: requested {requested} bytes, available {available} bytes")]
    SharedMemoryAllocationFailed { requested: usize, available: usize },

    /// Generic error
    #[error("{0}")]
    Other(String),
}

impl BackendError {
    /// Create a type mismatch error
    pub fn type_mismatch(expected: impl fmt::Display, actual: impl fmt::Display) -> Self {
        Self::TypeMismatch {
            expected: expected.to_string(),
            actual: actual.to_string(),
        }
    }

    /// Create an execution error
    pub fn execution_error(msg: impl Into<String>) -> Self {
        Self::ExecutionError(msg.into())
    }

    /// Create an unsupported operation error
    pub fn unsupported(msg: impl Into<String>) -> Self {
        Self::UnsupportedOperation(msg.into())
    }
}
