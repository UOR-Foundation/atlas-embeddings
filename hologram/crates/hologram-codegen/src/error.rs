//! Error types for code generation

use thiserror::Error;

#[derive(Debug, Error)]
pub enum CodegenError {
    #[error("JSON parsing error: {0}")]
    JsonParse(#[from] serde_json::Error),

    #[error("Invalid schema: {0}")]
    InvalidSchema(String),

    #[error("Type error: {0}")]
    TypeError(String),

    #[error("Unsupported operation: {0}")]
    UnsupportedOperation(String),

    #[error("Code generation error: {0}")]
    CodegenFailed(String),
}

pub type Result<T> = std::result::Result<T, CodegenError>;
