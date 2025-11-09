//! Schema types and marshalling for kernel codegen
//!
//! This module provides the type system and parameter marshalling infrastructure
//! for kernel code generation.

use std::fmt;
use thiserror::Error;

/// Scalar types supported by Atlas
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScalarType {
    F32,
    F64,
    I32,
    I64,
    U32,
    U64,
    Bool,
}

impl ScalarType {
    /// Get the size of this type in bytes
    pub const fn size(&self) -> usize {
        match self {
            ScalarType::F32 => 4,
            ScalarType::F64 => 8,
            ScalarType::I32 => 4,
            ScalarType::I64 => 8,
            ScalarType::U32 => 4,
            ScalarType::U64 => 8,
            ScalarType::Bool => 1,
        }
    }

    /// Get the alignment of this type in bytes
    pub const fn alignment(&self) -> usize {
        self.size()
    }
}

impl fmt::Display for ScalarType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScalarType::F32 => write!(f, "f32"),
            ScalarType::F64 => write!(f, "f64"),
            ScalarType::I32 => write!(f, "i32"),
            ScalarType::I64 => write!(f, "i64"),
            ScalarType::U32 => write!(f, "u32"),
            ScalarType::U64 => write!(f, "u64"),
            ScalarType::Bool => write!(f, "bool"),
        }
    }
}

/// Parameter type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParamType {
    Scalar(ScalarType),
    DevicePtr(ScalarType),
    DeviceArray(ScalarType),
}

impl ParamType {
    pub fn size(&self) -> usize {
        match self {
            ParamType::Scalar(t) => t.size(),
            ParamType::DevicePtr(_) | ParamType::DeviceArray(_) => 8, // 64-bit pointer
        }
    }

    pub fn alignment(&self) -> usize {
        match self {
            ParamType::Scalar(t) => t.alignment(),
            ParamType::DevicePtr(_) | ParamType::DeviceArray(_) => 8,
        }
    }
}

impl fmt::Display for ParamType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParamType::Scalar(t) => write!(f, "{}", t),
            ParamType::DevicePtr(t) => write!(f, "DevicePtr<{}>", t),
            ParamType::DeviceArray(t) => write!(f, "DeviceArray<{}>", t),
        }
    }
}

/// Schema-related errors
#[derive(Debug, Error)]
pub enum SchemaError {
    #[error("Type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },

    #[error("Parameter count mismatch: expected {expected}, got {actual}")]
    ParameterCountMismatch { expected: usize, actual: usize },

    #[error("Invalid buffer size: {0}")]
    InvalidBufferSize(String),

    #[error("Alignment error: {0}")]
    AlignmentError(String),

    #[error("Out of bounds access: index {index}, size {size}")]
    OutOfBounds { index: usize, size: usize },
}

/// Result type for schema operations
pub type SchemaResult<T> = std::result::Result<T, SchemaError>;

/// Parameter unmarshaller for reading kernel parameters
pub struct Unmarshaller<'a> {
    buffer: &'a [u8],
    offset: usize,
}

impl<'a> Unmarshaller<'a> {
    /// Create a new unmarshaller from parameter buffer
    pub fn new(buffer: &'a [u8]) -> Self {
        Self { buffer, offset: 0 }
    }

    /// Align offset to given alignment
    fn align(&mut self, alignment: usize) {
        let misalignment = self.offset % alignment;
        if misalignment != 0 {
            self.offset += alignment - misalignment;
        }
    }

    /// Unpack bytes for a scalar type
    fn unpack_bytes(&mut self, ty: ScalarType) -> SchemaResult<Vec<u8>> {
        let alignment = ty.alignment();
        let size = ty.size();

        self.align(alignment);

        if self.offset + size > self.buffer.len() {
            return Err(SchemaError::InvalidBufferSize(format!(
                "buffer too small: need {} bytes at offset {}, have {}",
                size,
                self.offset,
                self.buffer.len()
            )));
        }

        let bytes = self.buffer[self.offset..self.offset + size].to_vec();
        self.offset += size;

        Ok(bytes)
    }

    /// Unpack a device pointer
    pub fn unpack_device_ptr(&mut self) -> SchemaResult<u64> {
        self.align(8);

        if self.offset + 8 > self.buffer.len() {
            return Err(SchemaError::InvalidBufferSize(
                "buffer too small for device pointer".to_string(),
            ));
        }

        let bytes = &self.buffer[self.offset..self.offset + 8];
        self.offset += 8;

        Ok(u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }

    /// Convenience methods for specific types
    pub fn unpack_u8(&mut self) -> SchemaResult<u8> {
        let bytes = self.unpack_bytes(ScalarType::U32)?;
        Ok(bytes[0])
    }

    pub fn unpack_u16(&mut self) -> SchemaResult<u16> {
        let bytes = self.unpack_bytes(ScalarType::U32)?;
        Ok(u16::from_le_bytes([bytes[0], bytes[1]]))
    }

    pub fn unpack_u32(&mut self) -> SchemaResult<u32> {
        let bytes = self.unpack_bytes(ScalarType::U32)?;
        Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    pub fn unpack_u64(&mut self) -> SchemaResult<u64> {
        let bytes = self.unpack_bytes(ScalarType::U64)?;
        Ok(u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }

    pub fn unpack_i8(&mut self) -> SchemaResult<i8> {
        let bytes = self.unpack_bytes(ScalarType::I32)?;
        Ok(bytes[0] as i8)
    }

    pub fn unpack_i16(&mut self) -> SchemaResult<i16> {
        let bytes = self.unpack_bytes(ScalarType::I32)?;
        Ok(i16::from_le_bytes([bytes[0], bytes[1]]))
    }

    pub fn unpack_i32(&mut self) -> SchemaResult<i32> {
        let bytes = self.unpack_bytes(ScalarType::I32)?;
        Ok(i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    pub fn unpack_i64(&mut self) -> SchemaResult<i64> {
        let bytes = self.unpack_bytes(ScalarType::I64)?;
        Ok(i64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }

    pub fn unpack_f32(&mut self) -> SchemaResult<f32> {
        let bytes = self.unpack_bytes(ScalarType::F32)?;
        Ok(f32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    pub fn unpack_f64(&mut self) -> SchemaResult<f64> {
        let bytes = self.unpack_bytes(ScalarType::F64)?;
        Ok(f64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }
}

/// C-compatible error code for ABI
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub enum ErrorCode {
    Success = 0,
    InvalidParams = 1,
    ExecutionFailed = 2,
    Unknown = 99,
}

/// C-compatible launch configuration for ABI
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct CLaunchConfig {
    pub grid_dim_x: u32,
    pub grid_dim_y: u32,
    pub grid_dim_z: u32,
    pub block_dim_x: u32,
    pub block_dim_y: u32,
    pub block_dim_z: u32,
}

/// ABI version for compatibility checking
pub const ABI_VERSION: u32 = 1;
