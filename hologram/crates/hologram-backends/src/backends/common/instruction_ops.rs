//! Shared instruction implementations for all backends
//!
//! This module contains instruction implementations that are backend-agnostic
//! and can be shared across CPU, GPU, TPU, and FPGA backends. These implementations
//! only depend on the ExecutionState and MemoryStorage abstractions.
//!
//! # Architecture
//!
//! All instruction implementations are generic over `MemoryStorage`, allowing them
//! to work with any backend's memory implementation. The functions only manipulate:
//! - Register file (via ExecutionState::current_lane_mut())
//! - Program counter and control flow state
//! - Memory through the MemoryStorage trait
//!
//! # Categories
//!
//! - **Data Movement**: MOV, CVT
//! - **Arithmetic**: ADD, SUB, MUL, DIV, MAD, FMA, MIN, MAX, ABS, NEG
//! - **Bitwise**: AND, OR, XOR, NOT, SHL, SHR
//! - **Comparison**: SETcc
//! - **Control Flow**: BRA, CALL, RET, LOOP, EXIT
//! - **Math Functions**: SIN, COS, TAN, TANH, SIGMOID, EXP, LOG, SQRT, etc.
//! - **Reductions**: ReduceAdd, ReduceMin, ReduceMax, ReduceMul
//! - **Pool Operations**: PoolAlloc, PoolFree, PoolLoad, PoolStore
//! - **Selection**: SEL

use super::{ExecutionState, MemoryStorage};
use crate::backend::PoolHandle;
use crate::error::{BackendError, Result};
use crate::isa::{Condition, Register, Type};

// ================================================================================================
// Data Movement Operations
// ================================================================================================

/// MOV - Move data between registers
///
/// Copies value from source register to destination register.
/// Supports all 12 data types.
pub fn execute_mov<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();

    match ty {
        Type::I8 => {
            let value = lane.registers.read_i8(src)?;
            lane.registers.write_i8(dst, value)?;
        }
        Type::I16 => {
            let value = lane.registers.read_i16(src)?;
            lane.registers.write_i16(dst, value)?;
        }
        Type::I32 => {
            let value = lane.registers.read_i32(src)?;
            lane.registers.write_i32(dst, value)?;
        }
        Type::I64 => {
            let value = lane.registers.read_i64(src)?;
            lane.registers.write_i64(dst, value)?;
        }
        Type::U8 => {
            let value = lane.registers.read_u8(src)?;
            lane.registers.write_u8(dst, value)?;
        }
        Type::U16 => {
            let value = lane.registers.read_u16(src)?;
            lane.registers.write_u16(dst, value)?;
        }
        Type::U32 => {
            let value = lane.registers.read_u32(src)?;
            lane.registers.write_u32(dst, value)?;
        }
        Type::U64 => {
            let value = lane.registers.read_u64(src)?;
            lane.registers.write_u64(dst, value)?;
        }
        Type::F16 => {
            let value = lane.registers.read_f16_bits(src)?;
            lane.registers.write_f16_bits(dst, value)?;
        }
        Type::BF16 => {
            let value = lane.registers.read_bf16_bits(src)?;
            lane.registers.write_bf16_bits(dst, value)?;
        }
        Type::F32 => {
            let value = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, value)?;
        }
        Type::F64 => {
            let value = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, value)?;
        }
    }

    Ok(())
}

/// CVT - Convert between types
///
/// Performs type conversion between source and destination types.
/// Handles all combinations of integer, unsigned, and float conversions.
pub fn execute_cvt<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    src_ty: Type,
    dst_ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();

    // Macro to handle type conversion for all combinations
    macro_rules! convert {
        ($src_ty:ty, $dst_ty:ty, $read:ident, $write:ident) => {{
            let value = lane.registers.$read(src)?;
            let converted = value as $dst_ty;
            lane.registers.$write(dst, converted)?;
        }};
    }

    match (src_ty, dst_ty) {
        // Same type conversions (no-op)
        (a, b) if a == b => match src_ty {
            Type::I8 => {
                let v = lane.registers.read_i8(src)?;
                lane.registers.write_i8(dst, v)?;
            }
            Type::I16 => {
                let v = lane.registers.read_i16(src)?;
                lane.registers.write_i16(dst, v)?;
            }
            Type::I32 => {
                let v = lane.registers.read_i32(src)?;
                lane.registers.write_i32(dst, v)?;
            }
            Type::I64 => {
                let v = lane.registers.read_i64(src)?;
                lane.registers.write_i64(dst, v)?;
            }
            Type::U8 => {
                let v = lane.registers.read_u8(src)?;
                lane.registers.write_u8(dst, v)?;
            }
            Type::U16 => {
                let v = lane.registers.read_u16(src)?;
                lane.registers.write_u16(dst, v)?;
            }
            Type::U32 => {
                let v = lane.registers.read_u32(src)?;
                lane.registers.write_u32(dst, v)?;
            }
            Type::U64 => {
                let v = lane.registers.read_u64(src)?;
                lane.registers.write_u64(dst, v)?;
            }
            Type::F32 => {
                let v = lane.registers.read_f32(src)?;
                lane.registers.write_f32(dst, v)?;
            }
            Type::F64 => {
                let v = lane.registers.read_f64(src)?;
                lane.registers.write_f64(dst, v)?;
            }
            _ => return Err(BackendError::UnsupportedOperation(format!("CVT for type {}", src_ty))),
        },

        // Integer to integer conversions
        (Type::I8, Type::I16) => convert!(i8, i16, read_i8, write_i16),
        (Type::I8, Type::I32) => convert!(i8, i32, read_i8, write_i32),
        (Type::I8, Type::I64) => convert!(i8, i64, read_i8, write_i64),
        (Type::I16, Type::I8) => convert!(i16, i8, read_i16, write_i8),
        (Type::I16, Type::I32) => convert!(i16, i32, read_i16, write_i32),
        (Type::I16, Type::I64) => convert!(i16, i64, read_i16, write_i64),
        (Type::I32, Type::I8) => convert!(i32, i8, read_i32, write_i8),
        (Type::I32, Type::I16) => convert!(i32, i16, read_i32, write_i16),
        (Type::I32, Type::I64) => convert!(i32, i64, read_i32, write_i64),
        (Type::I64, Type::I8) => convert!(i64, i8, read_i64, write_i8),
        (Type::I64, Type::I16) => convert!(i64, i16, read_i64, write_i16),
        (Type::I64, Type::I32) => convert!(i64, i32, read_i64, write_i32),

        // Unsigned to unsigned conversions
        (Type::U8, Type::U16) => convert!(u8, u16, read_u8, write_u16),
        (Type::U8, Type::U32) => convert!(u8, u32, read_u8, write_u32),
        (Type::U8, Type::U64) => convert!(u8, u64, read_u8, write_u64),
        (Type::U16, Type::U8) => convert!(u16, u8, read_u16, write_u8),
        (Type::U16, Type::U32) => convert!(u16, u32, read_u16, write_u32),
        (Type::U16, Type::U64) => convert!(u16, u64, read_u16, write_u64),
        (Type::U32, Type::U8) => convert!(u32, u8, read_u32, write_u8),
        (Type::U32, Type::U16) => convert!(u32, u16, read_u32, write_u16),
        (Type::U32, Type::U64) => convert!(u32, u64, read_u32, write_u64),
        (Type::U64, Type::U8) => convert!(u64, u8, read_u64, write_u8),
        (Type::U64, Type::U16) => convert!(u64, u16, read_u64, write_u16),
        (Type::U64, Type::U32) => convert!(u64, u32, read_u64, write_u32),

        // Signed to unsigned conversions
        (Type::I8, Type::U8) => convert!(i8, u8, read_i8, write_u8),
        (Type::I16, Type::U16) => convert!(i16, u16, read_i16, write_u16),
        (Type::I32, Type::U32) => convert!(i32, u32, read_i32, write_u32),
        (Type::I64, Type::U64) => convert!(i64, u64, read_i64, write_u64),

        // Unsigned to signed conversions
        (Type::U8, Type::I8) => convert!(u8, i8, read_u8, write_i8),
        (Type::U16, Type::I16) => convert!(u16, i16, read_u16, write_i16),
        (Type::U32, Type::I32) => convert!(u32, i32, read_u32, write_i32),
        (Type::U64, Type::I64) => convert!(u64, i64, read_u64, write_i64),

        // Integer to float conversions
        (Type::I32, Type::F32) => convert!(i32, f32, read_i32, write_f32),
        (Type::I64, Type::F64) => convert!(i64, f64, read_i64, write_f64),
        (Type::U32, Type::F32) => convert!(u32, f32, read_u32, write_f32),
        (Type::U64, Type::F64) => convert!(u64, f64, read_u64, write_f64),

        // Float to integer conversions
        (Type::F32, Type::I32) => convert!(f32, i32, read_f32, write_i32),
        (Type::F64, Type::I64) => convert!(f64, i64, read_f64, write_i64),
        (Type::F32, Type::U32) => convert!(f32, u32, read_f32, write_u32),
        (Type::F64, Type::U64) => convert!(f64, u64, read_f64, write_u64),

        // Float to float conversions
        (Type::F32, Type::F64) => convert!(f32, f64, read_f32, write_f64),
        (Type::F64, Type::F32) => convert!(f64, f32, read_f64, write_f32),

        _ => {
            return Err(BackendError::UnsupportedOperation(format!(
                "CVT from {} to {}",
                src_ty, dst_ty
            )))
        }
    }
    Ok(())
}

/// MOV_IMM - Move immediate value to register
///
/// Loads a 64-bit immediate value into a register, converting to the specified type.
/// The immediate value is interpreted based on the destination type:
/// - Integer types: Direct conversion (with truncation for smaller types)
/// - Float types: Reinterpret bits as float
pub fn execute_mov_imm<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    value: u64,
) -> Result<()> {
    let lane = state.current_lane_mut();

    match ty {
        Type::I8 => {
            lane.registers.write_i8(dst, value as i8)?;
        }
        Type::I16 => {
            lane.registers.write_i16(dst, value as i16)?;
        }
        Type::I32 => {
            lane.registers.write_i32(dst, value as i32)?;
        }
        Type::I64 => {
            lane.registers.write_i64(dst, value as i64)?;
        }
        Type::U8 => {
            lane.registers.write_u8(dst, value as u8)?;
        }
        Type::U16 => {
            lane.registers.write_u16(dst, value as u16)?;
        }
        Type::U32 => {
            lane.registers.write_u32(dst, value as u32)?;
        }
        Type::U64 => {
            lane.registers.write_u64(dst, value)?;
        }
        Type::F16 => {
            // Store as 16-bit value (reinterpret bits)
            lane.registers.write_f16_bits(dst, value as u16)?;
        }
        Type::BF16 => {
            // Store as 16-bit value (reinterpret bits)
            lane.registers.write_bf16_bits(dst, value as u16)?;
        }
        Type::F32 => {
            // Reinterpret lower 32 bits as f32
            lane.registers.write_f32(dst, f32::from_bits(value as u32))?;
        }
        Type::F64 => {
            // Reinterpret 64 bits as f64
            lane.registers.write_f64(dst, f64::from_bits(value))?;
        }
    }

    Ok(())
}

// ================================================================================================
// Arithmetic Operations
// ================================================================================================

pub fn execute_add<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src1: Register,
    src2: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src1)?;
            let b = lane.registers.read_i8(src2)?;
            lane.registers.write_i8(dst, a.wrapping_add(b))?;
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src1)?;
            let b = lane.registers.read_i16(src2)?;
            lane.registers.write_i16(dst, a.wrapping_add(b))?;
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src1)?;
            let b = lane.registers.read_i32(src2)?;
            lane.registers.write_i32(dst, a.wrapping_add(b))?;
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src1)?;
            let b = lane.registers.read_i64(src2)?;
            lane.registers.write_i64(dst, a.wrapping_add(b))?;
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src1)?;
            let b = lane.registers.read_u8(src2)?;
            lane.registers.write_u8(dst, a.wrapping_add(b))?;
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src1)?;
            let b = lane.registers.read_u16(src2)?;
            lane.registers.write_u16(dst, a.wrapping_add(b))?;
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src1)?;
            let b = lane.registers.read_u32(src2)?;
            lane.registers.write_u32(dst, a.wrapping_add(b))?;
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src1)?;
            let b = lane.registers.read_u64(src2)?;
            lane.registers.write_u64(dst, a.wrapping_add(b))?;
        }
        Type::F32 => {
            let a = lane.registers.read_f32(src1)?;
            let b = lane.registers.read_f32(src2)?;
            lane.registers.write_f32(dst, a + b)?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src1)?;
            let b = lane.registers.read_f64(src2)?;
            lane.registers.write_f64(dst, a + b)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("ADD for type {}", ty))),
    }
    Ok(())
}

pub fn execute_sub<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src1: Register,
    src2: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src1)?;
            let b = lane.registers.read_i8(src2)?;
            lane.registers.write_i8(dst, a.wrapping_sub(b))?;
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src1)?;
            let b = lane.registers.read_i16(src2)?;
            lane.registers.write_i16(dst, a.wrapping_sub(b))?;
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src1)?;
            let b = lane.registers.read_i32(src2)?;
            lane.registers.write_i32(dst, a.wrapping_sub(b))?;
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src1)?;
            let b = lane.registers.read_i64(src2)?;
            lane.registers.write_i64(dst, a.wrapping_sub(b))?;
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src1)?;
            let b = lane.registers.read_u8(src2)?;
            lane.registers.write_u8(dst, a.wrapping_sub(b))?;
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src1)?;
            let b = lane.registers.read_u16(src2)?;
            lane.registers.write_u16(dst, a.wrapping_sub(b))?;
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src1)?;
            let b = lane.registers.read_u32(src2)?;
            lane.registers.write_u32(dst, a.wrapping_sub(b))?;
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src1)?;
            let b = lane.registers.read_u64(src2)?;
            lane.registers.write_u64(dst, a.wrapping_sub(b))?;
        }
        Type::F32 => {
            let a = lane.registers.read_f32(src1)?;
            let b = lane.registers.read_f32(src2)?;
            lane.registers.write_f32(dst, a - b)?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src1)?;
            let b = lane.registers.read_f64(src2)?;
            lane.registers.write_f64(dst, a - b)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("SUB for type {}", ty))),
    }
    Ok(())
}

pub fn execute_mul<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src1: Register,
    src2: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src1)?;
            let b = lane.registers.read_i8(src2)?;
            lane.registers.write_i8(dst, a.wrapping_mul(b))?;
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src1)?;
            let b = lane.registers.read_i16(src2)?;
            lane.registers.write_i16(dst, a.wrapping_mul(b))?;
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src1)?;
            let b = lane.registers.read_i32(src2)?;
            lane.registers.write_i32(dst, a.wrapping_mul(b))?;
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src1)?;
            let b = lane.registers.read_i64(src2)?;
            lane.registers.write_i64(dst, a.wrapping_mul(b))?;
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src1)?;
            let b = lane.registers.read_u8(src2)?;
            lane.registers.write_u8(dst, a.wrapping_mul(b))?;
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src1)?;
            let b = lane.registers.read_u16(src2)?;
            lane.registers.write_u16(dst, a.wrapping_mul(b))?;
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src1)?;
            let b = lane.registers.read_u32(src2)?;
            lane.registers.write_u32(dst, a.wrapping_mul(b))?;
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src1)?;
            let b = lane.registers.read_u64(src2)?;
            lane.registers.write_u64(dst, a.wrapping_mul(b))?;
        }
        Type::F32 => {
            let a = lane.registers.read_f32(src1)?;
            let b = lane.registers.read_f32(src2)?;
            lane.registers.write_f32(dst, a * b)?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src1)?;
            let b = lane.registers.read_f64(src2)?;
            lane.registers.write_f64(dst, a * b)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("MUL for type {}", ty))),
    }
    Ok(())
}

pub fn execute_div<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src1: Register,
    src2: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src1)?;
            let b = lane.registers.read_i8(src2)?;
            if b == 0 {
                return Err(BackendError::DivisionByZero);
            }
            lane.registers.write_i8(dst, a.wrapping_div(b))?;
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src1)?;
            let b = lane.registers.read_i16(src2)?;
            if b == 0 {
                return Err(BackendError::DivisionByZero);
            }
            lane.registers.write_i16(dst, a.wrapping_div(b))?;
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src1)?;
            let b = lane.registers.read_i32(src2)?;
            if b == 0 {
                return Err(BackendError::DivisionByZero);
            }
            lane.registers.write_i32(dst, a.wrapping_div(b))?;
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src1)?;
            let b = lane.registers.read_i64(src2)?;
            if b == 0 {
                return Err(BackendError::DivisionByZero);
            }
            lane.registers.write_i64(dst, a.wrapping_div(b))?;
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src1)?;
            let b = lane.registers.read_u8(src2)?;
            if b == 0 {
                return Err(BackendError::DivisionByZero);
            }
            lane.registers.write_u8(dst, a / b)?;
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src1)?;
            let b = lane.registers.read_u16(src2)?;
            if b == 0 {
                return Err(BackendError::DivisionByZero);
            }
            lane.registers.write_u16(dst, a / b)?;
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src1)?;
            let b = lane.registers.read_u32(src2)?;
            if b == 0 {
                return Err(BackendError::DivisionByZero);
            }
            lane.registers.write_u32(dst, a / b)?;
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src1)?;
            let b = lane.registers.read_u64(src2)?;
            if b == 0 {
                return Err(BackendError::DivisionByZero);
            }
            lane.registers.write_u64(dst, a / b)?;
        }
        Type::F32 => {
            let a = lane.registers.read_f32(src1)?;
            let b = lane.registers.read_f32(src2)?;
            lane.registers.write_f32(dst, a / b)?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src1)?;
            let b = lane.registers.read_f64(src2)?;
            lane.registers.write_f64(dst, a / b)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("DIV for type {}", ty))),
    }
    Ok(())
}

pub fn execute_mad<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    a: Register,
    b: Register,
    c: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I32 => {
            let va = lane.registers.read_i32(a)?;
            let vb = lane.registers.read_i32(b)?;
            let vc = lane.registers.read_i32(c)?;
            lane.registers.write_i32(dst, va.wrapping_mul(vb).wrapping_add(vc))?;
        }
        Type::I64 => {
            let va = lane.registers.read_i64(a)?;
            let vb = lane.registers.read_i64(b)?;
            let vc = lane.registers.read_i64(c)?;
            lane.registers.write_i64(dst, va.wrapping_mul(vb).wrapping_add(vc))?;
        }
        Type::F32 => {
            let va = lane.registers.read_f32(a)?;
            let vb = lane.registers.read_f32(b)?;
            let vc = lane.registers.read_f32(c)?;
            lane.registers.write_f32(dst, va * vb + vc)?;
        }
        Type::F64 => {
            let va = lane.registers.read_f64(a)?;
            let vb = lane.registers.read_f64(b)?;
            let vc = lane.registers.read_f64(c)?;
            lane.registers.write_f64(dst, va * vb + vc)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("MAD for type {}", ty))),
    }
    Ok(())
}

pub fn execute_fma<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    a: Register,
    b: Register,
    c: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::F32 => {
            let va = lane.registers.read_f32(a)?;
            let vb = lane.registers.read_f32(b)?;
            let vc = lane.registers.read_f32(c)?;
            lane.registers.write_f32(dst, va.mul_add(vb, vc))?;
        }
        Type::F64 => {
            let va = lane.registers.read_f64(a)?;
            let vb = lane.registers.read_f64(b)?;
            let vc = lane.registers.read_f64(c)?;
            lane.registers.write_f64(dst, va.mul_add(vb, vc))?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("FMA for type {}", ty))),
    }
    Ok(())
}

pub fn execute_min<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src1: Register,
    src2: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src1)?;
            let b = lane.registers.read_i8(src2)?;
            lane.registers.write_i8(dst, a.min(b))?;
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src1)?;
            let b = lane.registers.read_i16(src2)?;
            lane.registers.write_i16(dst, a.min(b))?;
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src1)?;
            let b = lane.registers.read_i32(src2)?;
            lane.registers.write_i32(dst, a.min(b))?;
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src1)?;
            let b = lane.registers.read_i64(src2)?;
            lane.registers.write_i64(dst, a.min(b))?;
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src1)?;
            let b = lane.registers.read_u8(src2)?;
            lane.registers.write_u8(dst, a.min(b))?;
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src1)?;
            let b = lane.registers.read_u16(src2)?;
            lane.registers.write_u16(dst, a.min(b))?;
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src1)?;
            let b = lane.registers.read_u32(src2)?;
            lane.registers.write_u32(dst, a.min(b))?;
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src1)?;
            let b = lane.registers.read_u64(src2)?;
            lane.registers.write_u64(dst, a.min(b))?;
        }
        Type::F32 => {
            let a = lane.registers.read_f32(src1)?;
            let b = lane.registers.read_f32(src2)?;
            lane.registers.write_f32(dst, a.min(b))?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src1)?;
            let b = lane.registers.read_f64(src2)?;
            lane.registers.write_f64(dst, a.min(b))?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("MIN for type {}", ty))),
    }
    Ok(())
}

pub fn execute_max<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src1: Register,
    src2: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src1)?;
            let b = lane.registers.read_i8(src2)?;
            lane.registers.write_i8(dst, a.max(b))?;
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src1)?;
            let b = lane.registers.read_i16(src2)?;
            lane.registers.write_i16(dst, a.max(b))?;
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src1)?;
            let b = lane.registers.read_i32(src2)?;
            lane.registers.write_i32(dst, a.max(b))?;
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src1)?;
            let b = lane.registers.read_i64(src2)?;
            lane.registers.write_i64(dst, a.max(b))?;
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src1)?;
            let b = lane.registers.read_u8(src2)?;
            lane.registers.write_u8(dst, a.max(b))?;
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src1)?;
            let b = lane.registers.read_u16(src2)?;
            lane.registers.write_u16(dst, a.max(b))?;
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src1)?;
            let b = lane.registers.read_u32(src2)?;
            lane.registers.write_u32(dst, a.max(b))?;
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src1)?;
            let b = lane.registers.read_u64(src2)?;
            lane.registers.write_u64(dst, a.max(b))?;
        }
        Type::F32 => {
            let a = lane.registers.read_f32(src1)?;
            let b = lane.registers.read_f32(src2)?;
            lane.registers.write_f32(dst, a.max(b))?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src1)?;
            let b = lane.registers.read_f64(src2)?;
            lane.registers.write_f64(dst, a.max(b))?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("MAX for type {}", ty))),
    }
    Ok(())
}

pub fn execute_abs<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let v = lane.registers.read_i8(src)?;
            lane.registers.write_i8(dst, v.abs())?;
        }
        Type::I16 => {
            let v = lane.registers.read_i16(src)?;
            lane.registers.write_i16(dst, v.abs())?;
        }
        Type::I32 => {
            let v = lane.registers.read_i32(src)?;
            lane.registers.write_i32(dst, v.abs())?;
        }
        Type::I64 => {
            let v = lane.registers.read_i64(src)?;
            lane.registers.write_i64(dst, v.abs())?;
        }
        Type::F32 => {
            let v = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, v.abs())?;
        }
        Type::F64 => {
            let v = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, v.abs())?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("ABS for type {}", ty))),
    }
    Ok(())
}

pub fn execute_neg<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let v = lane.registers.read_i8(src)?;
            lane.registers.write_i8(dst, v.wrapping_neg())?;
        }
        Type::I16 => {
            let v = lane.registers.read_i16(src)?;
            lane.registers.write_i16(dst, v.wrapping_neg())?;
        }
        Type::I32 => {
            let v = lane.registers.read_i32(src)?;
            lane.registers.write_i32(dst, v.wrapping_neg())?;
        }
        Type::I64 => {
            let v = lane.registers.read_i64(src)?;
            lane.registers.write_i64(dst, v.wrapping_neg())?;
        }
        Type::F32 => {
            let v = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, -v)?;
        }
        Type::F64 => {
            let v = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, -v)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("NEG for type {}", ty))),
    }
    Ok(())
}

// ================================================================================================
// Logical Instructions (Stubs)
// ================================================================================================

pub fn execute_and<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src1: Register,
    src2: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src1)?;
            let b = lane.registers.read_i8(src2)?;
            lane.registers.write_i8(dst, a & b)?;
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src1)?;
            let b = lane.registers.read_i16(src2)?;
            lane.registers.write_i16(dst, a & b)?;
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src1)?;
            let b = lane.registers.read_i32(src2)?;
            lane.registers.write_i32(dst, a & b)?;
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src1)?;
            let b = lane.registers.read_i64(src2)?;
            lane.registers.write_i64(dst, a & b)?;
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src1)?;
            let b = lane.registers.read_u8(src2)?;
            lane.registers.write_u8(dst, a & b)?;
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src1)?;
            let b = lane.registers.read_u16(src2)?;
            lane.registers.write_u16(dst, a & b)?;
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src1)?;
            let b = lane.registers.read_u32(src2)?;
            lane.registers.write_u32(dst, a & b)?;
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src1)?;
            let b = lane.registers.read_u64(src2)?;
            lane.registers.write_u64(dst, a & b)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("AND for type {}", ty))),
    }
    Ok(())
}

pub fn execute_or<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src1: Register,
    src2: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src1)?;
            let b = lane.registers.read_i8(src2)?;
            lane.registers.write_i8(dst, a | b)?;
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src1)?;
            let b = lane.registers.read_i16(src2)?;
            lane.registers.write_i16(dst, a | b)?;
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src1)?;
            let b = lane.registers.read_i32(src2)?;
            lane.registers.write_i32(dst, a | b)?;
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src1)?;
            let b = lane.registers.read_i64(src2)?;
            lane.registers.write_i64(dst, a | b)?;
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src1)?;
            let b = lane.registers.read_u8(src2)?;
            lane.registers.write_u8(dst, a | b)?;
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src1)?;
            let b = lane.registers.read_u16(src2)?;
            lane.registers.write_u16(dst, a | b)?;
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src1)?;
            let b = lane.registers.read_u32(src2)?;
            lane.registers.write_u32(dst, a | b)?;
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src1)?;
            let b = lane.registers.read_u64(src2)?;
            lane.registers.write_u64(dst, a | b)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("OR for type {}", ty))),
    }
    Ok(())
}

pub fn execute_xor<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src1: Register,
    src2: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src1)?;
            let b = lane.registers.read_i8(src2)?;
            lane.registers.write_i8(dst, a ^ b)?;
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src1)?;
            let b = lane.registers.read_i16(src2)?;
            lane.registers.write_i16(dst, a ^ b)?;
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src1)?;
            let b = lane.registers.read_i32(src2)?;
            lane.registers.write_i32(dst, a ^ b)?;
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src1)?;
            let b = lane.registers.read_i64(src2)?;
            lane.registers.write_i64(dst, a ^ b)?;
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src1)?;
            let b = lane.registers.read_u8(src2)?;
            lane.registers.write_u8(dst, a ^ b)?;
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src1)?;
            let b = lane.registers.read_u16(src2)?;
            lane.registers.write_u16(dst, a ^ b)?;
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src1)?;
            let b = lane.registers.read_u32(src2)?;
            lane.registers.write_u32(dst, a ^ b)?;
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src1)?;
            let b = lane.registers.read_u64(src2)?;
            lane.registers.write_u64(dst, a ^ b)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("XOR for type {}", ty))),
    }
    Ok(())
}

pub fn execute_not<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src)?;
            lane.registers.write_i8(dst, !a)?;
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src)?;
            lane.registers.write_i16(dst, !a)?;
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src)?;
            lane.registers.write_i32(dst, !a)?;
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src)?;
            lane.registers.write_i64(dst, !a)?;
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src)?;
            lane.registers.write_u8(dst, !a)?;
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src)?;
            lane.registers.write_u16(dst, !a)?;
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src)?;
            lane.registers.write_u32(dst, !a)?;
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src)?;
            lane.registers.write_u64(dst, !a)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("NOT for type {}", ty))),
    }
    Ok(())
}

pub fn execute_shl<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
    amount: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_i8(dst, a.wrapping_shl(shift))?;
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_i16(dst, a.wrapping_shl(shift))?;
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_i32(dst, a.wrapping_shl(shift))?;
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_i64(dst, a.wrapping_shl(shift))?;
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_u8(dst, a.wrapping_shl(shift))?;
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_u16(dst, a.wrapping_shl(shift))?;
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_u32(dst, a.wrapping_shl(shift))?;
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_u64(dst, a.wrapping_shl(shift))?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("SHL for type {}", ty))),
    }
    Ok(())
}

pub fn execute_shr<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
    amount: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_i8(dst, a.wrapping_shr(shift))?;
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_i16(dst, a.wrapping_shr(shift))?;
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_i32(dst, a.wrapping_shr(shift))?;
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_i64(dst, a.wrapping_shr(shift))?;
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_u8(dst, a.wrapping_shr(shift))?;
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_u16(dst, a.wrapping_shr(shift))?;
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_u32(dst, a.wrapping_shr(shift))?;
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src)?;
            let shift = lane.registers.read_u32(amount)?;
            lane.registers.write_u64(dst, a.wrapping_shr(shift))?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("SHR for type {}", ty))),
    }
    Ok(())
}

// ================================================================================================
// Comparison Instructions (Stubs)
// ================================================================================================

pub fn execute_setcc<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    cond: Condition,
    ty: Type,
    pred: crate::isa::Predicate,
    src1: Register,
    src2: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    let result = match ty {
        Type::I8 => {
            let a = lane.registers.read_i8(src1)?;
            let b = lane.registers.read_i8(src2)?;
            compare_signed(a, b, cond)
        }
        Type::I16 => {
            let a = lane.registers.read_i16(src1)?;
            let b = lane.registers.read_i16(src2)?;
            compare_signed(a, b, cond)
        }
        Type::I32 => {
            let a = lane.registers.read_i32(src1)?;
            let b = lane.registers.read_i32(src2)?;
            compare_signed(a, b, cond)
        }
        Type::I64 => {
            let a = lane.registers.read_i64(src1)?;
            let b = lane.registers.read_i64(src2)?;
            compare_signed(a, b, cond)
        }
        Type::U8 => {
            let a = lane.registers.read_u8(src1)?;
            let b = lane.registers.read_u8(src2)?;
            compare_unsigned(a, b, cond)
        }
        Type::U16 => {
            let a = lane.registers.read_u16(src1)?;
            let b = lane.registers.read_u16(src2)?;
            compare_unsigned(a, b, cond)
        }
        Type::U32 => {
            let a = lane.registers.read_u32(src1)?;
            let b = lane.registers.read_u32(src2)?;
            compare_unsigned(a, b, cond)
        }
        Type::U64 => {
            let a = lane.registers.read_u64(src1)?;
            let b = lane.registers.read_u64(src2)?;
            compare_unsigned(a, b, cond)
        }
        Type::F32 => {
            let a = lane.registers.read_f32(src1)?;
            let b = lane.registers.read_f32(src2)?;
            compare_float(a, b, cond)
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src1)?;
            let b = lane.registers.read_f64(src2)?;
            compare_float(a, b, cond)
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("SETcc for type {}", ty))),
    };
    lane.registers.write_predicate(pred, result)?;
    Ok(())
}

fn compare_signed<T: PartialOrd>(a: T, b: T, cond: Condition) -> bool {
    match cond {
        Condition::EQ => a == b,
        Condition::NE => a != b,
        Condition::LT => a < b,
        Condition::LE => a <= b,
        Condition::GT => a > b,
        Condition::GE => a >= b,
        Condition::LTU | Condition::LEU | Condition::GTU | Condition::GEU => {
            // Unsigned comparisons on signed types are treated as signed
            panic!("Unsigned comparison on signed type")
        }
    }
}

fn compare_unsigned<T: PartialOrd>(a: T, b: T, cond: Condition) -> bool {
    match cond {
        Condition::EQ => a == b,
        Condition::NE => a != b,
        Condition::LT | Condition::LTU => a < b,
        Condition::LE | Condition::LEU => a <= b,
        Condition::GT | Condition::GTU => a > b,
        Condition::GE | Condition::GEU => a >= b,
    }
}

fn compare_float<T: PartialOrd>(a: T, b: T, cond: Condition) -> bool {
    match cond {
        Condition::EQ => a == b,
        Condition::NE => a != b,
        Condition::LT => a < b,
        Condition::LE => a <= b,
        Condition::GT => a > b,
        Condition::GE => a >= b,
        Condition::LTU | Condition::LEU | Condition::GTU | Condition::GEU => {
            // Unsigned comparisons on floats don't make sense
            panic!("Unsigned comparison on float type")
        }
    }
}

// ================================================================================================
// Control Flow Instructions
// ================================================================================================

// ================================================================================================
// Transcendental Functions
// ================================================================================================

pub fn execute_sin<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::F32 => {
            let a = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, a.sin())?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, a.sin())?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("SIN for type {}", ty))),
    }
    Ok(())
}

pub fn execute_cos<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::F32 => {
            let a = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, a.cos())?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, a.cos())?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("COS for type {}", ty))),
    }
    Ok(())
}

pub fn execute_exp<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::F32 => {
            let a = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, a.exp())?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, a.exp())?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("EXP for type {}", ty))),
    }
    Ok(())
}

pub fn execute_log<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::F32 => {
            let a = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, a.ln())?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, a.ln())?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("LOG for type {}", ty))),
    }
    Ok(())
}

pub fn execute_sqrt<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::F32 => {
            let a = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, a.sqrt())?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, a.sqrt())?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("SQRT for type {}", ty))),
    }
    Ok(())
}

pub fn execute_tan<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::F32 => {
            let a = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, a.tan())?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, a.tan())?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("TAN for type {}", ty))),
    }
    Ok(())
}

pub fn execute_tanh<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::F32 => {
            let a = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, a.tanh())?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, a.tanh())?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("TANH for type {}", ty))),
    }
    Ok(())
}

pub fn execute_sigmoid<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::F32 => {
            let a = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, 1.0 / (1.0 + (-a).exp()))?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, 1.0 / (1.0 + (-a).exp()))?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("SIGMOID for type {}", ty))),
    }
    Ok(())
}

pub fn execute_log2<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::F32 => {
            let a = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, a.log2())?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, a.log2())?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("LOG2 for type {}", ty))),
    }
    Ok(())
}

pub fn execute_log10<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::F32 => {
            let a = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, a.log10())?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, a.log10())?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("LOG10 for type {}", ty))),
    }
    Ok(())
}

pub fn execute_rsqrt<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::F32 => {
            let a = lane.registers.read_f32(src)?;
            lane.registers.write_f32(dst, 1.0 / a.sqrt())?;
        }
        Type::F64 => {
            let a = lane.registers.read_f64(src)?;
            lane.registers.write_f64(dst, 1.0 / a.sqrt())?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("RSQRT for type {}", ty))),
    }
    Ok(())
}

// ================================================================================================
// Selection Operation
// ================================================================================================

pub fn execute_sel<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    pred: crate::isa::Predicate,
    src_true: Register,
    src_false: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    let condition = lane.registers.read_predicate(pred)?;

    match ty {
        Type::I8 => {
            let v = if condition {
                lane.registers.read_i8(src_true)?
            } else {
                lane.registers.read_i8(src_false)?
            };
            lane.registers.write_i8(dst, v)?;
        }
        Type::I16 => {
            let v = if condition {
                lane.registers.read_i16(src_true)?
            } else {
                lane.registers.read_i16(src_false)?
            };
            lane.registers.write_i16(dst, v)?;
        }
        Type::I32 => {
            let v = if condition {
                lane.registers.read_i32(src_true)?
            } else {
                lane.registers.read_i32(src_false)?
            };
            lane.registers.write_i32(dst, v)?;
        }
        Type::I64 => {
            let v = if condition {
                lane.registers.read_i64(src_true)?
            } else {
                lane.registers.read_i64(src_false)?
            };
            lane.registers.write_i64(dst, v)?;
        }
        Type::U8 => {
            let v = if condition {
                lane.registers.read_u8(src_true)?
            } else {
                lane.registers.read_u8(src_false)?
            };
            lane.registers.write_u8(dst, v)?;
        }
        Type::U16 => {
            let v = if condition {
                lane.registers.read_u16(src_true)?
            } else {
                lane.registers.read_u16(src_false)?
            };
            lane.registers.write_u16(dst, v)?;
        }
        Type::U32 => {
            let v = if condition {
                lane.registers.read_u32(src_true)?
            } else {
                lane.registers.read_u32(src_false)?
            };
            lane.registers.write_u32(dst, v)?;
        }
        Type::U64 => {
            let v = if condition {
                lane.registers.read_u64(src_true)?
            } else {
                lane.registers.read_u64(src_false)?
            };
            lane.registers.write_u64(dst, v)?;
        }
        Type::F32 => {
            let v = if condition {
                lane.registers.read_f32(src_true)?
            } else {
                lane.registers.read_f32(src_false)?
            };
            lane.registers.write_f32(dst, v)?;
        }
        Type::F64 => {
            let v = if condition {
                lane.registers.read_f64(src_true)?
            } else {
                lane.registers.read_f64(src_false)?
            };
            lane.registers.write_f64(dst, v)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("SEL for type {}", ty))),
    }
    Ok(())
}

// ================================================================================================
// Reduction Operations
// ================================================================================================

pub fn execute_reduce_add<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src_base: Register,
    count: u32,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I32 => {
            let mut sum = 0i32;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                sum = sum.wrapping_add(lane.registers.read_i32(reg)?);
            }
            lane.registers.write_i32(dst, sum)?;
        }
        Type::I64 => {
            let mut sum = 0i64;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                sum = sum.wrapping_add(lane.registers.read_i64(reg)?);
            }
            lane.registers.write_i64(dst, sum)?;
        }
        Type::F32 => {
            let mut sum = 0.0f32;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                sum += lane.registers.read_f32(reg)?;
            }
            lane.registers.write_f32(dst, sum)?;
        }
        Type::F64 => {
            let mut sum = 0.0f64;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                sum += lane.registers.read_f64(reg)?;
            }
            lane.registers.write_f64(dst, sum)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("ReduceAdd for type {}", ty))),
    }
    Ok(())
}

pub fn execute_reduce_min<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src_base: Register,
    count: u32,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I32 => {
            let mut min = i32::MAX;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                min = min.min(lane.registers.read_i32(reg)?);
            }
            lane.registers.write_i32(dst, min)?;
        }
        Type::I64 => {
            let mut min = i64::MAX;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                min = min.min(lane.registers.read_i64(reg)?);
            }
            lane.registers.write_i64(dst, min)?;
        }
        Type::F32 => {
            let mut min = f32::INFINITY;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                min = min.min(lane.registers.read_f32(reg)?);
            }
            lane.registers.write_f32(dst, min)?;
        }
        Type::F64 => {
            let mut min = f64::INFINITY;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                min = min.min(lane.registers.read_f64(reg)?);
            }
            lane.registers.write_f64(dst, min)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("ReduceMin for type {}", ty))),
    }
    Ok(())
}

pub fn execute_reduce_max<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src_base: Register,
    count: u32,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I32 => {
            let mut max = i32::MIN;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                max = max.max(lane.registers.read_i32(reg)?);
            }
            lane.registers.write_i32(dst, max)?;
        }
        Type::I64 => {
            let mut max = i64::MIN;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                max = max.max(lane.registers.read_i64(reg)?);
            }
            lane.registers.write_i64(dst, max)?;
        }
        Type::F32 => {
            let mut max = f32::NEG_INFINITY;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                max = max.max(lane.registers.read_f32(reg)?);
            }
            lane.registers.write_f32(dst, max)?;
        }
        Type::F64 => {
            let mut max = f64::NEG_INFINITY;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                max = max.max(lane.registers.read_f64(reg)?);
            }
            lane.registers.write_f64(dst, max)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("ReduceMax for type {}", ty))),
    }
    Ok(())
}

pub fn execute_reduce_mul<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    dst: Register,
    src_base: Register,
    count: u32,
) -> Result<()> {
    let lane = state.current_lane_mut();
    match ty {
        Type::I32 => {
            let mut product = 1i32;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                product = product.wrapping_mul(lane.registers.read_i32(reg)?);
            }
            lane.registers.write_i32(dst, product)?;
        }
        Type::I64 => {
            let mut product = 1i64;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                product = product.wrapping_mul(lane.registers.read_i64(reg)?);
            }
            lane.registers.write_i64(dst, product)?;
        }
        Type::F32 => {
            let mut product = 1.0f32;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                product *= lane.registers.read_f32(reg)?;
            }
            lane.registers.write_f32(dst, product)?;
        }
        Type::F64 => {
            let mut product = 1.0f64;
            for i in 0..count {
                let reg = Register::new(src_base.index() + i as u8);
                product *= lane.registers.read_f64(reg)?;
            }
            lane.registers.write_f64(dst, product)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("ReduceMul for type {}", ty))),
    }
    Ok(())
}

// ================================================================================================
// Helper Functions

// ================================================================================================
// Pool Storage Operations
// ================================================================================================

pub fn execute_pool_alloc<M: MemoryStorage>(state: &mut ExecutionState<M>, size: u64, dst: Register) -> Result<()> {
    // Allocate pool through memory manager
    let handle = {
        let mut memory = state.shared.memory.write();
        memory.allocate_pool(size as usize)?
    };

    // Store handle ID in destination register as U64
    let lane = state.current_lane_mut();
    lane.registers.write_u64(dst, handle.id())?;

    Ok(())
}

pub fn execute_pool_free<M: MemoryStorage>(state: &mut ExecutionState<M>, handle: Register) -> Result<()> {
    // Read pool handle from register
    let lane = state.current_lane_mut();
    let handle_id = lane.registers.read_u64(handle)?;

    // Free pool through memory manager
    let mut memory = state.shared.memory.write();
    memory.free_pool(PoolHandle::new(handle_id))?;

    Ok(())
}

pub fn execute_pool_load<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    pool: Register,
    offset: Register,
    dst: Register,
) -> Result<()> {
    // Read pool handle and offset from registers
    let (handle_id, offset_val) = {
        let lane = state.current_lane();
        let h = lane.registers.read_u64(pool)?;
        let o = lane.registers.read_u64(offset)?;
        (h, o)
    };

    // Load data from pool
    let value_bytes = {
        let memory = state.shared.memory.read();
        let mut buffer = vec![0u8; ty.size_bytes()];
        memory.copy_from_pool(PoolHandle::new(handle_id), offset_val as usize, &mut buffer)?;
        buffer
    };

    // Write to destination register
    let lane = state.current_lane_mut();
    match ty {
        Type::I8 => {
            let v = *bytemuck::from_bytes::<i8>(&value_bytes);
            lane.registers.write_i8(dst, v)?;
        }
        Type::I16 => {
            let v = *bytemuck::from_bytes::<i16>(&value_bytes);
            lane.registers.write_i16(dst, v)?;
        }
        Type::I32 => {
            let v = *bytemuck::from_bytes::<i32>(&value_bytes);
            lane.registers.write_i32(dst, v)?;
        }
        Type::I64 => {
            let v = *bytemuck::from_bytes::<i64>(&value_bytes);
            lane.registers.write_i64(dst, v)?;
        }
        Type::U8 => {
            let v = *bytemuck::from_bytes::<u8>(&value_bytes);
            lane.registers.write_u8(dst, v)?;
        }
        Type::U16 => {
            let v = *bytemuck::from_bytes::<u16>(&value_bytes);
            lane.registers.write_u16(dst, v)?;
        }
        Type::U32 => {
            let v = *bytemuck::from_bytes::<u32>(&value_bytes);
            lane.registers.write_u32(dst, v)?;
        }
        Type::U64 => {
            let v = *bytemuck::from_bytes::<u64>(&value_bytes);
            lane.registers.write_u64(dst, v)?;
        }
        Type::F32 => {
            let v = *bytemuck::from_bytes::<f32>(&value_bytes);
            lane.registers.write_f32(dst, v)?;
        }
        Type::F64 => {
            let v = *bytemuck::from_bytes::<f64>(&value_bytes);
            lane.registers.write_f64(dst, v)?;
        }
        _ => return Err(BackendError::UnsupportedOperation(format!("PoolLoad for type {}", ty))),
    }

    Ok(())
}

pub fn execute_pool_store<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    ty: Type,
    pool: Register,
    offset: Register,
    src: Register,
) -> Result<()> {
    // Read pool handle, offset, and value from registers
    let (handle_id, offset_val, value_bytes) = {
        let lane = state.current_lane();
        let h = lane.registers.read_u64(pool)?;
        let o = lane.registers.read_u64(offset)?;

        let bytes = match ty {
            Type::I8 => bytemuck::bytes_of(&lane.registers.read_i8(src)?).to_vec(),
            Type::I16 => bytemuck::bytes_of(&lane.registers.read_i16(src)?).to_vec(),
            Type::I32 => bytemuck::bytes_of(&lane.registers.read_i32(src)?).to_vec(),
            Type::I64 => bytemuck::bytes_of(&lane.registers.read_i64(src)?).to_vec(),
            Type::U8 => bytemuck::bytes_of(&lane.registers.read_u8(src)?).to_vec(),
            Type::U16 => bytemuck::bytes_of(&lane.registers.read_u16(src)?).to_vec(),
            Type::U32 => bytemuck::bytes_of(&lane.registers.read_u32(src)?).to_vec(),
            Type::U64 => bytemuck::bytes_of(&lane.registers.read_u64(src)?).to_vec(),
            Type::F32 => bytemuck::bytes_of(&lane.registers.read_f32(src)?).to_vec(),
            Type::F64 => bytemuck::bytes_of(&lane.registers.read_f64(src)?).to_vec(),
            _ => return Err(BackendError::UnsupportedOperation(format!("PoolStore for type {}", ty))),
        };

        (h, o, bytes)
    };

    // Store data to pool
    let mut memory = state.shared.memory.write();
    memory.copy_to_pool(PoolHandle::new(handle_id), offset_val as usize, &value_bytes)?;

    Ok(())
}

// ================================================================================================
// Transcendental Instructions (Stubs)
