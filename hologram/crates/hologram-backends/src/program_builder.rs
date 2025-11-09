//! Program builder utilities for creating ISA programs
//!
//! This module provides reusable patterns for constructing ISA programs.
//! These builders are used both for runtime program creation (Plan B) and
//! can be reused during compile-time precompilation (Plan C).
//!
//! # Architecture
//!
//! Program builders follow common patterns:
//! - **Element-wise operations**: Parallel execution using GLOBAL_LANE_ID
//! - **Reductions**: Single-thread aggregation
//! - **Memory operations**: Efficient load/store patterns
//!
//! # Example
//!
//! ```text
//! use hologram_backends::program_builder::create_element_wise_binary;
//! use hologram_backends::isa::{Instruction, Type};
//!
//! let program = create_element_wise_binary(
//!     buf_a, buf_b, buf_c,
//!     Type::F32,
//!     |src1, src2, dst| Instruction::ADD { ty: Type::F32, dst, src1, src2 }
//! );
//! ```

use crate::isa::special_registers::*;
use crate::isa::{Address, Instruction, Program, Register, Type};
use std::collections::HashMap;

/// Create an element-wise binary operation program
///
/// This is the most common pattern for parallel operations. Each lane processes
/// one element using GLOBAL_LANE_ID for indexing.
///
/// # Parameters
///
/// - `buf_a`: Buffer handle for first input
/// - `buf_b`: Buffer handle for second input
/// - `buf_c`: Buffer handle for output
/// - `ty`: Element type (F32, I32, etc.)
/// - `op_fn`: Function that creates the operation instruction
///
/// # Generated Pattern
///
/// ```text
/// R1 = buf_a                      // Load buffer handles
/// R2 = buf_b
/// R3 = buf_c
/// R250 = 2                        // Shift amount for type size
/// R0 = GLOBAL_LANE_ID << 2        // Compute byte offset
/// R10 = load(R1 + R0)             // Load a[global_id]
/// R11 = load(R2 + R0)             // Load b[global_id]
/// R12 = op(R10, R11)              // Perform operation
/// store(R3 + R0, R12)             // Store c[global_id]
/// EXIT
/// ```
///
/// # Performance
///
/// - Program creation: ~100ns (one-time cost, or cached)
/// - Execution: ~10-20ns per element (highly parallel)
pub fn create_element_wise_binary<F>(buf_a: u64, buf_b: u64, buf_c: u64, ty: Type, op_fn: F) -> Program
where
    F: FnOnce(Register, Register, Register) -> Instruction,
{
    let shift_amount = type_size_shift(ty);

    Program {
        instructions: vec![
            // Load buffer handles into registers
            Instruction::MOV_IMM {
                ty: Type::U64,
                dst: Register(1),
                value: buf_a,
            },
            Instruction::MOV_IMM {
                ty: Type::U64,
                dst: Register(2),
                value: buf_b,
            },
            Instruction::MOV_IMM {
                ty: Type::U64,
                dst: Register(3),
                value: buf_c,
            },
            // Compute byte offset from GLOBAL_LANE_ID
            Instruction::MOV_IMM {
                ty: Type::U32,
                dst: Register(250),
                value: shift_amount,
            },
            Instruction::SHL {
                ty: Type::U64,
                dst: Register(0),
                src: GLOBAL_LANE_ID,
                amount: Register(250),
            },
            // Load operands
            Instruction::LDG {
                ty,
                dst: Register(10),
                addr: Address::RegisterIndirectComputed {
                    handle_reg: Register(1),
                    offset_reg: Register(0),
                },
            },
            Instruction::LDG {
                ty,
                dst: Register(11),
                addr: Address::RegisterIndirectComputed {
                    handle_reg: Register(2),
                    offset_reg: Register(0),
                },
            },
            // Perform operation
            op_fn(Register(10), Register(11), Register(12)),
            // Store result
            Instruction::STG {
                ty,
                src: Register(12),
                addr: Address::RegisterIndirectComputed {
                    handle_reg: Register(3),
                    offset_reg: Register(0),
                },
            },
            Instruction::EXIT,
        ],
        labels: HashMap::new(),
    }
}

/// Create an element-wise unary operation program
///
/// Similar to binary operations but with a single input buffer.
///
/// # Parameters
///
/// - `buf_a`: Buffer handle for input
/// - `buf_c`: Buffer handle for output
/// - `ty`: Element type (F32, I32, etc.)
/// - `op_fn`: Function that creates the operation instruction
///
/// # Generated Pattern
///
/// ```text
/// R1 = buf_a
/// R3 = buf_c
/// R250 = 2
/// R0 = GLOBAL_LANE_ID << 2
/// R10 = load(R1 + R0)
/// R12 = op(R10)
/// store(R3 + R0, R12)
/// EXIT
/// ```
pub fn create_element_wise_unary<F>(buf_a: u64, buf_c: u64, ty: Type, op_fn: F) -> Program
where
    F: FnOnce(Register, Register) -> Instruction,
{
    let shift_amount = type_size_shift(ty);

    Program {
        instructions: vec![
            // Load buffer handles
            Instruction::MOV_IMM {
                ty: Type::U64,
                dst: Register(1),
                value: buf_a,
            },
            Instruction::MOV_IMM {
                ty: Type::U64,
                dst: Register(3),
                value: buf_c,
            },
            // Compute byte offset
            Instruction::MOV_IMM {
                ty: Type::U32,
                dst: Register(250),
                value: shift_amount,
            },
            Instruction::SHL {
                ty: Type::U64,
                dst: Register(0),
                src: GLOBAL_LANE_ID,
                amount: Register(250),
            },
            // Load operand
            Instruction::LDG {
                ty,
                dst: Register(10),
                addr: Address::RegisterIndirectComputed {
                    handle_reg: Register(1),
                    offset_reg: Register(0),
                },
            },
            // Perform operation
            op_fn(Register(10), Register(12)),
            // Store result
            Instruction::STG {
                ty,
                src: Register(12),
                addr: Address::RegisterIndirectComputed {
                    handle_reg: Register(3),
                    offset_reg: Register(0),
                },
            },
            Instruction::EXIT,
        ],
        labels: HashMap::new(),
    }
}

/// Get the shift amount for a type's byte size
///
/// Returns the number of bits to shift left to multiply by the type size:
/// - 1 byte (i8, u8): shift 0 (multiply by 1)
/// - 2 bytes (i16, u16, f16, bf16): shift 1 (multiply by 2)
/// - 4 bytes (i32, u32, f32): shift 2 (multiply by 4)
/// - 8 bytes (i64, u64, f64): shift 3 (multiply by 8)
fn type_size_shift(ty: Type) -> u64 {
    match ty {
        Type::I8 | Type::U8 => 0,
        Type::I16 | Type::U16 | Type::F16 | Type::BF16 => 1,
        Type::I32 | Type::U32 | Type::F32 => 2,
        Type::I64 | Type::U64 | Type::F64 => 3,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_size_shift() {
        assert_eq!(type_size_shift(Type::I8), 0);
        assert_eq!(type_size_shift(Type::U8), 0);
        assert_eq!(type_size_shift(Type::I16), 1);
        assert_eq!(type_size_shift(Type::F16), 1);
        assert_eq!(type_size_shift(Type::I32), 2);
        assert_eq!(type_size_shift(Type::F32), 2);
        assert_eq!(type_size_shift(Type::I64), 3);
        assert_eq!(type_size_shift(Type::F64), 3);
    }

    #[test]
    fn test_create_element_wise_binary() {
        let program = create_element_wise_binary(100, 200, 300, Type::F32, |src1, src2, dst| Instruction::ADD {
            ty: Type::F32,
            dst,
            src1,
            src2,
        });

        // Should have expected number of instructions
        assert_eq!(program.instructions.len(), 10);

        // First instruction should load buffer handle
        if let Instruction::MOV_IMM { value, .. } = program.instructions[0] {
            assert_eq!(value, 100);
        } else {
            panic!("Expected MOV_IMM");
        }

        // Operation should be ADD
        if let Instruction::ADD { .. } = program.instructions[7] {
            // Good
        } else {
            panic!("Expected ADD instruction at position 7");
        }

        // Last instruction should be EXIT
        assert!(matches!(program.instructions[9], Instruction::EXIT));
    }

    #[test]
    fn test_create_element_wise_unary() {
        let program = create_element_wise_unary(100, 300, Type::F32, |src, dst| Instruction::ABS {
            ty: Type::F32,
            dst,
            src,
        });

        // Unary should have fewer instructions than binary
        assert_eq!(program.instructions.len(), 8);

        // Should have ABS operation
        if let Instruction::ABS { .. } = program.instructions[5] {
            // Good
        } else {
            panic!("Expected ABS instruction");
        }
    }
}
