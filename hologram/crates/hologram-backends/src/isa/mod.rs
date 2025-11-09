//! Atlas ISA (Instruction Set Architecture)
//!
//! This module defines the complete Atlas ISA instruction set as specified in the
//! Atlas ISA specification. All backends implementing `Backend` MUST support the
//! complete instruction set defined here.
//!
//! # Architecture
//!
//! - **Register-based**: 256 typed registers (0-255)
//! - **Predicate registers**: 16 boolean predicates (0-15)
//! - **Typed operations**: All operations specify their type explicitly
//! - **Type safety**: CVT instruction for explicit type conversions
//!
//! # Instruction Categories
//!
//! - **Data Movement**: LDG, STG, LDS, STS, MOV, CVT
//! - **Arithmetic**: ADD, SUB, MUL, DIV, MAD, FMA, MIN, MAX, ABS, NEG
//! - **Logic**: AND, OR, XOR, NOT, SHL, SHR, SETcc, SEL
//! - **Control Flow**: BRA, CALL, RET, LOOP, EXIT
//! - **Synchronization**: BarSync, MemFence
//! - **Atlas-Specific**: ClsGet, MIRROR, UnityTest, NBR*, ResAccum, Phase*, BoundMap
//! - **Reductions**: ReduceAdd, ReduceMin, ReduceMax, ReduceMul
//! - **Transcendentals**: EXP, LOG, SQRT, SIN, COS, TANH, etc.
//! - **Pool Storage**: PoolAlloc, PoolFree, PoolLoad, PoolStore

mod instruction;
mod program;
pub mod special_registers;
mod types;

pub use instruction::{Instruction, InstructionCategory};
pub use program::{Program, ProgramError, ProgramResult};
pub use types::{Address, Condition, Label, MemoryScope, Predicate, Register, Type};
