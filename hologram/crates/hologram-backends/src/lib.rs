//! Backend implementations for hologram kernel execution
//!
//! This crate provides:
//! - **Atlas ISA**: Complete instruction set architecture
//! - **Backend Trait**: Pluggable backend interface
//! - **CPU Backend**: Reference CPU implementation
//! - **Pool Storage**: O(1) space streaming computation
//!
//! # Architecture
//!
//! The hologram-backends crate enables kernel execution across diverse hardware:
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────┐
//! │                    Hologram Kernel                       │
//! │              (Sigmatics Circuit Compiled)                │
//! └─────────────────────┬───────────────────────────────────┘
//!                       │
//!                       ▼
//! ┌─────────────────────────────────────────────────────────┐
//! │                     Atlas ISA                            │
//! │  (Instruction Set: 50+ ops + Pool Storage)               │
//! └─────────────────────┬───────────────────────────────────┘
//!                       │
//!         ┌─────────────┼─────────────┬─────────────┐
//!         ▼             ▼             ▼             ▼
//!   ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐
//!   │   CPU   │  │   GPU   │  │   TPU   │  │  FPGA   │
//!   │ Backend │  │ Backend │  │ Backend │  │ Backend │
//!   └─────────┘  └─────────┘  └─────────┘  └─────────┘
//! ```
//!
//! # Usage
//!
//! ```rust
//! use hologram_backends::{CpuBackend, Backend, Program, Instruction, Register, Type};
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! // Create backend
//! let mut backend = CpuBackend::new();
//!
//! // Allocate buffer and initialize with data
//! let buffer = backend.allocate_buffer(16)?;
//! let data = vec![1.0f32, 2.0f32, 3.0f32, 4.0f32];
//! backend.copy_to_buffer(buffer, bytemuck::cast_slice(&data))?;
//!
//! // Create program that loads values and performs addition
//! let mut program = Program::new();
//! program.instructions.push(Instruction::LDG {
//!     ty: Type::F32,
//!     dst: Register::new(1),
//!     addr: hologram_backends::Address::BufferOffset { handle: buffer.id(), offset: 0 },
//! });
//! program.instructions.push(Instruction::LDG {
//!     ty: Type::F32,
//!     dst: Register::new(2),
//!     addr: hologram_backends::Address::BufferOffset { handle: buffer.id(), offset: 4 },
//! });
//! program.instructions.push(Instruction::ADD {
//!     ty: Type::F32,
//!     dst: Register::new(0),
//!     src1: Register::new(1),
//!     src2: Register::new(2),
//! });
//!
//! // Execute
//! let config = Default::default();
//! backend.execute_program(&program, &config)?;
//!
//! backend.free_buffer(buffer)?;
//! # Ok(())
//! # }
//! ```

pub mod backend;
pub mod backends;
pub mod error;
pub mod isa;
pub mod json_to_isa;
pub mod pool;
pub mod program_builder;
pub mod program_cache;
pub mod sigmatics_to_isa;

// Re-export public API
pub use backend::{Backend, BufferHandle, LaunchConfig, PoolHandle};
pub use backends::{CpuBackend, CudaBackend, MetalBackend};
pub use error::{BackendError, Result};
pub use isa::{
    Address, Condition, Instruction, InstructionCategory, Label, MemoryScope, Predicate, Program, ProgramError,
    ProgramResult, Register, Type,
};
pub use pool::LinearPool;
pub use program_cache::{ProgramCache, ProgramKey};
