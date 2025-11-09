//! Common backend infrastructure
//!
//! This module provides shared functionality that can be used across all backend
//! implementations (CPU, GPU, TPU, FPGA, etc.).
//!
//! # Modules
//!
//! - `registers` - Register file implementation (256 typed registers + 16 predicates)
//! - `address` - Address resolution for all addressing modes
//! - `execution_state` - Lane and execution state management
//! - `atlas_ops` - Atlas-specific instruction implementations
//! - `instruction_ops` - Shared instruction implementations (arithmetic, bitwise, control flow, etc.)
//! - `memory` - Memory management traits and utilities

pub mod address;
pub mod atlas_ops;
pub mod execution_state;
pub mod executor_trait;
pub mod instruction_ops;
pub mod memory;
pub mod registers;

// Re-export commonly used types
pub use address::resolve_address;
pub use execution_state::{ExecutionState, LaneState};
pub use memory::{MemoryManager, MemoryStorage};
pub use registers::RegisterFile;

// Tests
#[cfg(test)]
mod instruction_ops_test;
