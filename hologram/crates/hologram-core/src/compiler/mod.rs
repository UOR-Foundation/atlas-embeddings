//! ISA Program Compilation Utilities
//!
//! This module provides utilities for building ISA Programs:
//! - `ProgramBuilder`: Fluent API for constructing ISA programs
//! - `RegisterAllocator`, `PredicateAllocator`: Register management
//! - `AddressBuilder`: Memory address construction

pub mod address;
pub mod builder;
pub mod registers;

// Re-export primary types for convenience
pub use address::AddressBuilder;
pub use builder::ProgramBuilder;
pub use registers::{PredicateAllocator, RegisterAllocator};
