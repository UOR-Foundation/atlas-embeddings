//! Special Registers - CUDA-Style Thread Indexing
//!
//! Atlas ISA reserves registers 252-255 for built-in thread indexing values.
//! These registers are pre-loaded by the backend before program execution begins,
//! providing zero-overhead access to thread positioning information.
//!
//! # Special Register Layout
//!
//! | Register | Name            | Type | Description                              |
//! |----------|-----------------|------|------------------------------------------|
//! | R252     | `LANE_IDX_X`    | U32  | Lane X index within block (threadIdx.x)  |
//! | R253     | `BLOCK_IDX_X`   | U32  | Block X index within grid (blockIdx.x)   |
//! | R254     | `BLOCK_DIM_X`   | U32  | Block X dimension (blockDim.x)           |
//! | R255     | `GLOBAL_LANE_ID`| U64  | Global linear lane ID across all blocks  |
//!
//! # Computation
//!
//! The backend pre-computes these values before execution:
//!
//! ```text
//! LANE_IDX_X    = context.lane_idx.0
//! BLOCK_IDX_X   = context.block_idx.0
//! BLOCK_DIM_X   = context.block_dim.x
//! GLOBAL_LANE_ID = block_linear_index * block_dim.total_lanes() + lane_linear_index
//! ```
//!
//! # Usage Example
//!
//! ```text
//! use hologram_backends::isa::{Program, Instruction, Register, Type, Address};
//! use hologram_backends::isa::special_registers::*;
//!
//! // Vector addition: c[i] = a[i] + b[i]
//! let mut program = Program::new();
//!
//! // r1 = global_lane_id * 4 (byte offset for f32)
//! program.instructions.push(Instruction::SHL {
//!     ty: Type::U64,
//!     dst: Register::new(1),
//!     src: GLOBAL_LANE_ID,
//!     amount: 2,  // multiply by 4 (sizeof f32)
//! });
//!
//! // Load a[global_lane_id]
//! program.instructions.push(Instruction::LDG {
//!     ty: Type::F32,
//!     dst: Register::new(2),
//!     addr: Address::RegisterIndirect {
//!         handle: buffer_a,
//!         offset_reg: Register::new(1),
//!     },
//! });
//!
//! // Load b[global_lane_id]
//! program.instructions.push(Instruction::LDG {
//!     ty: Type::F32,
//!     dst: Register::new(3),
//!     addr: Address::RegisterIndirect {
//!         handle: buffer_b,
//!         offset_reg: Register::new(1),
//!     },
//! });
//!
//! // Add: r4 = r2 + r3
//! program.instructions.push(Instruction::ADD {
//!     ty: Type::F32,
//!     dst: Register::new(4),
//!     src1: Register::new(2),
//!     src2: Register::new(3),
//! });
//!
//! // Store c[global_lane_id]
//! program.instructions.push(Instruction::STG {
//!     ty: Type::F32,
//!     src: Register::new(4),
//!     addr: Address::RegisterIndirect {
//!         handle: buffer_c,
//!         offset_reg: Register::new(1),
//!     },
//! });
//!
//! // Execute with 1000 lanes in parallel
//! let config = LaunchConfig::linear(1000, 256);  // 4 blocks × 256 threads
//! backend.execute_program(&program, &config)?;
//! ```
//!
//! # Performance
//!
//! Special registers provide:
//! - **Zero runtime overhead**: Pre-computed before program execution
//! - **No additional instructions**: Values already in registers
//! - **Familiar model**: Matches CUDA/OpenCL `threadIdx`/`blockIdx` semantics
//!
//! # Backend Requirements
//!
//! All backends must initialize special registers before executing the first instruction:
//!
//! ```text
//! // For each lane before execution:
//! lane.registers.write_u32(LANE_IDX_X, context.lane_idx.0)?;
//! lane.registers.write_u32(BLOCK_IDX_X, context.block_idx.0)?;
//! lane.registers.write_u32(BLOCK_DIM_X, context.block_dim.x)?;
//! lane.registers.write_u64(GLOBAL_LANE_ID, context.global_lane_index())?;
//! ```

use crate::isa::Register;

/// Lane X index within block (equivalent to CUDA's `threadIdx.x`)
///
/// Type: U32
///
/// Value range: [0, block_dim.x)
pub const LANE_IDX_X: Register = Register(252);

/// Block X index within grid (equivalent to CUDA's `blockIdx.x`)
///
/// Type: U32
///
/// Value range: [0, grid_dim.x)
pub const BLOCK_IDX_X: Register = Register(253);

/// Block X dimension (equivalent to CUDA's `blockDim.x`)
///
/// Type: U32
///
/// Value: Number of lanes per block in X dimension
pub const BLOCK_DIM_X: Register = Register(254);

/// Global linear lane ID across all blocks
///
/// Type: U64
///
/// Computed as: `block_linear_index * block_dim.total_lanes() + lane_linear_index`
///
/// This is the most commonly used special register for computing array offsets:
///
/// ```text
/// // Compute byte offset for element at global_lane_id
/// let offset = GLOBAL_LANE_ID * element_size;
/// LDG { ty: F32, dst: r0, addr: RegisterIndirect { handle: buf, offset_reg: offset } }
/// ```
pub const GLOBAL_LANE_ID: Register = Register(255);

/// Check if a register is a special register
///
/// Returns true if the register index is in the special register range [252, 255].
pub const fn is_special_register(reg: Register) -> bool {
    reg.index() >= 252
}

/// Get the name of a special register
///
/// Returns a human-readable name for special registers, or None for regular registers.
pub fn special_register_name(reg: Register) -> Option<&'static str> {
    match reg.index() {
        252 => Some("LANE_IDX_X"),
        253 => Some("BLOCK_IDX_X"),
        254 => Some("BLOCK_DIM_X"),
        255 => Some("GLOBAL_LANE_ID"),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_special_register_constants() {
        assert_eq!(LANE_IDX_X.index(), 252);
        assert_eq!(BLOCK_IDX_X.index(), 253);
        assert_eq!(BLOCK_DIM_X.index(), 254);
        assert_eq!(GLOBAL_LANE_ID.index(), 255);
    }

    #[test]
    fn test_is_special_register() {
        assert!(!is_special_register(Register::new(0)));
        assert!(!is_special_register(Register::new(100)));
        assert!(!is_special_register(Register::new(251)));
        assert!(is_special_register(Register::new(252)));
        assert!(is_special_register(Register::new(253)));
        assert!(is_special_register(Register::new(254)));
        assert!(is_special_register(Register::new(255)));
    }

    #[test]
    fn test_special_register_names() {
        assert_eq!(special_register_name(Register::new(252)), Some("LANE_IDX_X"));
        assert_eq!(special_register_name(Register::new(253)), Some("BLOCK_IDX_X"));
        assert_eq!(special_register_name(Register::new(254)), Some("BLOCK_DIM_X"));
        assert_eq!(special_register_name(Register::new(255)), Some("GLOBAL_LANE_ID"));
        assert_eq!(special_register_name(Register::new(0)), None);
        assert_eq!(special_register_name(Register::new(100)), None);
    }

    #[test]
    fn test_all_special_registers_unique() {
        let registers = [LANE_IDX_X, BLOCK_IDX_X, BLOCK_DIM_X, GLOBAL_LANE_ID];
        let mut indices: Vec<u8> = registers.iter().map(|r| r.index()).collect();
        indices.sort();
        indices.dedup();
        assert_eq!(indices.len(), 4, "All special registers must have unique indices");
    }
}
