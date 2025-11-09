//! Address resolution shared across all backends
//!
//! Provides address resolution for all three addressing modes:
//! - BufferOffset: Direct buffer + offset
//! - PhiCoordinate: Atlas categorical × cellular addressing (class, page, byte)
//! - RegisterIndirect: Base register + offset
//!
//! This implementation is shared across CPU, GPU, TPU, and FPGA backends.

use crate::backend::BufferHandle;
use crate::backends::common::memory::MemoryStorage;
use crate::backends::common::ExecutionState;
use crate::error::{BackendError, Result};
use crate::isa::Address;
use atlas_core::{PhiCoordinate, TOTAL_ELEMENTS};

/// Resolve an address to a buffer handle and byte offset
///
/// This function is shared across all backends and provides consistent address
/// resolution semantics.
///
/// # Addressing Modes
///
/// ## BufferOffset
/// Direct addressing with explicit handle and offset:
/// ```text
/// Address::BufferOffset { handle: 5, offset: 128 }
/// → (BufferHandle(5), 128)
/// ```
///
/// ## PhiCoordinate
/// Atlas categorical × cellular addressing using (class, page, byte):
/// ```text
/// Address::PhiCoordinate { class: 42, page: 10, byte: 200 }
/// → Validates page < 48 via atlas-core PhiCoordinate
/// → Calculates linear_index using atlas-core
/// → class_offset = class × 12,288 (TOTAL_ELEMENTS per class)
/// → (BufferHandle(0), class_offset + linear_index)
/// ```
///
/// ## RegisterIndirect
/// Base address from register + signed offset:
/// ```text
/// Address::RegisterIndirect { base: Register(5), offset: -16 }
/// → Requires execution context to read register value
/// → Current limitation: simplified implementation
/// ```
///
/// # Returns
///
/// Returns `(BufferHandle, byte_offset)` for memory access.
///
/// # Errors
///
/// - `InvalidPhiCoordinate` if page ≥ 48 in PhiCoordinate mode
/// - Other errors may be added for RegisterIndirect validation
pub fn resolve_address(addr: &Address) -> Result<(BufferHandle, usize)> {
    match addr {
        Address::BufferOffset { handle, offset } => Ok((BufferHandle(*handle), *offset)),

        Address::PhiCoordinate { class, page, byte } => {
            // Φ-coordinate: (class, page, byte) → linear offset using atlas-core structure
            // Use PhiCoordinate from atlas-core for validation and linear indexing
            let phi = PhiCoordinate::new(*page, *byte)
                .map_err(|e| BackendError::execution_error(format!("Invalid Φ-coordinate: {}", e)))?;

            // Get offset within class using atlas-core's linear_index method
            let page_byte_offset = phi.linear_index();

            // Each class has TOTAL_ELEMENTS (12,288) bytes in atlas-core's categorical structure
            let class_offset = (*class as usize) * TOTAL_ELEMENTS;
            let linear_offset = class_offset + page_byte_offset;

            // Return with buffer handle 0 (default buffer for Φ-coordinate space)
            // Φ-coordinates map to Atlas's categorical × cellular memory structure
            Ok((BufferHandle::new(0), linear_offset))
        }

        Address::RegisterIndirect { base, offset } => {
            // Register-indirect: read base address from register, add offset
            // NOTE: This addressing mode requires execution context to read the register
            // Use resolve_address_with_state() instead for proper register resolution
            Err(BackendError::execution_error(format!(
                "RegisterIndirect addressing requires execution state. Use resolve_address_with_state() instead. Register: {}, offset: {}",
                base, offset
            )))
        }

        Address::RegisterIndirectComputed { handle_reg, offset_reg } => {
            // Register-indirect with computed offset: requires execution context
            // Use resolve_address_with_state() instead for proper register resolution
            Err(BackendError::execution_error(format!(
                "RegisterIndirectComputed addressing requires execution state. Use resolve_address_with_state() instead. Handle register: {}, offset register: {}",
                handle_reg, offset_reg
            )))
        }
    }
}

/// Resolve an address with execution state (supports RegisterIndirect)
///
/// This function extends `resolve_address()` with execution state access,
/// enabling proper RegisterIndirect addressing by reading register values.
///
/// # RegisterIndirect Addressing
///
/// ```text
/// Address::RegisterIndirect { base: Register(1), offset: 16 }
/// → Read register R1 value as u64 (buffer handle)
/// → Read register R1+1 value as u64 (base offset in bytes) - future enhancement
/// → final_offset = base_offset + offset
/// → (BufferHandle(handle_from_r1), final_offset)
/// ```
///
/// Current implementation expects the base register to contain a u64 buffer handle ID,
/// and uses `offset` directly as the byte offset.
///
/// # Arguments
///
/// * `addr` - The address to resolve
/// * `state` - Execution state (needed to read register values for RegisterIndirect)
///
/// # Returns
///
/// Returns `(BufferHandle, byte_offset)` for memory access.
///
/// # Errors
///
/// - Same errors as `resolve_address()`
/// - `UninitializedRegister` if RegisterIndirect base register is not initialized
/// - `TypeMismatch` if RegisterIndirect base register is not U64
pub fn resolve_address_with_state<M: MemoryStorage>(
    addr: &Address,
    state: &ExecutionState<M>,
) -> Result<(BufferHandle, usize)> {
    match addr {
        Address::BufferOffset { .. } | Address::PhiCoordinate { .. } => {
            // Delegate to stateless resolver
            resolve_address(addr)
        }

        Address::RegisterIndirect { base, offset } => {
            // Read buffer handle from register
            let lane = state.current_lane();
            let handle_id = lane.registers.read_u64(*base)?;

            // Apply offset
            let final_offset = if *offset >= 0 {
                *offset as usize
            } else {
                // Negative offset: compute (0 - abs(offset))
                // This will panic if offset is too negative, which is a programming error
                0usize.checked_sub(offset.unsigned_abs() as usize).ok_or_else(|| {
                    BackendError::execution_error(format!(
                        "RegisterIndirect negative offset {} would underflow byte offset",
                        offset
                    ))
                })?
            };

            Ok((BufferHandle::new(handle_id), final_offset))
        }

        Address::RegisterIndirectComputed { handle_reg, offset_reg } => {
            // Read buffer handle and offset from registers
            let lane = state.current_lane();
            let handle_id = lane.registers.read_u64(*handle_reg)?;
            let byte_offset = lane.registers.read_u64(*offset_reg)? as usize;

            Ok((BufferHandle::new(handle_id), byte_offset))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isa::Register;

    #[test]
    fn test_buffer_offset_resolution() {
        let addr = Address::BufferOffset { handle: 5, offset: 128 };
        let (handle, offset) = resolve_address(&addr).unwrap();
        assert_eq!(handle.id(), 5);
        assert_eq!(offset, 128);
    }

    #[test]
    fn test_phi_coordinate_resolution() {
        // Class 0, page 0, byte 0 → offset 0
        let addr = Address::PhiCoordinate {
            class: 0,
            page: 0,
            byte: 0,
        };
        let (handle, offset) = resolve_address(&addr).unwrap();
        assert_eq!(handle.id(), 0);
        assert_eq!(offset, 0);

        // Class 0, page 0, byte 255 → offset 255
        let addr = Address::PhiCoordinate {
            class: 0,
            page: 0,
            byte: 255,
        };
        let (handle, offset) = resolve_address(&addr).unwrap();
        assert_eq!(handle.id(), 0);
        assert_eq!(offset, 255);

        // Class 0, page 1, byte 0 → offset 256
        let addr = Address::PhiCoordinate {
            class: 0,
            page: 1,
            byte: 0,
        };
        let (handle, offset) = resolve_address(&addr).unwrap();
        assert_eq!(handle.id(), 0);
        assert_eq!(offset, 256);

        // Class 1, page 0, byte 0 → offset 12,288 (TOTAL_ELEMENTS)
        let addr = Address::PhiCoordinate {
            class: 1,
            page: 0,
            byte: 0,
        };
        let (handle, offset) = resolve_address(&addr).unwrap();
        assert_eq!(handle.id(), 0);
        assert_eq!(offset, TOTAL_ELEMENTS);
    }

    #[test]
    fn test_phi_coordinate_invalid_page() {
        // Page 48 is invalid (must be < 48)
        let addr = Address::PhiCoordinate {
            class: 0,
            page: 48,
            byte: 0,
        };
        let result = resolve_address(&addr);
        assert!(result.is_err());
    }

    #[test]
    fn test_register_indirect_requires_state() {
        // RegisterIndirect addressing requires execution state
        let addr = Address::RegisterIndirect {
            base: Register::new(10),
            offset: 64,
        };

        // Should error when using stateless resolver
        let result = resolve_address(&addr);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("RegisterIndirect addressing requires execution state"));
    }

    #[test]
    fn test_register_indirect_with_state() {
        use crate::backend::{BlockDim, GridDim};
        use crate::backends::common::execution_state::ExecutionState;
        use crate::backends::common::memory::MemoryStorage;
        use parking_lot::RwLock;
        use std::sync::Arc;

        // Mock memory storage for testing
        struct MockStorage;
        impl MemoryStorage for MockStorage {
            fn allocate_buffer(&mut self, _size: usize) -> crate::error::Result<crate::backend::BufferHandle> {
                Ok(crate::backend::BufferHandle::new(0))
            }
            fn free_buffer(&mut self, _handle: crate::backend::BufferHandle) -> crate::error::Result<()> {
                Ok(())
            }
            fn copy_to_buffer(
                &mut self,
                _handle: crate::backend::BufferHandle,
                _data: &[u8],
            ) -> crate::error::Result<()> {
                Ok(())
            }
            fn copy_from_buffer(
                &self,
                _handle: crate::backend::BufferHandle,
                _data: &mut [u8],
            ) -> crate::error::Result<()> {
                Ok(())
            }
            fn buffer_size(&self, _handle: crate::backend::BufferHandle) -> crate::error::Result<usize> {
                Ok(0)
            }
            fn allocate_pool(&mut self, _size: usize) -> crate::error::Result<crate::backend::PoolHandle> {
                Ok(crate::backend::PoolHandle::new(0))
            }
            fn free_pool(&mut self, _handle: crate::backend::PoolHandle) -> crate::error::Result<()> {
                Ok(())
            }
            fn copy_to_pool(
                &mut self,
                _handle: crate::backend::PoolHandle,
                _offset: usize,
                _data: &[u8],
            ) -> crate::error::Result<()> {
                Ok(())
            }
            fn copy_from_pool(
                &self,
                _handle: crate::backend::PoolHandle,
                _offset: usize,
                _data: &mut [u8],
            ) -> crate::error::Result<()> {
                Ok(())
            }
            fn pool_size(&self, _handle: crate::backend::PoolHandle) -> crate::error::Result<usize> {
                Ok(0)
            }
        }

        let memory = Arc::new(RwLock::new(MockStorage));
        let context =
            crate::backend::ExecutionContext::new((0, 0, 0), (0, 0, 0), GridDim::new(1, 1, 1), BlockDim::new(1, 1, 1));
        let labels = std::collections::HashMap::new();

        let mut state = ExecutionState::new(1, memory, context, labels);

        // Initialize the base register with a buffer handle
        let base_reg = Register::new(10);
        state.lane_states[0].lane.registers.write_u64(base_reg, 42).unwrap();

        // Test positive offset
        let addr_pos = Address::RegisterIndirect {
            base: base_reg,
            offset: 64,
        };
        let (handle, offset) = resolve_address_with_state(&addr_pos, &state).unwrap();
        assert_eq!(handle.id(), 42);
        assert_eq!(offset, 64);

        // Test zero offset
        let addr_zero = Address::RegisterIndirect {
            base: base_reg,
            offset: 0,
        };
        let (handle, offset) = resolve_address_with_state(&addr_zero, &state).unwrap();
        assert_eq!(handle.id(), 42);
        assert_eq!(offset, 0);
    }
}
