//! Address Builder for Memory Operations
//!
//! Utilities for constructing ISA Address values from buffer handles and offsets.

use hologram_backends::{Address, BufferHandle as BackendHandle, Register};

/// Builder for ISA addresses
///
/// Provides convenient methods for creating Address values from buffer handles.
#[derive(Debug)]
pub struct AddressBuilder;

impl AddressBuilder {
    /// Create direct address: buffer[offset]
    pub fn direct(handle: BackendHandle, offset: usize) -> Address {
        Address::BufferOffset {
            handle: handle.0,
            offset,
        }
    }

    /// Create direct address for element index
    ///
    /// Automatically multiplies by element size for f32 (4 bytes)
    pub fn element_f32(handle: BackendHandle, index: usize) -> Address {
        Address::BufferOffset {
            handle: handle.0,
            offset: index * 4,
        }
    }

    /// Create direct address for element index (generic size)
    pub fn element(handle: BackendHandle, index: usize, element_size: usize) -> Address {
        Address::BufferOffset {
            handle: handle.0,
            offset: index * element_size,
        }
    }

    /// Create register-indirect address: buffer[base_reg]
    pub fn indirect(_handle: BackendHandle, base: Register) -> Address {
        Address::RegisterIndirect { base, offset: 0 }
    }

    /// Create register-indirect with offset: buffer[base_reg + offset]
    pub fn indirect_offset(_handle: BackendHandle, base: Register, offset: i32) -> Address {
        // Note: Current Address enum doesn't include handle in RegisterIndirect
        // For Phase 9, we'll use BufferOffset addresses for simplicity
        // Future: Enhance Address enum to support buffer handles in indirect mode
        Address::RegisterIndirect { base, offset }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_direct_address() {
        let handle = BackendHandle(1);
        let addr = AddressBuilder::direct(handle, 100);

        match addr {
            Address::BufferOffset { handle: h, offset } => {
                assert_eq!(h, 1);
                assert_eq!(offset, 100);
            }
            _ => panic!("Expected BufferOffset address"),
        }
    }

    #[test]
    fn test_element_address() {
        let handle = BackendHandle(2);
        let addr = AddressBuilder::element_f32(handle, 10);

        match addr {
            Address::BufferOffset { handle: h, offset } => {
                assert_eq!(h, 2);
                assert_eq!(offset, 40); // 10 * 4 bytes
            }
            _ => panic!("Expected BufferOffset address"),
        }
    }

    #[test]
    fn test_indirect_address() {
        use hologram_backends::Register;

        let handle = BackendHandle(3);
        let addr = AddressBuilder::indirect(handle, Register::new(5));

        match addr {
            Address::RegisterIndirect { base, offset } => {
                assert_eq!(base.index(), 5);
                assert_eq!(offset, 0);
            }
            _ => panic!("Expected RegisterIndirect address"),
        }
    }
}
