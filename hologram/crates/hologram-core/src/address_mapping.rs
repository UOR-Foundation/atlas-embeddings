//! Address mapping utilities for PhiCoordinate addressing
//!
//! This module provides utilities to convert between linear buffer offsets
//! and PhiCoordinate addresses for cache-resident boundary pool operations.
//!
//! # Cache-Resident Architecture
//!
//! PhiCoordinate addressing enables O(1) space complexity through circuit-as-index
//! resolution, mapping arbitrary input sizes to a fixed 1.125 MB boundary pool.
//!
//! ## Address Format
//!
//! ```text
//! PhiCoordinate {
//!     class: u8,  // 0-95 (96 total classes)
//!     page: u8,   // 0-47 (48 pages per class)
//!     byte: u8,   // 0-255 (256 bytes per page)
//! }
//! ```
//!
//! ## Memory Layout
//!
//! Each class contains 12,288 bytes (48 pages × 256 bytes):
//! - Total pool: 96 classes × 12,288 bytes = 1,179,648 bytes (1.125 MB)
//! - L1 cache: 8 hot classes × 4,096 bytes = 32 KB
//! - L2/L3 cache: 96 classes × 12,288 bytes = 1.125 MB
//!
//! # Example
//!
//! ```
//! use hologram_core::address_mapping::{offset_to_phi_coordinate, fits_in_class};
//!
//! // Convert offset 1024 in class 42 to PhiCoordinate
//! let addr = offset_to_phi_coordinate(42, 1024).unwrap();
//! // Result: PhiCoordinate { class: 42, page: 4, byte: 0 }
//!
//! // Check if 3072 f32 elements fit in single class
//! assert!(fits_in_class::<f32>(3072));  // 12,288 bytes
//! assert!(!fits_in_class::<f32>(3073)); // 12,292 bytes (exceeds limit)
//! ```

use crate::error::{Error, Result};
use hologram_backends::Address;

/// Bytes per class in boundary pool
///
/// Each class contains 48 pages × 256 bytes = 12,288 bytes
pub const BYTES_PER_CLASS: usize = 12_288;

/// Pages per class (0-47)
pub const PAGES_PER_CLASS: usize = 48;

/// Bytes per page (0-255)
pub const BYTES_PER_PAGE: usize = 256;

/// Convert linear offset within a class to PhiCoordinate address
///
/// # Arguments
///
/// * `class` - Class index (0-95)
/// * `offset` - Byte offset within the class (0-12,287)
///
/// # Returns
///
/// PhiCoordinate address with page and byte calculated from offset
///
/// # Errors
///
/// Returns error if:
/// - `class >= 96`
/// - `offset >= 12,288`
///
/// # Example
///
/// ```
/// use hologram_core::address_mapping::offset_to_phi_coordinate;
/// use hologram_backends::Address;
///
/// // First byte of class 0
/// let addr = offset_to_phi_coordinate(0, 0).unwrap();
/// assert_eq!(addr, Address::PhiCoordinate { class: 0, page: 0, byte: 0 });
///
/// // Last byte of first page
/// let addr = offset_to_phi_coordinate(42, 255).unwrap();
/// assert_eq!(addr, Address::PhiCoordinate { class: 42, page: 0, byte: 255 });
///
/// // First byte of second page
/// let addr = offset_to_phi_coordinate(42, 256).unwrap();
/// assert_eq!(addr, Address::PhiCoordinate { class: 42, page: 1, byte: 0 });
///
/// // Last byte of class
/// let addr = offset_to_phi_coordinate(95, 12287).unwrap();
/// assert_eq!(addr, Address::PhiCoordinate { class: 95, page: 47, byte: 255 });
/// ```
pub fn offset_to_phi_coordinate(class: u8, offset: usize) -> Result<Address> {
    // Validate class index
    if class >= 96 {
        return Err(Error::InvalidOperation(format!(
            "Invalid class index: {} (must be < 96)",
            class
        )));
    }

    // Validate offset
    if offset >= BYTES_PER_CLASS {
        return Err(Error::InvalidOperation(format!(
            "Offset {} exceeds class capacity {} bytes",
            offset, BYTES_PER_CLASS
        )));
    }

    // Calculate page and byte from linear offset
    let page = (offset / BYTES_PER_PAGE) as u8; // 0-47
    let byte = (offset % BYTES_PER_PAGE) as u8; // 0-255

    Ok(Address::PhiCoordinate { class, page, byte })
}

/// Convert PhiCoordinate address back to linear offset
///
/// This is useful for validation and testing roundtrip conversions.
///
/// # Arguments
///
/// * `class` - Class index (0-95)
/// * `page` - Page within class (0-47)
/// * `byte` - Byte within page (0-255)
///
/// # Returns
///
/// Linear offset within the class (0-12,287)
///
/// # Errors
///
/// Returns error if:
/// - `class >= 96`
/// - `page >= 48`
///
/// # Example
///
/// ```
/// use hologram_core::address_mapping::phi_coordinate_to_offset;
///
/// // First byte
/// assert_eq!(phi_coordinate_to_offset(0, 0, 0).unwrap(), 0);
///
/// // Last byte of first page
/// assert_eq!(phi_coordinate_to_offset(42, 0, 255).unwrap(), 255);
///
/// // First byte of second page
/// assert_eq!(phi_coordinate_to_offset(42, 1, 0).unwrap(), 256);
///
/// // Last byte of class
/// assert_eq!(phi_coordinate_to_offset(95, 47, 255).unwrap(), 12287);
/// ```
pub fn phi_coordinate_to_offset(class: u8, page: u8, byte: u8) -> Result<usize> {
    // Validate class index
    if class >= 96 {
        return Err(Error::InvalidOperation(format!(
            "Invalid class index: {} (must be < 96)",
            class
        )));
    }

    // Validate page index
    if page >= PAGES_PER_CLASS as u8 {
        return Err(Error::InvalidOperation(format!(
            "Invalid page index: {} (must be < {})",
            page, PAGES_PER_CLASS
        )));
    }

    // Calculate linear offset
    let offset = (page as usize * BYTES_PER_PAGE) + byte as usize;

    Ok(offset)
}

/// Check if buffer of given length fits in a single class
///
/// Each class can hold 12,288 bytes. This function checks if a buffer
/// of `len` elements of type `T` fits within this limit.
///
/// # Type Parameters
///
/// * `T` - Element type (size determined via `std::mem::size_of`)
///
/// # Arguments
///
/// * `len` - Number of elements
///
/// # Returns
///
/// `true` if `len * sizeof(T) <= 12,288`, `false` otherwise
///
/// # Example
///
/// ```
/// use hologram_core::address_mapping::fits_in_class;
///
/// // f32 (4 bytes): 3,072 elements = 12,288 bytes ✓
/// assert!(fits_in_class::<f32>(3072));
/// assert!(!fits_in_class::<f32>(3073));
///
/// // f64 (8 bytes): 1,536 elements = 12,288 bytes ✓
/// assert!(fits_in_class::<f64>(1536));
/// assert!(!fits_in_class::<f64>(1537));
///
/// // u8 (1 byte): 12,288 elements = 12,288 bytes ✓
/// assert!(fits_in_class::<u8>(12288));
/// assert!(!fits_in_class::<u8>(12289));
///
/// // i32 (4 bytes): 3,072 elements = 12,288 bytes ✓
/// assert!(fits_in_class::<i32>(3072));
/// assert!(!fits_in_class::<i32>(3073));
/// ```
pub fn fits_in_class<T>(len: usize) -> bool {
    len * std::mem::size_of::<T>() <= BYTES_PER_CLASS
}

/// Calculate the number of elements of type T that fit in a single class
///
/// # Type Parameters
///
/// * `T` - Element type
///
/// # Returns
///
/// Maximum number of elements of type `T` that fit in 12,288 bytes
///
/// # Example
///
/// ```
/// use hologram_core::address_mapping::max_elements_per_class;
///
/// assert_eq!(max_elements_per_class::<f32>(), 3072);  // 12,288 / 4
/// assert_eq!(max_elements_per_class::<f64>(), 1536);  // 12,288 / 8
/// assert_eq!(max_elements_per_class::<u8>(), 12288);  // 12,288 / 1
/// assert_eq!(max_elements_per_class::<i32>(), 3072);  // 12,288 / 4
/// ```
pub fn max_elements_per_class<T>() -> usize {
    BYTES_PER_CLASS / std::mem::size_of::<T>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_offset_to_phi_coordinate_first_byte() {
        let addr = offset_to_phi_coordinate(0, 0).unwrap();
        assert_eq!(
            addr,
            Address::PhiCoordinate {
                class: 0,
                page: 0,
                byte: 0
            }
        );
    }

    #[test]
    fn test_offset_to_phi_coordinate_last_byte_of_first_page() {
        let addr = offset_to_phi_coordinate(42, 255).unwrap();
        assert_eq!(
            addr,
            Address::PhiCoordinate {
                class: 42,
                page: 0,
                byte: 255
            }
        );
    }

    #[test]
    fn test_offset_to_phi_coordinate_first_byte_of_second_page() {
        let addr = offset_to_phi_coordinate(42, 256).unwrap();
        assert_eq!(
            addr,
            Address::PhiCoordinate {
                class: 42,
                page: 1,
                byte: 0
            }
        );
    }

    #[test]
    fn test_offset_to_phi_coordinate_middle_offset() {
        // Offset 1024 = page 4, byte 0 (1024 / 256 = 4, 1024 % 256 = 0)
        let addr = offset_to_phi_coordinate(42, 1024).unwrap();
        assert_eq!(
            addr,
            Address::PhiCoordinate {
                class: 42,
                page: 4,
                byte: 0
            }
        );
    }

    #[test]
    fn test_offset_to_phi_coordinate_last_byte_of_class() {
        // Last byte: offset 12,287 = page 47, byte 255
        let addr = offset_to_phi_coordinate(95, 12287).unwrap();
        assert_eq!(
            addr,
            Address::PhiCoordinate {
                class: 95,
                page: 47,
                byte: 255
            }
        );
    }

    #[test]
    fn test_offset_to_phi_coordinate_invalid_class() {
        let result = offset_to_phi_coordinate(96, 0);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Invalid class index: 96"));
    }

    #[test]
    fn test_offset_to_phi_coordinate_out_of_bounds_offset() {
        let result = offset_to_phi_coordinate(0, 12288);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("exceeds class capacity"));
    }

    #[test]
    fn test_phi_coordinate_to_offset_first_byte() {
        assert_eq!(phi_coordinate_to_offset(0, 0, 0).unwrap(), 0);
    }

    #[test]
    fn test_phi_coordinate_to_offset_last_byte_of_first_page() {
        assert_eq!(phi_coordinate_to_offset(42, 0, 255).unwrap(), 255);
    }

    #[test]
    fn test_phi_coordinate_to_offset_first_byte_of_second_page() {
        assert_eq!(phi_coordinate_to_offset(42, 1, 0).unwrap(), 256);
    }

    #[test]
    fn test_phi_coordinate_to_offset_middle() {
        assert_eq!(phi_coordinate_to_offset(42, 4, 0).unwrap(), 1024);
    }

    #[test]
    fn test_phi_coordinate_to_offset_last_byte_of_class() {
        assert_eq!(phi_coordinate_to_offset(95, 47, 255).unwrap(), 12287);
    }

    #[test]
    fn test_phi_coordinate_to_offset_invalid_class() {
        let result = phi_coordinate_to_offset(96, 0, 0);
        assert!(result.is_err());
    }

    #[test]
    fn test_phi_coordinate_to_offset_invalid_page() {
        let result = phi_coordinate_to_offset(0, 48, 0);
        assert!(result.is_err());
    }

    #[test]
    fn test_roundtrip_conversion() {
        // Test roundtrip: offset -> phi -> offset
        for class in [0, 42, 95] {
            for offset in [0, 255, 256, 1024, 12287] {
                let addr = offset_to_phi_coordinate(class, offset).unwrap();

                if let Address::PhiCoordinate { class: c, page, byte } = addr {
                    assert_eq!(c, class);
                    let roundtrip_offset = phi_coordinate_to_offset(c, page, byte).unwrap();
                    assert_eq!(roundtrip_offset, offset);
                } else {
                    panic!("Expected PhiCoordinate address");
                }
            }
        }
    }

    #[test]
    fn test_roundtrip_all_pages() {
        // Test all page boundaries
        for page in 0..48u8 {
            let offset = page as usize * 256;
            let addr = offset_to_phi_coordinate(0, offset).unwrap();

            if let Address::PhiCoordinate {
                class: c,
                page: p,
                byte: b,
            } = addr
            {
                assert_eq!(p, page);
                assert_eq!(b, 0);
                let roundtrip = phi_coordinate_to_offset(c, p, b).unwrap();
                assert_eq!(roundtrip, offset);
            }
        }
    }

    #[test]
    fn test_fits_in_class_f32() {
        // f32: 4 bytes per element
        // 12,288 bytes / 4 = 3,072 elements max
        assert!(fits_in_class::<f32>(3072));
        assert!(fits_in_class::<f32>(1));
        assert!(fits_in_class::<f32>(1536));
        assert!(!fits_in_class::<f32>(3073));
        assert!(!fits_in_class::<f32>(10000));
    }

    #[test]
    fn test_fits_in_class_f64() {
        // f64: 8 bytes per element
        // 12,288 bytes / 8 = 1,536 elements max
        assert!(fits_in_class::<f64>(1536));
        assert!(fits_in_class::<f64>(1));
        assert!(fits_in_class::<f64>(768));
        assert!(!fits_in_class::<f64>(1537));
        assert!(!fits_in_class::<f64>(5000));
    }

    #[test]
    fn test_fits_in_class_u8() {
        // u8: 1 byte per element
        // 12,288 bytes / 1 = 12,288 elements max
        assert!(fits_in_class::<u8>(12288));
        assert!(fits_in_class::<u8>(1));
        assert!(fits_in_class::<u8>(6144));
        assert!(!fits_in_class::<u8>(12289));
        assert!(!fits_in_class::<u8>(20000));
    }

    #[test]
    fn test_fits_in_class_i32() {
        // i32: 4 bytes per element
        // 12,288 bytes / 4 = 3,072 elements max
        assert!(fits_in_class::<i32>(3072));
        assert!(fits_in_class::<i32>(1));
        assert!(!fits_in_class::<i32>(3073));
    }

    #[test]
    fn test_max_elements_per_class() {
        assert_eq!(max_elements_per_class::<f32>(), 3072);
        assert_eq!(max_elements_per_class::<f64>(), 1536);
        assert_eq!(max_elements_per_class::<u8>(), 12288);
        assert_eq!(max_elements_per_class::<i32>(), 3072);
        assert_eq!(max_elements_per_class::<i64>(), 1536);
    }

    #[test]
    fn test_constants() {
        assert_eq!(BYTES_PER_CLASS, 12_288);
        assert_eq!(PAGES_PER_CLASS, 48);
        assert_eq!(BYTES_PER_PAGE, 256);
        assert_eq!(PAGES_PER_CLASS * BYTES_PER_PAGE, BYTES_PER_CLASS);
    }
}
