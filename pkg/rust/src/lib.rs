//! Rust bindings for the UOR Prime Structure FFI
//!
//! This crate provides safe Rust bindings to the UOR Prime Structure
//! mathematical framework through its C FFI interface.

use std::fmt;

// FFI bindings to C functions (minimal wrapper)
extern "C" {
    fn lean_uor_pages_minimal() -> u32;
    fn lean_uor_bytes_minimal() -> u32;
    fn lean_uor_rclasses_minimal() -> u32;
    fn lean_uor_r96_classify_minimal(b: u8) -> u8;
    fn lean_uor_phi_encode_minimal(page: u8, byte: u8) -> u32;
    fn lean_uor_phi_page_minimal(code: u32) -> u8;
    fn lean_uor_phi_byte_minimal(code: u32) -> u8;
    fn lean_uor_truth_zero_minimal(budget: u32) -> u8;
    fn lean_uor_truth_add_minimal(a: u32, b: u32) -> u8;
}

/// Prime Structure constants
pub mod constants {
    /// Number of pages in the structure
    pub const PAGES: u32 = 48;
    
    /// Number of bytes per page
    pub const BYTES: u32 = 256;
    
    /// Number of resonance classes
    pub const RCLASSES: u32 = 96;
    
    /// Total number of elements (12,288)
    pub const TOTAL_ELEMENTS: u32 = PAGES * BYTES;
    
    /// Compression ratio (3/8)
    pub const COMPRESSION_RATIO: f64 = RCLASSES as f64 / BYTES as f64;
}

/// Returns the number of pages (48)
pub fn pages() -> u32 {
    unsafe { lean_uor_pages_minimal() }
}

/// Returns the number of bytes per page (256)
pub fn bytes() -> u32 {
    unsafe { lean_uor_bytes_minimal() }
}

/// Returns the number of resonance classes (96)
pub fn rclasses() -> u32 {
    unsafe { lean_uor_rclasses_minimal() }
}

/// Classifies a byte into one of 96 resonance classes
pub fn r96_classify(b: u8) -> u8 {
    unsafe { lean_uor_r96_classify_minimal(b) }
}

/// Encodes page and byte coordinates into a 32-bit code
pub fn phi_encode(page: u8, byte: u8) -> u32 {
    unsafe { lean_uor_phi_encode_minimal(page, byte) }
}

/// Extracts the page component from a Phi code
pub fn phi_page(code: u32) -> u8 {
    unsafe { lean_uor_phi_page_minimal(code) }
}

/// Extracts the byte component from a Phi code
pub fn phi_byte(code: u32) -> u8 {
    unsafe { lean_uor_phi_byte_minimal(code) }
}

/// Checks if a budget value represents truth (conservation)
pub fn truth_zero(budget: u32) -> bool {
    unsafe { lean_uor_truth_zero_minimal(budget) != 0 }
}

/// Checks if the sum of two values represents truth
pub fn truth_add(a: u32, b: u32) -> bool {
    unsafe { lean_uor_truth_add_minimal(a, b) != 0 }
}

/// A coordinate in the Phi-Atlas boundary encoding
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PhiCoordinate {
    pub page: u8,
    pub byte: u8,
}

impl PhiCoordinate {
    /// Creates a new PhiCoordinate
    pub fn new(page: u8, byte: u8) -> Self {
        Self { page, byte }
    }
    
    /// Encodes the coordinate to a 32-bit code
    pub fn encode(&self) -> u32 {
        phi_encode(self.page, self.byte)
    }
    
    /// Decodes a 32-bit code to a PhiCoordinate
    pub fn decode(code: u32) -> Self {
        Self {
            page: phi_page(code),
            byte: phi_byte(code),
        }
    }
}

impl fmt::Display for PhiCoordinate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Φ({},{})", self.page, self.byte)
    }
}

/// A resonance class value
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ResonanceClass(u8);

impl ResonanceClass {
    /// Creates a ResonanceClass from a byte value
    pub fn classify(b: u8) -> Self {
        Self(r96_classify(b))
    }
    
    /// Gets the raw class value
    pub fn value(&self) -> u8 {
        self.0
    }
}

impl fmt::Display for ResonanceClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "R96[{}]", self.0)
    }
}

/// Conservation checker for truth values
pub struct Conservation;

impl Conservation {
    /// Checks if a value conserves truth (equals zero)
    pub fn is_zero(value: u32) -> bool {
        truth_zero(value)
    }
    
    /// Checks if a sum conserves truth (equals zero)
    pub fn sum_is_zero(a: u32, b: u32) -> bool {
        truth_add(a, b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_constants() {
        assert_eq!(pages(), 48);
        assert_eq!(bytes(), 256);
        assert_eq!(rclasses(), 96);
        assert_eq!(pages() * bytes(), 12288);
    }
    
    #[test]
    fn test_r96_classifier() {
        assert_eq!(r96_classify(0), 0);
        assert_eq!(r96_classify(95), 95);
        assert_eq!(r96_classify(96), 0);
        assert_eq!(r96_classify(255), 63);
        
        // Test range
        for i in 0..=255 {
            assert!(r96_classify(i) < 96);
        }
        
        // Test periodicity
        for i in 0..96 {
            assert_eq!(r96_classify(i), r96_classify(i + 96));
        }
    }
    
    #[test]
    fn test_phi_encoding() {
        // Test round-trip
        for page in 0..48 {
            for byte in (0..256).step_by(17) {
                let code = phi_encode(page, byte as u8);
                assert_eq!(phi_page(code), page);
                assert_eq!(phi_byte(code), byte as u8);
            }
        }
        
        // Test coordinate type
        let coord = PhiCoordinate::new(3, 16);
        let code = coord.encode();
        let decoded = PhiCoordinate::decode(code);
        assert_eq!(coord, decoded);
        assert_eq!(format!("{}", coord), "Φ(3,16)");
    }
    
    #[test]
    fn test_truth_conservation() {
        assert!(truth_zero(0));
        assert!(!truth_zero(1));
        assert!(!truth_zero(100));
        
        assert!(truth_add(0, 0));
        assert!(!truth_add(1, 0));
        assert!(!truth_add(5, 10));
        
        // Test overflow wrapping
        assert!(truth_add(u32::MAX, 1));
    }
    
    #[test]
    fn test_resonance_class() {
        let rc = ResonanceClass::classify(100);
        assert_eq!(rc.value(), 4);
        
        // Verify all classes are produced
        let mut classes = std::collections::HashSet::new();
        for i in 0..=255 {
            classes.insert(ResonanceClass::classify(i));
        }
        assert_eq!(classes.len(), 96);
    }
    
    #[test]
    fn test_conservation() {
        assert!(Conservation::is_zero(0));
        assert!(!Conservation::is_zero(42));
        assert!(Conservation::sum_is_zero(0, 0));
        assert!(!Conservation::sum_is_zero(1, 2));
    }
}