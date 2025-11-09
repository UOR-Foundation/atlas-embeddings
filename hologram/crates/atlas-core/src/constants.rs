//! Constants defining the Atlas-12288 UOR structure

use num_rational::Ratio;

/// Number of pages in the UOR structure
pub const PAGES: u32 = 48;

/// Number of bytes per page
pub const BYTES_PER_PAGE: u32 = 256;

/// Number of resonance classes (R96)
pub const RESONANCE_CLASSES: u32 = 96;

/// Total elements in the structure (48 × 256 = 12,288)
pub const TOTAL_ELEMENTS: usize = (PAGES * BYTES_PER_PAGE) as usize;

/// Compression ratio for R96 classification (3/8)
pub fn compression_ratio() -> Ratio<u32> {
    Ratio::new(RESONANCE_CLASSES, BYTES_PER_PAGE)
}

/// Phase counter modulus (768 = 8 × 96)
pub const PHASE_MODULUS: u32 = 768;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constants_validity() {
        assert_eq!(PAGES, 48);
        assert_eq!(BYTES_PER_PAGE, 256);
        assert_eq!(RESONANCE_CLASSES, 96);
        assert_eq!(TOTAL_ELEMENTS, 12288);
        assert_eq!(PHASE_MODULUS, 768);
        assert_eq!(PHASE_MODULUS, 8 * RESONANCE_CLASSES);
    }

    #[test]
    fn test_compression_ratio() {
        let ratio = compression_ratio();
        assert_eq!(*ratio.numer(), 3);
        assert_eq!(*ratio.denom(), 8);
    }
}
