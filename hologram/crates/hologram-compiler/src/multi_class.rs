//! Multi-Class Vector Support
//!
//! Enables vectors larger than 3,072 elements by spanning multiple resonance classes.
//!
//! ## Design
//!
//! - Each class holds 12,288 bytes = 3,072 f32 elements
//! - Vectors span contiguous classes sequentially
//! - Address calculation: `element_index → (class_index, offset_in_class)`
//!
//! ## Example
//!
//! ```
//! use hologram_compiler::multi_class::MultiClassVector;
//!
//! // Vector with 10,000 f32 elements spans 4 classes
//! let vec = MultiClassVector::<f32>::new(0, 10000).unwrap();
//! assert_eq!(vec.num_classes(), 4);
//! assert_eq!(vec.length(), 10000);
//! ```

use std::marker::PhantomData;
use std::mem;

/// Number of bytes per class
pub const CLASS_SIZE_BYTES: usize = 12_288;

/// Maximum number of classes available
pub const MAX_CLASSES: usize = 96;

/// Multi-class vector spanning contiguous resonance classes
///
/// Provides a logical view of a contiguous vector that may span
/// multiple physical classes in ClassMemory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MultiClassVector<T> {
    /// Starting class index (0-95)
    start_class: u8,

    /// Number of classes spanned
    num_classes: u8,

    /// Total number of elements in the vector
    length: usize,

    /// Element type marker
    _phantom: PhantomData<T>,
}

impl<T> MultiClassVector<T> {
    /// Calculate elements per class for type T
    pub const fn elements_per_class() -> usize {
        CLASS_SIZE_BYTES / mem::size_of::<T>()
    }

    /// Create a new multi-class vector
    ///
    /// # Arguments
    ///
    /// * `start_class` - First class index (0-95)
    /// * `length` - Number of elements
    ///
    /// # Returns
    ///
    /// `Ok(MultiClassVector)` if allocation is valid, `Err` otherwise
    ///
    /// # Errors
    ///
    /// - `InvalidLength`: length is 0
    /// - `InsufficientClasses`: not enough contiguous classes available
    /// - `InvalidStartClass`: start_class >= MAX_CLASSES
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::multi_class::MultiClassVector;
    ///
    /// let vec = MultiClassVector::<f32>::new(0, 10000).unwrap();
    /// assert_eq!(vec.length(), 10000);
    /// ```
    pub fn new(start_class: u8, length: usize) -> Result<Self, MultiClassError> {
        // Validate parameters
        if length == 0 {
            return Err(MultiClassError::InvalidLength);
        }

        if start_class as usize >= MAX_CLASSES {
            return Err(MultiClassError::InvalidStartClass(start_class));
        }

        // Calculate required number of classes
        let elements_per_class = Self::elements_per_class();
        let num_classes = length.div_ceil(elements_per_class) as u8;

        // Verify we don't exceed class bounds
        if start_class as usize + num_classes as usize > MAX_CLASSES {
            return Err(MultiClassError::InsufficientClasses {
                required: num_classes,
                available: (MAX_CLASSES - start_class as usize) as u8,
            });
        }

        Ok(MultiClassVector {
            start_class,
            num_classes,
            length,
            _phantom: PhantomData,
        })
    }

    /// Get the starting class index
    pub fn start_class(&self) -> u8 {
        self.start_class
    }

    /// Get the number of classes spanned
    pub fn num_classes(&self) -> u8 {
        self.num_classes
    }

    /// Get the total number of elements
    pub fn length(&self) -> usize {
        self.length
    }

    /// Get the ending class index (inclusive)
    pub fn end_class(&self) -> u8 {
        self.start_class + self.num_classes - 1
    }

    /// Calculate which class contains a given element index
    ///
    /// # Arguments
    ///
    /// * `element_index` - Index of the element (0-based)
    ///
    /// # Returns
    ///
    /// Class index containing the element
    ///
    /// # Panics
    ///
    /// Panics if `element_index >= self.length()`
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::multi_class::MultiClassVector;
    ///
    /// let vec = MultiClassVector::<f32>::new(10, 10000).unwrap();
    /// assert_eq!(vec.class_for_element(0), 10);      // First class
    /// assert_eq!(vec.class_for_element(3072), 11);   // Second class
    /// assert_eq!(vec.class_for_element(6144), 12);   // Third class
    /// ```
    pub fn class_for_element(&self, element_index: usize) -> u8 {
        assert!(
            element_index < self.length,
            "Element index {} out of bounds (length: {})",
            element_index,
            self.length
        );

        let elements_per_class = Self::elements_per_class();
        self.start_class + (element_index / elements_per_class) as u8
    }

    /// Calculate the byte offset within a class for a given element index
    ///
    /// # Arguments
    ///
    /// * `element_index` - Index of the element (0-based)
    ///
    /// # Returns
    ///
    /// Byte offset within the class
    ///
    /// # Panics
    ///
    /// Panics if `element_index >= self.length()`
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::multi_class::MultiClassVector;
    ///
    /// let vec = MultiClassVector::<f32>::new(0, 10000).unwrap();
    /// assert_eq!(vec.offset_in_class(0), 0);         // First element, offset 0
    /// assert_eq!(vec.offset_in_class(1), 4);         // Second element, offset 4 bytes
    /// assert_eq!(vec.offset_in_class(3072), 0);      // First element of second class
    /// ```
    pub fn offset_in_class(&self, element_index: usize) -> usize {
        assert!(
            element_index < self.length,
            "Element index {} out of bounds (length: {})",
            element_index,
            self.length
        );

        let elements_per_class = Self::elements_per_class();
        let element_within_class = element_index % elements_per_class;
        element_within_class * mem::size_of::<T>()
    }

    /// Calculate class index and byte offset for an element
    ///
    /// # Arguments
    ///
    /// * `element_index` - Index of the element (0-based)
    ///
    /// # Returns
    ///
    /// Tuple of (class_index, byte_offset)
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::multi_class::MultiClassVector;
    ///
    /// let vec = MultiClassVector::<f32>::new(5, 10000).unwrap();
    /// let (class, offset) = vec.address_for_element(5000);
    /// assert_eq!(class, 6);  // Second class (5 + 1)
    /// ```
    pub fn address_for_element(&self, element_index: usize) -> (u8, usize) {
        (
            self.class_for_element(element_index),
            self.offset_in_class(element_index),
        )
    }

    /// Get the number of elements in a specific class
    ///
    /// Most classes contain `elements_per_class()` elements, except
    /// possibly the last class which may be partially filled.
    ///
    /// # Arguments
    ///
    /// * `class_offset` - Offset from start_class (0-based)
    ///
    /// # Returns
    ///
    /// Number of elements in the specified class
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::multi_class::MultiClassVector;
    ///
    /// let vec = MultiClassVector::<f32>::new(0, 10000).unwrap();
    /// assert_eq!(vec.elements_in_class(0), 3072);  // First class full
    /// assert_eq!(vec.elements_in_class(1), 3072);  // Second class full
    /// assert_eq!(vec.elements_in_class(2), 3072);  // Third class full
    /// assert_eq!(vec.elements_in_class(3), 784);   // Fourth class partial
    /// ```
    pub fn elements_in_class(&self, class_offset: u8) -> usize {
        assert!(
            class_offset < self.num_classes,
            "Class offset {} exceeds num_classes {}",
            class_offset,
            self.num_classes
        );

        let elements_per_class = Self::elements_per_class();

        if class_offset < self.num_classes - 1 {
            // Full class
            elements_per_class
        } else {
            // Last class may be partial
            let full_classes = (self.num_classes - 1) as usize;
            self.length - (full_classes * elements_per_class)
        }
    }
}

/// Errors that can occur when creating or using multi-class vectors
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum MultiClassError {
    #[error("Invalid length: length must be > 0")]
    InvalidLength,

    #[error("Invalid start class {0}: must be < {MAX_CLASSES}")]
    InvalidStartClass(u8),

    #[error("Insufficient contiguous classes: required {required}, available {available}")]
    InsufficientClasses { required: u8, available: u8 },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_elements_per_class() {
        assert_eq!(MultiClassVector::<f32>::elements_per_class(), 3072);
        assert_eq!(MultiClassVector::<i32>::elements_per_class(), 3072);
        assert_eq!(MultiClassVector::<u8>::elements_per_class(), 12288);
        assert_eq!(MultiClassVector::<f64>::elements_per_class(), 1536);
    }

    #[test]
    fn test_new_single_class() {
        let vec = MultiClassVector::<f32>::new(0, 3072).unwrap();
        assert_eq!(vec.start_class(), 0);
        assert_eq!(vec.num_classes(), 1);
        assert_eq!(vec.length(), 3072);
        assert_eq!(vec.end_class(), 0);
    }

    #[test]
    fn test_new_multiple_classes() {
        let vec = MultiClassVector::<f32>::new(10, 10000).unwrap();
        assert_eq!(vec.start_class(), 10);
        assert_eq!(vec.num_classes(), 4); // ceil(10000 / 3072) = 4
        assert_eq!(vec.length(), 10000);
        assert_eq!(vec.end_class(), 13);
    }

    #[test]
    fn test_new_invalid_length() {
        let result = MultiClassVector::<f32>::new(0, 0);
        assert_eq!(result, Err(MultiClassError::InvalidLength));
    }

    #[test]
    fn test_new_invalid_start_class() {
        let result = MultiClassVector::<f32>::new(96, 1000);
        assert_eq!(result, Err(MultiClassError::InvalidStartClass(96)));
    }

    #[test]
    fn test_new_insufficient_classes() {
        // Try to allocate 300,000 elements starting at class 95
        // Would need ~98 classes, but only 1 available
        let result = MultiClassVector::<f32>::new(95, 300000);
        assert!(matches!(result, Err(MultiClassError::InsufficientClasses { .. })));
    }

    #[test]
    fn test_class_for_element() {
        let vec = MultiClassVector::<f32>::new(5, 10000).unwrap();

        assert_eq!(vec.class_for_element(0), 5); // First element, first class
        assert_eq!(vec.class_for_element(3071), 5); // Last element, first class
        assert_eq!(vec.class_for_element(3072), 6); // First element, second class
        assert_eq!(vec.class_for_element(6144), 7); // First element, third class
        assert_eq!(vec.class_for_element(9999), 8); // Last element, fourth class
    }

    #[test]
    fn test_offset_in_class() {
        let vec = MultiClassVector::<f32>::new(0, 10000).unwrap();

        assert_eq!(vec.offset_in_class(0), 0); // First element, offset 0
        assert_eq!(vec.offset_in_class(1), 4); // Second element, offset 4 bytes
        assert_eq!(vec.offset_in_class(100), 400); // Element 100, offset 400 bytes
        assert_eq!(vec.offset_in_class(3072), 0); // First of second class, offset 0
        assert_eq!(vec.offset_in_class(3073), 4); // Second of second class, offset 4
    }

    #[test]
    fn test_address_for_element() {
        let vec = MultiClassVector::<f32>::new(20, 10000).unwrap();

        let (class, offset) = vec.address_for_element(0);
        assert_eq!(class, 20);
        assert_eq!(offset, 0);

        let (class, offset) = vec.address_for_element(5000);
        assert_eq!(class, 21); // 5000 / 3072 = 1 (second class)
        assert_eq!(offset, (5000 % 3072) * 4); // Remainder × 4 bytes
    }

    #[test]
    fn test_elements_in_class() {
        let vec = MultiClassVector::<f32>::new(0, 10000).unwrap();

        // 10000 / 3072 = 3.25, so 4 classes needed
        // First 3 classes: 3072 elements each
        // Last class: 10000 - (3 * 3072) = 784 elements
        assert_eq!(vec.elements_in_class(0), 3072);
        assert_eq!(vec.elements_in_class(1), 3072);
        assert_eq!(vec.elements_in_class(2), 3072);
        assert_eq!(vec.elements_in_class(3), 784);
    }

    #[test]
    fn test_large_vector() {
        // Maximum usable: 95 classes × 3,072 = 291,840 f32 elements
        let vec = MultiClassVector::<f32>::new(0, 291_840).unwrap();

        // 291,840 / 3,072 = 95 classes exactly
        assert_eq!(vec.num_classes(), 95);
        assert_eq!(vec.end_class(), 94);

        // Verify address calculation for random elements
        let (class, _) = vec.address_for_element(150_000);
        assert_eq!(class, 48); // 150,000 / 3,072 ≈ 48
    }

    #[test]
    #[should_panic(expected = "Element index 10000 out of bounds")]
    fn test_class_for_element_out_of_bounds() {
        let vec = MultiClassVector::<f32>::new(0, 10000).unwrap();
        vec.class_for_element(10000); // Should panic
    }

    #[test]
    #[should_panic(expected = "Class offset 5 exceeds num_classes 4")]
    fn test_elements_in_class_out_of_bounds() {
        let vec = MultiClassVector::<f32>::new(0, 10000).unwrap();
        vec.elements_in_class(5); // Should panic (only 4 classes)
    }
}
