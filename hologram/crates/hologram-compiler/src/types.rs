//! Core type definitions for the Atlas Sigil Algebra
//!
//! Based on formal specification v1.0

use std::fmt;
use std::str::FromStr;

// ============================================================================
// Class Sigil (h₂, d, ℓ) triple
// ============================================================================

/// Scope quadrant (h₂) - cardinal direction
pub type ScopeQuadrant = u8; // 0..3

/// Modality (d) - neutral, produce, consume
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Modality {
    Neutral = 0, // (b4, b5) = (0, 0)
    Produce = 1, // (b4, b5) = (1, 0)
    Consume = 2, // (b4, b5) = (0, 1)
}

impl Modality {
    pub fn from_u8(value: u8) -> Option<Self> {
        match value {
            0 => Some(Modality::Neutral),
            1 => Some(Modality::Produce),
            2 => Some(Modality::Consume),
            _ => None,
        }
    }

    pub fn as_u8(self) -> u8 {
        self as u8
    }
}

/// Context slot (ℓ) - 8-ring position
pub type ContextSlot = u8; // 0..7

/// Sigil components: (h₂, d, ℓ) triple
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SigilComponents {
    pub h2: ScopeQuadrant, // 0..3
    pub d: Modality,       // 0, 1, or 2
    pub l: ContextSlot,    // 0..7
}

impl SigilComponents {
    pub fn new(h2: u8, d: Modality, l: u8) -> Result<Self, String> {
        if h2 > 3 {
            return Err(format!("h2 must be 0..3, got {}", h2));
        }
        if l > 7 {
            return Err(format!("l must be 0..7, got {}", l));
        }
        Ok(SigilComponents { h2, d, l })
    }
}

// ============================================================================
// Seven Generators
// ============================================================================

/// The seven fundamental generators of the Atlas Sigil Algebra
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Generator {
    /// Introduce/remove distinction
    Mark,
    /// Comultiplication (fan-out)
    Copy,
    /// Symmetry/braid operation
    Swap,
    /// Fold/meet operation
    Merge,
    /// Case analysis/deconstruct
    Split,
    /// Suspend computation
    Quote,
    /// Force/discharge thunk
    Evaluate,
}

impl FromStr for Generator {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "mark" => Ok(Generator::Mark),
            "copy" => Ok(Generator::Copy),
            "swap" => Ok(Generator::Swap),
            "merge" => Ok(Generator::Merge),
            "split" => Ok(Generator::Split),
            "quote" => Ok(Generator::Quote),
            "evaluate" => Ok(Generator::Evaluate),
            _ => Err(()),
        }
    }
}

impl Generator {
    pub fn as_str(&self) -> &'static str {
        match self {
            Generator::Mark => "mark",
            Generator::Copy => "copy",
            Generator::Swap => "swap",
            Generator::Merge => "merge",
            Generator::Split => "split",
            Generator::Quote => "quote",
            Generator::Evaluate => "evaluate",
        }
    }
}

// ============================================================================
// Transform Operations
// ============================================================================

/// Transform combining R (rotate), T (twist), M (mirror), and S (scope)
///
/// ## Automorphism Components
///
/// Transforms correspond to elements of the automorphism group Aut(Atlas₁₂₂₈₈):
/// - **R** (rotate): Dihedral rotation on h₂ quadrants
/// - **T** (twist): Context ring phase shift on ℓ
/// - **M** (mirror): Dihedral reflection (modality flip)
/// - **S** (scope): Scope group permutation S₁₆ on (h₂, d)
///
/// Together these generate the 2,048 automorphisms: D₈ × T₈ × S₁₆
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Transform {
    /// Rotate quadrants (mod 4 on h₂)
    pub r: Option<i32>,
    /// Twist context ring (mod 8 on ℓ)
    pub t: Option<i32>,
    /// Mirror modality (flip 1↔2, 0→0)
    pub m: bool,
    /// Scope permutation (0..15) from S₁₆
    pub s: Option<u8>,
}

impl Transform {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_rotate(mut self, k: i32) -> Self {
        self.r = Some(k);
        self
    }

    pub fn with_twist(mut self, k: i32) -> Self {
        self.t = Some(k);
        self
    }

    pub fn with_mirror(mut self) -> Self {
        self.m = true;
        self
    }

    pub fn with_scope(mut self, s: u8) -> Self {
        assert!(s < 16, "Scope permutation must be 0..15");
        self.s = Some(s);
        self
    }

    /// Combine two transforms
    ///
    /// Composition follows automorphism group structure:
    /// - R, T: Additive (mod 4, mod 8 respectively)
    /// - M: XOR (group Z₂)
    /// - S: Composition via S₁₆ group operation
    pub fn combine(&self, other: &Transform) -> Transform {
        Transform {
            r: match (self.r, other.r) {
                (Some(a), Some(b)) => Some(a + b),
                (Some(a), None) => Some(a),
                (None, Some(b)) => Some(b),
                (None, None) => None,
            },
            t: match (self.t, other.t) {
                (Some(a), Some(b)) => Some(a + b),
                (Some(a), None) => Some(a),
                (None, Some(b)) => Some(b),
                (None, None) => None,
            },
            m: self.m ^ other.m, // XOR for mirror
            s: match (self.s, other.s) {
                (Some(a), Some(b)) => {
                    // Compose via S₁₆ group structure
                    use crate::automorphism_group::ScopeElement;
                    let s1 = ScopeElement::new(a);
                    let s2 = ScopeElement::new(b);
                    Some(s1.compose(s2).permutation_index)
                }
                (Some(a), None) => Some(a),
                (None, Some(b)) => Some(b),
                (None, None) => None,
            },
        }
    }
}

// ============================================================================
// Class Sigil
// ============================================================================

/// A class sigil with optional transforms and belt page
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassSigil {
    /// Class index (0..95)
    pub class_index: u8,
    /// Optional R±k transform
    pub rotate: Option<i32>,
    /// Optional T±k transform
    pub twist: Option<i32>,
    /// Optional M transform
    pub mirror: bool,
    /// Optional S scope permutation (0..15)
    pub scope: Option<u8>,
    /// Optional belt page λ ∈ {0..47}
    pub page: Option<u8>,
}

impl ClassSigil {
    pub fn new(class_index: u8) -> Result<Self, String> {
        if class_index > 95 {
            return Err(format!("Class index must be 0..95, got {}", class_index));
        }
        Ok(ClassSigil {
            class_index,
            rotate: None,
            twist: None,
            mirror: false,
            scope: None,
            page: None,
        })
    }

    pub fn with_rotate(mut self, k: i32) -> Self {
        self.rotate = Some(k);
        self
    }

    pub fn with_twist(mut self, k: i32) -> Self {
        self.twist = Some(k);
        self
    }

    pub fn with_mirror(mut self) -> Self {
        self.mirror = true;
        self
    }

    pub fn with_scope(mut self, s: u8) -> Result<Self, String> {
        if s > 15 {
            return Err(format!("Scope permutation must be 0..15, got {}", s));
        }
        self.scope = Some(s);
        Ok(self)
    }

    pub fn with_page(mut self, page: u8) -> Result<Self, String> {
        if page > 47 {
            return Err(format!("Page must be 0..47, got {}", page));
        }
        self.page = Some(page);
        Ok(self)
    }

    pub fn to_transform(&self) -> Transform {
        Transform {
            r: self.rotate,
            t: self.twist,
            m: self.mirror,
            s: self.scope,
        }
    }
}

// ============================================================================
// Class Range
// ============================================================================

/// A class range for multi-class operations
///
/// Represents a contiguous range of classes [start..end] (inclusive).
/// Used for operations that span multiple classes, enabling processing
/// of large vectors that exceed a single class capacity (3,072 f32 elements).
///
/// # Syntax
///
/// Range syntax in sigil expressions:
/// - `c[start..end]` - Basic range (inclusive)
/// - `c[start..end]^+k` - Range with twist transform
/// - `c[start..end]~` - Range with mirror transform
/// - `c[start..end]^+k~` - Range with both transforms
///
/// # Examples
///
/// ## Basic Range
///
/// ```
/// use hologram_compiler::ClassRange;
///
/// // Range from class 0 to 9 (10 classes total)
/// let range = ClassRange::new(0, 9).unwrap();
/// assert_eq!(range.num_classes(), 10);
/// assert_eq!(range.start_class(), 0);
/// assert_eq!(range.end_class(), 9);
/// ```
///
/// ## Capacity Calculation
///
/// ```
/// use hologram_compiler::ClassRange;
///
/// // 10 classes × 3,072 elements/class = 30,720 f32 elements
/// let range = ClassRange::new(0, 9).unwrap();
/// let capacity = range.num_classes() as usize * 3072;
/// assert_eq!(capacity, 30_720);
/// ```
///
/// ## Range with Transforms
///
/// ```
/// use hologram_compiler::ClassRange;
///
/// let range = ClassRange::new(5, 14)
///     .unwrap()
///     .with_twist(1)
///     .with_mirror();
///
/// assert_eq!(range.twist, Some(1));
/// assert!(range.mirror);
/// ```
///
/// ## Large Vector Support
///
/// ```text
/// 10,000 elements  → 4 classes   (c[0..3])
/// 100,000 elements → 33 classes  (c[0..32])
/// 1M elements      → 326 classes (c[0..325])  // Note: max is 95
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassRange {
    /// Start class index (inclusive, 0..95)
    pub start_class: u8,
    /// End class index (inclusive, 0..95)
    pub end_class: u8,
    /// Optional R±k transform
    pub rotate: Option<i32>,
    /// Optional T±k transform
    pub twist: Option<i32>,
    /// Optional M transform
    pub mirror: bool,
    /// Optional S scope permutation (0..15)
    pub scope: Option<u8>,
}

impl ClassRange {
    /// Create a new class range
    ///
    /// # Arguments
    ///
    /// * `start_class` - Starting class (inclusive), must be in [0, 95]
    /// * `end_class` - Ending class (inclusive), must be in [0, 95] and > start_class
    ///
    /// # Errors
    ///
    /// Returns error if:
    /// - start_class or end_class > 95
    /// - start_class >= end_class (range must contain at least 2 classes)
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::ClassRange;
    ///
    /// let range = ClassRange::new(5, 14).unwrap();
    /// assert_eq!(range.start_class(), 5);
    /// assert_eq!(range.end_class(), 14);
    /// assert_eq!(range.num_classes(), 10);
    /// ```
    pub fn new(start_class: u8, end_class: u8) -> Result<Self, String> {
        if start_class > 95 {
            return Err(format!("Start class must be 0..95, got {}", start_class));
        }
        if end_class > 95 {
            return Err(format!("End class must be 0..95, got {}", end_class));
        }
        if start_class >= end_class {
            return Err(format!(
                "Start class {} must be less than end class {}",
                start_class, end_class
            ));
        }
        Ok(ClassRange {
            start_class,
            end_class,
            rotate: None,
            twist: None,
            mirror: false,
            scope: None,
        })
    }

    pub fn start_class(&self) -> u8 {
        self.start_class
    }

    pub fn end_class(&self) -> u8 {
        self.end_class
    }

    /// Get the number of classes in this range
    pub fn num_classes(&self) -> u8 {
        self.end_class - self.start_class + 1
    }

    pub fn with_rotate(mut self, k: i32) -> Self {
        self.rotate = Some(k);
        self
    }

    pub fn with_twist(mut self, k: i32) -> Self {
        self.twist = Some(k);
        self
    }

    pub fn with_mirror(mut self) -> Self {
        self.mirror = true;
        self
    }

    pub fn with_scope(mut self, s: u8) -> Result<Self, String> {
        if s > 15 {
            return Err(format!("Scope permutation must be 0..15, got {}", s));
        }
        self.scope = Some(s);
        Ok(self)
    }

    pub fn to_transform(&self) -> Transform {
        Transform {
            r: self.rotate,
            t: self.twist,
            m: self.mirror,
            s: self.scope,
        }
    }
}

// ============================================================================
// Class Target (Single or Range)
// ============================================================================

/// Target for a generator operation - either a single class or a range
///
/// This enum unifies single-class and multi-class operations in the AST.
/// Single-class targets use `ClassSigil` with full transform support,
/// while range targets use `ClassRange` for contiguous multi-class operations.
///
/// # Examples
///
/// ## Single Class Target
///
/// ```
/// use hologram_compiler::ClassTarget;
///
/// // Create single class target: c42
/// let target = ClassTarget::single(42).unwrap();
/// assert!(target.is_single());
/// ```
///
/// ## Range Target
///
/// ```
/// use hologram_compiler::ClassTarget;
///
/// // Create range target: c[0..9]
/// let target = ClassTarget::range(0, 9).unwrap();
/// assert!(target.is_range());
/// ```
///
/// ## In Parser Context
///
/// The parser automatically creates the appropriate target type:
///
/// ```text
/// mark@c21       -> ClassTarget::Single(ClassSigil { class: 21, ... })
/// merge@c[0..9]  -> ClassTarget::Range(ClassRange { start: 0, end: 9, ... })
/// mark@c[5..14]^+1~ -> ClassTarget::Range with transforms
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassTarget {
    /// Single class with optional transforms and page
    Single(ClassSigil),
    /// Range of classes with optional transforms
    Range(ClassRange),
    /// Copy operation: source -> destination
    CopyPair { src: ClassSigil, dst: ClassSigil },
    /// Swap operation: class_a <-> class_b
    SwapPair { a: ClassSigil, b: ClassSigil },
    /// Merge/Split operation: primary\[context,secondary\]
    TripleClass {
        primary: ClassSigil,
        context: ClassSigil,
        secondary: ClassSigil,
    },
}

impl ClassTarget {
    /// Create a single-class target
    pub fn single(class_index: u8) -> Result<Self, String> {
        Ok(ClassTarget::Single(ClassSigil::new(class_index)?))
    }

    /// Create a range target
    pub fn range(start: u8, end: u8) -> Result<Self, String> {
        Ok(ClassTarget::Range(ClassRange::new(start, end)?))
    }

    /// Check if this is a single class target
    pub fn is_single(&self) -> bool {
        matches!(self, ClassTarget::Single(_))
    }

    /// Check if this is a range target
    pub fn is_range(&self) -> bool {
        matches!(self, ClassTarget::Range(_))
    }

    /// Check if this is a copy pair target
    pub fn is_copy_pair(&self) -> bool {
        matches!(self, ClassTarget::CopyPair { .. })
    }

    /// Check if this is a swap pair target
    pub fn is_swap_pair(&self) -> bool {
        matches!(self, ClassTarget::SwapPair { .. })
    }

    /// Check if this is a triple class target
    pub fn is_triple_class(&self) -> bool {
        matches!(self, ClassTarget::TripleClass { .. })
    }
}

// ============================================================================
// Operation (Generator + Sigil)
// ============================================================================

/// An operation: generator applied to a class sigil
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Operation {
    pub generator: Generator,
    pub sigil: ClassSigil,
}

impl Operation {
    pub fn new(generator: Generator, sigil: ClassSigil) -> Self {
        Operation { generator, sigil }
    }
}

// ============================================================================
// Evaluation Results
// ============================================================================

/// Result of literal evaluation (byte semantics)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiteralResult {
    /// Canonical byte representatives
    pub bytes: Vec<u8>,
    /// Belt addresses if pages specified
    pub addresses: Option<Vec<u16>>,
}

/// Result of operational evaluation (word semantics)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OperationalResult {
    /// Lowered generator words
    pub words: Vec<String>,
}

// ============================================================================
// Class Info
// ============================================================================

/// Complete information about a class
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassInfo {
    /// Class index (0..95)
    pub class_index: u8,
    /// Decoded components
    pub components: SigilComponents,
    /// Canonical byte representative (b0=0)
    pub canonical_byte: u8,
}

// ============================================================================
// Display Implementations for AST Serialization
// ============================================================================

impl fmt::Display for Generator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Generator::Mark => write!(f, "mark"),
            Generator::Copy => write!(f, "copy"),
            Generator::Swap => write!(f, "swap"),
            Generator::Merge => write!(f, "merge"),
            Generator::Split => write!(f, "split"),
            Generator::Quote => write!(f, "quote"),
            Generator::Evaluate => write!(f, "evaluate"),
        }
    }
}

impl fmt::Display for Transform {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts = Vec::new();

        if let Some(r) = self.r {
            parts.push(format!("R{:+}", r));
        }
        if let Some(t) = self.t {
            parts.push(format!("T{:+}", t));
        }
        if self.m {
            parts.push("~".to_string());
        }
        if let Some(s) = self.s {
            parts.push(format!("S{}", s));
        }

        write!(f, "{}", parts.join(""))
    }
}

impl fmt::Display for ClassSigil {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "c{:02}", self.class_index)?;

        if let Some(r) = self.rotate {
            write!(f, "^{:+}", r)?;
        }
        if let Some(t) = self.twist {
            write!(f, "T{:+}", t)?;
        }
        if self.mirror {
            write!(f, "~")?;
        }
        if let Some(s) = self.scope {
            write!(f, "S{}", s)?;
        }
        if let Some(p) = self.page {
            write!(f, "@{}", p)?;
        }

        Ok(())
    }
}

impl fmt::Display for ClassRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "c[{}..{}]", self.start_class(), self.end_class())?;

        if let Some(r) = self.rotate {
            write!(f, "^{:+}", r)?;
        }
        if let Some(t) = self.twist {
            write!(f, "T{:+}", t)?;
        }
        if self.mirror {
            write!(f, "~")?;
        }
        if let Some(s) = self.scope {
            write!(f, "S{}", s)?;
        }

        Ok(())
    }
}

impl fmt::Display for ClassTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClassTarget::Single(sigil) => write!(f, "{}", sigil),
            ClassTarget::Range(range) => write!(f, "{}", range),
            ClassTarget::CopyPair { src, dst } => write!(f, "{}->{}", src, dst),
            ClassTarget::SwapPair { a, b } => write!(f, "{}<->{}", a, b),
            ClassTarget::TripleClass {
                primary,
                context,
                secondary,
            } => {
                write!(f, "{}[{},{}]", primary, context, secondary)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_class_range_validation() {
        // Valid range
        let range = ClassRange::new(0, 9).unwrap();
        assert_eq!(range.start_class(), 0);
        assert_eq!(range.end_class(), 9);
        assert_eq!(range.num_classes(), 10);

        // Start >= end (invalid)
        assert!(ClassRange::new(5, 5).is_err());
        assert!(ClassRange::new(10, 5).is_err());

        // Out of bounds
        assert!(ClassRange::new(96, 100).is_err());
        assert!(ClassRange::new(0, 96).is_err());
    }

    #[test]
    fn test_class_range_with_transforms() {
        let range = ClassRange::new(5, 14)
            .unwrap()
            .with_rotate(2)
            .with_twist(-3)
            .with_mirror();

        assert_eq!(range.rotate, Some(2));
        assert_eq!(range.twist, Some(-3));
        assert!(range.mirror);

        let transform = range.to_transform();
        assert_eq!(transform.r, Some(2));
        assert_eq!(transform.t, Some(-3));
        assert!(transform.m);
    }

    #[test]
    fn test_class_range_boundaries() {
        // Minimum range (2 classes)
        let range = ClassRange::new(0, 1).unwrap();
        assert_eq!(range.num_classes(), 2);

        // Maximum range (all 96 classes)
        let range = ClassRange::new(0, 95).unwrap();
        assert_eq!(range.num_classes(), 96);

        // Near end
        let range = ClassRange::new(90, 94).unwrap();
        assert_eq!(range.num_classes(), 5);
    }

    #[test]
    fn test_class_target_single() {
        let target = ClassTarget::single(21).unwrap();
        assert!(target.is_single());
        assert!(!target.is_range());

        match target {
            ClassTarget::Single(sigil) => {
                assert_eq!(sigil.class_index, 21);
            }
            _ => panic!("Expected Single target"),
        }
    }

    #[test]
    fn test_class_target_range() {
        let target = ClassTarget::range(0, 9).unwrap();
        assert!(!target.is_single());
        assert!(target.is_range());

        match target {
            ClassTarget::Range(range) => {
                assert_eq!(range.start_class(), 0);
                assert_eq!(range.end_class(), 9);
                assert_eq!(range.num_classes(), 10);
            }
            _ => panic!("Expected Range target"),
        }
    }

    #[test]
    fn test_class_target_validation() {
        // Single class out of bounds
        assert!(ClassTarget::single(96).is_err());

        // Range invalid
        assert!(ClassTarget::range(5, 5).is_err());
        assert!(ClassTarget::range(10, 5).is_err());
        assert!(ClassTarget::range(0, 96).is_err());
    }
}
