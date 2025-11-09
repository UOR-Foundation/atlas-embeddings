//! Core types for the Atlas ISA
//!
//! This module defines the fundamental types used throughout the ISA:
//! - Registers and predicates
//! - Data types
//! - Memory addresses
//! - Condition codes
//! - Labels for control flow

use std::fmt;

// ================================================================================================
// Register Types
// ================================================================================================

/// Register identifier (0-255)
///
/// Represents one of 256 general-purpose registers in the Atlas execution model.
/// Registers are typed, with type tracking enforced at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Register(pub u8);

impl Register {
    /// Create a new register
    pub const fn new(index: u8) -> Self {
        Register(index)
    }

    /// Get register index
    pub const fn index(self) -> u8 {
        self.0
    }
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "r{}", self.0)
    }
}

/// Predicate register identifier (0-15)
///
/// Represents one of 16 predicate (boolean) registers used for conditional execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Predicate(pub u8);

impl Predicate {
    /// Create a new predicate register
    pub const fn new(index: u8) -> Self {
        assert!(index < 16, "Predicate index must be < 16");
        Predicate(index)
    }

    /// Get predicate index
    pub const fn index(self) -> u8 {
        self.0
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "p{}", self.0)
    }
}

// ================================================================================================
// Data Types
// ================================================================================================

/// Type of data operated on by instructions
///
/// All instructions that operate on typed data must specify the type explicitly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Type {
    // Signed integers
    I8,
    I16,
    I32,
    I64,

    // Unsigned integers
    U8,
    U16,
    U32,
    U64,

    // Floating point
    F16,  // IEEE 754 half precision
    BF16, // Brain floating point 16
    F32,  // IEEE 754 single precision
    F64,  // IEEE 754 double precision
}

impl Type {
    /// Size of this type in bytes
    pub const fn size_bytes(self) -> usize {
        match self {
            Type::I8 | Type::U8 => 1,
            Type::I16 | Type::U16 | Type::F16 | Type::BF16 => 2,
            Type::I32 | Type::U32 | Type::F32 => 4,
            Type::I64 | Type::U64 | Type::F64 => 8,
        }
    }

    /// Is this an integer type?
    pub const fn is_integer(self) -> bool {
        matches!(
            self,
            Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::U8 | Type::U16 | Type::U32 | Type::U64
        )
    }

    /// Is this a floating-point type?
    pub const fn is_float(self) -> bool {
        matches!(self, Type::F16 | Type::BF16 | Type::F32 | Type::F64)
    }

    /// Is this a signed type?
    pub const fn is_signed(self) -> bool {
        matches!(
            self,
            Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::F16 | Type::BF16 | Type::F32 | Type::F64
        )
    }

    /// Is this an unsigned integer type?
    pub const fn is_unsigned(self) -> bool {
        matches!(self, Type::U8 | Type::U16 | Type::U32 | Type::U64)
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::I8 => write!(f, "i8"),
            Type::I16 => write!(f, "i16"),
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::U8 => write!(f, "u8"),
            Type::U16 => write!(f, "u16"),
            Type::U32 => write!(f, "u32"),
            Type::U64 => write!(f, "u64"),
            Type::F16 => write!(f, "f16"),
            Type::BF16 => write!(f, "bf16"),
            Type::F32 => write!(f, "f32"),
            Type::F64 => write!(f, "f64"),
        }
    }
}

// ================================================================================================
// Control Flow Types
// ================================================================================================

/// Label for control flow targets
///
/// Labels mark positions in the instruction stream for branches, calls, and loops.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Label(pub String);

impl Label {
    /// Create a new label
    pub fn new(name: impl Into<String>) -> Self {
        Label(name.into())
    }

    /// Get label name
    pub fn name(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}", self.0)
    }
}

impl From<&str> for Label {
    fn from(s: &str) -> Self {
        Label(s.to_string())
    }
}

impl From<String> for Label {
    fn from(s: String) -> Self {
        Label(s)
    }
}

/// Condition code for comparisons
///
/// Used by SETcc instruction to set predicate registers based on comparisons.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Condition {
    EQ,  // Equal
    NE,  // Not equal
    LT,  // Less than
    LE,  // Less than or equal
    GT,  // Greater than
    GE,  // Greater than or equal
    LTU, // Less than (unsigned)
    LEU, // Less than or equal (unsigned)
    GTU, // Greater than (unsigned)
    GEU, // Greater than or equal (unsigned)
}

impl fmt::Display for Condition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Condition::EQ => write!(f, "eq"),
            Condition::NE => write!(f, "ne"),
            Condition::LT => write!(f, "lt"),
            Condition::LE => write!(f, "le"),
            Condition::GT => write!(f, "gt"),
            Condition::GE => write!(f, "ge"),
            Condition::LTU => write!(f, "ltu"),
            Condition::LEU => write!(f, "leu"),
            Condition::GTU => write!(f, "gtu"),
            Condition::GEU => write!(f, "geu"),
        }
    }
}

// ================================================================================================
// Memory Types
// ================================================================================================

/// Memory fence scope
///
/// Defines the scope of memory ordering enforcement for MemFence instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum MemoryScope {
    Thread, // Single thread (no-op on most architectures)
    Block,  // Thread block/workgroup
    Device, // Entire device (GPU)
    System, // Across all devices (CPU + GPU)
}

impl fmt::Display for MemoryScope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MemoryScope::Thread => write!(f, "thread"),
            MemoryScope::Block => write!(f, "block"),
            MemoryScope::Device => write!(f, "device"),
            MemoryScope::System => write!(f, "system"),
        }
    }
}

/// Memory address
///
/// Represents a memory location that can be loaded from or stored to.
/// Supports multiple addressing modes:
/// - Buffer handle + offset (linear addressing)
/// - Φ-coordinates (boundary pool addressing: class, page, byte)
/// - Register-indirect (address in register)
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Address {
    /// Linear buffer addressing: handle + byte offset
    BufferOffset { handle: u64, offset: usize },

    /// Boundary pool Φ-coordinate addressing
    PhiCoordinate {
        class: u8, // Resonance class (0-95)
        page: u8,  // Page within class (0-47)
        byte: u8,  // Byte within page (0-255)
    },

    /// Register-indirect addressing (address in register + static offset)
    RegisterIndirect { base: Register, offset: i32 },

    /// Register-indirect with computed offset (handle_reg contains buffer handle, offset_reg contains byte offset)
    ///
    /// Used for parallel operations where each lane computes its own offset.
    /// Example: Load a[global_lane_id * 4] where handle is in R0 and offset is in R10
    RegisterIndirectComputed { handle_reg: Register, offset_reg: Register },
}

impl fmt::Display for Address {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Address::BufferOffset { handle, offset } => {
                write!(f, "[buf{} + {}]", handle, offset)
            }
            Address::PhiCoordinate { class, page, byte } => {
                write!(f, "[Φ({}, {}, {})]", class, page, byte)
            }
            Address::RegisterIndirect { base, offset } => {
                if *offset >= 0 {
                    write!(f, "[{} + {}]", base, offset)
                } else {
                    write!(f, "[{} - {}]", base, -offset)
                }
            }
            Address::RegisterIndirectComputed { handle_reg, offset_reg } => {
                write!(f, "[{} + {}]", handle_reg, offset_reg)
            }
        }
    }
}

// ================================================================================================
// Tests
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_creation() {
        let r0 = Register::new(0);
        let r255 = Register::new(255);
        assert_eq!(r0.index(), 0);
        assert_eq!(r255.index(), 255);
        assert_eq!(r0.to_string(), "r0");
        assert_eq!(r255.to_string(), "r255");
    }

    #[test]
    fn test_predicate_creation() {
        let p0 = Predicate::new(0);
        let p15 = Predicate::new(15);
        assert_eq!(p0.index(), 0);
        assert_eq!(p15.index(), 15);
        assert_eq!(p0.to_string(), "p0");
        assert_eq!(p15.to_string(), "p15");
    }

    #[test]
    fn test_type_properties() {
        assert_eq!(Type::F32.size_bytes(), 4);
        assert_eq!(Type::I64.size_bytes(), 8);
        assert_eq!(Type::U8.size_bytes(), 1);
        assert_eq!(Type::F16.size_bytes(), 2);

        assert!(Type::F32.is_float());
        assert!(Type::I32.is_integer());
        assert!(Type::I32.is_signed());
        assert!(!Type::U32.is_signed());
        assert!(Type::U32.is_unsigned());
        assert!(!Type::I32.is_unsigned());
    }

    #[test]
    fn test_type_display() {
        assert_eq!(Type::F32.to_string(), "f32");
        assert_eq!(Type::I64.to_string(), "i64");
        assert_eq!(Type::U8.to_string(), "u8");
        assert_eq!(Type::BF16.to_string(), "bf16");
    }

    #[test]
    fn test_label_creation() {
        let label = Label::new("loop_start");
        assert_eq!(label.name(), "loop_start");
        assert_eq!(label.to_string(), "@loop_start");

        let label2: Label = "end".into();
        assert_eq!(label2.name(), "end");
    }

    #[test]
    fn test_condition_display() {
        assert_eq!(Condition::EQ.to_string(), "eq");
        assert_eq!(Condition::LT.to_string(), "lt");
        assert_eq!(Condition::GEU.to_string(), "geu");
    }

    #[test]
    fn test_memory_scope_display() {
        assert_eq!(MemoryScope::Thread.to_string(), "thread");
        assert_eq!(MemoryScope::Block.to_string(), "block");
        assert_eq!(MemoryScope::Device.to_string(), "device");
        assert_eq!(MemoryScope::System.to_string(), "system");
    }

    #[test]
    fn test_address_display() {
        let addr1 = Address::BufferOffset {
            handle: 42,
            offset: 128,
        };
        assert_eq!(addr1.to_string(), "[buf42 + 128]");

        let addr2 = Address::PhiCoordinate {
            class: 5,
            page: 12,
            byte: 200,
        };
        assert_eq!(addr2.to_string(), "[Φ(5, 12, 200)]");

        let addr3 = Address::RegisterIndirect {
            base: Register::new(10),
            offset: 64,
        };
        assert_eq!(addr3.to_string(), "[r10 + 64]");

        let addr4 = Address::RegisterIndirect {
            base: Register::new(10),
            offset: -32,
        };
        assert_eq!(addr4.to_string(), "[r10 - 32]");
    }
}
