//! Register file implementation shared across all backends
//!
//! Provides:
//! - 256 general-purpose typed registers
//! - 16 predicate registers (boolean)
//! - Type tracking for runtime validation
//! - Initialization state tracking
//! - Read/write operations with bounds checking
//!
//! This implementation is shared across CPU, GPU, TPU, and FPGA backends.

use crate::error::{BackendError, Result};
use crate::isa::{Predicate, Register, Type};
use std::fmt;

// ================================================================================================
// Register Value Storage
// ================================================================================================

/// Register value with type information
///
/// Each register can hold a value of any supported type. The type is tracked
/// to ensure type safety at runtime.
#[derive(Debug, Clone, PartialEq)]
enum RegisterValue {
    // Signed integers
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),

    // Unsigned integers
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),

    // Floating point (F16/BF16 stored as bits)
    F16(u16),
    BF16(u16),
    F32(f32),
    F64(f64),

    // Uninitialized state
    Uninitialized,
}

impl RegisterValue {
    /// Get the type of this register value
    fn get_type(&self) -> Option<Type> {
        match self {
            RegisterValue::I8(_) => Some(Type::I8),
            RegisterValue::I16(_) => Some(Type::I16),
            RegisterValue::I32(_) => Some(Type::I32),
            RegisterValue::I64(_) => Some(Type::I64),
            RegisterValue::U8(_) => Some(Type::U8),
            RegisterValue::U16(_) => Some(Type::U16),
            RegisterValue::U32(_) => Some(Type::U32),
            RegisterValue::U64(_) => Some(Type::U64),
            RegisterValue::F16(_) => Some(Type::F16),
            RegisterValue::BF16(_) => Some(Type::BF16),
            RegisterValue::F32(_) => Some(Type::F32),
            RegisterValue::F64(_) => Some(Type::F64),
            RegisterValue::Uninitialized => None,
        }
    }

    /// Check if this register is initialized
    fn is_initialized(&self) -> bool {
        !matches!(self, RegisterValue::Uninitialized)
    }
}

impl fmt::Display for RegisterValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RegisterValue::I8(v) => write!(f, "i8({})", v),
            RegisterValue::I16(v) => write!(f, "i16({})", v),
            RegisterValue::I32(v) => write!(f, "i32({})", v),
            RegisterValue::I64(v) => write!(f, "i64({})", v),
            RegisterValue::U8(v) => write!(f, "u8({})", v),
            RegisterValue::U16(v) => write!(f, "u16({})", v),
            RegisterValue::U32(v) => write!(f, "u32({})", v),
            RegisterValue::U64(v) => write!(f, "u64({})", v),
            RegisterValue::F16(v) => write!(f, "f16(0x{:04x})", v),
            RegisterValue::BF16(v) => write!(f, "bf16(0x{:04x})", v),
            RegisterValue::F32(v) => write!(f, "f32({})", v),
            RegisterValue::F64(v) => write!(f, "f64({})", v),
            RegisterValue::Uninitialized => write!(f, "<uninitialized>"),
        }
    }
}

// ================================================================================================
// Register File
// ================================================================================================

/// Register file shared across all backends
///
/// Manages 256 general-purpose typed registers and 16 predicate registers.
/// Tracks initialization state and enforces type safety.
///
/// This implementation is used by CPU, GPU, TPU, and FPGA backends. Each backend
/// uses this register file to maintain per-lane execution state.
///
/// # Example
///
/// ```rust
/// use hologram_backends::backends::common::RegisterFile;
/// use hologram_backends::isa::{Register, Type};
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let mut regs = RegisterFile::new();
///
/// // Write a value
/// regs.write_i32(Register::new(0), 42)?;
///
/// // Read it back
/// let value = regs.read_i32(Register::new(0))?;
/// assert_eq!(value, 42);
/// # Ok(())
/// # }
/// ```
pub struct RegisterFile {
    /// General-purpose registers (256)
    registers: [RegisterValue; 256],

    /// Predicate registers (16)
    predicates: [Option<bool>; 16],
}

impl RegisterFile {
    /// Create a new register file with all registers uninitialized
    pub fn new() -> Self {
        Self {
            registers: std::array::from_fn(|_| RegisterValue::Uninitialized),
            predicates: [None; 16],
        }
    }

    /// Reset all registers to uninitialized state
    pub fn reset(&mut self) {
        self.registers.fill(RegisterValue::Uninitialized);
        self.predicates.fill(None);
    }

    // ============================================================================================
    // General Register Operations
    // ============================================================================================

    /// Check if a register is initialized
    pub fn is_initialized(&self, reg: Register) -> bool {
        self.registers[reg.index() as usize].is_initialized()
    }

    /// Get the type of a register
    pub fn get_type(&self, reg: Register) -> Option<Type> {
        self.registers[reg.index() as usize].get_type()
    }

    /// Validate register is initialized and has expected type
    fn validate_read(&self, reg: Register, expected_type: Type) -> Result<()> {
        let value = &self.registers[reg.index() as usize];

        if !value.is_initialized() {
            return Err(BackendError::UninitializedRegister(reg.index()));
        }

        match value.get_type() {
            Some(ty) if ty == expected_type => Ok(()),
            Some(ty) => Err(BackendError::TypeMismatch {
                expected: expected_type.to_string(),
                actual: ty.to_string(),
            }),
            None => unreachable!("Initialized value must have type"),
        }
    }

    // ============================================================================================
    // Typed Read Operations
    // ============================================================================================

    /// Read i8 value from register
    pub fn read_i8(&self, reg: Register) -> Result<i8> {
        self.validate_read(reg, Type::I8)?;
        match self.registers[reg.index() as usize] {
            RegisterValue::I8(v) => Ok(v),
            _ => unreachable!("Type validation ensures correct variant"),
        }
    }

    /// Read i16 value from register
    pub fn read_i16(&self, reg: Register) -> Result<i16> {
        self.validate_read(reg, Type::I16)?;
        match self.registers[reg.index() as usize] {
            RegisterValue::I16(v) => Ok(v),
            _ => unreachable!(),
        }
    }

    /// Read i32 value from register
    pub fn read_i32(&self, reg: Register) -> Result<i32> {
        self.validate_read(reg, Type::I32)?;
        match self.registers[reg.index() as usize] {
            RegisterValue::I32(v) => Ok(v),
            _ => unreachable!(),
        }
    }

    /// Read i64 value from register
    pub fn read_i64(&self, reg: Register) -> Result<i64> {
        self.validate_read(reg, Type::I64)?;
        match self.registers[reg.index() as usize] {
            RegisterValue::I64(v) => Ok(v),
            _ => unreachable!(),
        }
    }

    /// Read u8 value from register
    pub fn read_u8(&self, reg: Register) -> Result<u8> {
        self.validate_read(reg, Type::U8)?;
        match self.registers[reg.index() as usize] {
            RegisterValue::U8(v) => Ok(v),
            _ => unreachable!(),
        }
    }

    /// Read u16 value from register
    pub fn read_u16(&self, reg: Register) -> Result<u16> {
        self.validate_read(reg, Type::U16)?;
        match self.registers[reg.index() as usize] {
            RegisterValue::U16(v) => Ok(v),
            _ => unreachable!(),
        }
    }

    /// Read u32 value from register
    pub fn read_u32(&self, reg: Register) -> Result<u32> {
        self.validate_read(reg, Type::U32)?;
        match self.registers[reg.index() as usize] {
            RegisterValue::U32(v) => Ok(v),
            _ => unreachable!(),
        }
    }

    /// Read u64 value from register
    pub fn read_u64(&self, reg: Register) -> Result<u64> {
        self.validate_read(reg, Type::U64)?;
        match self.registers[reg.index() as usize] {
            RegisterValue::U64(v) => Ok(v),
            _ => unreachable!(),
        }
    }

    /// Read f16 value from register (as bits)
    pub fn read_f16_bits(&self, reg: Register) -> Result<u16> {
        self.validate_read(reg, Type::F16)?;
        match self.registers[reg.index() as usize] {
            RegisterValue::F16(v) => Ok(v),
            _ => unreachable!(),
        }
    }

    /// Read bf16 value from register (as bits)
    pub fn read_bf16_bits(&self, reg: Register) -> Result<u16> {
        self.validate_read(reg, Type::BF16)?;
        match self.registers[reg.index() as usize] {
            RegisterValue::BF16(v) => Ok(v),
            _ => unreachable!(),
        }
    }

    /// Read f32 value from register
    pub fn read_f32(&self, reg: Register) -> Result<f32> {
        self.validate_read(reg, Type::F32)?;
        match self.registers[reg.index() as usize] {
            RegisterValue::F32(v) => Ok(v),
            _ => unreachable!(),
        }
    }

    /// Read f64 value from register
    pub fn read_f64(&self, reg: Register) -> Result<f64> {
        self.validate_read(reg, Type::F64)?;
        match self.registers[reg.index() as usize] {
            RegisterValue::F64(v) => Ok(v),
            _ => unreachable!(),
        }
    }

    // ============================================================================================
    // Typed Write Operations
    // ============================================================================================

    /// Write i8 value to register
    pub fn write_i8(&mut self, reg: Register, value: i8) -> Result<()> {
        self.registers[reg.index() as usize] = RegisterValue::I8(value);
        Ok(())
    }

    /// Write i16 value to register
    pub fn write_i16(&mut self, reg: Register, value: i16) -> Result<()> {
        self.registers[reg.index() as usize] = RegisterValue::I16(value);
        Ok(())
    }

    /// Write i32 value to register
    pub fn write_i32(&mut self, reg: Register, value: i32) -> Result<()> {
        self.registers[reg.index() as usize] = RegisterValue::I32(value);
        Ok(())
    }

    /// Write i64 value to register
    pub fn write_i64(&mut self, reg: Register, value: i64) -> Result<()> {
        self.registers[reg.index() as usize] = RegisterValue::I64(value);
        Ok(())
    }

    /// Write u8 value to register
    pub fn write_u8(&mut self, reg: Register, value: u8) -> Result<()> {
        self.registers[reg.index() as usize] = RegisterValue::U8(value);
        Ok(())
    }

    /// Write u16 value to register
    pub fn write_u16(&mut self, reg: Register, value: u16) -> Result<()> {
        self.registers[reg.index() as usize] = RegisterValue::U16(value);
        Ok(())
    }

    /// Write u32 value to register
    pub fn write_u32(&mut self, reg: Register, value: u32) -> Result<()> {
        self.registers[reg.index() as usize] = RegisterValue::U32(value);
        Ok(())
    }

    /// Write u64 value to register
    pub fn write_u64(&mut self, reg: Register, value: u64) -> Result<()> {
        self.registers[reg.index() as usize] = RegisterValue::U64(value);
        Ok(())
    }

    /// Write f16 value to register (as bits)
    pub fn write_f16_bits(&mut self, reg: Register, bits: u16) -> Result<()> {
        self.registers[reg.index() as usize] = RegisterValue::F16(bits);
        Ok(())
    }

    /// Write bf16 value to register (as bits)
    pub fn write_bf16_bits(&mut self, reg: Register, bits: u16) -> Result<()> {
        self.registers[reg.index() as usize] = RegisterValue::BF16(bits);
        Ok(())
    }

    /// Write f32 value to register
    pub fn write_f32(&mut self, reg: Register, value: f32) -> Result<()> {
        self.registers[reg.index() as usize] = RegisterValue::F32(value);
        Ok(())
    }

    /// Write f64 value to register
    pub fn write_f64(&mut self, reg: Register, value: f64) -> Result<()> {
        self.registers[reg.index() as usize] = RegisterValue::F64(value);
        Ok(())
    }

    // ============================================================================================
    // Predicate Register Operations
    // ============================================================================================

    /// Read predicate register
    pub fn read_predicate(&self, pred: Predicate) -> Result<bool> {
        self.predicates[pred.index() as usize].ok_or(BackendError::UninitializedPredicate(pred.index()))
    }

    /// Write predicate register
    pub fn write_predicate(&mut self, pred: Predicate, value: bool) -> Result<()> {
        self.predicates[pred.index() as usize] = Some(value);
        Ok(())
    }

    /// Check if predicate is initialized
    pub fn is_predicate_initialized(&self, pred: Predicate) -> bool {
        self.predicates[pred.index() as usize].is_some()
    }
}

impl Default for RegisterFile {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for RegisterFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "RegisterFile {{")?;

        // Show initialized general registers
        writeln!(f, "  registers: [")?;
        for (i, reg) in self.registers.iter().enumerate() {
            if reg.is_initialized() {
                writeln!(f, "    r{}: {},", i, reg)?;
            }
        }
        writeln!(f, "  ],")?;

        // Show initialized predicates
        writeln!(f, "  predicates: [")?;
        for (i, pred) in self.predicates.iter().enumerate() {
            if let Some(value) = pred {
                writeln!(f, "    p{}: {},", i, value)?;
            }
        }
        writeln!(f, "  ],")?;

        write!(f, "}}")
    }
}

// ================================================================================================
// Tests
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_file_creation() {
        let regs = RegisterFile::new();

        // All registers should be uninitialized
        for i in 0..=255 {
            let reg = Register::new(i);
            assert!(!regs.is_initialized(reg));
            assert!(regs.get_type(reg).is_none());
        }

        // All predicates should be uninitialized
        for i in 0..16 {
            let pred = Predicate::new(i);
            assert!(!regs.is_predicate_initialized(pred));
        }
    }

    #[test]
    fn test_register_write_read_i32() {
        let mut regs = RegisterFile::new();
        let r0 = Register::new(0);

        // Write value
        regs.write_i32(r0, 42).unwrap();

        // Check initialized
        assert!(regs.is_initialized(r0));
        assert_eq!(regs.get_type(r0), Some(Type::I32));

        // Read value
        let value = regs.read_i32(r0).unwrap();
        assert_eq!(value, 42);
    }

    #[test]
    fn test_register_write_read_all_types() {
        let mut regs = RegisterFile::new();

        // Test all integer types
        regs.write_i8(Register::new(0), -42).unwrap();
        assert_eq!(regs.read_i8(Register::new(0)).unwrap(), -42);

        regs.write_i16(Register::new(1), -1234).unwrap();
        assert_eq!(regs.read_i16(Register::new(1)).unwrap(), -1234);

        regs.write_i32(Register::new(2), -123456).unwrap();
        assert_eq!(regs.read_i32(Register::new(2)).unwrap(), -123456);

        regs.write_i64(Register::new(3), -12345678901234).unwrap();
        assert_eq!(regs.read_i64(Register::new(3)).unwrap(), -12345678901234);

        regs.write_u8(Register::new(4), 200).unwrap();
        assert_eq!(regs.read_u8(Register::new(4)).unwrap(), 200);

        regs.write_u16(Register::new(5), 50000).unwrap();
        assert_eq!(regs.read_u16(Register::new(5)).unwrap(), 50000);

        regs.write_u32(Register::new(6), 3000000000).unwrap();
        assert_eq!(regs.read_u32(Register::new(6)).unwrap(), 3000000000);

        regs.write_u64(Register::new(7), 12345678901234567890).unwrap();
        assert_eq!(regs.read_u64(Register::new(7)).unwrap(), 12345678901234567890);

        // Test floating point types
        regs.write_f32(Register::new(8), std::f32::consts::PI).unwrap();
        assert!((regs.read_f32(Register::new(8)).unwrap() - std::f32::consts::PI).abs() < 0.00001);

        regs.write_f64(Register::new(9), std::f64::consts::E).unwrap();
        assert!((regs.read_f64(Register::new(9)).unwrap() - std::f64::consts::E).abs() < 0.0000001);

        // Test F16/BF16 as bits
        regs.write_f16_bits(Register::new(10), 0x3c00).unwrap(); // 1.0 in f16
        assert_eq!(regs.read_f16_bits(Register::new(10)).unwrap(), 0x3c00);

        regs.write_bf16_bits(Register::new(11), 0x3f80).unwrap(); // 1.0 in bf16
        assert_eq!(regs.read_bf16_bits(Register::new(11)).unwrap(), 0x3f80);
    }

    #[test]
    fn test_register_type_mismatch() {
        let mut regs = RegisterFile::new();
        let r0 = Register::new(0);

        // Write as i32
        regs.write_i32(r0, 42).unwrap();

        // Try to read as f32 - should fail
        let result = regs.read_f32(r0);
        assert!(result.is_err());
        assert!(matches!(result, Err(BackendError::TypeMismatch { .. })));
    }

    #[test]
    fn test_register_uninitialized_read() {
        let regs = RegisterFile::new();
        let r0 = Register::new(0);

        // Try to read uninitialized register
        let result = regs.read_i32(r0);
        assert!(result.is_err());
        assert!(matches!(result, Err(BackendError::UninitializedRegister(_))));
    }

    #[test]
    fn test_predicate_operations() {
        let mut regs = RegisterFile::new();
        let p0 = Predicate::new(0);
        let p15 = Predicate::new(15);

        // Initially uninitialized
        assert!(!regs.is_predicate_initialized(p0));

        // Write values
        regs.write_predicate(p0, true).unwrap();
        regs.write_predicate(p15, false).unwrap();

        // Read values
        assert!(regs.read_predicate(p0).unwrap());
        assert!(!regs.read_predicate(p15).unwrap());

        // Check initialized
        assert!(regs.is_predicate_initialized(p0));
        assert!(regs.is_predicate_initialized(p15));
    }

    #[test]
    fn test_predicate_uninitialized_read() {
        let regs = RegisterFile::new();
        let p0 = Predicate::new(0);

        // Try to read uninitialized predicate
        let result = regs.read_predicate(p0);
        assert!(result.is_err());
        assert!(matches!(result, Err(BackendError::UninitializedPredicate(_))));
    }

    #[test]
    fn test_register_reset() {
        let mut regs = RegisterFile::new();

        // Write some values
        regs.write_i32(Register::new(0), 42).unwrap();
        regs.write_f32(Register::new(1), std::f32::consts::PI).unwrap();
        regs.write_predicate(Predicate::new(0), true).unwrap();

        // Verify initialized
        assert!(regs.is_initialized(Register::new(0)));
        assert!(regs.is_initialized(Register::new(1)));
        assert!(regs.is_predicate_initialized(Predicate::new(0)));

        // Reset
        regs.reset();

        // All should be uninitialized
        assert!(!regs.is_initialized(Register::new(0)));
        assert!(!regs.is_initialized(Register::new(1)));
        assert!(!regs.is_predicate_initialized(Predicate::new(0)));
    }

    #[test]
    fn test_register_overwrite() {
        let mut regs = RegisterFile::new();
        let r0 = Register::new(0);

        // Write as i32
        regs.write_i32(r0, 42).unwrap();
        assert_eq!(regs.get_type(r0), Some(Type::I32));
        assert_eq!(regs.read_i32(r0).unwrap(), 42);

        // Overwrite with f32 (type changes)
        regs.write_f32(r0, std::f32::consts::PI).unwrap();
        assert_eq!(regs.get_type(r0), Some(Type::F32));
        assert!((regs.read_f32(r0).unwrap() - std::f32::consts::PI).abs() < 0.001);
    }

    #[test]
    fn test_all_256_registers() {
        let mut regs = RegisterFile::new();

        // Write to all 256 registers
        for i in 0..=255 {
            let reg = Register::new(i);
            regs.write_i32(reg, i as i32).unwrap();
        }

        // Read back all values
        for i in 0..=255 {
            let reg = Register::new(i);
            assert!(regs.is_initialized(reg));
            assert_eq!(regs.read_i32(reg).unwrap(), i as i32);
        }
    }

    #[test]
    fn test_all_16_predicates() {
        let mut regs = RegisterFile::new();

        // Write to all 16 predicates
        for i in 0..16 {
            let pred = Predicate::new(i);
            regs.write_predicate(pred, i % 2 == 0).unwrap();
        }

        // Read back all values
        for i in 0..16 {
            let pred = Predicate::new(i);
            assert!(regs.is_predicate_initialized(pred));
            assert_eq!(regs.read_predicate(pred).unwrap(), i % 2 == 0);
        }
    }

    #[test]
    fn test_register_value_display() {
        let v1 = RegisterValue::I32(42);
        assert_eq!(v1.to_string(), "i32(42)");

        let v2 = RegisterValue::F32(std::f32::consts::PI);
        // F32 precision is limited, so check the prefix
        assert!(v2.to_string().starts_with("f32(3.1415"));

        let v3 = RegisterValue::Uninitialized;
        assert_eq!(v3.to_string(), "<uninitialized>");

        let v4 = RegisterValue::F16(0x3c00);
        assert_eq!(v4.to_string(), "f16(0x3c00)");
    }
}
