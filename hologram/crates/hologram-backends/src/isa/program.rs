//! Program container for Atlas ISA instructions
//!
//! A Program is a sequence of instructions with label metadata for control flow.

use super::instruction::Instruction;
use std::collections::HashMap;

/// Errors that can occur when building or manipulating programs
#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ProgramError {
    /// Duplicate label definition
    #[error("duplicate label '{0}' at instruction {1}")]
    DuplicateLabel(String, usize),

    /// Undefined label referenced
    #[error("undefined label '{0}' referenced in instruction {1}")]
    UndefinedLabel(String, usize),

    /// Label points to invalid instruction index
    #[error("label '{0}' points to invalid instruction index {1} (max: {2})")]
    InvalidLabelTarget(String, usize, usize),
}

/// Result type for program operations
pub type ProgramResult<T> = std::result::Result<T, ProgramError>;

/// A program is a sequence of instructions with label metadata for control flow
///
/// Programs are executed by backends implementing `Backend::execute_program()`.
/// Labels mark jump targets for BRA, CALL, and LOOP instructions.
///
/// Programs can be serialized to binary format for ahead-of-time compilation
/// and deserialized at runtime for execution.
///
/// # Example
///
/// ```
/// use hologram_backends::{Program, Instruction, Register, Type, Label};
///
/// let mut program = Program::new();
///
/// // Add instructions
/// program.instructions.push(Instruction::MOV {
///     ty: Type::I32,
///     dst: Register::new(0),
///     src: Register::new(1),
/// });
///
/// // Add a label
/// program.add_label("loop_start").unwrap();
///
/// program.instructions.push(Instruction::BRA {
///     target: Label::new("loop_start"),
///     pred: None,
/// });
///
/// // Resolve label to instruction index
/// assert_eq!(program.resolve_label("loop_start"), Some(1));
/// ```
///
/// # Serialization
///
/// Programs can be serialized to binary format using bincode:
///
/// ```
/// use hologram_backends::Program;
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let program = Program::new();
///
/// // Serialize to bytes
/// let bytes = program.to_bytes()?;
///
/// // Deserialize from bytes
/// let loaded = Program::from_bytes(&bytes)?;
/// assert_eq!(program, loaded);
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Program {
    /// Instruction sequence
    pub instructions: Vec<Instruction>,

    /// Label definitions (name → instruction index)
    ///
    /// Labels mark jump targets for control flow instructions.
    /// Instruction indices are 0-based positions in the instructions vector.
    pub labels: HashMap<String, usize>,
}

impl Program {
    /// Create a new empty program
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            labels: HashMap::new(),
        }
    }

    /// Create a program from a sequence of instructions (no labels)
    pub fn from_instructions(instructions: Vec<Instruction>) -> Self {
        Self {
            instructions,
            labels: HashMap::new(),
        }
    }

    /// Create a program with preallocated capacity
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            instructions: Vec::with_capacity(capacity),
            labels: HashMap::new(),
        }
    }

    /// Add a label at the current instruction position
    ///
    /// Labels mark the position for control flow instructions (BRA, CALL, LOOP).
    /// The label will point to the next instruction that will be added.
    ///
    /// # Errors
    ///
    /// Returns `ProgramError::DuplicateLabel` if a label with the same name already exists.
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_backends::Program;
    ///
    /// let mut program = Program::new();
    /// program.add_label("start").unwrap();
    /// assert_eq!(program.resolve_label("start"), Some(0));
    /// ```
    pub fn add_label(&mut self, name: impl Into<String>) -> ProgramResult<()> {
        let name = name.into();
        let idx = self.instructions.len();

        if self.labels.contains_key(&name) {
            return Err(ProgramError::DuplicateLabel(name, idx));
        }

        self.labels.insert(name, idx);
        Ok(())
    }

    /// Resolve a label to its instruction index
    ///
    /// Returns `None` if the label is not defined.
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_backends::Program;
    ///
    /// let mut program = Program::new();
    /// program.add_label("loop_start").unwrap();
    /// assert_eq!(program.resolve_label("loop_start"), Some(0));
    /// assert_eq!(program.resolve_label("undefined"), None);
    /// ```
    pub fn resolve_label(&self, name: &str) -> Option<usize> {
        self.labels.get(name).copied()
    }

    /// Check if a label exists
    pub fn has_label(&self, name: &str) -> bool {
        self.labels.contains_key(name)
    }

    /// Get the number of instructions in the program
    pub fn len(&self) -> usize {
        self.instructions.len()
    }

    /// Check if the program is empty
    pub fn is_empty(&self) -> bool {
        self.instructions.is_empty()
    }

    /// Validate the program
    ///
    /// Checks that:
    /// - All label targets are within instruction bounds
    /// - All control flow instructions reference defined labels
    ///
    /// # Errors
    ///
    /// Returns errors for undefined labels or invalid label targets.
    pub fn validate(&self) -> ProgramResult<()> {
        // Validate that all labels point to valid instruction indices
        for (name, &idx) in &self.labels {
            if idx > self.instructions.len() {
                return Err(ProgramError::InvalidLabelTarget(
                    name.clone(),
                    idx,
                    self.instructions.len(),
                ));
            }
        }

        // Validate that all control flow instructions reference defined labels
        for (idx, instruction) in self.instructions.iter().enumerate() {
            match instruction {
                Instruction::BRA { target, .. } | Instruction::CALL { target } => {
                    if !self.has_label(target.name()) {
                        return Err(ProgramError::UndefinedLabel(target.name().to_string(), idx));
                    }
                }
                Instruction::LOOP { body, .. } => {
                    if !self.has_label(body.name()) {
                        return Err(ProgramError::UndefinedLabel(body.name().to_string(), idx));
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }

    /// Serialize the program to binary format
    ///
    /// Uses bincode for efficient binary serialization. The serialized format
    /// preserves instructions and labels for deserialization at runtime.
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_backends::Program;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let program = Program::new();
    /// let bytes = program.to_bytes()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn to_bytes(&self) -> Result<Vec<u8>, bincode::Error> {
        bincode::serialize(self)
    }

    /// Deserialize a program from binary format
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_backends::Program;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let program = Program::new();
    /// let bytes = program.to_bytes()?;
    /// let loaded = Program::from_bytes(&bytes)?;
    /// assert_eq!(program, loaded);
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, bincode::Error> {
        bincode::deserialize(bytes)
    }

    /// Save program to a file
    ///
    /// # Example
    ///
    /// ```no_run
    /// use hologram_backends::Program;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let program = Program::new();
    /// program.save_to_file("program.bin")?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn save_to_file(&self, path: impl AsRef<std::path::Path>) -> std::io::Result<()> {
        let bytes = self
            .to_bytes()
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        std::fs::write(path, bytes)
    }

    /// Load program from a file
    ///
    /// # Example
    ///
    /// ```no_run
    /// use hologram_backends::Program;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let program = Program::load_from_file("program.bin")?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn load_from_file(path: impl AsRef<std::path::Path>) -> std::io::Result<Self> {
        let bytes = std::fs::read(path)?;
        Self::from_bytes(&bytes).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }
}

impl Default for Program {
    fn default() -> Self {
        Self::new()
    }
}

// Compatibility helpers for migration from Vec<Instruction>
impl From<Vec<Instruction>> for Program {
    fn from(instructions: Vec<Instruction>) -> Self {
        Self::from_instructions(instructions)
    }
}

impl From<Program> for Vec<Instruction> {
    fn from(program: Program) -> Self {
        program.instructions
    }
}

// ================================================================================================
// Tests
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isa::types::{Label, Register, Type};

    #[test]
    fn test_program_new() {
        let program = Program::new();
        assert_eq!(program.len(), 0);
        assert!(program.is_empty());
        assert_eq!(program.labels.len(), 0);
    }

    #[test]
    fn test_program_from_instructions() {
        let instructions = vec![
            Instruction::MOV {
                ty: Type::I32,
                dst: Register::new(0),
                src: Register::new(1),
            },
            Instruction::EXIT,
        ];

        let program = Program::from_instructions(instructions);
        assert_eq!(program.len(), 2);
        assert_eq!(program.labels.len(), 0);
    }

    #[test]
    fn test_program_with_capacity() {
        let program = Program::with_capacity(10);
        assert_eq!(program.len(), 0);
        assert!(program.instructions.capacity() >= 10);
    }

    #[test]
    fn test_program_add_label() {
        let mut program = Program::new();

        // Add label at position 0
        program.add_label("start").unwrap();
        assert_eq!(program.resolve_label("start"), Some(0));
        assert!(program.has_label("start"));

        // Add instruction
        program.instructions.push(Instruction::EXIT);

        // Add label at position 1
        program.add_label("end").unwrap();
        assert_eq!(program.resolve_label("end"), Some(1));
    }

    #[test]
    fn test_program_duplicate_label() {
        let mut program = Program::new();

        program.add_label("loop").unwrap();

        // Try to add duplicate label
        let result = program.add_label("loop");
        assert!(result.is_err());

        match result {
            Err(ProgramError::DuplicateLabel(name, _idx)) => {
                assert_eq!(name, "loop");
            }
            _ => panic!("Expected DuplicateLabel error"),
        }
    }

    #[test]
    fn test_program_resolve_undefined_label() {
        let program = Program::new();
        assert_eq!(program.resolve_label("undefined"), None);
        assert!(!program.has_label("undefined"));
    }

    #[test]
    fn test_program_from_vec_instruction() {
        let instructions = vec![Instruction::MOV {
            ty: Type::I32,
            dst: Register::new(0),
            src: Register::new(1),
        }];

        let program: Program = instructions.into();
        assert_eq!(program.len(), 1);
    }

    #[test]
    fn test_program_to_vec_instruction() {
        let mut program = Program::new();
        program.instructions.push(Instruction::EXIT);

        let instructions: Vec<Instruction> = program.into();
        assert_eq!(instructions.len(), 1);
    }

    #[test]
    fn test_program_default() {
        let program: Program = Default::default();
        assert_eq!(program.len(), 0);
    }

    #[test]
    fn test_program_with_control_flow() {
        let mut program = Program::new();

        // loop_start:
        program.add_label("loop_start").unwrap();

        // MOV r0, r1
        program.instructions.push(Instruction::MOV {
            ty: Type::I32,
            dst: Register::new(0),
            src: Register::new(1),
        });

        // BRA loop_start
        program.instructions.push(Instruction::BRA {
            target: Label::new("loop_start"),
            pred: None,
        });

        assert_eq!(program.len(), 2);
        assert_eq!(program.resolve_label("loop_start"), Some(0));

        // Validation should pass
        assert!(program.validate().is_ok());
    }

    #[test]
    fn test_program_multiple_labels() {
        let mut program = Program::new();

        program.add_label("label1").unwrap();
        program.instructions.push(Instruction::EXIT);

        program.add_label("label2").unwrap();
        program.instructions.push(Instruction::EXIT);

        program.add_label("label3").unwrap();
        program.instructions.push(Instruction::EXIT);

        assert_eq!(program.resolve_label("label1"), Some(0));
        assert_eq!(program.resolve_label("label2"), Some(1));
        assert_eq!(program.resolve_label("label3"), Some(2));
        assert_eq!(program.labels.len(), 3);
    }

    #[test]
    fn test_program_validate_undefined_label() {
        let mut program = Program::new();

        program.instructions.push(Instruction::BRA {
            target: Label::new("undefined"),
            pred: None,
        });

        let result = program.validate();
        assert!(result.is_err());

        match result {
            Err(ProgramError::UndefinedLabel(name, idx)) => {
                assert_eq!(name, "undefined");
                assert_eq!(idx, 0);
            }
            _ => panic!("Expected UndefinedLabel error"),
        }
    }

    #[test]
    fn test_program_validate_invalid_label_target() {
        let mut program = Program::new();

        // Manually insert an invalid label (beyond instruction bounds)
        program.labels.insert("bad_label".to_string(), 100);
        program.instructions.push(Instruction::EXIT);

        let result = program.validate();
        assert!(result.is_err());

        match result {
            Err(ProgramError::InvalidLabelTarget(name, idx, max)) => {
                assert_eq!(name, "bad_label");
                assert_eq!(idx, 100);
                assert_eq!(max, 1);
            }
            _ => panic!("Expected InvalidLabelTarget error"),
        }
    }

    #[test]
    fn test_program_error_display() {
        let err = ProgramError::DuplicateLabel("test".to_string(), 5);
        assert_eq!(err.to_string(), "duplicate label 'test' at instruction 5");

        let err = ProgramError::UndefinedLabel("missing".to_string(), 10);
        assert_eq!(
            err.to_string(),
            "undefined label 'missing' referenced in instruction 10"
        );

        let err = ProgramError::InvalidLabelTarget("bad".to_string(), 100, 50);
        assert_eq!(
            err.to_string(),
            "label 'bad' points to invalid instruction index 100 (max: 50)"
        );
    }

    #[test]
    fn test_program_error_equality() {
        let err1 = ProgramError::DuplicateLabel("test".to_string(), 5);
        let err2 = ProgramError::DuplicateLabel("test".to_string(), 5);
        let err3 = ProgramError::DuplicateLabel("other".to_string(), 5);

        assert_eq!(err1, err2);
        assert_ne!(err1, err3);
    }

    #[test]
    fn test_program_serialization() {
        let mut program = Program::new();

        program.add_label("start").unwrap();
        program.instructions.push(Instruction::MOV {
            ty: Type::I32,
            dst: Register::new(0),
            src: Register::new(1),
        });
        program.add_label("end").unwrap();
        program.instructions.push(Instruction::EXIT);

        // Serialize to bytes
        let bytes = program.to_bytes().unwrap();
        assert!(!bytes.is_empty());

        // Deserialize from bytes
        let loaded = Program::from_bytes(&bytes).unwrap();
        assert_eq!(loaded, program);
        assert_eq!(loaded.len(), 2);
        assert_eq!(loaded.resolve_label("start"), Some(0));
        assert_eq!(loaded.resolve_label("end"), Some(1));
    }

    #[test]
    fn test_program_serialization_with_control_flow() {
        let mut program = Program::new();

        program.add_label("loop_start").unwrap();
        program.instructions.push(Instruction::ADD {
            ty: Type::F32,
            dst: Register::new(0),
            src1: Register::new(1),
            src2: Register::new(2),
        });
        program.instructions.push(Instruction::BRA {
            target: Label::new("loop_start"),
            pred: None,
        });

        // Serialize and deserialize
        let bytes = program.to_bytes().unwrap();
        let loaded = Program::from_bytes(&bytes).unwrap();

        assert_eq!(loaded, program);
        assert!(loaded.validate().is_ok());
    }

    #[test]
    fn test_program_serialization_empty() {
        let program = Program::new();

        let bytes = program.to_bytes().unwrap();
        let loaded = Program::from_bytes(&bytes).unwrap();

        assert_eq!(loaded, program);
        assert!(loaded.is_empty());
    }
}
