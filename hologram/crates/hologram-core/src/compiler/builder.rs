//! Program Builder for ISA Instruction Generation
//!
//! Provides a fluent API for constructing Atlas ISA programs.

use crate::compiler::registers::{PredicateAllocator, RegisterAllocator};
use hologram_backends::{
    Address, BufferHandle as BackendHandle, Condition, Instruction, Label, Predicate, Program, Register, Type,
};
use std::collections::HashMap;

/// Builder for constructing ISA programs
///
/// Provides high-level methods for common instruction patterns with integrated
/// register allocation and label management.
#[derive(Debug)]
pub struct ProgramBuilder {
    instructions: Vec<Instruction>,
    reg_alloc: RegisterAllocator,
    pred_alloc: PredicateAllocator,
    labels: HashMap<String, usize>,
    next_label_id: u32,
}

impl Default for ProgramBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// Macro to generate load/store/mov methods for all types
macro_rules! typed_mem_ops {
    ($ty:ident, $suffix:ident) => {
        paste::paste! {
            #[doc = concat!("Load ", stringify!($suffix), " from global memory")]
            pub fn [<load_ $suffix>](&mut self, dst: Register, handle: BackendHandle, offset: usize) {
                self.instructions.push(Instruction::LDG {
                    ty: Type::$ty,
                    dst,
                    addr: Address::BufferOffset {
                        handle: handle.0,
                        offset,
                    },
                });
            }

            #[doc = concat!("Store ", stringify!($suffix), " to global memory")]
            pub fn [<store_ $suffix>](&mut self, src: Register, handle: BackendHandle, offset: usize) {
                self.instructions.push(Instruction::STG {
                    ty: Type::$ty,
                    src,
                    addr: Address::BufferOffset {
                        handle: handle.0,
                        offset,
                    },
                });
            }

            #[doc = concat!("Move ", stringify!($suffix), " between registers")]
            pub fn [<mov_ $suffix>](&mut self, dst: Register, src: Register) {
                self.instructions.push(Instruction::MOV {
                    ty: Type::$ty,
                    dst,
                    src,
                });
            }
        }
    };
}

impl ProgramBuilder {
    /// Create a new program builder
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            reg_alloc: RegisterAllocator::new(),
            pred_alloc: PredicateAllocator::new(),
            labels: HashMap::new(),
            next_label_id: 0,
        }
    }

    /// Build the final program with label map
    pub fn build(self) -> Program {
        Program {
            instructions: self.instructions,
            labels: self.labels,
        }
    }

    // ============================================================================
    // Register and Predicate Allocation
    // ============================================================================

    /// Allocate a new register
    ///
    /// Returns the next available register from the allocator.
    ///
    /// # Example
    ///
    /// ```text
    /// let mut builder = ProgramBuilder::new();
    /// let r0 = builder.alloc_reg()?;
    /// let r1 = builder.alloc_reg()?;
    /// ```
    pub fn alloc_reg(&mut self) -> crate::Result<Register> {
        self.reg_alloc.alloc()
    }

    /// Allocate a range of consecutive registers
    ///
    /// Useful for operations that need adjacent registers (e.g., REDUCE operations).
    ///
    /// # Example
    ///
    /// ```text
    /// let mut builder = ProgramBuilder::new();
    /// let base = builder.alloc_reg_range(4)?; // Allocates R0-R3
    /// ```
    pub fn alloc_reg_range(&mut self, count: u8) -> crate::Result<Register> {
        // Allocate the first register and return its index as the base
        let base = self.reg_alloc.alloc()?;
        // Allocate the rest
        for _ in 1..count {
            self.reg_alloc.alloc()?;
        }
        Ok(base)
    }

    /// Free a register for reuse
    pub fn free_reg(&mut self, reg: Register) {
        self.reg_alloc.free(reg);
    }

    /// Allocate a predicate register
    pub fn alloc_pred(&mut self) -> crate::Result<Predicate> {
        self.pred_alloc.alloc()
    }

    /// Free a predicate register
    pub fn free_pred(&mut self, pred: Predicate) {
        self.pred_alloc.free(pred);
    }

    // ============================================================================
    // Label Management
    // ============================================================================

    /// Generate a unique label with the given prefix
    ///
    /// # Example
    ///
    /// ```text
    /// let mut builder = ProgramBuilder::new();
    /// let loop_start = builder.gen_label("loop_start");
    /// let loop_end = builder.gen_label("loop_end");
    /// ```
    pub fn gen_label(&mut self, prefix: &str) -> Label {
        let label_name = format!("{}{}", prefix, self.next_label_id);
        self.next_label_id += 1;
        Label(label_name)
    }

    /// Add a label at the current program counter
    ///
    /// Labels mark positions in the program for branch/call targets.
    ///
    /// # Example
    ///
    /// ```text
    /// let mut builder = ProgramBuilder::new();
    /// let loop_label = Label::new("loop_start");
    /// builder.add_label(loop_label.clone());
    /// // ... add loop body instructions ...
    /// builder.branch(loop_label);
    /// ```
    pub fn add_label(&mut self, label: Label) -> crate::Result<()> {
        let pc = self.current_pc();
        if self.labels.insert(label.0.clone(), pc).is_some() {
            return Err(crate::Error::InvalidOperation(format!("Duplicate label: {}", label.0)));
        }
        Ok(())
    }

    /// Get current instruction count (useful for labels)
    pub fn current_pc(&self) -> usize {
        self.instructions.len()
    }

    // ============================================================================
    // Control Flow
    // ============================================================================

    /// Add EXIT instruction
    pub fn exit(&mut self) {
        self.instructions.push(Instruction::EXIT);
    }

    /// Add unconditional branch
    pub fn branch(&mut self, target: Label) {
        self.instructions.push(Instruction::BRA { target, pred: None });
    }

    /// Add conditional branch
    pub fn branch_if(&mut self, pred: Predicate, target: Label) {
        self.instructions.push(Instruction::BRA {
            target,
            pred: Some(pred),
        });
    }

    /// Add CALL instruction
    pub fn call(&mut self, target: Label) {
        self.instructions.push(Instruction::CALL { target });
    }

    /// Add RET instruction
    pub fn ret(&mut self) {
        self.instructions.push(Instruction::RET);
    }

    /// Add LOOP instruction
    pub fn loop_instr(&mut self, count: Register, body: Label) {
        self.instructions.push(Instruction::LOOP { count, body });
    }

    // ============================================================================
    // Arithmetic Operations (F32)
    // ============================================================================

    /// Add f32 addition: dst = src1 + src2
    pub fn add_f32(&mut self, dst: Register, src1: Register, src2: Register) {
        self.instructions.push(Instruction::ADD {
            ty: Type::F32,
            dst,
            src1,
            src2,
        });
    }

    /// Add f32 subtraction: dst = src1 - src2
    pub fn sub_f32(&mut self, dst: Register, src1: Register, src2: Register) {
        self.instructions.push(Instruction::SUB {
            ty: Type::F32,
            dst,
            src1,
            src2,
        });
    }

    /// Add f32 multiplication: dst = src1 * src2
    pub fn mul_f32(&mut self, dst: Register, src1: Register, src2: Register) {
        self.instructions.push(Instruction::MUL {
            ty: Type::F32,
            dst,
            src1,
            src2,
        });
    }

    /// Add f32 division: dst = src1 / src2
    pub fn div_f32(&mut self, dst: Register, src1: Register, src2: Register) {
        self.instructions.push(Instruction::DIV {
            ty: Type::F32,
            dst,
            src1,
            src2,
        });
    }

    /// Add f32 minimum: dst = min(src1, src2)
    pub fn min_f32(&mut self, dst: Register, src1: Register, src2: Register) {
        self.instructions.push(Instruction::MIN {
            ty: Type::F32,
            dst,
            src1,
            src2,
        });
    }

    /// Add f32 maximum: dst = max(src1, src2)
    pub fn max_f32(&mut self, dst: Register, src1: Register, src2: Register) {
        self.instructions.push(Instruction::MAX {
            ty: Type::F32,
            dst,
            src1,
            src2,
        });
    }

    /// Add f32 absolute value: dst = |src|
    pub fn abs_f32(&mut self, dst: Register, src: Register) {
        self.instructions.push(Instruction::ABS {
            ty: Type::F32,
            dst,
            src,
        });
    }

    /// Add f32 negation: dst = -src
    pub fn neg_f32(&mut self, dst: Register, src: Register) {
        self.instructions.push(Instruction::NEG {
            ty: Type::F32,
            dst,
            src,
        });
    }

    // ============================================================================
    // Memory Operations
    // ============================================================================

    /// Load f32 from global memory: dst = mem[handle + offset]
    pub fn load_f32(&mut self, dst: Register, handle: BackendHandle, offset: usize) {
        self.instructions.push(Instruction::LDG {
            ty: Type::F32,
            dst,
            addr: Address::BufferOffset {
                handle: handle.0,
                offset,
            },
        });
    }

    /// Store f32 to global memory: mem[handle + offset] = src
    pub fn store_f32(&mut self, src: Register, handle: BackendHandle, offset: usize) {
        self.instructions.push(Instruction::STG {
            ty: Type::F32,
            src,
            addr: Address::BufferOffset {
                handle: handle.0,
                offset,
            },
        });
    }

    /// Move value between registers: dst = src
    pub fn mov_f32(&mut self, dst: Register, src: Register) {
        self.instructions.push(Instruction::MOV {
            ty: Type::F32,
            dst,
            src,
        });
    }

    // ============================================================================
    // Typed Memory Operations (All 12 Types)
    // ============================================================================

    // Generate for all integer types
    typed_mem_ops!(I8, i8);
    typed_mem_ops!(I16, i16);
    typed_mem_ops!(I32, i32);
    typed_mem_ops!(I64, i64);
    typed_mem_ops!(U8, u8);
    typed_mem_ops!(U16, u16);
    typed_mem_ops!(U32, u32);
    typed_mem_ops!(U64, u64);

    // Generate for floating-point types
    typed_mem_ops!(F16, f16);
    typed_mem_ops!(BF16, bf16);
    typed_mem_ops!(F64, f64);
    // F32 already defined above

    // ============================================================================
    // Transcendental Operations
    // ============================================================================

    /// Add f32 sigmoid: dst = sigmoid(src)
    pub fn sigmoid_f32(&mut self, dst: Register, src: Register) {
        self.instructions.push(Instruction::SIGMOID {
            ty: Type::F32,
            dst,
            src,
        });
    }

    /// Add f32 tanh: dst = tanh(src)
    pub fn tanh_f32(&mut self, dst: Register, src: Register) {
        self.instructions.push(Instruction::TANH {
            ty: Type::F32,
            dst,
            src,
        });
    }

    /// Add f32 exp: dst = exp(src)
    pub fn exp_f32(&mut self, dst: Register, src: Register) {
        self.instructions.push(Instruction::EXP {
            ty: Type::F32,
            dst,
            src,
        });
    }

    /// Add f32 log: dst = log(src)
    pub fn log_f32(&mut self, dst: Register, src: Register) {
        self.instructions.push(Instruction::LOG {
            ty: Type::F32,
            dst,
            src,
        });
    }

    /// Add f32 sin: dst = sin(src)
    pub fn sin_f32(&mut self, dst: Register, src: Register) {
        self.instructions.push(Instruction::SIN {
            ty: Type::F32,
            dst,
            src,
        });
    }

    /// Add f32 cos: dst = cos(src)
    pub fn cos_f32(&mut self, dst: Register, src: Register) {
        self.instructions.push(Instruction::COS {
            ty: Type::F32,
            dst,
            src,
        });
    }

    // ============================================================================
    // Reduction Operations
    // ============================================================================

    /// Add parallel sum reduction: dst = sum(src_base[0..count])
    pub fn reduce_sum_f32(&mut self, dst: Register, src_base: Register, count: u32) {
        self.instructions.push(Instruction::ReduceAdd {
            ty: Type::F32,
            dst,
            src_base,
            count,
        });
    }

    /// Add parallel min reduction: dst = min(src_base[0..count])
    pub fn reduce_min_f32(&mut self, dst: Register, src_base: Register, count: u32) {
        self.instructions.push(Instruction::ReduceMin {
            ty: Type::F32,
            dst,
            src_base,
            count,
        });
    }

    /// Add parallel max reduction: dst = max(src_base[0..count])
    pub fn reduce_max_f32(&mut self, dst: Register, src_base: Register, count: u32) {
        self.instructions.push(Instruction::ReduceMax {
            ty: Type::F32,
            dst,
            src_base,
            count,
        });
    }

    // ============================================================================
    // Comparison and Selection
    // ============================================================================

    /// Compare and set predicate: pred = (src1 > src2)
    pub fn set_gt_f32(&mut self, pred: Predicate, src1: Register, src2: Register) {
        self.instructions.push(Instruction::SETcc {
            ty: Type::F32,
            cond: Condition::GT,
            dst: pred,
            src1,
            src2,
        });
    }

    /// Select based on predicate: dst = pred ? src_true : src_false
    pub fn select_f32(&mut self, dst: Register, pred: Predicate, src_true: Register, src_false: Register) {
        self.instructions.push(Instruction::SEL {
            ty: Type::F32,
            dst,
            pred,
            src_true,
            src_false,
        });
    }

    // ============================================================================
    // Atlas-Specific Operations
    // ============================================================================

    /// Get current resonance class
    pub fn cls_get(&mut self, dst: Register) {
        self.instructions.push(Instruction::ClsGet { dst });
    }

    /// Get mirror of class
    pub fn mirror(&mut self, dst: Register, src: Register) {
        self.instructions.push(Instruction::MIRROR { dst, src });
    }

    /// Get current phase
    pub fn phase_get(&mut self, dst: Register) {
        self.instructions.push(Instruction::PhaseGet { dst });
    }

    /// Advance phase counter
    pub fn phase_adv(&mut self, delta: u16) {
        self.instructions.push(Instruction::PhaseAdv { delta });
    }

    // ============================================================================
    // Raw Instruction Insertion
    // ============================================================================

    /// Add a raw instruction (for advanced use)
    pub fn push(&mut self, instruction: Instruction) {
        self.instructions.push(instruction);
    }

    /// Add multiple instructions
    pub fn extend(&mut self, instructions: impl IntoIterator<Item = Instruction>) {
        self.instructions.extend(instructions);
    }

    // ============================================================================
    // Type-Generic Instruction Helpers
    // ============================================================================

    /// Load from global memory (type-generic)
    pub fn load(&mut self, ty: Type, dst: Register, handle: BackendHandle, offset: usize) {
        self.instructions.push(Instruction::LDG {
            ty,
            dst,
            addr: Address::BufferOffset {
                handle: handle.0,
                offset,
            },
        });
    }

    /// Store to global memory (type-generic)
    pub fn store(&mut self, ty: Type, src: Register, handle: BackendHandle, offset: usize) {
        self.instructions.push(Instruction::STG {
            ty,
            src,
            addr: Address::BufferOffset {
                handle: handle.0,
                offset,
            },
        });
    }

    /// Add operation (type-generic)
    pub fn add(&mut self, ty: Type, dst: Register, src1: Register, src2: Register) {
        self.instructions.push(Instruction::ADD { ty, dst, src1, src2 });
    }

    /// Subtract operation (type-generic)
    pub fn sub(&mut self, ty: Type, dst: Register, src1: Register, src2: Register) {
        self.instructions.push(Instruction::SUB { ty, dst, src1, src2 });
    }

    /// Multiply operation (type-generic)
    pub fn mul(&mut self, ty: Type, dst: Register, src1: Register, src2: Register) {
        self.instructions.push(Instruction::MUL { ty, dst, src1, src2 });
    }

    /// Divide operation (type-generic)
    pub fn div(&mut self, ty: Type, dst: Register, src1: Register, src2: Register) {
        self.instructions.push(Instruction::DIV { ty, dst, src1, src2 });
    }

    /// Minimum operation (type-generic)
    pub fn min(&mut self, ty: Type, dst: Register, src1: Register, src2: Register) {
        self.instructions.push(Instruction::MIN { ty, dst, src1, src2 });
    }

    /// Maximum operation (type-generic)
    pub fn max(&mut self, ty: Type, dst: Register, src1: Register, src2: Register) {
        self.instructions.push(Instruction::MAX { ty, dst, src1, src2 });
    }

    /// Absolute value (type-generic)
    pub fn abs(&mut self, ty: Type, dst: Register, src: Register) {
        self.instructions.push(Instruction::ABS { ty, dst, src });
    }

    /// Negation (type-generic)
    pub fn neg(&mut self, ty: Type, dst: Register, src: Register) {
        self.instructions.push(Instruction::NEG { ty, dst, src });
    }

    /// Reduction sum (type-generic)
    pub fn reduce_sum(&mut self, ty: Type, dst: Register, src_base: Register, count: u32) {
        self.instructions.push(Instruction::ReduceAdd {
            ty,
            dst,
            src_base,
            count,
        });
    }

    /// Reduction min (type-generic)
    pub fn reduce_min(&mut self, ty: Type, dst: Register, src_base: Register, count: u32) {
        self.instructions.push(Instruction::ReduceMin {
            ty,
            dst,
            src_base,
            count,
        });
    }

    /// Reduction max (type-generic)
    pub fn reduce_max(&mut self, ty: Type, dst: Register, src_base: Register, count: u32) {
        self.instructions.push(Instruction::ReduceMax {
            ty,
            dst,
            src_base,
            count,
        });
    }

    /// Natural logarithm (type-generic)
    pub fn log(&mut self, ty: Type, dst: Register, src: Register) {
        self.instructions.push(Instruction::LOG { ty, dst, src });
    }

    /// Sigmoid activation (type-generic)
    pub fn sigmoid(&mut self, ty: Type, dst: Register, src: Register) {
        self.instructions.push(Instruction::SIGMOID { ty, dst, src });
    }

    /// Hyperbolic tangent (type-generic)
    pub fn tanh(&mut self, ty: Type, dst: Register, src: Register) {
        self.instructions.push(Instruction::TANH { ty, dst, src });
    }

    /// Exponential function (type-generic)
    pub fn exp(&mut self, ty: Type, dst: Register, src: Register) {
        self.instructions.push(Instruction::EXP { ty, dst, src });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builder_basic() {
        let mut builder = ProgramBuilder::new();
        builder.add_f32(Register::new(0), Register::new(1), Register::new(2));
        builder.exit();

        let program = builder.build();
        assert_eq!(program.len(), 2);
    }

    #[test]
    fn test_builder_arithmetic() {
        let mut builder = ProgramBuilder::new();

        // a = b + c
        builder.add_f32(Register::new(0), Register::new(1), Register::new(2));
        // d = a * e
        builder.mul_f32(Register::new(3), Register::new(0), Register::new(4));
        builder.exit();

        let program = builder.build();
        assert_eq!(program.len(), 3);
    }

    #[test]
    fn test_builder_memory() {
        let mut builder = ProgramBuilder::new();
        let handle = BackendHandle(1);

        builder.load_f32(Register::new(0), handle, 0);
        builder.load_f32(Register::new(1), handle, 4);
        builder.add_f32(Register::new(2), Register::new(0), Register::new(1));
        builder.store_f32(Register::new(2), handle, 8);
        builder.exit();

        let program = builder.build();
        assert_eq!(program.len(), 5);
    }

    // ============================================================================
    // Register Allocation Tests
    // ============================================================================

    #[test]
    fn test_alloc_reg() {
        let mut builder = ProgramBuilder::new();

        // Allocate first register (should be R0)
        let r0 = builder.alloc_reg().unwrap();
        assert_eq!(r0.0, 0);

        // Allocate second register (should be R1)
        let r1 = builder.alloc_reg().unwrap();
        assert_eq!(r1.0, 1);

        // Allocate third register (should be R2)
        let r2 = builder.alloc_reg().unwrap();
        assert_eq!(r2.0, 2);
    }

    #[test]
    fn test_alloc_reg_range() {
        let mut builder = ProgramBuilder::new();

        // Allocate range of 4 registers starting at R0
        let base = builder.alloc_reg_range(4).unwrap();
        assert_eq!(base.0, 0);

        // Next allocation should be R4
        let next = builder.alloc_reg().unwrap();
        assert_eq!(next.0, 4);
    }

    #[test]
    fn test_free_reg() {
        let mut builder = ProgramBuilder::new();

        // Allocate R0, R1, R2
        let r0 = builder.alloc_reg().unwrap();
        let r1 = builder.alloc_reg().unwrap();
        let r2 = builder.alloc_reg().unwrap();

        assert_eq!(r0.0, 0);
        assert_eq!(r1.0, 1);
        assert_eq!(r2.0, 2);

        // Free R1
        builder.free_reg(r1);

        // Next allocation should reuse R1
        let reused = builder.alloc_reg().unwrap();
        assert_eq!(reused.0, 1);
    }

    #[test]
    fn test_alloc_pred() {
        let mut builder = ProgramBuilder::new();

        // Allocate first predicate (P0)
        let p0 = builder.alloc_pred().unwrap();
        assert_eq!(p0.0, 0);

        // Allocate second predicate (P1)
        let p1 = builder.alloc_pred().unwrap();
        assert_eq!(p1.0, 1);
    }

    #[test]
    fn test_free_pred() {
        let mut builder = ProgramBuilder::new();

        // Allocate P0, P1
        let p0 = builder.alloc_pred().unwrap();
        let _p1 = builder.alloc_pred().unwrap();

        // Free P0
        builder.free_pred(p0);

        // Next allocation should reuse P0
        let reused = builder.alloc_pred().unwrap();
        assert_eq!(reused.0, 0);
    }

    // ============================================================================
    // Label Generation Tests
    // ============================================================================

    #[test]
    fn test_gen_label() {
        let mut builder = ProgramBuilder::new();

        // Generate labels with prefix
        let loop_start = builder.gen_label("loop");
        let loop_end = builder.gen_label("loop");
        let branch_target = builder.gen_label("branch");

        // Labels should have unique IDs
        assert_eq!(loop_start.0, "loop0");
        assert_eq!(loop_end.0, "loop1");
        assert_eq!(branch_target.0, "branch2");
    }

    #[test]
    fn test_add_label() {
        let mut builder = ProgramBuilder::new();

        // Add some instructions
        builder.add_f32(Register::new(0), Register::new(1), Register::new(2));
        builder.add_f32(Register::new(3), Register::new(4), Register::new(5));

        // Add label at current position (PC = 2)
        let label = Label("loop_start".to_string());
        builder.add_label(label.clone()).unwrap();

        // Verify label was added to map at correct PC
        let program = builder.build();
        assert_eq!(program.labels.get("loop_start"), Some(&2));
    }

    #[test]
    fn test_duplicate_label_error() {
        let mut builder = ProgramBuilder::new();

        let label = Label("duplicate".to_string());

        // Add label once - should succeed
        assert!(builder.add_label(label.clone()).is_ok());

        // Add same label again - should fail
        let result = builder.add_label(label);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Duplicate label"));
    }

    #[test]
    fn test_current_pc() {
        let mut builder = ProgramBuilder::new();

        assert_eq!(builder.current_pc(), 0);

        builder.add_f32(Register::new(0), Register::new(1), Register::new(2));
        assert_eq!(builder.current_pc(), 1);

        builder.mul_f32(Register::new(3), Register::new(4), Register::new(5));
        assert_eq!(builder.current_pc(), 2);

        builder.exit();
        assert_eq!(builder.current_pc(), 3);
    }

    // ============================================================================
    // Control Flow Tests
    // ============================================================================

    #[test]
    fn test_control_flow_instructions() {
        let mut builder = ProgramBuilder::new();

        let target = Label("target".to_string());
        let pred = Predicate::new(0);

        builder.branch(target.clone());
        builder.branch_if(pred, target.clone());
        builder.call(target.clone());
        builder.ret();
        builder.loop_instr(Register::new(5), target);
        builder.exit();

        let program = builder.build();
        assert_eq!(program.len(), 6);
    }

    // ============================================================================
    // Arithmetic Operation Tests
    // ============================================================================

    #[test]
    fn test_all_arithmetic_ops() {
        let mut builder = ProgramBuilder::new();
        let r0 = Register::new(0);
        let r1 = Register::new(1);
        let r2 = Register::new(2);

        builder.add_f32(r0, r1, r2);
        builder.sub_f32(r0, r1, r2);
        builder.mul_f32(r0, r1, r2);
        builder.div_f32(r0, r1, r2);
        builder.min_f32(r0, r1, r2);
        builder.max_f32(r0, r1, r2);
        builder.abs_f32(r0, r1);
        builder.neg_f32(r0, r1);
        builder.exit();

        let program = builder.build();
        assert_eq!(program.len(), 9);
    }

    // ============================================================================
    // Transcendental Operation Tests
    // ============================================================================

    #[test]
    fn test_transcendental_ops() {
        let mut builder = ProgramBuilder::new();
        let r0 = Register::new(0);
        let r1 = Register::new(1);

        builder.sigmoid_f32(r0, r1);
        builder.tanh_f32(r0, r1);
        builder.exp_f32(r0, r1);
        builder.log_f32(r0, r1);
        builder.sin_f32(r0, r1);
        builder.cos_f32(r0, r1);
        builder.exit();

        let program = builder.build();
        assert_eq!(program.len(), 7);
    }

    // ============================================================================
    // Reduction Operation Tests
    // ============================================================================

    #[test]
    fn test_reduction_ops() {
        let mut builder = ProgramBuilder::new();
        let dst = Register::new(100);
        let src_base = Register::new(0);

        builder.reduce_sum_f32(dst, src_base, 16);
        builder.reduce_min_f32(dst, src_base, 16);
        builder.reduce_max_f32(dst, src_base, 16);
        builder.exit();

        let program = builder.build();
        assert_eq!(program.len(), 4);
    }

    // ============================================================================
    // Comparison and Selection Tests
    // ============================================================================

    #[test]
    fn test_comparison_and_selection() {
        let mut builder = ProgramBuilder::new();
        let pred = Predicate::new(0);
        let r0 = Register::new(0);
        let r1 = Register::new(1);
        let r2 = Register::new(2);
        let r3 = Register::new(3);

        builder.set_gt_f32(pred, r0, r1);
        builder.select_f32(r2, pred, r0, r3);
        builder.exit();

        let program = builder.build();
        assert_eq!(program.len(), 3);
    }

    // ============================================================================
    // Atlas-Specific Operation Tests
    // ============================================================================

    #[test]
    fn test_atlas_ops() {
        let mut builder = ProgramBuilder::new();
        let r0 = Register::new(0);
        let r1 = Register::new(1);

        builder.cls_get(r0);
        builder.mirror(r0, r1);
        builder.phase_get(r0);
        builder.phase_adv(10);
        builder.exit();

        let program = builder.build();
        assert_eq!(program.len(), 5);
    }

    // ============================================================================
    // Typed Memory Operations Tests
    // ============================================================================

    #[test]
    fn test_typed_memory_ops() {
        let mut builder = ProgramBuilder::new();
        let handle = BackendHandle(1);
        let r0 = Register::new(0);
        let r1 = Register::new(1);

        // Test integer types
        builder.load_i8(r0, handle, 0);
        builder.store_i8(r0, handle, 0);
        builder.load_i32(r0, handle, 0);
        builder.store_i32(r0, handle, 0);
        builder.load_u8(r0, handle, 0);
        builder.store_u8(r0, handle, 0);
        builder.load_u32(r0, handle, 0);
        builder.store_u32(r0, handle, 0);

        // Test floating-point types
        builder.load_f16(r0, handle, 0);
        builder.store_f16(r0, handle, 0);
        builder.load_bf16(r0, handle, 0);
        builder.store_bf16(r0, handle, 0);
        builder.load_f64(r0, handle, 0);
        builder.store_f64(r0, handle, 0);

        // Test mov
        builder.mov_i32(r0, r1);
        builder.mov_f64(r0, r1);

        builder.exit();

        let program = builder.build();
        assert_eq!(program.len(), 17);
    }

    // ============================================================================
    // Raw Instruction Tests
    // ============================================================================

    #[test]
    fn test_raw_instructions() {
        let mut builder = ProgramBuilder::new();

        // Push single instruction
        builder.push(Instruction::EXIT);

        // Extend with multiple instructions
        let instrs = vec![
            Instruction::ADD {
                ty: Type::F32,
                dst: Register::new(0),
                src1: Register::new(1),
                src2: Register::new(2),
            },
            Instruction::EXIT,
        ];
        builder.extend(instrs);

        let program = builder.build();
        assert_eq!(program.len(), 3);
    }

    // ============================================================================
    // Integration Tests
    // ============================================================================

    #[test]
    fn test_loop_with_labels() {
        let mut builder = ProgramBuilder::new();

        // Generate labels
        let loop_start = builder.gen_label("loop");
        let loop_end = builder.gen_label("end");

        // Add loop start label
        builder.add_label(loop_start.clone()).unwrap();

        // Loop body
        builder.add_f32(Register::new(0), Register::new(1), Register::new(2));

        // Branch back to loop start
        builder.branch(loop_start);

        // Add loop end label
        builder.add_label(loop_end.clone()).unwrap();
        builder.exit();

        let program = builder.build();

        // Verify labels are at correct positions
        assert_eq!(program.labels.get("loop0"), Some(&0));
        assert_eq!(program.labels.get("end1"), Some(&2));
        assert_eq!(program.len(), 3);
    }

    #[test]
    fn test_register_allocation_in_program() {
        let mut builder = ProgramBuilder::new();
        let handle = BackendHandle(1);

        // Allocate registers for computation
        let temp1 = builder.alloc_reg().unwrap();
        let temp2 = builder.alloc_reg().unwrap();
        let result = builder.alloc_reg().unwrap();

        // Use allocated registers
        builder.load_f32(temp1, handle, 0);
        builder.load_f32(temp2, handle, 4);
        builder.add_f32(result, temp1, temp2);
        builder.store_f32(result, handle, 8);

        // Free temp registers
        builder.free_reg(temp1);
        builder.free_reg(temp2);

        // Allocate new register (should reuse freed one)
        let reused = builder.alloc_reg().unwrap();
        assert!(reused.0 == 0 || reused.0 == 1);

        builder.exit();

        let program = builder.build();
        assert_eq!(program.len(), 5);
    }
}
