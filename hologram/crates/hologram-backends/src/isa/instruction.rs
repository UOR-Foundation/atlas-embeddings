//! Atlas ISA Instruction Set
//!
//! Complete instruction set including:
//! - Data movement (LDG, STG, LDS, STS, MOV, CVT)
//! - Arithmetic (ADD, SUB, MUL, DIV, FMA, MIN, MAX, ABS, NEG)
//! - Logic (AND, OR, XOR, NOT, SHL, SHR, SETcc, SEL)
//! - Control flow (BRA, CALL, RET, LOOP, EXIT)
//! - Synchronization (BarSync, MemFence)
//! - Atlas-specific (ClsGet, MIRROR, UnityTest, NBR*, ResAccum, Phase*, BoundMap)
//! - Reductions (ReduceAdd, ReduceMin, ReduceMax, ReduceMul)
//! - Transcendentals (EXP, LOG, SQRT, SIN, COS, TANH, SIGMOID)
//! - Pool storage (PoolAlloc, PoolFree, PoolLoad, PoolStore)

use super::types::{Address, Condition, Label, MemoryScope, Predicate, Register, Type};
use std::fmt;

/// Complete Atlas ISA instruction set
///
/// Every instruction type from the Atlas ISA specification plus pool storage extensions.
/// Backends MUST implement all instruction types for compliance.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum Instruction {
    // ============================================================================================
    // Data Movement
    // ============================================================================================
    /// Load from global memory to register
    LDG { ty: Type, dst: Register, addr: Address },

    /// Store from register to global memory
    STG { ty: Type, src: Register, addr: Address },

    /// Load from shared memory to register
    LDS { ty: Type, dst: Register, addr: Address },

    /// Store from register to shared memory
    STS { ty: Type, src: Register, addr: Address },

    /// Move value from one register to another
    MOV { ty: Type, dst: Register, src: Register },

    /// Move immediate value to register
    ///
    /// Loads a constant value into a register. The value is interpreted according to the type.
    /// For integer types, the value is zero-extended or sign-extended as needed.
    /// For floating-point types, the value is reinterpreted as the bit pattern.
    #[allow(non_camel_case_types)]
    MOV_IMM { ty: Type, dst: Register, value: u64 },

    /// Convert between types
    CVT {
        src_ty: Type,
        dst_ty: Type,
        dst: Register,
        src: Register,
    },

    // ============================================================================================
    // Arithmetic
    // ============================================================================================
    /// Addition: dst = src1 + src2
    ADD {
        ty: Type,
        dst: Register,
        src1: Register,
        src2: Register,
    },

    /// Subtraction: dst = src1 - src2
    SUB {
        ty: Type,
        dst: Register,
        src1: Register,
        src2: Register,
    },

    /// Multiplication: dst = src1 * src2
    MUL {
        ty: Type,
        dst: Register,
        src1: Register,
        src2: Register,
    },

    /// Division: dst = src1 / src2
    DIV {
        ty: Type,
        dst: Register,
        src1: Register,
        src2: Register,
    },

    /// Multiply-add: dst = a * b + c
    MAD {
        ty: Type,
        dst: Register,
        a: Register,
        b: Register,
        c: Register,
    },

    /// Fused multiply-add: dst = a * b + c (single rounding)
    FMA {
        ty: Type,
        dst: Register,
        a: Register,
        b: Register,
        c: Register,
    },

    /// Minimum: dst = min(src1, src2)
    MIN {
        ty: Type,
        dst: Register,
        src1: Register,
        src2: Register,
    },

    /// Maximum: dst = max(src1, src2)
    MAX {
        ty: Type,
        dst: Register,
        src1: Register,
        src2: Register,
    },

    /// Absolute value: dst = |src|
    ABS { ty: Type, dst: Register, src: Register },

    /// Negation: dst = -src
    NEG { ty: Type, dst: Register, src: Register },

    // ============================================================================================
    // Logic
    // ============================================================================================
    /// Bitwise AND: dst = src1 & src2
    AND {
        ty: Type,
        dst: Register,
        src1: Register,
        src2: Register,
    },

    /// Bitwise OR: dst = src1 | src2
    OR {
        ty: Type,
        dst: Register,
        src1: Register,
        src2: Register,
    },

    /// Bitwise XOR: dst = src1 ^ src2
    XOR {
        ty: Type,
        dst: Register,
        src1: Register,
        src2: Register,
    },

    /// Bitwise NOT: dst = ~src
    NOT { ty: Type, dst: Register, src: Register },

    /// Shift left: dst = src << amount
    SHL {
        ty: Type,
        dst: Register,
        src: Register,
        amount: Register,
    },

    /// Shift right: dst = src >> amount
    SHR {
        ty: Type,
        dst: Register,
        src: Register,
        amount: Register,
    },

    /// Set condition code: dst = (src1 cond src2)
    SETcc {
        ty: Type,
        cond: Condition,
        dst: Predicate,
        src1: Register,
        src2: Register,
    },

    /// Select based on predicate: dst = pred ? src_true : src_false
    SEL {
        ty: Type,
        dst: Register,
        pred: Predicate,
        src_true: Register,
        src_false: Register,
    },

    // ============================================================================================
    // Control Flow
    // ============================================================================================
    /// Branch to label (conditional if pred is Some)
    BRA { target: Label, pred: Option<Predicate> },

    /// Call subroutine at label
    CALL { target: Label },

    /// Return from subroutine
    RET,

    /// Loop with register count
    LOOP { count: Register, body: Label },

    /// Exit program execution
    EXIT,

    // ============================================================================================
    // Synchronization
    // ============================================================================================
    /// Barrier synchronization
    BarSync { id: u8 },

    /// Memory fence
    MemFence { scope: MemoryScope },

    // ============================================================================================
    // Atlas-Specific
    // ============================================================================================
    /// Get current resonance class
    ClsGet { dst: Register },

    /// Get mirror class: dst = mirror(src)
    MIRROR { dst: Register, src: Register },

    /// Test unity neutrality: dst = (sum(R[96]) < epsilon)
    UnityTest { dst: Predicate, epsilon: f64 },

    /// Get neighbor count for class
    NbrCount { class: Register, dst: Register },

    /// Get neighbor by index
    NbrGet { class: Register, index: u8, dst: Register },

    /// Accumulate resonance: R[class] += value
    ResAccum { class: Register, value: Register },

    /// Get current phase counter
    PhaseGet { dst: Register },

    /// Advance phase counter
    PhaseAdv { delta: u16 },

    /// Map Φ-coordinates to linear address
    BoundMap {
        class: Register,
        page: Register,
        byte: Register,
        dst: Register,
    },

    // ============================================================================================
    // Reductions
    // ============================================================================================
    /// Parallel reduction: sum
    ReduceAdd {
        ty: Type,
        dst: Register,
        src_base: Register,
        count: u32,
    },

    /// Parallel reduction: minimum
    ReduceMin {
        ty: Type,
        dst: Register,
        src_base: Register,
        count: u32,
    },

    /// Parallel reduction: maximum
    ReduceMax {
        ty: Type,
        dst: Register,
        src_base: Register,
        count: u32,
    },

    /// Parallel reduction: product
    ReduceMul {
        ty: Type,
        dst: Register,
        src_base: Register,
        count: u32,
    },

    // ============================================================================================
    // Transcendentals
    // ============================================================================================
    /// Exponential: dst = e^src
    EXP { ty: Type, dst: Register, src: Register },

    /// Natural logarithm: dst = ln(src)
    LOG { ty: Type, dst: Register, src: Register },

    /// Base-2 logarithm: dst = log2(src)
    LOG2 { ty: Type, dst: Register, src: Register },

    /// Base-10 logarithm: dst = log10(src)
    LOG10 { ty: Type, dst: Register, src: Register },

    /// Square root: dst = sqrt(src)
    SQRT { ty: Type, dst: Register, src: Register },

    /// Reciprocal square root: dst = 1/sqrt(src)
    RSQRT { ty: Type, dst: Register, src: Register },

    /// Sine: dst = sin(src)
    SIN { ty: Type, dst: Register, src: Register },

    /// Cosine: dst = cos(src)
    COS { ty: Type, dst: Register, src: Register },

    /// Tangent: dst = tan(src)
    TAN { ty: Type, dst: Register, src: Register },

    /// Hyperbolic tangent: dst = tanh(src)
    TANH { ty: Type, dst: Register, src: Register },

    /// Sigmoid: dst = 1 / (1 + e^(-src))
    SIGMOID { ty: Type, dst: Register, src: Register },

    // ============================================================================================
    // Pool Storage (NEW)
    // ============================================================================================
    /// Allocate linear pool storage
    PoolAlloc { size: u64, dst: Register },

    /// Free linear pool storage
    PoolFree { handle: Register },

    /// Load from linear pool to register
    PoolLoad {
        ty: Type,
        pool: Register,
        offset: Register,
        dst: Register,
    },

    /// Store from register to linear pool
    PoolStore {
        ty: Type,
        pool: Register,
        offset: Register,
        src: Register,
    },
}

// ================================================================================================
// Display Implementation
// ================================================================================================

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // Data Movement
            Instruction::LDG { ty, dst, addr } => write!(f, "ldg.{} {}, {}", ty, dst, addr),
            Instruction::STG { ty, src, addr } => write!(f, "stg.{} {}, {}", ty, addr, src),
            Instruction::LDS { ty, dst, addr } => write!(f, "lds.{} {}, {}", ty, dst, addr),
            Instruction::STS { ty, src, addr } => write!(f, "sts.{} {}, {}", ty, addr, src),
            Instruction::MOV { ty, dst, src } => write!(f, "mov.{} {}, {}", ty, dst, src),
            Instruction::MOV_IMM { ty, dst, value } => write!(f, "mov_imm.{} {}, {}", ty, dst, value),
            Instruction::CVT {
                src_ty,
                dst_ty,
                dst,
                src,
            } => write!(f, "cvt.{}.{} {}, {}", dst_ty, src_ty, dst, src),

            // Arithmetic
            Instruction::ADD { ty, dst, src1, src2 } => write!(f, "add.{} {}, {}, {}", ty, dst, src1, src2),
            Instruction::SUB { ty, dst, src1, src2 } => write!(f, "sub.{} {}, {}, {}", ty, dst, src1, src2),
            Instruction::MUL { ty, dst, src1, src2 } => write!(f, "mul.{} {}, {}, {}", ty, dst, src1, src2),
            Instruction::DIV { ty, dst, src1, src2 } => write!(f, "div.{} {}, {}, {}", ty, dst, src1, src2),
            Instruction::MAD { ty, dst, a, b, c } => {
                write!(f, "mad.{} {}, {}, {}, {}", ty, dst, a, b, c)
            }
            Instruction::FMA { ty, dst, a, b, c } => {
                write!(f, "fma.{} {}, {}, {}, {}", ty, dst, a, b, c)
            }
            Instruction::MIN { ty, dst, src1, src2 } => write!(f, "min.{} {}, {}, {}", ty, dst, src1, src2),
            Instruction::MAX { ty, dst, src1, src2 } => write!(f, "max.{} {}, {}, {}", ty, dst, src1, src2),
            Instruction::ABS { ty, dst, src } => write!(f, "abs.{} {}, {}", ty, dst, src),
            Instruction::NEG { ty, dst, src } => write!(f, "neg.{} {}, {}", ty, dst, src),

            // Logic
            Instruction::AND { ty, dst, src1, src2 } => write!(f, "and.{} {}, {}, {}", ty, dst, src1, src2),
            Instruction::OR { ty, dst, src1, src2 } => write!(f, "or.{} {}, {}, {}", ty, dst, src1, src2),
            Instruction::XOR { ty, dst, src1, src2 } => write!(f, "xor.{} {}, {}, {}", ty, dst, src1, src2),
            Instruction::NOT { ty, dst, src } => write!(f, "not.{} {}, {}", ty, dst, src),
            Instruction::SHL { ty, dst, src, amount } => write!(f, "shl.{} {}, {}, {}", ty, dst, src, amount),
            Instruction::SHR { ty, dst, src, amount } => write!(f, "shr.{} {}, {}, {}", ty, dst, src, amount),
            Instruction::SETcc {
                ty,
                cond,
                dst,
                src1,
                src2,
            } => write!(f, "set{}.{} {}, {}, {}", cond, ty, dst, src1, src2),
            Instruction::SEL {
                ty,
                dst,
                pred,
                src_true,
                src_false,
            } => write!(f, "sel.{} {}, {}, {}, {}", ty, dst, pred, src_true, src_false),

            // Control Flow
            Instruction::BRA { target, pred } => {
                if let Some(p) = pred {
                    write!(f, "bra.{} {}", p, target)
                } else {
                    write!(f, "bra {}", target)
                }
            }
            Instruction::CALL { target } => write!(f, "call {}", target),
            Instruction::RET => write!(f, "ret"),
            Instruction::LOOP { count, body } => write!(f, "loop {}, {}", count, body),
            Instruction::EXIT => write!(f, "exit"),

            // Synchronization
            Instruction::BarSync { id } => write!(f, "bar.sync {}", id),
            Instruction::MemFence { scope } => write!(f, "memfence.{}", scope),

            // Atlas-Specific
            Instruction::ClsGet { dst } => write!(f, "cls.get {}", dst),
            Instruction::MIRROR { dst, src } => write!(f, "mirror {}, {}", dst, src),
            Instruction::UnityTest { dst, epsilon } => write!(f, "unity.test {}, {}", dst, epsilon),
            Instruction::NbrCount { class, dst } => write!(f, "nbr.count {}, {}", dst, class),
            Instruction::NbrGet { class, index, dst } => {
                write!(f, "nbr.get {}, {}, {}", dst, class, index)
            }
            Instruction::ResAccum { class, value } => write!(f, "res.accum {}, {}", class, value),
            Instruction::PhaseGet { dst } => write!(f, "phase.get {}", dst),
            Instruction::PhaseAdv { delta } => write!(f, "phase.adv {}", delta),
            Instruction::BoundMap { class, page, byte, dst } => {
                write!(f, "bound.map {}, {}, {}, {}", dst, class, page, byte)
            }

            // Reductions
            Instruction::ReduceAdd {
                ty,
                dst,
                src_base,
                count,
            } => write!(f, "reduce.add.{} {}, {}, {}", ty, dst, src_base, count),
            Instruction::ReduceMin {
                ty,
                dst,
                src_base,
                count,
            } => write!(f, "reduce.min.{} {}, {}, {}", ty, dst, src_base, count),
            Instruction::ReduceMax {
                ty,
                dst,
                src_base,
                count,
            } => write!(f, "reduce.max.{} {}, {}, {}", ty, dst, src_base, count),
            Instruction::ReduceMul {
                ty,
                dst,
                src_base,
                count,
            } => write!(f, "reduce.mul.{} {}, {}, {}", ty, dst, src_base, count),

            // Transcendentals
            Instruction::EXP { ty, dst, src } => write!(f, "exp.{} {}, {}", ty, dst, src),
            Instruction::LOG { ty, dst, src } => write!(f, "log.{} {}, {}", ty, dst, src),
            Instruction::LOG2 { ty, dst, src } => write!(f, "log2.{} {}, {}", ty, dst, src),
            Instruction::LOG10 { ty, dst, src } => write!(f, "log10.{} {}, {}", ty, dst, src),
            Instruction::SQRT { ty, dst, src } => write!(f, "sqrt.{} {}, {}", ty, dst, src),
            Instruction::RSQRT { ty, dst, src } => write!(f, "rsqrt.{} {}, {}", ty, dst, src),
            Instruction::SIN { ty, dst, src } => write!(f, "sin.{} {}, {}", ty, dst, src),
            Instruction::COS { ty, dst, src } => write!(f, "cos.{} {}, {}", ty, dst, src),
            Instruction::TAN { ty, dst, src } => write!(f, "tan.{} {}, {}", ty, dst, src),
            Instruction::TANH { ty, dst, src } => write!(f, "tanh.{} {}, {}", ty, dst, src),
            Instruction::SIGMOID { ty, dst, src } => write!(f, "sigmoid.{} {}, {}", ty, dst, src),

            // Pool Storage
            Instruction::PoolAlloc { size, dst } => write!(f, "pool.alloc {}, {}", dst, size),
            Instruction::PoolFree { handle } => write!(f, "pool.free {}", handle),
            Instruction::PoolLoad { ty, pool, offset, dst } => {
                write!(f, "pool.load.{} {}, {}, {}", ty, dst, pool, offset)
            }
            Instruction::PoolStore { ty, pool, offset, src } => {
                write!(f, "pool.store.{} {}, {}, {}", ty, pool, offset, src)
            }
        }
    }
}

// ================================================================================================
// Helper Functions
// ================================================================================================

impl Instruction {
    /// Get the category of this instruction
    pub fn category(&self) -> InstructionCategory {
        match self {
            Instruction::LDG { .. }
            | Instruction::STG { .. }
            | Instruction::LDS { .. }
            | Instruction::STS { .. }
            | Instruction::MOV { .. }
            | Instruction::MOV_IMM { .. }
            | Instruction::CVT { .. } => InstructionCategory::DataMovement,

            Instruction::ADD { .. }
            | Instruction::SUB { .. }
            | Instruction::MUL { .. }
            | Instruction::DIV { .. }
            | Instruction::MAD { .. }
            | Instruction::FMA { .. }
            | Instruction::MIN { .. }
            | Instruction::MAX { .. }
            | Instruction::ABS { .. }
            | Instruction::NEG { .. } => InstructionCategory::Arithmetic,

            Instruction::AND { .. }
            | Instruction::OR { .. }
            | Instruction::XOR { .. }
            | Instruction::NOT { .. }
            | Instruction::SHL { .. }
            | Instruction::SHR { .. }
            | Instruction::SETcc { .. }
            | Instruction::SEL { .. } => InstructionCategory::Logic,

            Instruction::BRA { .. }
            | Instruction::CALL { .. }
            | Instruction::RET
            | Instruction::LOOP { .. }
            | Instruction::EXIT => InstructionCategory::ControlFlow,

            Instruction::BarSync { .. } | Instruction::MemFence { .. } => InstructionCategory::Synchronization,

            Instruction::ClsGet { .. }
            | Instruction::MIRROR { .. }
            | Instruction::UnityTest { .. }
            | Instruction::NbrCount { .. }
            | Instruction::NbrGet { .. }
            | Instruction::ResAccum { .. }
            | Instruction::PhaseGet { .. }
            | Instruction::PhaseAdv { .. }
            | Instruction::BoundMap { .. } => InstructionCategory::AtlasSpecific,

            Instruction::ReduceAdd { .. }
            | Instruction::ReduceMin { .. }
            | Instruction::ReduceMax { .. }
            | Instruction::ReduceMul { .. } => InstructionCategory::Reduction,

            Instruction::EXP { .. }
            | Instruction::LOG { .. }
            | Instruction::LOG2 { .. }
            | Instruction::LOG10 { .. }
            | Instruction::SQRT { .. }
            | Instruction::RSQRT { .. }
            | Instruction::SIN { .. }
            | Instruction::COS { .. }
            | Instruction::TAN { .. }
            | Instruction::TANH { .. }
            | Instruction::SIGMOID { .. } => InstructionCategory::Transcendental,

            Instruction::PoolAlloc { .. }
            | Instruction::PoolFree { .. }
            | Instruction::PoolLoad { .. }
            | Instruction::PoolStore { .. } => InstructionCategory::PoolStorage,
        }
    }

    /// Does this instruction modify control flow?
    pub fn is_control_flow(&self) -> bool {
        matches!(
            self,
            Instruction::BRA { .. }
                | Instruction::CALL { .. }
                | Instruction::RET
                | Instruction::LOOP { .. }
                | Instruction::EXIT
        )
    }

    /// Does this instruction access memory?
    pub fn is_memory_access(&self) -> bool {
        matches!(
            self,
            Instruction::LDG { .. }
                | Instruction::STG { .. }
                | Instruction::LDS { .. }
                | Instruction::STS { .. }
                | Instruction::PoolLoad { .. }
                | Instruction::PoolStore { .. }
        )
    }

    /// Does this instruction access pool storage?
    pub fn is_pool_operation(&self) -> bool {
        matches!(
            self,
            Instruction::PoolAlloc { .. }
                | Instruction::PoolFree { .. }
                | Instruction::PoolLoad { .. }
                | Instruction::PoolStore { .. }
        )
    }
}

/// Instruction category
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum InstructionCategory {
    DataMovement,
    Arithmetic,
    Logic,
    ControlFlow,
    Synchronization,
    AtlasSpecific,
    Reduction,
    Transcendental,
    PoolStorage,
}

impl fmt::Display for InstructionCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InstructionCategory::DataMovement => write!(f, "Data Movement"),
            InstructionCategory::Arithmetic => write!(f, "Arithmetic"),
            InstructionCategory::Logic => write!(f, "Logic"),
            InstructionCategory::ControlFlow => write!(f, "Control Flow"),
            InstructionCategory::Synchronization => write!(f, "Synchronization"),
            InstructionCategory::AtlasSpecific => write!(f, "Atlas-Specific"),
            InstructionCategory::Reduction => write!(f, "Reduction"),
            InstructionCategory::Transcendental => write!(f, "Transcendental"),
            InstructionCategory::PoolStorage => write!(f, "Pool Storage"),
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
    fn test_instruction_display() {
        let inst = Instruction::ADD {
            ty: Type::F32,
            dst: Register(0),
            src1: Register(1),
            src2: Register(2),
        };
        assert_eq!(inst.to_string(), "add.f32 r0, r1, r2");
    }

    #[test]
    fn test_instruction_category() {
        let add = Instruction::ADD {
            ty: Type::F32,
            dst: Register(0),
            src1: Register(1),
            src2: Register(2),
        };
        assert_eq!(add.category(), InstructionCategory::Arithmetic);

        let bra = Instruction::BRA {
            target: Label::new("loop"),
            pred: None,
        };
        assert_eq!(bra.category(), InstructionCategory::ControlFlow);
        assert!(bra.is_control_flow());

        let pool_alloc = Instruction::PoolAlloc {
            size: 4096,
            dst: Register(10),
        };
        assert_eq!(pool_alloc.category(), InstructionCategory::PoolStorage);
        assert!(pool_alloc.is_pool_operation());
    }

    #[test]
    fn test_pool_instructions_display() {
        let alloc = Instruction::PoolAlloc {
            size: 4096,
            dst: Register(0),
        };
        assert_eq!(alloc.to_string(), "pool.alloc r0, 4096");

        let free = Instruction::PoolFree { handle: Register(0) };
        assert_eq!(free.to_string(), "pool.free r0");

        let load = Instruction::PoolLoad {
            ty: Type::F32,
            pool: Register(0),
            offset: Register(1),
            dst: Register(2),
        };
        assert_eq!(load.to_string(), "pool.load.f32 r2, r0, r1");

        let store = Instruction::PoolStore {
            ty: Type::F32,
            pool: Register(0),
            offset: Register(1),
            src: Register(2),
        };
        assert_eq!(store.to_string(), "pool.store.f32 r0, r1, r2");
    }

    #[test]
    fn test_memory_access_detection() {
        let ldg = Instruction::LDG {
            ty: Type::F32,
            dst: Register(0),
            addr: Address::BufferOffset { handle: 1, offset: 0 },
        };
        assert!(ldg.is_memory_access());

        let pool_load = Instruction::PoolLoad {
            ty: Type::F32,
            pool: Register(0),
            offset: Register(1),
            dst: Register(2),
        };
        assert!(pool_load.is_memory_access());
        assert!(pool_load.is_pool_operation());

        let add = Instruction::ADD {
            ty: Type::F32,
            dst: Register(0),
            src1: Register(1),
            src2: Register(2),
        };
        assert!(!add.is_memory_access());
        assert!(!add.is_pool_operation());
    }

    #[test]
    fn test_instruction_serialization() {
        // Test arithmetic instruction
        let add = Instruction::ADD {
            ty: Type::F32,
            dst: Register(0),
            src1: Register(1),
            src2: Register(2),
        };
        let bytes = bincode::serialize(&add).unwrap();
        let loaded: Instruction = bincode::deserialize(&bytes).unwrap();
        assert_eq!(loaded, add);

        // Test control flow instruction
        let bra = Instruction::BRA {
            target: Label::new("loop"),
            pred: None,
        };
        let bytes = bincode::serialize(&bra).unwrap();
        let loaded: Instruction = bincode::deserialize(&bytes).unwrap();
        assert_eq!(loaded, bra);

        // Test pool instruction
        let pool_alloc = Instruction::PoolAlloc {
            size: 4096,
            dst: Register(10),
        };
        let bytes = bincode::serialize(&pool_alloc).unwrap();
        let loaded: Instruction = bincode::deserialize(&bytes).unwrap();
        assert_eq!(loaded, pool_alloc);

        // Test transcendental
        let sin = Instruction::SIN {
            ty: Type::F32,
            dst: Register(5),
            src: Register(6),
        };
        let bytes = bincode::serialize(&sin).unwrap();
        let loaded: Instruction = bincode::deserialize(&bytes).unwrap();
        assert_eq!(loaded, sin);
    }

    #[test]
    fn test_instruction_category_serialization() {
        let category = InstructionCategory::Arithmetic;
        let bytes = bincode::serialize(&category).unwrap();
        let loaded: InstructionCategory = bincode::deserialize(&bytes).unwrap();
        assert_eq!(loaded, category);
    }
}
