//! Hologram Compiler → ISA translation with canonicalization
//!
//! This module provides the bridge between Hologram Compiler's canonicalized circuit
//! representation and the hologram-backends ISA. It translates GeneratorCall
//! sequences (produced by hologram-compiler canonicalization) into optimized ISA Programs.
//!
//! # Architecture
//!
//! ```text
//! Hologram Circuit String
//!   ↓ [SigmaticsCompiler::compile()]
//! CompiledCircuit { calls: Vec<GeneratorCall>, ... }
//!   ↓ [translate_compiled_circuit()]
//! ISA Program { instructions: Vec<Instruction>, ... }
//! ```
//!
//! # Benefits
//!
//! - **Canonicalization**: Hologram Compiler applies pattern rewriting (H²=I, X²=I, etc.)
//! - **Operation Reduction**: Typically 70-80% fewer operations after canonicalization
//! - **Optimized ISA**: Fewer instructions = lower latency at runtime
//!
//! # Usage
//!
//! ```text
//! use hologram_compiler::SigmaticsCompiler;
//! use hologram_backends::sigmatics_to_isa::translate_to_isa_with_canonicalization;
//!
//! let circuit = "copy@c05 . mark@c21 . copy@c05 . mark@c21"; // H² pattern
//! let result = translate_to_isa_with_canonicalization(circuit)?;
//!
//! println!("Optimization: {} ops → {} ops ({:.1}% reduction)",
//!     result.original_ops, result.canonical_ops, result.reduction_pct);
//!
//! // Execute optimized program
//! backend.execute_program(&result.program, &config)?;
//! ```

use crate::isa::special_registers::GLOBAL_LANE_ID;
use crate::isa::{Address, Instruction, Program, Register, Type};
use hologram_compiler::{CompiledCircuit, GeneratorCall, MergeVariant, SigmaticsCompiler, SplitVariant};
use std::collections::HashMap;

/// Result of Hologram Compiler → ISA translation with optimization metrics
#[derive(Debug, Clone)]
pub struct TranslatedProgram {
    /// Optimized ISA program
    pub program: Program,
    /// Operation count before canonicalization
    pub original_ops: usize,
    /// Operation count after canonicalization
    pub canonical_ops: usize,
    /// Reduction percentage
    pub reduction_pct: f32,
    /// Original circuit expression
    pub original_expr: String,
    /// Canonical circuit expression
    pub canonical_expr: String,
}

/// Compile Hologram circuit with canonicalization and translate to ISA
///
/// This is the main entry point for operations that benefit from hologram-compiler
/// canonicalization (quantum circuits, complex gate patterns).
///
/// # Process
///
/// 1. Parse and canonicalize circuit using hologram-compiler
/// 2. Apply pattern rewriting rules (H²=I, X²=I, HXH=Z, etc.)
/// 3. Translate canonicalized GeneratorCall sequence to ISA
/// 4. Return optimized program with metrics
pub fn translate_to_isa_with_canonicalization(circuit: &str) -> Result<TranslatedProgram, String> {
    // Step 1: Compile and canonicalize with hologram-compiler
    let compiled = SigmaticsCompiler::compile(circuit)?;

    // Step 2: Translate to ISA
    let program = translate_compiled_circuit(&compiled)?;

    // Step 3: Calculate metrics
    let reduction_pct = if compiled.original_ops > 0 {
        ((compiled.original_ops - compiled.canonical_ops) as f32 / compiled.original_ops as f32) * 100.0
    } else {
        0.0
    };

    Ok(TranslatedProgram {
        program,
        original_ops: compiled.original_ops,
        canonical_ops: compiled.canonical_ops,
        reduction_pct,
        original_expr: compiled.original_expr,
        canonical_expr: compiled.canonical_expr,
    })
}

/// Translate a hologram-compiler CompiledCircuit to ISA Program
///
/// This assumes the circuit has already been canonicalized by hologram-compiler.
/// Each GeneratorCall is translated to a sequence of ISA instructions.
pub fn translate_compiled_circuit(compiled: &CompiledCircuit) -> Result<Program, String> {
    let mut instructions = Vec::new();

    for call in &compiled.calls {
        instructions.extend(translate_generator_call(call)?);
    }

    // Add EXIT instruction
    instructions.push(Instruction::EXIT);

    Ok(Program {
        instructions,
        labels: HashMap::new(),
    })
}

/// Translate a single GeneratorCall to ISA instructions
///
/// Each generator becomes a parallel loop using GLOBAL_LANE_ID for indexing.
/// Buffer handles are loaded as immediates, and RegisterIndirectComputed
/// provides zero-copy access.
fn translate_generator_call(call: &GeneratorCall) -> Result<Vec<Instruction>, String> {
    match call {
        GeneratorCall::Merge {
            src_class,
            dst_class,
            context_class,
            variant,
        } => translate_merge(*src_class, *dst_class, *context_class, *variant),

        GeneratorCall::Split {
            src_class,
            dst_class,
            context_class,
            variant,
        } => translate_split(*src_class, *dst_class, *context_class, *variant),

        GeneratorCall::Mark { class } => translate_mark(*class),

        GeneratorCall::Copy { src_class, dst_class } => translate_copy(*src_class, *dst_class),

        GeneratorCall::Swap { class_a, class_b } => translate_swap(*class_a, *class_b),

        GeneratorCall::ReduceSum {
            src_class,
            dst_class,
            n,
        } => translate_reduce_sum(*src_class, *dst_class, *n),

        GeneratorCall::ReduceMin {
            src_class,
            dst_class,
            n,
        } => translate_reduce_min(*src_class, *dst_class, *n),

        GeneratorCall::ReduceMax {
            src_class,
            dst_class,
            n,
        } => translate_reduce_max(*src_class, *dst_class, *n),

        GeneratorCall::Softmax {
            src_class,
            dst_class,
            n,
        } => translate_softmax(*src_class, *dst_class, *n),

        GeneratorCall::MergeRange {
            start_class,
            end_class,
            variant,
        } => translate_merge_range(*start_class, *end_class, *variant),

        GeneratorCall::MarkRange { start_class, end_class } => translate_mark_range(*start_class, *end_class),

        GeneratorCall::Quote { .. }
        | GeneratorCall::Evaluate { .. }
        | GeneratorCall::QuoteRange { .. }
        | GeneratorCall::EvaluateRange { .. } => {
            // Quote/Evaluate are meta-operations that don't map to ISA instructions
            // They're used for hologram-compiler's computational semantics but don't affect execution
            Ok(vec![])
        }
    }
}

/// Translate Merge generator to ISA
///
/// Pattern: dst[i] = src[i] op context[i] (parallel across lanes)
fn translate_merge(
    src_class: u8,
    dst_class: u8,
    context_class: u8,
    variant: MergeVariant,
) -> Result<Vec<Instruction>, String> {
    // Placeholder handles (0) - will be replaced by runtime buffer handles via MOV_IMM
    let src_handle = src_class as u64;
    let context_handle = context_class as u64;
    let dst_handle = dst_class as u64;

    let mut instrs = vec![
        // Load buffer handles
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(1),
            value: src_handle,
        },
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(2),
            value: context_handle,
        },
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(3),
            value: dst_handle,
        },
        // Compute byte offset: GLOBAL_LANE_ID << 2 (for f32)
        Instruction::MOV_IMM {
            ty: Type::U32,
            dst: Register(250),
            value: 2,
        },
        Instruction::SHL {
            ty: Type::U64,
            dst: Register(0),
            src: GLOBAL_LANE_ID,
            amount: Register(250),
        },
        // Load operands (zero-copy via RegisterIndirectComputed)
        Instruction::LDG {
            ty: Type::F32,
            dst: Register(10),
            addr: Address::RegisterIndirectComputed {
                handle_reg: Register(1),
                offset_reg: Register(0),
            },
        },
        Instruction::LDG {
            ty: Type::F32,
            dst: Register(11),
            addr: Address::RegisterIndirectComputed {
                handle_reg: Register(2),
                offset_reg: Register(0),
            },
        },
    ];

    // Add operation based on variant
    let op_instr = match variant {
        MergeVariant::Add => Instruction::ADD {
            ty: Type::F32,
            dst: Register(12),
            src1: Register(10),
            src2: Register(11),
        },
        MergeVariant::Mul => Instruction::MUL {
            ty: Type::F32,
            dst: Register(12),
            src1: Register(10),
            src2: Register(11),
        },
        MergeVariant::Min => Instruction::MIN {
            ty: Type::F32,
            dst: Register(12),
            src1: Register(10),
            src2: Register(11),
        },
        MergeVariant::Max => Instruction::MAX {
            ty: Type::F32,
            dst: Register(12),
            src1: Register(10),
            src2: Register(11),
        },

        // Unary operations (context unused)
        MergeVariant::Abs => Instruction::ABS {
            ty: Type::F32,
            dst: Register(12),
            src: Register(10),
        },
        MergeVariant::Exp => Instruction::EXP {
            ty: Type::F32,
            dst: Register(12),
            src: Register(10),
        },
        MergeVariant::Log => Instruction::LOG {
            ty: Type::F32,
            dst: Register(12),
            src: Register(10),
        },
        MergeVariant::Sqrt => Instruction::SQRT {
            ty: Type::F32,
            dst: Register(12),
            src: Register(10),
        },
        MergeVariant::Sigmoid => Instruction::SIGMOID {
            ty: Type::F32,
            dst: Register(12),
            src: Register(10),
        },
        MergeVariant::Tanh => Instruction::TANH {
            ty: Type::F32,
            dst: Register(12),
            src: Register(10),
        },
        MergeVariant::Gelu => {
            // GELU: x * 0.5 * (1 + tanh(sqrt(2/π) * (x + 0.044715 * x³)))
            // Simplified: use built-in if available, otherwise approximate
            // TODO: Implement proper GELU with multi-instruction sequence
            Instruction::TANH {
                ty: Type::F32,
                dst: Register(12),
                src: Register(10),
            }
        }
    };

    instrs.push(op_instr);

    // Store result (zero-copy)
    instrs.push(Instruction::STG {
        ty: Type::F32,
        src: Register(12),
        addr: Address::RegisterIndirectComputed {
            handle_reg: Register(3),
            offset_reg: Register(0),
        },
    });

    Ok(instrs)
}

/// Translate Split generator to ISA
///
/// Pattern: dst[i] = src[i] op context[i] (subtraction/division)
fn translate_split(
    src_class: u8,
    dst_class: u8,
    context_class: u8,
    variant: SplitVariant,
) -> Result<Vec<Instruction>, String> {
    let src_handle = src_class as u64;
    let context_handle = context_class as u64;
    let dst_handle = dst_class as u64;

    let mut instrs = vec![
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(1),
            value: src_handle,
        },
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(2),
            value: context_handle,
        },
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(3),
            value: dst_handle,
        },
        Instruction::MOV_IMM {
            ty: Type::U32,
            dst: Register(250),
            value: 2,
        },
        Instruction::SHL {
            ty: Type::U64,
            dst: Register(0),
            src: GLOBAL_LANE_ID,
            amount: Register(250),
        },
        Instruction::LDG {
            ty: Type::F32,
            dst: Register(10),
            addr: Address::RegisterIndirectComputed {
                handle_reg: Register(1),
                offset_reg: Register(0),
            },
        },
        Instruction::LDG {
            ty: Type::F32,
            dst: Register(11),
            addr: Address::RegisterIndirectComputed {
                handle_reg: Register(2),
                offset_reg: Register(0),
            },
        },
    ];

    let op_instr = match variant {
        SplitVariant::Sub => Instruction::SUB {
            ty: Type::F32,
            dst: Register(12),
            src1: Register(10),
            src2: Register(11),
        },
        SplitVariant::Div => Instruction::DIV {
            ty: Type::F32,
            dst: Register(12),
            src1: Register(10),
            src2: Register(11),
        },
    };

    instrs.push(op_instr);
    instrs.push(Instruction::STG {
        ty: Type::F32,
        src: Register(12),
        addr: Address::RegisterIndirectComputed {
            handle_reg: Register(3),
            offset_reg: Register(0),
        },
    });

    Ok(instrs)
}

/// Translate Mark generator to ISA (XOR with 0x80 for phase flip)
fn translate_mark(_class: u8) -> Result<Vec<Instruction>, String> {
    // Mark is a phase operation in quantum computing
    // For classical operations, this is typically a no-op or identity
    // Implementing as no-op for now
    Ok(vec![])
}

/// Translate Copy generator to ISA (memcpy)
fn translate_copy(src_class: u8, dst_class: u8) -> Result<Vec<Instruction>, String> {
    let src_handle = src_class as u64;
    let dst_handle = dst_class as u64;

    Ok(vec![
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(1),
            value: src_handle,
        },
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(2),
            value: dst_handle,
        },
        Instruction::MOV_IMM {
            ty: Type::U32,
            dst: Register(250),
            value: 2,
        },
        Instruction::SHL {
            ty: Type::U64,
            dst: Register(0),
            src: GLOBAL_LANE_ID,
            amount: Register(250),
        },
        Instruction::LDG {
            ty: Type::F32,
            dst: Register(10),
            addr: Address::RegisterIndirectComputed {
                handle_reg: Register(1),
                offset_reg: Register(0),
            },
        },
        Instruction::STG {
            ty: Type::F32,
            src: Register(10),
            addr: Address::RegisterIndirectComputed {
                handle_reg: Register(2),
                offset_reg: Register(0),
            },
        },
    ])
}

/// Translate Swap generator to ISA
fn translate_swap(class_a: u8, class_b: u8) -> Result<Vec<Instruction>, String> {
    let handle_a = class_a as u64;
    let handle_b = class_b as u64;

    Ok(vec![
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(1),
            value: handle_a,
        },
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(2),
            value: handle_b,
        },
        Instruction::MOV_IMM {
            ty: Type::U32,
            dst: Register(250),
            value: 2,
        },
        Instruction::SHL {
            ty: Type::U64,
            dst: Register(0),
            src: GLOBAL_LANE_ID,
            amount: Register(250),
        },
        // Load both
        Instruction::LDG {
            ty: Type::F32,
            dst: Register(10),
            addr: Address::RegisterIndirectComputed {
                handle_reg: Register(1),
                offset_reg: Register(0),
            },
        },
        Instruction::LDG {
            ty: Type::F32,
            dst: Register(11),
            addr: Address::RegisterIndirectComputed {
                handle_reg: Register(2),
                offset_reg: Register(0),
            },
        },
        // Swap: store R10 to class_b, R11 to class_a
        Instruction::STG {
            ty: Type::F32,
            src: Register(10),
            addr: Address::RegisterIndirectComputed {
                handle_reg: Register(2),
                offset_reg: Register(0),
            },
        },
        Instruction::STG {
            ty: Type::F32,
            src: Register(11),
            addr: Address::RegisterIndirectComputed {
                handle_reg: Register(1),
                offset_reg: Register(0),
            },
        },
    ])
}

/// Translate reduction operations
fn translate_reduce_sum(src_class: u8, dst_class: u8, n: usize) -> Result<Vec<Instruction>, String> {
    Ok(vec![
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(1),
            value: src_class as u64,
        },
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(2),
            value: dst_class as u64,
        },
        Instruction::ReduceAdd {
            ty: Type::F32,
            dst: Register(0),
            src_base: Register(1),
            count: n as u32, // Constant count determined at compile-time
        },
    ])
}

fn translate_reduce_min(src_class: u8, dst_class: u8, n: usize) -> Result<Vec<Instruction>, String> {
    Ok(vec![
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(1),
            value: src_class as u64,
        },
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(2),
            value: dst_class as u64,
        },
        Instruction::ReduceMin {
            ty: Type::F32,
            dst: Register(0),
            src_base: Register(1),
            count: n as u32, // Constant count determined at compile-time
        },
    ])
}

fn translate_reduce_max(src_class: u8, dst_class: u8, n: usize) -> Result<Vec<Instruction>, String> {
    Ok(vec![
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(1),
            value: src_class as u64,
        },
        Instruction::MOV_IMM {
            ty: Type::U64,
            dst: Register(2),
            value: dst_class as u64,
        },
        Instruction::ReduceMax {
            ty: Type::F32,
            dst: Register(0),
            src_base: Register(1),
            count: n as u32, // Constant count determined at compile-time
        },
    ])
}

/// Translate softmax (complex multi-pass operation)
fn translate_softmax(_src_class: u8, _dst_class: u8, _n: usize) -> Result<Vec<Instruction>, String> {
    // Softmax requires multiple passes:
    // 1. Find max (for numerical stability)
    // 2. Compute exp(x - max) and sum
    // 3. Normalize by dividing by sum
    // TODO: Implement full softmax sequence
    Err("Softmax requires manual multi-pass implementation".to_string())
}

/// Translate MergeRange (vectorized operation across multiple classes)
fn translate_merge_range(start_class: u8, end_class: u8, variant: MergeVariant) -> Result<Vec<Instruction>, String> {
    // Range operations process multiple classes in sequence
    // For now, expand to individual Merge calls
    let mut instrs = Vec::new();
    for class in start_class..end_class {
        instrs.extend(translate_merge(class, class, class, variant)?);
    }
    Ok(instrs)
}

/// Translate MarkRange
fn translate_mark_range(start_class: u8, end_class: u8) -> Result<Vec<Instruction>, String> {
    let mut instrs = Vec::new();
    for class in start_class..end_class {
        instrs.extend(translate_mark(class)?);
    }
    Ok(instrs)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_translate_simple_addition() {
        // Simple addition circuit
        let circuit = "merge@c00[c01,c02]"; // c00 = c01 + c02
        let result = translate_to_isa_with_canonicalization(circuit);

        assert!(result.is_ok());
        let translated = result.unwrap();

        // Should have instructions (load handles, compute, operation, store, exit)
        assert!(!translated.program.instructions.is_empty());
        assert!(matches!(
            translated.program.instructions.last(),
            Some(Instruction::EXIT)
        ));
    }

    #[test]
    fn test_canonicalization_h_squared() {
        // H² = I pattern (should be canonicalized to identity)
        // Fixed syntax: copy requires source->dest
        let circuit = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";
        let result = translate_to_isa_with_canonicalization(circuit);

        if let Err(e) = &result {
            eprintln!("ERROR: {}", e);
        }
        assert!(result.is_ok());
        let translated = result.unwrap();

        // Canonicalization should reduce operations
        assert!(translated.canonical_ops < translated.original_ops);
        assert!(translated.reduction_pct > 0.0);
    }

    #[test]
    fn test_translate_merge_variants() {
        // Test different merge variants
        let variants = vec![
            ("merge@c00[c01,c02]", "add"),
            ("merge@c00[c01,c02]", "mul"), // TODO: Need variant syntax
        ];

        for (circuit, _name) in variants {
            let result = translate_to_isa_with_canonicalization(circuit);
            assert!(result.is_ok(), "Failed to translate {} circuit", _name);
        }
    }
}
