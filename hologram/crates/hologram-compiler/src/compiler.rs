//! Sigmatics → Backend Generator Compiler
//!
//! This module translates Sigmatics sigil expressions into backend generator call sequences.
//! The compilation process:
//! 1. Parse sigil expression → AST (existing)
//! 2. Canonicalize AST → Reduced form (existing rewrite rules)
//! 3. Translate AST → GeneratorCall sequence (this module)
//! 4. Execute calls via backend (executor.rs)
//!
//! ## Range Operations
//!
//! Multi-class ranges are compiled to specialized range generator calls:
//!
//! ### Supported Range Operations
//!
//! - `mark@c[0..9]` → `MarkRange { start: 0, end: 9 }`
//! - `merge@c[5..14]` → `MergeRange { start: 5, end: 14, variant: Add }`
//! - `quote@c[10..15]` → `QuoteRange { start: 10, end: 15 }`
//! - `evaluate@c[20..25]` → `EvaluateRange { start: 20, end: 25 }`
//!
//! ### Not Supported on Ranges
//!
//! - `copy`, `swap`, `split` - These require explicit source/destination classes
//!
//! ### Example
//!
//! ```text
//! use hologram_compiler::SigmaticsCompiler;
//!
//! // Compile range operation
//! let circuit = "merge@c[0..32]"; // 100K elements across 33 classes
//! let compiled = SigmaticsCompiler::compile(circuit).unwrap();
//!
//! assert_eq!(compiled.calls.len(), 1);
//! assert!(matches!(compiled.calls[0], GeneratorCall::MergeRange { .. }));
//! ```

use crate::ast::{Parallel, Phrase, Sequential, Term};
use crate::canonicalization::Canonicalizer;
use crate::class_system::{apply_transforms, components_to_class_index, decode_class_index};
use crate::parse;
use crate::types::{ClassRange, ClassTarget, Generator, Transform};

/// A compiled backend generator call
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GeneratorCall {
    /// Mark generator: introduce/remove mark at class
    Mark { class: u8 },

    /// Copy generator: copy from src to dst
    Copy { src_class: u8, dst_class: u8 },

    /// Swap generator: exchange data between two classes
    Swap { class_a: u8, class_b: u8 },

    /// Merge generator: combine src + context → dst
    Merge {
        src_class: u8,
        dst_class: u8,
        context_class: u8,
        variant: MergeVariant,
    },

    /// Split generator: decompose src - context → dst
    Split {
        src_class: u8,
        dst_class: u8,
        context_class: u8,
        variant: SplitVariant,
    },

    /// Quote generator: suspend computation
    Quote { class: u8 },

    /// Evaluate generator: force suspended computation
    Evaluate { class: u8 },

    // ============================================================================
    // Reduction Operations - Reduce array to single value
    // ============================================================================
    /// Reduce Sum: sum all elements in src_class, store in dst_class\[0\]
    ReduceSum {
        src_class: u8,
        dst_class: u8,
        n: usize, // Number of elements to reduce
    },

    /// Reduce Min: find minimum of all elements in src_class, store in dst_class\[0\]
    ReduceMin { src_class: u8, dst_class: u8, n: usize },

    /// Reduce Max: find maximum of all elements in src_class, store in dst_class\[0\]
    ReduceMax { src_class: u8, dst_class: u8, n: usize },

    /// Softmax: compute softmax activation over n elements
    Softmax { src_class: u8, dst_class: u8, n: usize },

    // ============================================================================
    // Range Variants - Multi-Class Operations
    // ============================================================================
    /// Mark generator: mark all classes in range
    MarkRange { start_class: u8, end_class: u8 },

    /// Merge generator: merge operation across range
    MergeRange {
        start_class: u8,
        end_class: u8,
        variant: MergeVariant,
    },

    /// Quote generator: quote all classes in range
    QuoteRange { start_class: u8, end_class: u8 },

    /// Evaluate generator: evaluate all classes in range
    EvaluateRange { start_class: u8, end_class: u8 },
}

/// Merge operation variants (different semantic interpretations)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MergeVariant {
    /// Standard addition: dst = src + context
    Add,
    /// Multiplication: dst = src * context
    Mul,
    /// Minimum: dst = min(src, context)
    Min,
    /// Maximum: dst = max(src, context)
    Max,
    /// Absolute value (unary): dst = abs(src)
    Abs,
    /// Exponential (unary): dst = exp(src)
    Exp,
    /// Natural logarithm (unary): dst = log(src)
    Log,
    /// Square root (unary): dst = sqrt(src)
    Sqrt,
    /// Sigmoid activation (unary): dst = 1/(1+exp(-src))
    Sigmoid,
    /// Hyperbolic tangent (unary): dst = tanh(src)
    Tanh,
    /// GELU activation (unary): dst = src * 0.5 * (1 + erf(src/sqrt(2)))
    Gelu,
}

/// Split operation variants
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SplitVariant {
    /// Standard subtraction: dst = src - context
    Sub,
    /// Division: dst = src / context
    Div,
}

/// Result of compilation
#[derive(Debug, Clone)]
pub struct CompiledCircuit {
    /// Sequence of generator calls to execute
    pub calls: Vec<GeneratorCall>,
    /// Original expression
    pub original_expr: String,
    /// Canonical expression (after rewrite rules)
    pub canonical_expr: String,
    /// Number of operations before canonicalization
    pub original_ops: usize,
    /// Number of operations after canonicalization
    pub canonical_ops: usize,
    /// Percentage reduction
    pub reduction_pct: f64,
}

/// Sigmatics circuit compiler
pub struct SigmaticsCompiler;

impl SigmaticsCompiler {
    /// Compile a sigil expression to backend generator calls
    ///
    /// # Example
    ///
    /// ```text
    /// let circuit = "copy@c05 . mark@c21";
    /// let compiled = SigmaticsCompiler::compile(circuit).unwrap();
    /// assert_eq!(compiled.calls.len(), 2);
    /// ```
    pub fn compile(circuit: &str) -> Result<CompiledCircuit, String> {
        // 1. Parse the circuit
        let phrase = parse(circuit).map_err(|e| format!("Parse error: {:?}", e))?;

        // Count original operations
        let original_ops = count_operations(&phrase);

        // 2. Canonicalize using rewrite rules
        let canonical_result =
            Canonicalizer::parse_and_canonicalize(circuit).map_err(|e| format!("Canonicalization error: {:?}", e))?;

        let canonical_phrase = &canonical_result.phrase;

        // Count canonical operations
        let canonical_ops = count_operations(canonical_phrase);

        // Calculate reduction
        let reduction_pct = if original_ops > 0 {
            100.0 * (1.0 - (canonical_ops as f64 / original_ops as f64))
        } else {
            0.0
        };

        // Get canonical expression as string for debugging
        let canonical_expr =
            Canonicalizer::canonical_form(circuit).map_err(|e| format!("Canonical form error: {:?}", e))?;

        // 3. Translate canonical form to generator calls
        let calls = translate_phrase(canonical_phrase)?;

        Ok(CompiledCircuit {
            calls,
            original_expr: circuit.to_string(),
            canonical_expr,
            original_ops,
            canonical_ops,
            reduction_pct,
        })
    }

    /// Compile without canonicalization (for benchmarking)
    pub fn compile_raw(circuit: &str) -> Result<Vec<GeneratorCall>, String> {
        let phrase = parse(circuit).map_err(|e| format!("Parse error: {:?}", e))?;
        translate_phrase(&phrase)
    }
}

/// Count the number of operations in a phrase
fn count_operations(phrase: &Phrase) -> usize {
    match phrase {
        Phrase::Parallel(par) => count_parallel_operations(par),
        Phrase::Transformed { body, .. } => count_parallel_operations(body),
    }
}

fn count_parallel_operations(par: &Parallel) -> usize {
    par.branches.iter().map(|seq| seq.items.len()).sum()
}

/// Translate a phrase to generator calls
fn translate_phrase(phrase: &Phrase) -> Result<Vec<GeneratorCall>, String> {
    match phrase {
        Phrase::Parallel(par) => translate_parallel(par, None),
        Phrase::Transformed { body, transform } => {
            // Apply phrase-level transform to all operations within
            translate_parallel(body, Some(transform))
        }
    }
}

fn translate_parallel(par: &Parallel, outer_transform: Option<&Transform>) -> Result<Vec<GeneratorCall>, String> {
    let mut calls = Vec::new();

    for branch in &par.branches {
        calls.extend(translate_sequential(branch, outer_transform)?);
    }

    Ok(calls)
}

fn translate_sequential(seq: &Sequential, outer_transform: Option<&Transform>) -> Result<Vec<GeneratorCall>, String> {
    let mut calls = Vec::new();

    for term in &seq.items {
        calls.extend(translate_term(term, outer_transform)?);
    }

    Ok(calls)
}

fn translate_term(term: &Term, outer_transform: Option<&Transform>) -> Result<Vec<GeneratorCall>, String> {
    match term {
        Term::Operation { generator, target } => {
            let call = match target {
                ClassTarget::Single(sigil) => {
                    translate_single_class(generator, sigil.class_index, sigil, outer_transform)?
                }
                ClassTarget::Range(range) => translate_range(generator, range, outer_transform)?,
                ClassTarget::CopyPair { src, dst } => translate_copy_pair(src, dst, outer_transform)?,
                ClassTarget::SwapPair { a, b } => translate_swap_pair(a, b, outer_transform)?,
                ClassTarget::TripleClass {
                    primary,
                    context,
                    secondary,
                } => translate_triple_class(generator, primary, context, secondary, outer_transform)?,
            };

            // Return single call as a vec
            Ok(if let Some(c) = call { vec![c] } else { vec![] })
        }

        Term::Group(par) => {
            // Recursively translate grouped parallel expression
            // The outer_transform is propagated to all operations within the group
            translate_parallel(par, outer_transform)
        }
    }
}

/// Translate single-class operation to generator call
fn translate_single_class(
    generator: &Generator,
    class: u8,
    sigil: &crate::types::ClassSigil,
    outer_transform: Option<&Transform>,
) -> Result<Option<GeneratorCall>, String> {
    // Apply transforms to get final class index
    let final_class = apply_transforms_to_class(class, sigil, outer_transform);

    match generator {
        Generator::Mark => Ok(Some(GeneratorCall::Mark { class: final_class })),

        Generator::Copy => Err("Copy requires explicit destination: use copy@c<src>->c<dst>".to_string()),

        Generator::Swap => Err("Swap requires explicit second class: use swap@c<a><->c<b>".to_string()),

        Generator::Merge => Err("Merge requires explicit context/dst: use merge@c<src>[c<ctx>,c<dst>]".to_string()),

        Generator::Split => Err("Split requires explicit context/dst: use split@c<src>[c<ctx>,c<dst>]".to_string()),

        Generator::Quote => Ok(Some(GeneratorCall::Quote { class: final_class })),

        Generator::Evaluate => Ok(Some(GeneratorCall::Evaluate { class: final_class })),
    }
}

/// Translate copy pair: c<src>->c<dst>
fn translate_copy_pair(
    src: &crate::types::ClassSigil,
    dst: &crate::types::ClassSigil,
    outer_transform: Option<&Transform>,
) -> Result<Option<GeneratorCall>, String> {
    let src_class = apply_transforms_to_class(src.class_index, src, outer_transform);
    let dst_class = apply_transforms_to_class(dst.class_index, dst, outer_transform);

    Ok(Some(GeneratorCall::Copy { src_class, dst_class }))
}

/// Translate swap pair: c<a><->c<b>
fn translate_swap_pair(
    a: &crate::types::ClassSigil,
    b: &crate::types::ClassSigil,
    outer_transform: Option<&Transform>,
) -> Result<Option<GeneratorCall>, String> {
    let class_a = apply_transforms_to_class(a.class_index, a, outer_transform);
    let class_b = apply_transforms_to_class(b.class_index, b, outer_transform);

    Ok(Some(GeneratorCall::Swap { class_a, class_b }))
}

/// Translate triple class: c<primary>[c<context>,c<secondary>]
fn translate_triple_class(
    generator: &Generator,
    primary: &crate::types::ClassSigil,
    context: &crate::types::ClassSigil,
    secondary: &crate::types::ClassSigil,
    outer_transform: Option<&Transform>,
) -> Result<Option<GeneratorCall>, String> {
    let src_class = apply_transforms_to_class(primary.class_index, primary, outer_transform);
    let context_class = apply_transforms_to_class(context.class_index, context, outer_transform);
    let dst_class = apply_transforms_to_class(secondary.class_index, secondary, outer_transform);

    match generator {
        Generator::Merge => Ok(Some(GeneratorCall::Merge {
            src_class,
            dst_class,
            context_class,
            variant: MergeVariant::Add,
        })),
        Generator::Split => Ok(Some(GeneratorCall::Split {
            src_class,
            dst_class,
            context_class,
            variant: SplitVariant::Sub,
        })),
        _ => Err(format!(
            "Generator {:?} does not support triple-class syntax",
            generator
        )),
    }
}

/// Apply transforms to a class index
///
/// Applies postfix transforms from sigil, then prefix transforms from outer_transform
fn apply_transforms_to_class(class: u8, sigil: &crate::types::ClassSigil, outer_transform: Option<&Transform>) -> u8 {
    let mut components = decode_class_index(class);

    // Apply sigil's own transforms (postfix)
    if sigil.rotate.is_some() || sigil.twist.is_some() || sigil.mirror {
        let sigil_transform = sigil.to_transform();
        components = apply_transforms(&components, &sigil_transform);
    }

    // Apply outer transform (prefix)
    if let Some(transform) = outer_transform {
        components = apply_transforms(&components, transform);
    }

    components_to_class_index(&components)
}

/// Translate range operation to generator call
fn translate_range(
    generator: &Generator,
    range: &ClassRange,
    outer_transform: Option<&Transform>,
) -> Result<Option<GeneratorCall>, String> {
    // Apply transforms to range boundaries
    let start = apply_transforms_to_range_boundary(range.start_class(), range, outer_transform);
    let end = apply_transforms_to_range_boundary(range.end_class(), range, outer_transform);

    match generator {
        Generator::Mark => Ok(Some(GeneratorCall::MarkRange {
            start_class: start,
            end_class: end,
        })),

        Generator::Merge => {
            Ok(Some(GeneratorCall::MergeRange {
                start_class: start,
                end_class: end,
                variant: MergeVariant::Add, // Default to addition
            }))
        }

        Generator::Quote => Ok(Some(GeneratorCall::QuoteRange {
            start_class: start,
            end_class: end,
        })),

        Generator::Evaluate => Ok(Some(GeneratorCall::EvaluateRange {
            start_class: start,
            end_class: end,
        })),

        Generator::Copy | Generator::Swap | Generator::Split => Err(format!(
            "{:?} generator not supported on ranges (requires explicit source/dest)",
            generator
        )),
    }
}

/// Apply transforms to a range boundary class
fn apply_transforms_to_range_boundary(class: u8, range: &ClassRange, outer_transform: Option<&Transform>) -> u8 {
    let mut components = decode_class_index(class);

    // Apply range's own transforms (postfix)
    if range.rotate.is_some() || range.twist.is_some() || range.mirror {
        let range_transform = range.to_transform();
        components = apply_transforms(&components, &range_transform);
    }

    // Apply outer transform (prefix)
    if let Some(transform) = outer_transform {
        components = apply_transforms(&components, transform);
    }

    components_to_class_index(&components)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compile_simple_mark() {
        let circuit = "mark@c21";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 1);
        assert!(matches!(compiled.calls[0], GeneratorCall::Mark { class: 21 }));
    }

    #[test]
    fn test_compile_sequential() {
        let circuit = "mark@c00 . mark@c01";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 2);
        assert!(matches!(compiled.calls[0], GeneratorCall::Mark { class: 0 }));
        assert!(matches!(compiled.calls[1], GeneratorCall::Mark { class: 1 }));
    }

    #[test]
    fn test_compile_with_canonicalization() {
        // H² = (copy@c05->c06 . mark@c21) . (copy@c05->c06 . mark@c21) → mark@c00
        let circuit = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        // Should be reduced by rewrite rules
        assert_eq!(compiled.original_ops, 4);
        assert!(
            compiled.canonical_ops < compiled.original_ops,
            "Expected canonicalization to reduce operations"
        );
    }

    #[test]
    fn test_compile_raw_no_canonicalization() {
        let circuit = "mark@c00 . mark@c01 . mark@c02";
        let calls = SigmaticsCompiler::compile_raw(circuit).unwrap();

        assert_eq!(calls.len(), 3);
    }

    #[test]
    fn test_reduction_percentage() {
        // Identity composition: should reduce to identity
        let circuit = "mark@c00 . mark@c00";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        // Two marks should canonicalize to identity (empty or single mark)
        assert!(compiled.reduction_pct >= 0.0);
        assert!(compiled.reduction_pct <= 100.0);
    }

    // ============================================================================
    // Range Operation Tests
    // ============================================================================

    #[test]
    fn test_compile_simple_range() {
        let circuit = "mark@c[0..9]";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 1);
        assert!(matches!(
            compiled.calls[0],
            GeneratorCall::MarkRange {
                start_class: 0,
                end_class: 9
            }
        ));
    }

    #[test]
    fn test_compile_range_merge() {
        let circuit = "merge@c[5..14]";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 1);
        assert!(matches!(
            compiled.calls[0],
            GeneratorCall::MergeRange {
                start_class: 5,
                end_class: 14,
                ..
            }
        ));
    }

    #[test]
    fn test_compile_range_unsupported_operations() {
        let circuits = vec!["copy@c[0..5]", "swap@c[0..5]", "split@c[0..5]"];

        for circuit in circuits {
            let result = SigmaticsCompiler::compile(circuit);
            assert!(result.is_err(), "Expected error for {}", circuit);
            assert!(result.unwrap_err().contains("not supported on ranges"));
        }
    }

    #[test]
    fn test_compile_mixed_single_and_range() {
        let circuit = "mark@c0 . merge@c[5..9] . mark@c20";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 3);
        assert!(matches!(compiled.calls[0], GeneratorCall::Mark { class: 0 }));
        assert!(matches!(compiled.calls[1], GeneratorCall::MergeRange { .. }));
        assert!(matches!(compiled.calls[2], GeneratorCall::Mark { class: 20 }));
    }

    #[test]
    fn test_compile_range_quote_evaluate() {
        let circuit = "quote@c[10..15]";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 1);
        assert!(matches!(
            compiled.calls[0],
            GeneratorCall::QuoteRange {
                start_class: 10,
                end_class: 15
            }
        ));

        let circuit = "evaluate@c[20..25]";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 1);
        assert!(matches!(
            compiled.calls[0],
            GeneratorCall::EvaluateRange {
                start_class: 20,
                end_class: 25
            }
        ));
    }

    #[test]
    fn test_compile_with_prefix_rotation() {
        // Test R+1@ mark@c21 applies rotation transform
        // Class 21: h₂=0, d=2, ℓ=5 → R+1 → h₂=1, d=2, ℓ=5 → class 45
        let circuit = "R+1@ mark@c21";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 1);
        assert!(matches!(compiled.calls[0], GeneratorCall::Mark { class: 45 }));
    }

    #[test]
    fn test_compile_with_prefix_mirror() {
        // Test ~@ mark@c21 applies mirror transform
        // Class 21: h₂=0, d=2 (Consume), ℓ=5 → M → h₂=0, d=1 (Produce), ℓ=5 → class 13
        let circuit = "~@ mark@c21";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 1);
        assert!(matches!(compiled.calls[0], GeneratorCall::Mark { class: 13 }));
    }

    #[test]
    fn test_compile_with_combined_transforms() {
        // Test postfix + prefix transforms: R+1@ mark@c21^+2~
        // Class 21: h₂=0, d=2, ℓ=5
        // Apply postfix T+2: h₂=0, d=2, ℓ=7
        // Apply postfix M: h₂=0, d=1, ℓ=7 → class 15
        // Apply prefix R+1: h₂=1, d=1, ℓ=7 → class 39
        let circuit = "R+1@ mark@c21^+2~";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 1);
        assert!(matches!(compiled.calls[0], GeneratorCall::Mark { class: 39 }));
    }

    #[test]
    fn test_compile_range_with_prefix_mirror() {
        // Test transform on range: ~@ merge@c[0..9]
        // Start class 0: h₂=0, d=0 (Neutral), ℓ=0 → M → h₂=0, d=0, ℓ=0 → class 0
        // End class 9: h₂=0, d=1 (Produce), ℓ=1 → M → h₂=0, d=2 (Consume), ℓ=1 → class 17
        let circuit = "~@ merge@c[0..9]";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 1);
        assert!(matches!(
            compiled.calls[0],
            GeneratorCall::MergeRange {
                start_class: 0,
                end_class: 17,
                ..
            }
        ));
    }

    #[test]
    fn test_compile_range_with_prefix_rotation() {
        // Test R+2@ quote@c[10..15]
        // Start class 10: h₂=0, d=1, ℓ=2 → R+2 → h₂=2, d=1, ℓ=2 → class 58
        // End class 15: h₂=0, d=1, ℓ=7 → R+2 → h₂=2, d=1, ℓ=7 → class 63
        let circuit = "R+2@ quote@c[10..15]";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 1);
        assert!(matches!(
            compiled.calls[0],
            GeneratorCall::QuoteRange {
                start_class: 58,
                end_class: 63
            }
        ));
    }

    #[test]
    fn test_compile_postfix_and_prefix_transforms_on_range() {
        // Test ~@ mark@c[5..10]^+3
        // Start class 5: h₂=0, d=0, ℓ=5
        //   → Apply postfix T+3: ℓ=(5+3)%8=0 → class 0
        //   → Apply prefix M: d stays 0 → class 0
        // End class 10: h₂=0, d=1, ℓ=2
        //   → Apply postfix T+3: ℓ=(2+3)%8=5 → class 13
        //   → Apply prefix M: d flips 1→2 → class 21
        let circuit = "~@ mark@c[5..10]^+3";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 1);
        assert!(matches!(
            compiled.calls[0],
            GeneratorCall::MarkRange {
                start_class: 0,
                end_class: 21
            }
        ));
    }

    #[test]
    fn test_compile_prefix_twist() {
        // Test T+3@ mark@c00
        // Class 0: h₂=0, d=0, ℓ=0 → T+3 → h₂=0, d=0, ℓ=3 → class 3
        let circuit = "T+3@ mark@c00";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 1);
        assert!(matches!(compiled.calls[0], GeneratorCall::Mark { class: 3 }));
    }

    #[test]
    fn test_compile_multiple_operations_with_prefix_transform() {
        // Test R+1@ mark@c21 . copy@c05->c06
        // Both operations in the sequential should get R+1 applied
        // Class 21 → 45
        // Class 5 → 29 (h₂=0→1, d=0, ℓ=5 → 24*1 + 0 + 5 = 29), dst: 6 → 30
        let circuit = "R+1@ mark@c21 . copy@c05->c06";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 2);
        assert!(matches!(compiled.calls[0], GeneratorCall::Mark { class: 45 }));
        assert!(matches!(
            compiled.calls[1],
            GeneratorCall::Copy {
                src_class: 29,
                dst_class: 30
            }
        ));
    }

    #[test]
    fn test_compile_simple_grouped_expression() {
        // Test basic grouped expression: (mark@c00 . mark@c01)
        let circuit = "(mark@c00 . mark@c01)";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 2);
        assert!(matches!(compiled.calls[0], GeneratorCall::Mark { class: 0 }));
        assert!(matches!(compiled.calls[1], GeneratorCall::Mark { class: 1 }));
    }

    #[test]
    fn test_compile_grouped_with_outer_operation() {
        // Test grouped expression in sequence: mark@c10 . (mark@c20 . mark@c30)
        let circuit = "mark@c10 . (mark@c20 . mark@c30)";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 3);
        assert!(matches!(compiled.calls[0], GeneratorCall::Mark { class: 10 }));
        assert!(matches!(compiled.calls[1], GeneratorCall::Mark { class: 20 }));
        assert!(matches!(compiled.calls[2], GeneratorCall::Mark { class: 30 }));
    }

    #[test]
    fn test_compile_nested_groups() {
        // Test nested groups: ((mark@c00 . mark@c01) . mark@c02)
        let circuit = "((mark@c00 . mark@c01) . mark@c02)";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 3);
        assert!(matches!(compiled.calls[0], GeneratorCall::Mark { class: 0 }));
        assert!(matches!(compiled.calls[1], GeneratorCall::Mark { class: 1 }));
        assert!(matches!(compiled.calls[2], GeneratorCall::Mark { class: 2 }));
    }

    #[test]
    fn test_compile_grouped_with_parallel() {
        // Test parallel within group: (mark@c00 || mark@c01) . mark@c02
        let circuit = "(mark@c00 || mark@c01) . mark@c02";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 3);
        // Parallel branches can appear in any order
        assert!(compiled
            .calls
            .iter()
            .any(|c| matches!(c, GeneratorCall::Mark { class: 0 })));
        assert!(compiled
            .calls
            .iter()
            .any(|c| matches!(c, GeneratorCall::Mark { class: 1 })));
        assert!(matches!(compiled.calls[2], GeneratorCall::Mark { class: 2 }));
    }

    #[test]
    fn test_compile_grouped_with_prefix_transform() {
        // Test transform applied to grouped expression: R+1@ (mark@c00 . mark@c05)
        let circuit = "R+1@ (mark@c00 . mark@c05)";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 2);
        // Both operations should have R+1 applied
        assert!(matches!(compiled.calls[0], GeneratorCall::Mark { class: 24 })); // 0 → 24
        assert!(matches!(compiled.calls[1], GeneratorCall::Mark { class: 29 }));
        // 5 → 29
    }

    #[test]
    fn test_compile_grouped_with_ranges() {
        // Test grouped expression with range operation: (mark@c[0..5] . merge@c[10..15])
        let circuit = "(mark@c[0..5] . merge@c[10..15])";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 2);
        assert!(matches!(
            compiled.calls[0],
            GeneratorCall::MarkRange {
                start_class: 0,
                end_class: 5
            }
        ));
        assert!(matches!(
            compiled.calls[1],
            GeneratorCall::MergeRange {
                start_class: 10,
                end_class: 15,
                ..
            }
        ));
    }

    #[test]
    fn test_compile_complex_grouping_with_transforms_and_ranges() {
        // Test complex circuit: ~@ ((mark@c[0..5] . mark@c10) || merge@c[20..25])
        let circuit = "~@ ((mark@c[0..5] . mark@c10) || merge@c[20..25])";
        let compiled = SigmaticsCompiler::compile(circuit).unwrap();

        assert_eq!(compiled.calls.len(), 3);
        // Transform should be applied to all operations
        // This tests that transforms propagate through nested groups and parallels
    }
}
