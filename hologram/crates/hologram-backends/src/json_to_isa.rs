//! Direct JSON → ISA translation for kernel operations
//!
//! This module translates kernel JSON schemas directly to ISA Programs.
//! This is used for operations that are already in optimal form and don't
//! benefit from hologram-compiler canonicalization.
//!
//! For operations that can benefit from canonicalization (quantum circuits,
//! complex gate patterns), use the sigmatics_to_isa module instead.

use crate::isa::{Instruction, Program, Register, Type};
use crate::program_builder::{create_element_wise_binary, create_element_wise_unary};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// JSON schema structure (matching hologram-codegen build.rs)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JsonSchema {
    pub version: String,
    pub kernel: KernelDef,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KernelDef {
    pub name: String,
    pub params: Vec<ParamDef>,
    pub body: Vec<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParamDef {
    pub name: String,
    #[serde(rename = "type")]
    pub param_type: ParamType,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum ParamType {
    #[serde(rename = "scalar")]
    Scalar {
        #[serde(rename = "type")]
        scalar_type: String,
    },
    #[serde(rename = "device_ptr")]
    DevicePtr,
    #[serde(rename = "device_array")]
    DeviceArray { element_type: Box<ParamType> },
}

/// Operation classification for translation strategy
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperationType {
    /// Binary element-wise: c[i] = a[i] op b[i]
    BinaryElementwise,
    /// Unary element-wise: c[i] = op(a[i])
    UnaryElementwise,
    /// Reduction: result = reduce(array, op)
    Reduction,
    /// Matrix operation (GEMM, GEMV)
    MatrixOp,
    /// Complex / custom operation
    Complex,
}

/// Translate JSON schema to ISA Program
///
/// This bypasses hologram-compiler for simple operations that are already optimal.
/// For operations that can benefit from canonicalization, use hologram-compiler pipeline.
pub fn translate_json_to_isa(json: &JsonSchema) -> Result<Program, String> {
    let op_type = classify_operation(&json.kernel)?;

    match op_type {
        OperationType::BinaryElementwise => translate_binary_elementwise(json),
        OperationType::UnaryElementwise => translate_unary_elementwise(json),
        OperationType::Reduction => translate_reduction(json),
        OperationType::MatrixOp => translate_matrix_op(json),
        OperationType::Complex => Err(format!(
            "Complex operation {} requires manual ISA translation",
            json.kernel.name
        )),
    }
}

/// Classify operation type from JSON kernel definition
fn classify_operation(kernel: &KernelDef) -> Result<OperationType, String> {
    let name = kernel.name.to_lowercase();

    // Check operation name patterns
    if name.contains("add") || name.contains("sub") || name.contains("mul") || name.contains("div") {
        return Ok(OperationType::BinaryElementwise);
    }

    if name.contains("relu")
        || name.contains("sigmoid")
        || name.contains("tanh")
        || name.contains("exp")
        || name.contains("log")
        || name.contains("sin")
        || name.contains("cos")
        || name.contains("abs")
        || name.contains("neg")
    {
        return Ok(OperationType::UnaryElementwise);
    }

    if name.contains("sum") || name.contains("max") || name.contains("min") || name.contains("dot") {
        return Ok(OperationType::Reduction);
    }

    if name.contains("gemm") || name.contains("gemv") || name.contains("matmul") {
        return Ok(OperationType::MatrixOp);
    }

    Ok(OperationType::Complex)
}

/// Translate binary element-wise operation to ISA
fn translate_binary_elementwise(json: &JsonSchema) -> Result<Program, String> {
    let name = json.kernel.name.to_lowercase();

    // Determine operation instruction
    let op_fn: Box<dyn Fn(Register, Register, Register) -> Instruction> = if name.contains("add") {
        Box::new(|src1, src2, dst| Instruction::ADD {
            ty: Type::F32,
            dst,
            src1,
            src2,
        })
    } else if name.contains("sub") {
        Box::new(|src1, src2, dst| Instruction::SUB {
            ty: Type::F32,
            dst,
            src1,
            src2,
        })
    } else if name.contains("mul") {
        Box::new(|src1, src2, dst| Instruction::MUL {
            ty: Type::F32,
            dst,
            src1,
            src2,
        })
    } else if name.contains("div") {
        Box::new(|src1, src2, dst| Instruction::DIV {
            ty: Type::F32,
            dst,
            src1,
            src2,
        })
    } else {
        return Err(format!("Unknown binary operation: {}", name));
    };

    // Use program builder with placeholder handles (will be replaced at runtime)
    // For compile-time precompilation, we generate a program template
    Ok(create_element_wise_binary(0, 0, 0, Type::F32, op_fn))
}

/// Translate unary element-wise operation to ISA
fn translate_unary_elementwise(json: &JsonSchema) -> Result<Program, String> {
    let name = json.kernel.name.to_lowercase();

    // Determine operation instruction
    let op_fn: Box<dyn Fn(Register, Register) -> Instruction> = if name.contains("relu") {
        // RELU: max(0, x) - requires comparison and selection
        Box::new(|src, dst| {
            // For now, use ABS as placeholder - TODO: implement proper RELU
            Instruction::ABS {
                ty: Type::F32,
                dst,
                src,
            }
        })
    } else if name.contains("sigmoid") {
        Box::new(|src, dst| Instruction::SIGMOID {
            ty: Type::F32,
            dst,
            src,
        })
    } else if name.contains("tanh") {
        Box::new(|src, dst| Instruction::TANH {
            ty: Type::F32,
            dst,
            src,
        })
    } else if name.contains("exp") {
        Box::new(|src, dst| Instruction::EXP {
            ty: Type::F32,
            dst,
            src,
        })
    } else if name.contains("log") {
        Box::new(|src, dst| Instruction::LOG {
            ty: Type::F32,
            dst,
            src,
        })
    } else if name.contains("sin") {
        Box::new(|src, dst| Instruction::SIN {
            ty: Type::F32,
            dst,
            src,
        })
    } else if name.contains("cos") {
        Box::new(|src, dst| Instruction::COS {
            ty: Type::F32,
            dst,
            src,
        })
    } else if name.contains("abs") {
        Box::new(|src, dst| Instruction::ABS {
            ty: Type::F32,
            dst,
            src,
        })
    } else if name.contains("neg") {
        Box::new(|src, dst| Instruction::NEG {
            ty: Type::F32,
            dst,
            src,
        })
    } else {
        return Err(format!("Unknown unary operation: {}", name));
    };

    // Use program builder with placeholder handles
    Ok(create_element_wise_unary(0, 0, Type::F32, op_fn))
}

/// Translate reduction operation to ISA
fn translate_reduction(json: &JsonSchema) -> Result<Program, String> {
    let name = json.kernel.name.to_lowercase();

    // Create reduction program
    // Note: count is a placeholder (0) - will be set at runtime based on array size
    let instruction = if name.contains("sum") || name.contains("add") || name.contains("dot") {
        Instruction::ReduceAdd {
            ty: Type::F32,
            dst: Register(0),
            src_base: Register(1),
            count: 0, // Placeholder - actual count determined at runtime
        }
    } else if name.contains("min") {
        Instruction::ReduceMin {
            ty: Type::F32,
            dst: Register(0),
            src_base: Register(1),
            count: 0, // Placeholder - actual count determined at runtime
        }
    } else if name.contains("max") {
        Instruction::ReduceMax {
            ty: Type::F32,
            dst: Register(0),
            src_base: Register(1),
            count: 0, // Placeholder - actual count determined at runtime
        }
    } else {
        return Err(format!("Unknown reduction operation: {}", name));
    };

    Ok(Program {
        instructions: vec![instruction, Instruction::EXIT],
        labels: HashMap::new(),
    })
}

/// Translate matrix operation to ISA (complex - requires custom implementation)
fn translate_matrix_op(json: &JsonSchema) -> Result<Program, String> {
    // Matrix operations are complex and require manual implementation
    // This is a placeholder that will be filled in with proper GEMM/GEMV implementations
    Err(format!(
        "Matrix operation {} requires manual implementation",
        json.kernel.name
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_classify_operations() {
        let mut kernel = KernelDef {
            name: "vector_add".to_string(),
            params: vec![],
            body: vec![],
        };

        assert_eq!(classify_operation(&kernel).unwrap(), OperationType::BinaryElementwise);

        kernel.name = "sigmoid".to_string();
        assert_eq!(classify_operation(&kernel).unwrap(), OperationType::UnaryElementwise);

        kernel.name = "sum".to_string();
        assert_eq!(classify_operation(&kernel).unwrap(), OperationType::Reduction);

        kernel.name = "gemm".to_string();
        assert_eq!(classify_operation(&kernel).unwrap(), OperationType::MatrixOp);
    }

    #[test]
    fn test_translate_vector_add() {
        let json = JsonSchema {
            version: "1.0".to_string(),
            kernel: KernelDef {
                name: "vector_add".to_string(),
                params: vec![],
                body: vec![],
            },
        };

        let program = translate_json_to_isa(&json).unwrap();
        assert!(!program.instructions.is_empty());
        assert!(matches!(program.instructions.last(), Some(Instruction::EXIT)));
    }
}
