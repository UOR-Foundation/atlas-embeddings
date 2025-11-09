//! JSON Schema Intermediate Representation
//!
//! This module defines the JSON schema format that serves as the intermediate
//! representation between frontend languages (Python/TypeScript) and Rust codegen.

use crate::error::{CodegenError, Result};
use serde::{Deserialize, Serialize};

/// Top-level JSON schema for an Atlas kernel
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JsonSchema {
    /// Schema format version
    pub version: String,
    /// Kernel function definition
    pub kernel: FunctionDef,
}

/// Function definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionDef {
    /// Function name
    pub name: String,
    /// Function parameters
    pub params: Vec<ParamDef>,
    /// Function body (list of statements)
    pub body: Vec<Statement>,
}

/// Parameter definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParamDef {
    /// Parameter name
    pub name: String,
    /// Parameter type
    #[serde(rename = "type")]
    pub param_type: Type,
}

/// Type system
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Type {
    /// Scalar types
    Scalar {
        #[serde(rename = "type")]
        scalar_type: ScalarType,
    },
    /// Device pointer (opaque)
    DevicePtr,
    /// Device array with element type
    DeviceArray { element_type: Box<Type> },
}

/// Scalar type variants
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ScalarType {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    Bool,
}

/// Statement types
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Statement {
    /// Variable declaration with initialization
    Let { name: String, value: Expression },
    /// Assignment to existing variable or array element
    Assign { target: Expression, value: Expression },
    /// If statement
    If {
        condition: Expression,
        then_body: Vec<Statement>,
        else_body: Option<Vec<Statement>>,
    },
    /// For loop (range-based)
    For {
        var: String,
        start: Expression,
        stop: Expression,
        step: Expression,
        body: Vec<Statement>,
    },
    /// While loop
    While {
        condition: Expression,
        body: Vec<Statement>,
    },
    /// Return statement
    Return { value: Option<Expression> },
}

/// Expression types
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Expression {
    /// Variable reference
    Var { name: String },
    /// Literal value
    Literal { value: LiteralValue },
    /// Binary operation
    BinaryOp {
        op: BinaryOperator,
        left: Box<Expression>,
        right: Box<Expression>,
    },
    /// Array indexing
    Index {
        array: Box<Expression>,
        index: Box<Expression>,
    },
    /// Function call
    Call { function: String, args: Vec<Expression> },
}

/// Literal values
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum LiteralValue {
    Int(i64),
    Float(f64),
    Bool(bool),
}

/// Binary operators
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    FloorDiv,
    Mod,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    And,
    Or,
}

/// Parse JSON schema from string
pub fn parse(json: &str) -> Result<JsonSchema> {
    let schema: JsonSchema = serde_json::from_str(json)?;
    validate(&schema)?;
    Ok(schema)
}

/// Validate schema
fn validate(schema: &JsonSchema) -> Result<()> {
    if schema.version != "1.0" {
        return Err(CodegenError::InvalidSchema(format!(
            "Unsupported schema version: {}",
            schema.version
        )));
    }

    if schema.kernel.name.is_empty() {
        return Err(CodegenError::InvalidSchema("Kernel name cannot be empty".to_string()));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_minimal_schema() {
        let json = r#"{
            "version": "1.0",
            "kernel": {
                "name": "test_kernel",
                "params": [],
                "body": []
            }
        }"#;

        let schema = parse(json).unwrap();
        assert_eq!(schema.version, "1.0");
        assert_eq!(schema.kernel.name, "test_kernel");
    }

    #[test]
    fn test_parse_vector_add_schema() {
        let json = r#"{
            "version": "1.0",
            "kernel": {
                "name": "vector_add",
                "params": [
                    {
                        "name": "a",
                        "type": {
                            "kind": "device_array",
                            "element_type": {
                                "kind": "scalar",
                                "type": "f32"
                            }
                        }
                    },
                    {
                        "name": "b",
                        "type": {
                            "kind": "device_array",
                            "element_type": {
                                "kind": "scalar",
                                "type": "f32"
                            }
                        }
                    },
                    {
                        "name": "c",
                        "type": {
                            "kind": "device_array",
                            "element_type": {
                                "kind": "scalar",
                                "type": "f32"
                            }
                        }
                    },
                    {
                        "name": "n",
                        "type": {
                            "kind": "scalar",
                            "type": "u32"
                        }
                    }
                ],
                "body": [
                    {
                        "type": "let",
                        "name": "idx",
                        "value": {
                            "type": "call",
                            "function": "get_global_id",
                            "args": []
                        }
                    },
                    {
                        "type": "if",
                        "condition": {
                            "type": "binary_op",
                            "op": "lt",
                            "left": {
                                "type": "var",
                                "name": "idx"
                            },
                            "right": {
                                "type": "var",
                                "name": "n"
                            }
                        },
                        "then_body": [
                            {
                                "type": "assign",
                                "target": {
                                    "type": "index",
                                    "array": {
                                        "type": "var",
                                        "name": "c"
                                    },
                                    "index": {
                                        "type": "var",
                                        "name": "idx"
                                    }
                                },
                                "value": {
                                    "type": "binary_op",
                                    "op": "add",
                                    "left": {
                                        "type": "index",
                                        "array": {
                                            "type": "var",
                                            "name": "a"
                                        },
                                        "index": {
                                            "type": "var",
                                            "name": "idx"
                                        }
                                    },
                                    "right": {
                                        "type": "index",
                                        "array": {
                                            "type": "var",
                                            "name": "b"
                                        },
                                        "index": {
                                            "type": "var",
                                            "name": "idx"
                                        }
                                    }
                                }
                            }
                        ],
                        "else_body": null
                    }
                ]
            }
        }"#;

        let schema = parse(json).unwrap();
        assert_eq!(schema.kernel.name, "vector_add");
        assert_eq!(schema.kernel.params.len(), 4);
        assert_eq!(schema.kernel.body.len(), 2);
    }

    #[test]
    fn test_invalid_version() {
        let json = r#"{
            "version": "2.0",
            "kernel": {
                "name": "test",
                "params": [],
                "body": []
            }
        }"#;

        assert!(parse(json).is_err());
    }
}
