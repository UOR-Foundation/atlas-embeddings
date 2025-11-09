//! Inline kernel code generation for embedding kernels directly in the binary
//!
//! This module generates Rust functions that are compiled directly into the binary,
//! eliminating FFI overhead and dynamic library loading for stdlib operations.

use crate::json_schema::{FunctionDef, JsonSchema, ScalarType, Type};

/// Generate an inline kernel function that can be compiled directly into the binary
///
/// Example output:
/// ```rust
/// pub fn vector_add(a: *const f32, b: *const f32, c: *mut f32, n: usize) {
///     unsafe {
///         for idx in 0..n {
///             *c.add(idx) = *a.add(idx) + *b.add(idx);
///         }
///     }
/// }
/// ```
pub fn generate_inline_kernel(schema: &JsonSchema) -> String {
    let mut code = String::new();

    // Function signature
    code.push_str(&format!("pub fn {}(\n", schema.kernel.name));

    // Parameters (convert from JSON to Rust types)
    for (i, param) in schema.kernel.params.iter().enumerate() {
        let rust_type = match param.param_type {
            Type::DevicePtr => "*const f32".to_string(),
            Type::DeviceArray { .. } => "*const f32".to_string(),
            Type::Scalar { scalar_type } => match scalar_type {
                ScalarType::F32 => "f32".to_string(),
                ScalarType::U32 | ScalarType::I32 => "usize".to_string(),
                _ => "usize".to_string(),
            },
        };

        code.push_str(&format!("    {}: {}", param.name, rust_type));
        if i < schema.kernel.params.len() - 1 {
            code.push(',');
        }
        code.push('\n');
    }
    code.push_str(") {\n");

    // Function body - sequential execution (rayon not safe with raw pointers)
    code.push_str("    unsafe {\n");

    // Find size parameter
    let size_param = schema
        .kernel
        .params
        .iter()
        .find(|p| matches!(&p.param_type, Type::Scalar { .. }))
        .map(|p| p.name.as_str())
        .unwrap_or("n");

    code.push_str(&format!("        for idx in 0..{} {{\n", size_param));

    // Generate computation based on kernel name
    let computation = generate_computation(&schema.kernel);
    code.push_str(&computation);

    code.push_str("        }\n");
    code.push_str("    }\n");
    code.push_str("}\n");

    code
}

fn generate_computation(kernel: &FunctionDef) -> String {
    // Find output parameter (usually 'c' or starts with 'out')
    let output_param = kernel
        .params
        .iter()
        .find(|p| p.name.starts_with('c') || p.name.contains("out"))
        .map(|p| p.name.as_str())
        .unwrap_or("out");

    // Find input parameters
    let inputs: Vec<&str> = kernel
        .params
        .iter()
        .filter(|p| p.name != output_param)
        .map(|p| p.name.as_str())
        .collect();

    let computation = match kernel.name.as_str() {
        name if name.contains("add") => {
            if inputs.len() >= 2 {
                format!(
                    "            *{}.add(idx) = *{}.add(idx) + *{}.add(idx);",
                    output_param, inputs[0], inputs[1]
                )
            } else {
                format!("            *{}.add(idx) = *{}.add(idx);", output_param, inputs[0])
            }
        }
        name if name.contains("mul") => {
            format!(
                "            *{}.add(idx) = *{}.add(idx) * *{}.add(idx);",
                output_param, inputs[0], inputs[1]
            )
        }
        name if name.contains("sub") => {
            format!(
                "            *{}.add(idx) = *{}.add(idx) - *{}.add(idx);",
                output_param, inputs[0], inputs[1]
            )
        }
        name if name.contains("sigmoid") => {
            format!(
                "            *{}.add(idx) = 1.0 / (1.0 + (-*{}.add(idx)).exp());",
                output_param, inputs[0]
            )
        }
        name if name.contains("relu") => {
            format!(
                "            *{}.add(idx) = {{ let v = *{}.add(idx); if v > 0.0 {{ v }} else {{ 0.0 }} }};",
                output_param, inputs[0]
            )
        }
        name if name.contains("exp") => {
            format!(
                "            *{}.add(idx) = (*{}.add(idx)).exp();",
                output_param, inputs[0]
            )
        }
        name if name.contains("log") => {
            format!(
                "            *{}.add(idx) = (*{}.add(idx)).ln();",
                output_param, inputs[0]
            )
        }
        name if name.contains("sin") => {
            format!(
                "            *{}.add(idx) = (*{}.add(idx)).sin();",
                output_param, inputs[0]
            )
        }
        name if name.contains("cos") => {
            format!(
                "            *{}.add(idx) = (*{}.add(idx)).cos();",
                output_param, inputs[0]
            )
        }
        _ => {
            format!("            *{}.add(idx) = *{}.add(idx);", output_param, inputs[0])
        }
    };

    format!("        {}\n", computation)
}

/// Generate module with all inline kernels
pub fn generate_kernels_module(schemas: &[JsonSchema]) -> String {
    let mut code = String::new();

    code.push_str("//! Auto-generated inline kernels module\n");
    code.push_str("//! \n");
    code.push_str("//! This file is generated at compile time and contains all stdlib kernel functions\n");
    code.push_str("//! compiled directly into the binary for zero-overhead execution.\n\n");

    // Note: Using sequential loops instead of rayon for raw pointer safety

    for schema in schemas {
        code.push_str(&generate_inline_kernel(schema));
        code.push('\n');
    }

    code
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::json_schema::ScalarType;
    use crate::{FunctionDef, JsonSchema, ParamDef, Type};

    #[test]
    fn test_generate_vector_add() {
        let schema = JsonSchema {
            version: "1.0".to_string(),
            kernel: FunctionDef {
                name: "vector_add".to_string(),
                params: vec![
                    ParamDef {
                        name: "a".to_string(),
                        param_type: Type::DevicePtr,
                    },
                    ParamDef {
                        name: "b".to_string(),
                        param_type: Type::DevicePtr,
                    },
                    ParamDef {
                        name: "c".to_string(),
                        param_type: Type::DevicePtr,
                    },
                    ParamDef {
                        name: "n".to_string(),
                        param_type: Type::Scalar {
                            scalar_type: ScalarType::U32,
                        },
                    },
                ],
                body: vec![],
            },
        };

        let code = generate_inline_kernel(&schema);
        assert!(code.contains("pub fn vector_add"));
        assert!(code.contains("*c.add(idx) = *a.add(idx) + *b.add(idx)"));
    }
}
