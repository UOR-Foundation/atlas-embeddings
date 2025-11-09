//! Dynamic Library Code Generation
//!
//! Generates Rust code that compiles to a dynamic library (.so/.dylib/.dll)
//! with C-compatible ABI for runtime loading.

use crate::error::{CodegenError, Result};
use crate::json_schema::*;

use std::collections::HashSet;

pub struct DylibCodegen;

impl DylibCodegen {
    pub fn new() -> Self {
        Self
    }

    /// Analyze statements to find all variables that are reassigned (need `mut`)
    fn find_mutable_vars(&self, statements: &[Statement]) -> HashSet<String> {
        let mut mutable_vars = HashSet::new();
        Self::collect_mutable_vars(statements, &mut mutable_vars);
        mutable_vars
    }

    /// Recursively collect variables that get reassigned
    fn collect_mutable_vars(statements: &[Statement], mutable_vars: &mut HashSet<String>) {
        for stmt in statements {
            match stmt {
                Statement::Assign {
                    target: Expression::Var { name },
                    ..
                } => {
                    mutable_vars.insert(name.clone());
                }
                Statement::If {
                    then_body, else_body, ..
                } => {
                    Self::collect_mutable_vars(then_body, mutable_vars);
                    if let Some(else_body) = else_body {
                        Self::collect_mutable_vars(else_body, mutable_vars);
                    }
                }
                Statement::For { body, .. } | Statement::While { body, .. } => {
                    Self::collect_mutable_vars(body, mutable_vars);
                }
                _ => {}
            }
        }
    }

    /// Generate Rust code for dynamic library with C ABI exports
    pub fn generate(&self, schema: &JsonSchema) -> Result<String> {
        let mut code = String::new();

        // Generate imports - use shared runtime library with macros
        code.push_str("#[macro_use]\nextern crate hologram_kernel_runtime;\n\n");
        code.push_str("use std::os::raw::c_char;\n");
        code.push_str("use rayon::prelude::*;\n");
        code.push_str("use hologram_kernel_runtime::*;\n\n");

        // No need to generate CLaunchConfig, ErrorCode, ABI_VERSION, or Unmarshaller
        // - they're all provided by hologram_kernel_runtime

        let kernel_name = &schema.kernel.name;

        // Generate kernel execution function (internal)
        code.push_str(&self.generate_kernel_impl(schema)?);
        code.push_str("\n\n");

        // Generate C ABI exports using macros from shared library
        code.push_str("define_kernel_abi_version!();\n");
        code.push_str(&format!("define_kernel_name!(\"{}\");\n", kernel_name));
        code.push_str("define_kernel_execute!();\n");

        Ok(code)
    }

    fn generate_kernel_impl(&self, schema: &JsonSchema) -> Result<String> {
        let mut code = String::new();

        code.push_str("/// Internal kernel execution (safe Rust)\n");
        code.push_str("fn kernel_execute_internal(params: &[u8]) -> anyhow::Result<()> {\n");

        // Generate parameter unpacking
        code.push_str("    let mut u = Unmarshaller::new(params);\n");

        for param in &schema.kernel.params {
            let unpack_call = self.generate_unpack(&param.param_type)?;
            code.push_str(&format!("    let {} = {};\n", param.name, unpack_call));
        }

        code.push('\n');

        // Analyze which variables need to be mutable
        let mutable_vars = self.find_mutable_vars(&schema.kernel.body);

        // Check if kernel uses get_global_id pattern (parallel execution)
        if self.uses_global_id(&schema.kernel.body) {
            // Generate parallel execution using rayon
            code.push_str("    // Parallel execution\n");
            code.push_str("    unsafe {\n");

            // Find the size parameter (usually 'n')
            let size_param = self.find_size_parameter(schema)?;

            code.push_str(&format!(
                "        (0..{} as usize).into_par_iter().for_each(|idx| {{\n",
                &size_param
            ));

            // Generate kernel body without the idx declaration and outer if
            for stmt in &schema.kernel.body {
                match stmt {
                    Statement::Let {
                        name,
                        value: Expression::Call { function, .. },
                    } if name == "idx" && function == "get_global_id" => continue,
                    Statement::If {
                        condition, then_body, ..
                    } if self.is_bounds_check(condition, &size_param) => {
                        // Generate the inner body directly without the if
                        for inner_stmt in then_body {
                            let stmt_code = Self::generate_statement(inner_stmt, 3, &mutable_vars)?;
                            code.push_str(&stmt_code);
                        }
                        continue;
                    }
                    _ => {}
                }
                let stmt_code = Self::generate_statement(stmt, 3, &mutable_vars)?;
                code.push_str(&stmt_code);
            }

            code.push_str("        });\n");
            code.push_str("    }\n");
        } else {
            // Generate sequential execution
            code.push_str("    // Kernel body\n");
            code.push_str("    unsafe {\n");

            for stmt in &schema.kernel.body {
                let stmt_code = Self::generate_statement(stmt, 2, &mutable_vars)?;
                code.push_str(&stmt_code);
            }

            code.push_str("    }\n");
        }

        code.push('\n');
        code.push_str("    Ok(())\n");
        code.push_str("}\n");

        Ok(code)
    }

    fn uses_global_id(&self, body: &[Statement]) -> bool {
        body.iter().any(|stmt| {
            matches!(
                stmt,
                Statement::Let {
                    value: Expression::Call { function, .. },
                    ..
                } if function == "get_global_id"
            )
        })
    }

    fn find_size_parameter(&self, schema: &JsonSchema) -> Result<String> {
        // Look for a scalar parameter (usually 'n')
        for param in &schema.kernel.params {
            if let Type::Scalar { .. } = param.param_type {
                return Ok(param.name.clone());
            }
        }
        Err(CodegenError::CodegenFailed(
            "Could not find size parameter for parallel execution".to_string(),
        ))
    }

    fn is_bounds_check(&self, condition: &Expression, size_param: &String) -> bool {
        if let Expression::BinaryOp { op, left, right } = condition {
            if matches!(op, BinaryOperator::Lt) {
                if let Expression::Var { name: left_name } = &**left {
                    if let Expression::Var { name: right_name } = &**right {
                        return left_name == "idx" && right_name == size_param;
                    }
                }
            }
        }
        false
    }

    fn generate_unpack(&self, ty: &Type) -> Result<String> {
        match ty {
            Type::Scalar { scalar_type } => {
                let method = match scalar_type {
                    ScalarType::U8 => "try_unpack_u8()? as usize",
                    ScalarType::U16 => "try_unpack_u16()? as usize",
                    ScalarType::U32 => "try_unpack_u32()? as usize",
                    ScalarType::U64 => "try_unpack_u64()? as usize",
                    ScalarType::I8 => "try_unpack_i8()? as usize",
                    ScalarType::I16 => "try_unpack_i16()? as usize",
                    ScalarType::I32 => "try_unpack_i32()? as usize",
                    ScalarType::I64 => "try_unpack_i64()? as usize",
                    ScalarType::F32 => "try_unpack_f32()?",
                    ScalarType::F64 => "try_unpack_f64()?",
                    ScalarType::Bool => "try_unpack_u8()? != 0",
                };
                Ok(format!("u.{}", method))
            }
            Type::DevicePtr => Ok("u.try_unpack_device_ptr()?".to_string()),
            Type::DeviceArray { .. } => Ok("u.try_unpack_device_ptr()?".to_string()),
        }
    }

    fn generate_statement(stmt: &Statement, indent: usize, mutable_vars: &HashSet<String>) -> Result<String> {
        let indent_str = "    ".repeat(indent);

        match stmt {
            Statement::Let { name, value } => {
                let value_code = Self::generate_expression(value)?;
                let mut_keyword = if mutable_vars.contains(name) { "mut " } else { "" };
                Ok(format!("{}let {}{} = {};\n", indent_str, mut_keyword, name, value_code))
            }
            Statement::Assign { target, value } => {
                let target_code = Self::generate_expression_mut(target)?;
                let value_code = Self::generate_expression(value)?;
                Ok(format!("{}{} = {};\n", indent_str, target_code, value_code))
            }
            Statement::If {
                condition,
                then_body,
                else_body,
            } => {
                let mut code = String::new();
                let condition_code = Self::generate_expression(condition)?;

                code.push_str(&format!("{}if {} {{\n", indent_str, condition_code));

                for stmt in then_body {
                    code.push_str(&Self::generate_statement(stmt, indent + 1, mutable_vars)?);
                }

                code.push_str(&format!("{}}}", indent_str));

                if let Some(else_stmts) = else_body {
                    code.push_str(" else {\n");
                    for stmt in else_stmts {
                        code.push_str(&Self::generate_statement(stmt, indent + 1, mutable_vars)?);
                    }
                    code.push_str(&format!("{}}}", indent_str));
                }

                code.push('\n');
                Ok(code)
            }
            Statement::For {
                var,
                start,
                stop,
                step,
                body,
            } => {
                let mut code = String::new();
                let start_code = Self::generate_expression(start)?;
                let stop_code = Self::generate_expression(stop)?;
                let step_code = Self::generate_expression(step)?;

                code.push_str(&format!(
                    "{}for {} in ({}).step_by({}) {{\n",
                    indent_str, var, start_code, step_code
                ));

                // Handle range properly based on step
                let range_code = if step_code == "1" {
                    format!("{}..{}", start_code, stop_code)
                } else {
                    format!("({}..{}).step_by({} as usize)", start_code, stop_code, step_code)
                };

                code = format!("{}for {} in {} {{\n", indent_str, var, range_code);

                for stmt in body {
                    code.push_str(&Self::generate_statement(stmt, indent + 1, mutable_vars)?);
                }

                code.push_str(&format!("{}}}\n", indent_str));
                Ok(code)
            }
            Statement::While { condition, body } => {
                let mut code = String::new();
                let condition_code = Self::generate_expression(condition)?;

                code.push_str(&format!("{}while {} {{\n", indent_str, condition_code));

                for stmt in body {
                    code.push_str(&Self::generate_statement(stmt, indent + 1, mutable_vars)?);
                }

                code.push_str(&format!("{}}}\n", indent_str));
                Ok(code)
            }
            Statement::Return { value } => {
                if let Some(expr) = value {
                    let expr_code = Self::generate_expression(expr)?;
                    Ok(format!("{}return {};\n", indent_str, expr_code))
                } else {
                    Ok(format!("{}return;\n", indent_str))
                }
            }
        }
    }

    fn generate_expression(expr: &Expression) -> Result<String> {
        match expr {
            Expression::Var { name } => Ok(name.clone()),
            Expression::Literal { value } => match value {
                LiteralValue::Int(i) => Ok(format!("{}usize", i)),
                LiteralValue::Float(f) => {
                    // Ensure float literals have explicit type
                    if f.fract() == 0.0 && *f >= 0.0 {
                        Ok(format!("{}.0f32", f))
                    } else {
                        Ok(format!("{}f32", f))
                    }
                }
                LiteralValue::Bool(b) => Ok(b.to_string()),
            },
            Expression::BinaryOp { op, left, right } => {
                let left_code = Self::generate_expression(left)?;
                let right_code = Self::generate_expression(right)?;
                let op_str = match op {
                    BinaryOperator::Add => "+",
                    BinaryOperator::Sub => "-",
                    BinaryOperator::Mul => "*",
                    BinaryOperator::Div => "/",
                    BinaryOperator::FloorDiv => "/", // Integer division in Rust
                    BinaryOperator::Mod => "%",
                    BinaryOperator::Lt => "<",
                    BinaryOperator::Le => "<=",
                    BinaryOperator::Gt => ">",
                    BinaryOperator::Ge => ">=",
                    BinaryOperator::Eq => "==",
                    BinaryOperator::Ne => "!=",
                    BinaryOperator::And => "&&",
                    BinaryOperator::Or => "||",
                };
                Ok(format!("{} {} {}", left_code, op_str, right_code))
            }
            Expression::Index { array, index } => {
                let array_code = Self::generate_expression(array)?;
                let index_code = Self::generate_expression(index)?;
                // array_code is already a u64 pointer variable (read-only)
                Ok(format!("*({} as *const f32).add({} as usize)", array_code, index_code))
            }
            Expression::Call { function, args: _ } => match function.as_str() {
                "get_global_id" => Ok("0".to_string()),
                _ => Err(CodegenError::UnsupportedOperation(format!(
                    "Unknown function: {}",
                    function
                ))),
            },
        }
    }

    /// Generate expression as mutable (for assignment targets)
    fn generate_expression_mut(expr: &Expression) -> Result<String> {
        match expr {
            Expression::Index { array, index } => {
                let array_code = Self::generate_expression(array)?;
                let index_code = Self::generate_expression(index)?;
                // array_code is already a u64 pointer variable (writable)
                Ok(format!("*({} as *mut f32).add({} as usize)", array_code, index_code))
            }
            _ => Self::generate_expression(expr),
        }
    }
}

impl Default for DylibCodegen {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_dylib_exports() {
        let schema = JsonSchema {
            version: "1.0".to_string(),
            kernel: FunctionDef {
                name: "test_kernel".to_string(),
                params: vec![],
                body: vec![],
            },
        };

        let codegen = DylibCodegen::new();
        let code = codegen.generate(&schema).unwrap();

        // Check for C ABI exports (now using macros from shared library)
        // The macros expand into the actual functions at compile time
        assert!(code.contains("define_kernel_execute!"));
        assert!(code.contains("define_kernel_name!"));
        assert!(code.contains("define_kernel_abi_version!"));
        assert!(code.contains("hologram_kernel_runtime"));
        assert!(code.contains("kernel_execute_internal"));
    }
}
