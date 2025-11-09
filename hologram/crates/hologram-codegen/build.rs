use serde::{Deserialize, Serialize};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

// Simple JSON schema types for build-time codegen
#[derive(Debug, Clone, Serialize, Deserialize)]
struct JsonSchema {
    version: String,
    kernel: FunctionDef,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct FunctionDef {
    name: String,
    params: Vec<ParamDef>,
    body: Vec<serde_json::Value>, // We don't need to fully parse body for simple compilation
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ParamDef {
    name: String,
    #[serde(rename = "type")]
    param_type: ParamType,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
enum ParamType {
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

/// Compile all Python kernel schemas to JSON
///
/// Finds all .py files in schemas/stdlib/ (recursively) and compiles them to JSON
/// using atlas_compile.py. Outputs to target/json/<kernel_name>.json.
fn compile_python_schemas_to_json(schemas_dir: &Path, json_output_dir: &Path) {
    use std::process::Command;

    if !schemas_dir.exists() {
        println!(
            "cargo:warning=Python schemas directory not found: {}",
            schemas_dir.display()
        );
        return;
    }

    // Find atlas_compile.py
    let compiler_script = schemas_dir.join("atlas_compile.py");
    if !compiler_script.exists() {
        println!(
            "cargo:warning=atlas_compile.py not found at {}",
            compiler_script.display()
        );
        return;
    }

    // Find all Python kernel files (excluding compiler infrastructure)
    let kernel_files = find_kernel_files(schemas_dir);

    if kernel_files.is_empty() {
        println!(
            "cargo:warning=No Python kernel files found in {}",
            schemas_dir.display()
        );
        return;
    }

    let mut compiled_count = 0;
    let mut failed_count = 0;

    for python_file in kernel_files {
        // Extract kernel name from file path
        let kernel_name = python_file.file_stem().and_then(|s| s.to_str()).unwrap_or("unknown");

        let json_output = json_output_dir.join(format!("{}.json", kernel_name));

        // Run Python compiler: python3 atlas_compile.py <input.py> -o <output.json>
        let output = Command::new("python3")
            .arg(&compiler_script)
            .arg(&python_file)
            .arg("-o")
            .arg(&json_output)
            .output();

        match output {
            Ok(result) if result.status.success() => {
                compiled_count += 1;
                // println!(
                //     "cargo:warning=✅ Compiled Python kernel: {} → {}",
                //     kernel_name,
                //     json_output.display()
                // );
            }
            Ok(result) => {
                failed_count += 1;
                let stderr = String::from_utf8_lossy(&result.stderr);
                println!("cargo:warning=❌ Failed to compile {}: {}", kernel_name, stderr);
            }
            Err(e) => {
                failed_count += 1;
                println!(
                    "cargo:warning=❌ Failed to run atlas_compile.py for {}: {}",
                    kernel_name, e
                );
            }
        }
    }

    println!(
        "cargo:warning=Python → JSON compilation: {} succeeded, {} failed",
        compiled_count, failed_count
    );
}

/// Find all kernel .py files (excluding infrastructure files)
fn find_kernel_files(base_dir: &Path) -> Vec<PathBuf> {
    let mut kernel_files = Vec::new();

    // Directories to search
    let search_dirs = vec![
        base_dir.join("vector"),
        base_dir.join("matrix"),
        base_dir.join("quantum"),
    ];

    for dir in search_dirs {
        if !dir.exists() {
            continue;
        }

        if let Ok(entries) = fs::read_dir(&dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().and_then(|s| s.to_str()) == Some("py") {
                    // Skip __init__.py and other infrastructure files
                    if let Some(name) = path.file_stem().and_then(|s| s.to_str()) {
                        if !name.starts_with("_") && name != "init" {
                            kernel_files.push(path);
                        }
                    }
                }
            }
        }
    }

    kernel_files
}

fn main() {
    println!("cargo:rerun-if-changed=../../schemas/stdlib/");
    println!("cargo:rerun-if-changed=../../target/json/");

    let python_schemas_dir = PathBuf::from("../../schemas/stdlib");
    let json_dir = PathBuf::from("../../target/json");
    let inline_out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    // Create directories
    fs::create_dir_all(&inline_out_dir).ok();
    fs::create_dir_all(&json_dir).ok();

    // ============================================================================
    // PHASE 1.1: Compile Python schemas to JSON
    // ============================================================================

    compile_python_schemas_to_json(&python_schemas_dir, &json_dir);

    // ============================================================================
    // PHASE 1.2: Generate inline kernels module
    // ============================================================================
    // Note: Inline kernels are for backward compatibility during ISA migration.
    // The new architecture uses compile-time precompiled ISA Programs (see hologram-core/build.rs).

    if !json_dir.exists() {
        return;
    }

    let mut all_schemas = Vec::new();

    // Collect all JSON schemas
    if let Ok(entries) = fs::read_dir(&json_dir) {
        for entry in entries.flatten() {
            let json_path = entry.path();
            if json_path.extension().map(|e| e == "json").unwrap_or(false) {
                if let Ok(json_content) = fs::read_to_string(&json_path) {
                    if let Ok(schema) = serde_json::from_str::<JsonSchema>(&json_content) {
                        all_schemas.push(schema);
                    }
                }
            }
        }
    }

    // Generate inline kernels module
    if !all_schemas.is_empty() {
        generate_inline_kernels_module(&all_schemas, &inline_out_dir);
    }
}

fn generate_inline_kernels_module(schemas: &[JsonSchema], output_dir: &Path) {
    let mut code = String::new();
    code.push_str("//! Auto-generated inline kernels module\n");
    code.push_str("//! \n");
    code.push_str("//! This file is generated at compile time and contains all stdlib kernel functions\n");
    code.push_str("//! compiled directly into the binary for zero-overhead execution.\n\n");

    code.push_str("use rayon::prelude::*;\n\n");

    for schema in schemas {
        code.push_str(&generate_inline_kernel_from_schema(schema));
        code.push('\n');
    }

    // Write to output directory
    let output_path = output_dir.join("inline_kernels.rs");
    if let Err(e) = fs::write(&output_path, &code) {
        println!("cargo:warning=Failed to write inline kernels: {}", e);
    } else {
        println!(
            "cargo:warning=✅ Generated inline kernels module: {}",
            output_path.display()
        );
    }
}

fn generate_inline_kernel_from_schema(schema: &JsonSchema) -> String {
    let mut code = String::new();
    let kernel_name = &schema.kernel.name;

    // Function signature with #[inline(always)]
    code.push_str("#[inline(always)]\n");
    code.push_str(&format!("pub fn {}(\n", kernel_name));

    // Determine parameter types and names
    let mut params = Vec::new();
    for (i, param) in schema.kernel.params.iter().enumerate() {
        let rust_type = match &param.param_type {
            ParamType::DevicePtr => {
                if param.name.starts_with('c') || param.name == "out" {
                    "*mut f32".to_string()
                } else {
                    "*const f32".to_string()
                }
            }
            ParamType::DeviceArray { .. } => {
                if param.name.starts_with('c') || param.name == "out" {
                    "*mut f32".to_string()
                } else {
                    "*const f32".to_string()
                }
            }
            ParamType::Scalar { scalar_type } => match scalar_type.as_str() {
                "f32" => "f32".to_string(),
                "u32" | "i32" => "usize".to_string(),
                _ => "usize".to_string(),
            },
        };

        code.push_str(&format!("    {}: {}", param.name, rust_type));
        if i < schema.kernel.params.len() - 1 {
            code.push(',');
        }
        code.push('\n');
        params.push((param.name.clone(), rust_type));
    }
    code.push_str(") {\n");

    // Find parameters and categorize them
    let size_param = schema
        .kernel
        .params
        .iter()
        .find(|p| p.name == "n" || matches!(p.param_type, ParamType::Scalar { .. }))
        .map(|p| p.name.as_str())
        .unwrap_or("n");

    let output_params: Vec<&str> = params
        .iter()
        .filter(|(_name, t)| t.starts_with("*mut"))
        .map(|(name, _)| name.as_str())
        .collect();

    let input_params: Vec<&str> = params
        .iter()
        .filter(|(_name, t)| t.starts_with("*const"))
        .map(|(name, _)| name.as_str())
        .collect();

    // Generate function body based on kernel type
    code.push_str("    unsafe {\n");

    if kernel_name == "softmax" {
        // First pass: find max for numerical stability
        if output_params.is_empty() || input_params.is_empty() {
            code.push_str("        // Invalid parameters for softmax\n");
        } else {
            let input = input_params[0];
            let output = output_params[0];
            code.push_str(&format!(
                "        let max_val = (0..{}).map(|idx| *{}.add(idx)).fold(f32::NEG_INFINITY, f32::max);\n\n",
                size_param, input
            ));
            code.push_str("        // Second pass: compute exp(x[i] - max_val) and sum\n");
            code.push_str(&format!(
                "        let sum_exp: f32 = (0..{}).map(|idx| {{\n",
                size_param
            ));
            code.push_str(&format!(
                "            let exp_val = (*{}.add(idx) - max_val).exp();\n",
                input
            ));
            code.push_str(&format!("            *{}.add(idx) = exp_val;\n", output));
            code.push_str("            exp_val\n");
            code.push_str("        }).sum();\n\n");
            code.push_str("        // Third pass: normalize\n");
            code.push_str("        let inv_sum = 1.0 / sum_exp;\n");
            code.push_str(&format!("        for idx in 0..{} {{\n", size_param));
            code.push_str(&format!("            *{}.add(idx) *= inv_sum;\n", output));
            code.push_str("        }\n");
        }
    } else {
        // Sequential loops for simple kernels
        code.push_str(&format!("        for idx in 0..{} {{\n", size_param));

        // Generate computation based on kernel type
        if kernel_name == "sigmoid" {
            if !output_params.is_empty() && !input_params.is_empty() {
                code.push_str(&format!(
                    "            *{}.add(idx) = 1.0 / (1.0 + (-*{}.add(idx)).exp());\n",
                    output_params[0], input_params[0]
                ));
            }
        } else if kernel_name == "tanh" {
            if !output_params.is_empty() && !input_params.is_empty() {
                code.push_str(&format!(
                    "            *{}.add(idx) = (*{}.add(idx)).tanh();\n",
                    output_params[0], input_params[0]
                ));
            }
        } else if kernel_name == "gelu" {
            if !output_params.is_empty() && !input_params.is_empty() {
                code.push_str(&format!("            let x = *{}.add(idx);\n", input_params[0]));
                code.push_str(&format!(
                    "            *{}.add(idx) = 0.5 * x * (1.0 + (x * 0.7071067811865476).tanh());\n",
                    output_params[0]
                ));
            }
        } else if kernel_name.contains("add") {
            if !output_params.is_empty() && input_params.len() >= 2 {
                code.push_str(&format!(
                    "            *{}.add(idx) = *{}.add(idx) + *{}.add(idx);\n",
                    output_params[0], input_params[0], input_params[1]
                ));
            }
        } else if kernel_name.contains("sub") {
            if !output_params.is_empty() && input_params.len() >= 2 {
                code.push_str(&format!(
                    "            *{}.add(idx) = *{}.add(idx) - *{}.add(idx);\n",
                    output_params[0], input_params[0], input_params[1]
                ));
            }
        } else if kernel_name.contains("mul") {
            if !output_params.is_empty() && input_params.len() >= 2 {
                code.push_str(&format!(
                    "            *{}.add(idx) = *{}.add(idx) * *{}.add(idx);\n",
                    output_params[0], input_params[0], input_params[1]
                ));
            }
        } else if kernel_name == "relu" {
            if !output_params.is_empty() && !input_params.is_empty() {
                code.push_str(&format!("            let val = *{}.add(idx);\n", input_params[0]));
                code.push_str(&format!(
                    "            *{}.add(idx) = if val > 0.0 {{ val }} else {{ 0.0 }};\n",
                    output_params[0]
                ));
            }
        } else if !output_params.is_empty() && !input_params.is_empty() {
            code.push_str(&format!(
                "            *{}.add(idx) = *{}.add(idx);\n",
                output_params[0], input_params[0]
            ));
        }
        code.push_str("        }\n");
    }

    code.push_str("    }\n");
    code.push_str("}\n");

    code
}
