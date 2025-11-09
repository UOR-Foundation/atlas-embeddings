# Kernel Schemas: Python → JSON → Rust → .so

This directory contains kernel definitions written in Python that compile to native Rust code and load as dynamic libraries.

## Architecture

```
Python Source (.py)
    ↓ (compile_to_json)
Python AST → JSON Schema (.json)
    ↓ (codegen.rs)
Rust Code (.rs)
    ↓ (cargo build)
Dynamic Library (.so/.dylib/.dll)
    ↓ (register_all_kernels_from_directory)
Runtime Execution (dlopen)
```

**Key principles:**

- Python used ONLY at build time (no Python interpreter at runtime)
- All kernels compile to native code (Rust/Assembly)
- Dynamic loading from directory (no hard-coded kernel names)
- Common primitives library (`atlas_kernel.py`) - no repetition

## Quick Start

### 1. Write Kernel in Python

Create `schemas/stdlib/vector/my_kernel.py`:

```python
"""My Kernel - Brief description"""

from atlas_kernel import DeviceArray, f32, u32, get_global_id

def my_kernel(a: DeviceArray[f32], b: DeviceArray[f32], c: DeviceArray[f32], n: u32):
    """Description of kernel"""
    idx = get_global_id()
    if idx < n:
        c[idx] = a[idx] + b[idx]
```

### 2. Compile Python → JSON

**Using CLI tool (RECOMMENDED):**

```bash
cd schemas/stdlib

# Compile a single kernel file:
python3 atlas_compile.py vector/add.py -o ../../target/json/add.json -v

# Compile all vector kernels:
for py_file in vector/*.py; do
    kernel_name=$(basename "$py_file" .py)
    python3 atlas_compile.py "$py_file" -o "../../target/json/${kernel_name}.json" -v
done

# Compile all matrix kernels:
for py_file in matrix/*.py; do
    kernel_name=$(basename "$py_file" .py)
    python3 atlas_compile.py "$py_file" -o "../../target/json/${kernel_name}.json" -v
done

# Verify JSON files were created:
ls -lh ../../target/json/
```

The CLI tool is **fully functional and tested** ✅

**Or programmatically:**

```python
from compiler import compile_to_json

json_schema = compile_to_json(my_kernel, output_path="my_kernel.json")
```

### 3. Build (JSON → Rust → .so)

**Status: Build system integration in progress**

Currently, you need to:

1. Compile Python → JSON (CLI working ✅)
2. Manually generate Rust from JSON (codegen.rs ready ⚠️ needs wiring)
3. Build to .so (not yet automated)

```bash
# Once build system is complete, this will work:
cargo build --package hologram-kernels

# Steps it will perform:
# 1. Run Python schemas → generate JSON
# 2. Read JSON files → generate Rust via codegen.rs
# 3. Compile Rust → .so libraries in kernels/
```

**To complete:** Need to wire up `crates/hologram-kernels/build.rs` to call codegen.rs

### 4. Runtime Loading

```rust
use hologram_kernels::register_all_kernels_from_directory;

// Automatically loads all kernels from directory
let loaded = register_all_kernels_from_directory("./kernels/")?;
// ✅ Loaded kernel: my_kernel from kernels/my_kernel.so

// Use by name
let handle = get_kernel("my_kernel")?;
execute_kernel(handle, &args)?;
```

## Directory Structure

```
schemas/
├── README.md              # This file (complete guide)
├── atlas_kernel.py        # Common primitives (all kernels import from here)
├── compiler.py            # Python→JSON compiler
├── examples/              # Example compilations
│   └── compile_kernel_example.py
└── vector/                # Kernel schemas
    ├── add.py
    ├── sub.py
    ├── mul.py
    ├── dot.py
    └── relu.py
```

## Kernel Primitives (atlas_kernel.py)

All kernels import from the common library - **no repetition needed:**

```python
from atlas_kernel import (
    DeviceArray,    # Type annotation for device arrays
    f32, f64,       # Floating point types
    i8, i16, i32, i64,   # Signed integers
    u8, u16, u32, u64,   # Unsigned integers
    get_global_id,  # Get thread ID (replaced during compilation)
    atomic_add_f32, # Atomic operations for reductions
)

# Example usage
def my_kernel(a: DeviceArray[f32], n: u32):
    idx = get_global_id()  # No need to define this!
    if idx < n:
        a[idx] = a[idx] * 2.0
```

**Available functions:**

- `get_global_id() -> int` - Thread ID for parallel execution
- `atomic_add_f32(addr, value)` - Atomic addition for reductions
- `atomic_add_u32(addr, value)` - Atomic add for unsigned
- `atomic_add_i32(addr, value)` - Atomic add for signed

**Types:**

- `DeviceArray[T]` - Array in device memory (element type T)
- `f32, f64` - Floating point
- `i8, i16, i32, i64` - Signed integers
- `u8, u16, u32, u64` - Unsigned integers
- `bool` - Boolean

## Supported Features

### ✅ Currently Supported

**Control Flow:**

- If statements: `if idx < n: ...`
- Variables: `idx = get_global_id()`

**Operations:**

- Array indexing: `a[idx]`
- Binary operations: `+`, `-`, `*`, `/`, `%`
- Comparisons: `<`, `<=`, `>`, `>=`, `==`, `!=`
- Function calls: `get_global_id()`, `atomic_add_f32()`

**Types:**

- Scalar: `f32`, `u32`, `i32`, etc.
- Arrays: `DeviceArray[f32]`, `DeviceArray[i32]`, etc.

### 🚧 Planned Support

- For loops
- Nested function calls
- Math functions (sin, cos, exp, log, etc.)
- Complex reductions (tree reductions)

## Pipeline Details

### Step 1: Python → JSON

**compiler.py** parses Python AST and generates JSON schema:

```python
from compiler import compile_to_json

def my_kernel(a: DeviceArray[f32], b: DeviceArray[f32], n: u32):
    idx = get_global_id()
    if idx < n:
        a[idx] = a[idx] + b[idx]

json_schema = compile_to_json(my_kernel)
```

**Output JSON:**

```json
{
  "version": "1.0",
  "kernel": {
    "name": "my_kernel",
    "params": [
      {"name": "a", "type": {"kind": "device_array", "element_type": {...}}},
      {"name": "b", "type": {"kind": "device_array", "element_type": {...}}},
      {"name": "n", "type": {"kind": "scalar", "type": "u32"}}
    ],
    "body": [
      {"type": "let", "name": "idx", "value": {...}},
      {"type": "if", "condition": {...}, "then_body": [...]}
    ]
  }
}
```

### Step 2: JSON → Rust

**codegen.rs** converts JSON to Rust code:

```rust
use hologram_kernels::codegen;

let schema = serde_json::from_str(&json)?;
let rust_code = codegen::json_to_rust(&schema);
```

**Generated Rust:**

```rust
#[no_mangle]
pub extern "C" fn my_kernel(
    a: *mut f32,
    b: *mut f32,
    n: usize
) {
    unsafe {
        // Generated code...
    }
}
```

### Step 3: Rust → .so

Standard cargo build compiles Rust to shared library:

```bash
cargo build --package hologram-kernels
# Output: kernels/my_kernel.so
```

### Step 4: Dynamic Loading

**Automatic directory scanning:**

```rust
use hologram_kernels::register_all_kernels_from_directory;

// Scans ./kernels/ for all .so/.dylib/.dll files
let loaded = register_all_kernels_from_directory("./kernels/")?;
// ✅ Loaded kernel: vector_add from kernels/vector_add.so
// ✅ Loaded kernel: vector_sub from kernels/vector_sub.so
// ✅ Loaded kernel: my_kernel from kernels/my_kernel.so
```

**No hard-coding needed!** Just drop `.so` files in the directory and they're loaded automatically.

## Example Kernels

See `schemas/stdlib/vector/` for examples:

### add.py - Vector Addition

```python
from atlas_kernel import DeviceArray, f32, u32, get_global_id

def vector_add(a: DeviceArray[f32], b: DeviceArray[f32], c: DeviceArray[f32], n: u32):
    """Add two vectors element-wise: c = a + b"""
    idx = get_global_id()
    if idx < n:
        c[idx] = a[idx] + b[idx]
```

### dot.py - Dot Product (Reduction)

```python
from atlas_kernel import DeviceArray, f32, u32, get_global_id, atomic_add_f32

def vector_dot(a: DeviceArray[f32], b: DeviceArray[f32], result: DeviceArray[f32], n: u32):
    """Compute dot product: result = Σ(a[i] * b[i])"""
    idx = get_global_id()
    if idx < n:
        product = a[idx] * b[idx]
        atomic_add_f32(result, product)
```

## File Structure

```
schemas/
├── README.md              # This file (complete guide)
├── SETUP.md               # Python development setup
├── IMPLEMENTATION.md      # Status tracking
├── requirements.txt       # Python dependencies (empty)
├── .gitignore            # Python artifacts
└── stdlib/
    ├── atlas_kernel.py   # Common primitives library
    ├── compiler.py       # Python→JSON compiler
    ├── atlas_compile.py  # CLI tool
    ├── examples/         # Compilation examples
    ├── vector/           # Vector kernels
    │   ├── add.py
    │   ├── sub.py
    │   ├── mul.py
    │   ├── dot.py
    │   └── relu.py
    └── matrix/           # Matrix kernels
        ├── gemm.py       # General matrix multiply
        └── gemv.py       # Matrix-vector multiply
```

## Development Setup

### Python Virtual Environment (Optional)

```bash
cd schemas
python3 -m venv .venv
source .venv/bin/activate  # Linux/Mac
# or
.venv\Scripts\activate     # Windows

# Install dependencies (none currently needed)
pip install -r requirements.txt
```

**Note:** Python is ONLY used for development. The actual build happens via `cargo build` which runs automatically.

### VSCode Integration

VSCode is configured in `.vscode/settings.json` to:

- Detect `.venv` in `schemas/.venv`
- Use Python for syntax highlighting
- Provide code completion for kernel primitives

## Workflow Summary

**Write → Compile → Build → Run**

1. **Write**: Create Python kernel with `DeviceArray` types
2. **Compile**: Run compiler to generate JSON schema
3. **Build**: `cargo build` generates Rust and compiles to .so
4. **Run**: Runtime automatically loads all .so files from directory

**Benefits:**

- ✅ Python for easy kernel development
- ✅ JSON intermediate (language-agnostic, debuggable)
- ✅ Rust for optimization and SIMD
- ✅ Dynamic loading (no hard-coding)
- ✅ Zero Python at runtime

## Integration with Cursor Rules

This implementation follows `.cursor/rules/project.mdc`:

- **NO runtime interpretation** - all code pre-compiled to native binaries
- **Compile-time kernel generation** - Python used only at build time
- **Geometric folding** - Class indices determined at compile time
- **Dynamic loading** - No hard-coded kernel names
- **Common library pattern** - No repetition of primitives

## References

Based on commit `be99542`'s `frontends/atlas_py/` approach:

- Python → JSON compiler
- JSON as intermediate format
- Dynamic library loading
- Zero-interpretation execution
