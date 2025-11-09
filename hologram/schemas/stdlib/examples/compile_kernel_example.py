"""
Example: Writing a Kernel in Python that Compiles to JSON → Rust → .so

This demonstrates the complete kernel generation pipeline.
"""

import sys
import os
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from compiler import compile_to_json
from atlas_kernel import DeviceArray, f32, u32, get_global_id, atomic_add_f32


# Define your kernel in Python!
def vector_add(a: DeviceArray[f32], b: DeviceArray[f32], c: DeviceArray[f32], n: u32):
    """Add two vectors element-wise: c = a + b"""
    idx = get_global_id()
    if idx < n:
        c[idx] = a[idx] + b[idx]


def vector_mul(a: DeviceArray[f32], b: DeviceArray[f32], c: DeviceArray[f32], n: u32):
    """Multiply two vectors element-wise: c = a * b"""
    idx = get_global_id()
    if idx < n:
        c[idx] = a[idx] * b[idx]


def vector_dot(a: DeviceArray[f32], b: DeviceArray[f32], result: DeviceArray[f32], n: u32):
    """Compute dot product: result = Σ(a[i] * b[i])"""
    idx = get_global_id()
    if idx < n:
        product = a[idx] * b[idx]
        atomic_add_f32(result, product)


def main():
    """Compile Python kernels to JSON schemas"""
    
    kernels = [
        ("vector_add", vector_add),
        ("vector_mul", vector_mul),
        ("vector_dot", vector_dot),
    ]
    
    # Output directory for JSON schemas
    output_dir = Path("../target/json")
    output_dir.mkdir(parents=True, exist_ok=True)
    
    print("🔄 Compiling Python kernels to JSON schemas...\n")
    
    for name, kernel_func in kernels:
        # Compile Python → JSON
        json_schema = compile_to_json(kernel_func)
        
        # Save to file
        output_file = output_dir / f"{name}.json"
        with open(output_file, 'w') as f:
            f.write(json_schema)
        
        print(f"✅ Generated: {output_file}")
    
    print(f"\n📁 JSON schemas saved to: {output_dir}/")
    print("\n✨ Next step: JSON schemas will be converted to Rust code by cargo build")


if __name__ == "__main__":
    main()

