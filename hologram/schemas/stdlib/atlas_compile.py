#!/usr/bin/env python3
"""
Atlas Kernel Compiler CLI

Compiles Python kernel source files to JSON schemas.
Usage: atlas-compile <python_file> [-o output.json] [--verbose]
"""

import argparse
import sys
import os
import importlib.util
import json
from pathlib import Path

from compiler import AtlasCompiler, compile_to_json


def find_kernels_in_file(file_path: Path):
    """Find all kernel functions in a Python file"""
    # Load the Python module
    spec = importlib.util.spec_from_file_location("kernel_module", file_path)
    module = importlib.util.module_from_spec(spec)
    
    try:
        spec.loader.exec_module(module)
    except Exception as e:
        print(f"❌ Error loading module: {e}", file=sys.stderr)
        return []
    
    # Helper functions that should be excluded from kernel compilation
    EXCLUDED_FUNCTIONS = {'get_global_id', 'atomic_add_f32', 'atomic_add_u32', 'atomic_add_i32'}
    
    # Get the module file name to check if it's atlas_kernel.py
    module_filename = Path(module.__file__).name if hasattr(module, '__file__') else ''
    is_atlas_kernel_module = module_filename == 'atlas_kernel.py'
    
    # Find all functions with type annotations
    kernels = []
    for name in dir(module):
        # Skip if it's a helper function
        if name in EXCLUDED_FUNCTIONS:
            continue
        
        # Skip entire module if it's atlas_kernel.py (contains only helper functions)
        if is_atlas_kernel_module:
            continue
        
        obj = getattr(module, name)
        if callable(obj) and not name.startswith('_'):
            # Check if decorated or has proper type annotations
            if hasattr(obj, '_atlas_kernel'):
                kernels.append((name, obj._atlas_kernel))
            elif hasattr(obj, '__annotations__') and obj.__annotations__:
                # Only include if it's not a built-in type
                if not isinstance(obj, type):
                    kernels.append((name, obj))
    
    return kernels


def main():
    parser = argparse.ArgumentParser(
        description='Atlas Kernel Compiler - Compile Python kernels to JSON',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Compile single file
  atlas-compile vector_add.py

  # Specify output
  atlas-compile vector_add.py -o vector_add.json

  # Verbose output
  atlas-compile matrix_multiply.py -v
        """
    )
    
    parser.add_argument('input', help='Python file containing kernel definitions')
    parser.add_argument('-o', '--output', help='Output JSON file')
    parser.add_argument('-v', '--verbose', action='store_true', help='Verbose output')
    
    args = parser.parse_args()
    
    # Find kernels
    kernels = find_kernels_in_file(Path(args.input))
    
    if not kernels:
        print(f"❌ No kernel functions found in {args.input}", file=sys.stderr)
        return 1
    
    if args.verbose:
        print(f"📖 Found {len(kernels)} kernel(s):")
        for name, _ in kernels:
            print(f"   • {name}")
    
    # Compile to JSON
    compiler = AtlasCompiler()
    schemas = []
    
    for name, func in kernels:
        try:
            if args.verbose:
                print(f"🔄 Compiling {name}...")
            
            schema = compiler.compile_function(func)
            schemas.append((name, schema))
            
            if args.verbose:
                print(f"   ✓ Compiled successfully")
        except Exception as e:
            print(f"❌ Error compiling {name}: {e}", file=sys.stderr)
            if args.verbose:
                import traceback
                traceback.print_exc()
            return 1
    
    # Determine output path
    if args.output:
        output_path = Path(args.output)
    else:
        output_path = Path(args.input).with_suffix('.json')
    
    # Write JSON
    if len(schemas) == 1:
        with open(output_path, 'w') as f:
            json.dump(schemas[0][1], f, indent=2)
        print(f"✅ Compiled {schemas[0][0]} → {output_path}")
    else:
        # Multiple kernels
        all_schemas = [schema for _, schema in schemas]
        with open(output_path, 'w') as f:
            json.dump(all_schemas, f, indent=2)
        print(f"✅ Compiled {len(schemas)} kernels → {output_path}")
    
    return 0


if __name__ == '__main__':
    sys.exit(main())

