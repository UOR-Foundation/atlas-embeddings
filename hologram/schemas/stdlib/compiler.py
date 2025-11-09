"""
Python to JSON Schema Compiler

Compiles Python functions to JSON schemas for Atlas kernel generation.
Based on historical frontends/atlas_py/compiler.py
"""

import ast
import json
import inspect
from typing import Any, Callable, Dict, List, Optional
from functools import wraps


class AtlasCompiler:
    """Compiles Python AST to Atlas JSON schema"""

    def __init__(self):
        self.declared_vars = set()  # Track declared variables for assignment vs declaration

    def compile_function(self, func: Callable) -> Dict[str, Any]:
        """Compile a Python function to JSON schema"""
        # Reset state for each function compilation
        self.declared_vars = set()

        # Get source code and parse to AST
        source = inspect.getsource(func)
        tree = ast.parse(source)

        # Find the function definition
        func_def = None
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef) and node.name == func.__name__:
                func_def = node
                break

        if not func_def:
            raise ValueError(f"Could not find function {func.__name__}")

        # Extract parameters and mark them as declared
        params = self._compile_parameters(func_def)
        for param in params:
            self.declared_vars.add(param["name"])

        # Compile function body
        body = self._compile_body(func_def.body)

        return {
            "version": "1.0",
            "kernel": {
                "name": func.__name__,
                "params": params,
                "body": body
            }
        }

    def _compile_parameters(self, func_def: ast.FunctionDef) -> List[Dict[str, Any]]:
        """Extract and compile function parameters"""
        params = []

        for arg in func_def.args.args:
            param_name = arg.arg
            param_type = self._parse_type_annotation(arg.annotation)

            params.append({
                "name": param_name,
                "type": param_type
            })

        return params

    def _parse_type_annotation(self, annotation) -> Dict[str, Any]:
        """Parse Python type annotation to Atlas type"""
        if annotation is None:
            raise ValueError("All kernel parameters must have type annotations")

        # DeviceArray[type]
        if isinstance(annotation, ast.Subscript):
            if isinstance(annotation.value, ast.Name):
                if annotation.value.id == "DeviceArray":
                    element_type = self._parse_scalar_type(annotation.slice)
                    return {
                        "kind": "device_array",
                        "element_type": element_type
                    }

        # Scalar types
        if isinstance(annotation, ast.Name):
            return self._parse_scalar_type(annotation)

        raise ValueError(f"Unsupported type annotation: {ast.dump(annotation)}")

    def _parse_scalar_type(self, node) -> Dict[str, Any]:
        """Parse scalar type"""
        if isinstance(node, ast.Name):
            type_map = {
                "int": "i32",
                "float": "f32",
                "bool": "bool",
                "u8": "u8",
                "u16": "u16",
                "u32": "u32",
                "u64": "u64",
                "i8": "i8",
                "i16": "i16",
                "i32": "i32",
                "i64": "i64",
                "f32": "f32",
                "f64": "f64",
                "usize": "usize",
            }

            scalar_type = type_map.get(node.id)
            if scalar_type:
                return {
                    "kind": "scalar",
                    "type": scalar_type
                }

        raise ValueError(f"Unsupported scalar type: {ast.dump(node)}")

    def _compile_body(self, statements: List[ast.stmt]) -> List[Dict[str, Any]]:
        """Compile function body statements"""
        result = []

        for stmt in statements:
            compiled = self._compile_statement(stmt)
            if compiled:
                result.append(compiled)

        return result

    def _compile_statement(self, stmt: ast.stmt) -> Optional[Dict[str, Any]]:
        """Compile a single statement"""
        if isinstance(stmt, ast.Assign):
            if len(stmt.targets) == 1:
                target = stmt.targets[0]
                # Variable declaration or reassignment
                if isinstance(target, ast.Name):
                    var_name = target.id
                    # Check if this variable has already been declared
                    if var_name in self.declared_vars:
                        # Reassignment
                        return {
                            "type": "assign",
                            "target": {"type": "var", "name": var_name},
                            "value": self._compile_expression(stmt.value)
                        }
                    else:
                        # Declaration
                        self.declared_vars.add(var_name)
                        return {
                            "type": "let",
                            "name": var_name,
                            "value": self._compile_expression(stmt.value)
                        }
                # Array assignment
                elif isinstance(target, ast.Subscript):
                    return {
                        "type": "assign",
                        "target": self._compile_expression(target),
                        "value": self._compile_expression(stmt.value)
                    }

        elif isinstance(stmt, ast.AugAssign):
            # Augmented assignment: c[idx] += value
            return {
                "type": "assign",
                "target": self._compile_expression(stmt.target),
                "value": {
                    "type": "binary_op",
                    "op": self._compile_aug_op(stmt.op),
                    "left": self._compile_expression(stmt.target),
                    "right": self._compile_expression(stmt.value)
                }
            }

        elif isinstance(stmt, ast.Expr):
            return None  # Skip bare expressions

        elif isinstance(stmt, ast.If):
            return {
                "type": "if",
                "condition": self._compile_expression(stmt.test),
                "then_body": self._compile_body(stmt.body),
                "else_body": self._compile_body(stmt.orelse) if stmt.orelse else None
            }

        elif isinstance(stmt, ast.Return):
            return {
                "type": "return",
                "value": self._compile_expression(stmt.value) if stmt.value else None
            }

        elif isinstance(stmt, ast.For):
            # Handle range() loops
            if isinstance(stmt.iter, ast.Call) and isinstance(stmt.iter.func, ast.Name):
                if stmt.iter.func.id == "range":
                    # Extract range arguments
                    if len(stmt.iter.args) == 1:
                        start = {"type": "literal", "value": 0}
                        stop = self._compile_expression(stmt.iter.args[0])
                        step = {"type": "literal", "value": 1}
                    elif len(stmt.iter.args) == 2:
                        start = self._compile_expression(stmt.iter.args[0])
                        stop = self._compile_expression(stmt.iter.args[1])
                        step = {"type": "literal", "value": 1}
                    elif len(stmt.iter.args) == 3:
                        start = self._compile_expression(stmt.iter.args[0])
                        stop = self._compile_expression(stmt.iter.args[1])
                        step = self._compile_expression(stmt.iter.args[2])
                    else:
                        raise ValueError("Invalid range() call")

                    var_name = stmt.target.id if isinstance(stmt.target, ast.Name) else None
                    if not var_name:
                        raise ValueError("For loop target must be a simple variable")

                    self.declared_vars.add(var_name)

                    return {
                        "type": "for",
                        "var": var_name,
                        "start": start,
                        "stop": stop,
                        "step": step,
                        "body": self._compile_body(stmt.body)
                    }

        return None

    def _compile_expression(self, expr: ast.expr) -> Dict[str, Any]:
        """Compile an expression"""
        if isinstance(expr, ast.Name):
            return {"type": "var", "name": expr.id}

        elif isinstance(expr, ast.Constant):
            return {"type": "literal", "value": expr.value}

        elif isinstance(expr, ast.BinOp):
            return {
                "type": "binary_op",
                "op": self._compile_binop(expr.op),
                "left": self._compile_expression(expr.left),
                "right": self._compile_expression(expr.right)
            }

        elif isinstance(expr, ast.Compare):
            # Handle single comparison
            if len(expr.ops) == 1 and len(expr.comparators) == 1:
                return {
                    "type": "binary_op",
                    "op": self._compile_cmpop(expr.ops[0]),
                    "left": self._compile_expression(expr.left),
                    "right": self._compile_expression(expr.comparators[0])
                }

        elif isinstance(expr, ast.Subscript):
            return {
                "type": "index",
                "array": self._compile_expression(expr.value),
                "index": self._compile_expression(expr.slice)
            }

        elif isinstance(expr, ast.Call):
            if isinstance(expr.func, ast.Name):
                return {
                    "type": "call",
                    "function": expr.func.id,
                    "args": [self._compile_expression(arg) for arg in expr.args]
                }

        raise ValueError(f"Unsupported expression: {ast.dump(expr)}")

    def _compile_binop(self, op: ast.operator) -> str:
        """Compile binary operator"""
        op_map = {
            ast.Add: "add",
            ast.Sub: "sub",
            ast.Mult: "mul",
            ast.Div: "div",
            ast.Mod: "mod",
        }
        return op_map.get(type(op), "unknown")

    def _compile_cmpop(self, op: ast.cmpop) -> str:
        """Compile comparison operator"""
        op_map = {
            ast.Lt: "lt",
            ast.LtE: "le",
            ast.Gt: "gt",
            ast.GtE: "ge",
            ast.Eq: "eq",
            ast.NotEq: "ne",
        }
        return op_map.get(type(op), "unknown")

    def _compile_aug_op(self, op: ast.operator) -> str:
        """Compile augmented assignment operator"""
        return self._compile_binop(op)


# Global compiler instance
_compiler = AtlasCompiler()


def atlas_kernel(func: Callable) -> Callable:
    """Decorator to mark function as Atlas kernel"""
    @wraps(func)
    def wrapper(*args, **kwargs):
        raise RuntimeError(
            f"Kernel {func.__name__} cannot be called directly. "
            "Use compile_to_json() to compile it first."
        )
    
    wrapper._atlas_kernel = func
    return wrapper


def compile_to_json(func: Callable, output_path: Optional[str] = None) -> str:
    """Compile a kernel function to JSON schema"""
    # Get original function if wrapped
    original_func = getattr(func, '_atlas_kernel', func)
    
    # Compile to JSON
    schema = _compiler.compile_function(original_func)
    json_str = json.dumps(schema, indent=2)
    
    # Write to file if requested
    if output_path:
        with open(output_path, 'w') as f:
            f.write(json_str)
    
    return json_str
