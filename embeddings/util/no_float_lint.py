#!/usr/bin/env python3
import ast
import pathlib
import re
import sys

ROOT = pathlib.Path(".")
SELF = pathlib.Path(__file__).resolve()
VIOLATIONS = []
TARGET_DIRS = [
    pathlib.Path("atlas/aep"),
    pathlib.Path("tools/lint"),
    pathlib.Path("cli"),
    pathlib.Path("util"),
    pathlib.Path("tests"),
]


def check_file(path: pathlib.Path):
    if path.resolve() == SELF:
        return
    try:
        text = path.read_text(encoding="utf-8")
    except Exception:
        return
    # fast string scan for dtype=float
    if re.search(r"dtype\s*=\s*float", text):
        VIOLATIONS.append(f"{path}: dtype=float found")
    try:
        tree = ast.parse(text, filename=str(path))
    except SyntaxError:
        return

    class V(ast.NodeVisitor):
        def visit_Constant(self, node: ast.Constant):
            if isinstance(node.value, float):
                VIOLATIONS.append(
                    f"{path}:{node.lineno}:{node.col_offset}: float literal {node.value}"
                )

        def visit_Call(self, node: ast.Call):
            if isinstance(node.func, ast.Name) and node.func.id == "float":
                VIOLATIONS.append(f"{path}:{node.lineno}:{node.col_offset}: float() call")
            self.generic_visit(node)

        def visit_Attribute(self, node: ast.Attribute):
            if (
                isinstance(node.value, ast.Name)
                and node.value.id in {"np", "numpy"}
                and node.attr.lower().startswith("float")
            ):
                VIOLATIONS.append(
                    f"{path}:{node.lineno}:{node.col_offset}: numpy float type {node.attr}"
                )
            self.generic_visit(node)

        def visit_Name(self, node: ast.Name):
            if node.id == "float":
                VIOLATIONS.append(f"{path}:{node.lineno}:{node.col_offset}: 'float' name")

    V().visit(tree)


def main():
    for rel in TARGET_DIRS:
        target = ROOT / rel
        if target.is_dir():
            for p in target.rglob("*.py"):
                check_file(p)
        elif target.is_file():
            check_file(target)
    if VIOLATIONS:
        print("\n".join(VIOLATIONS))
        sys.exit(1)
    print("no-float-lint: OK")


if __name__ == "__main__":
    main()
