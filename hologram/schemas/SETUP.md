# Python Development Setup (Optional)

This guide covers setting up Python for kernel development. **Python is optional** for normal use.

## When Do You Need Python?

### ✅ You DON'T need Python if:

- You're just using the project normally
- Running `cargo build` (handles everything automatically)
- Working on Rust code
- Adding new kernel schemas (just write Python in `schemas/`)

### ✅ You DO need Python if:

- You want to manually test the code generator
- You want to modify `build.py` (the code generator)
- You want IDE autocomplete for Python schemas
- You're adding Python-specific linting/formatting

## Setting Up Python (Optional)

### 1. Create Virtual Environment

```bash
cd schemas
python3 -m venv .venv
```

### 2. Activate It

**Linux/Mac:**

```bash
source .venv/bin/activate
```

**Windows:**

```bash
.venv\Scripts\activate
```

### 3. Install Dependencies (Optional)

```bash
pip install -r requirements.txt
```

(Currently none needed - build.py uses only standard library)

## VSCode Integration

If you want VSCode to recognize Python in schemas:

1. **Create `.venv`**: See above
2. **VSCode will auto-detect** it based on `.vscode/settings.json`
3. **Select interpreter**: VSCode should show `.venv` option

Or manually select:

- Press `Cmd+Shift+P` (Mac) or `Ctrl+Shift+P` (Windows/Linux)
- Type "Python: Select Interpreter"
- Choose `./schemas/.venv/bin/python`

## Why `.venv` in schemas/?

- **Isolated**: Python stuff stays in schemas/ directory
- **Optional**: Not needed for normal development
- **Clean**: Doesn't pollute workspace root
- **Conventional**: Python projects typically use `.venv` in their own directory

## Troubleshooting

### VSCode doesn't show Python support?

Make sure `.venv` exists:

```bash
cd schemas
python3 -m venv .venv
```

### Error about Python version?

Use Python 3.8+:

```bash
python3 --version  # Should show 3.8 or higher
```

### Kernel generator not running?

Normal `cargo build` should run it automatically. Check:

```bash
cargo build --package hologram-kernels 2>&1 | grep -i "kernel"
```

## Optional: @atlas_kernel Decorator

The historical `frontends/atlas_py/` used a `@atlas_kernel` decorator for safety:

```python
from atlas_py import atlas_kernel

@atlas_kernel  # Marks as kernel, prevents direct calls
def vector_add(...):
    ...
```

**Current approach doesn't need this** - direct functions work fine. We can add it later if you want development-time safety checks.

## Summary

- **For normal use**: Don't worry about Python, just use `cargo build`
- **For schema development**: Create `.venv` in schemas/ directory
- **For IDE support**: VSCode will auto-detect the .venv once created
