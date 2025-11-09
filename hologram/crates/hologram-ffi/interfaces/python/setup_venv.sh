#!/bin/bash
# Setup virtual environment for Python tests

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VENV_DIR="$SCRIPT_DIR/.venv"

# Create virtual environment if it doesn't exist
if [ ! -d "$VENV_DIR" ]; then
    echo "📦 Creating Python virtual environment..."
    python3 -m venv "$VENV_DIR"
fi

# Activate virtual environment
echo "🔧 Activating virtual environment..."
source "$VENV_DIR/bin/activate"

# Upgrade pip
echo "📦 Upgrading pip..."
pip install --upgrade pip

# Install the package in editable mode
echo "📦 Installing hologram-ffi in editable mode..."
pip install -e .

# Install development dependencies
echo "📦 Installing development dependencies (pytest, etc)..."
pip install pytest pytest-cov black flake8 mypy

echo "✅ Virtual environment setup complete!"
echo "💡 To activate: source .venv/bin/activate"
echo "💡 To run tests: pytest tests/ -v"

