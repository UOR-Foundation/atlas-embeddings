#!/bin/bash
# Setup script for examples virtual environment

set -e

echo "Setting up examples virtual environment..."

# Create venv if it doesn't exist
if [ ! -d ".venv" ]; then
    echo "Creating virtual environment..."
    python3 -m venv .venv
fi

# Activate the virtual environment
echo "Activating virtual environment..."
source .venv/bin/activate

# Upgrade pip
echo "Upgrading pip..."
pip install --upgrade pip setuptools wheel

# Install dependencies
echo "Installing dependencies from requirements.txt..."
echo "Note: This may take a few minutes..."
pip install -r requirements.txt

echo "Installing hologram-ffi in editable mode..."
pushd ../crates/hologram-ffi/interfaces/python && pip install -e . && popd

echo ""
echo "Setup complete! To use the virtual environment:"
echo "  cd /workspace/examples"
echo "  source .venv/bin/activate"
echo ""
echo "Then you can run the example scripts:"
echo "  python simple_example.py"
echo "  python pytorch_hologram_example.py"
echo ""
echo "To deactivate:"
echo "  deactivate"

