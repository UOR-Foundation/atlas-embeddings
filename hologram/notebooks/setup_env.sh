#!/bin/bash
# Setup script for notebooks virtual environment

set -e

echo "Setting up notebooks virtual environment..."

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

# Install dependencies (this may take a while)
echo "Installing dependencies from requirements.txt..."
echo "Note: This may take several minutes..."
pip install -r ./requirements.txt

echo ""
echo "Setup complete! To use the virtual environment:"
echo "  cd notebooks"
echo "  source .venv/bin/activate"
echo ""
echo "To deactivate:"
echo "  deactivate"
