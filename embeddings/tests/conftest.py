"""Pytest configuration for atlas-hologram tests."""
import sys
import os

# Force real numpy to be imported first before the local stub
# by removing the current directory from sys.path temporarily during numpy import
original_path = sys.path.copy()
# Remove current directory and parent to avoid local numpy stub
while '' in sys.path:
    sys.path.remove('')
cwd = os.getcwd()
sys.path = [p for p in sys.path if not p.startswith(cwd)]

# Import real numpy
import numpy as np_real

# Restore path
sys.path = original_path

# Inject real numpy into sys.modules before anything else imports it
sys.modules['numpy'] = np_real
