#!/usr/bin/env python3
"""
Setup script for UOR Runtime Python bindings (enhanced version).
Provides rich object-oriented API on top of the minimal C wrapper.
"""

from setuptools import setup, Extension, find_packages
import os
import sys

# Get the directory containing this setup.py
this_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(this_dir, '..', '..'))

# Enhanced runtime module with minimal C wrapper
uor_runtime = Extension(
    'uor_runtime._core',
    sources=[
        'src/_core.c',
        os.path.join(project_root, 'ffi', 'c', 'minimal_wrapper.c')
    ],
    include_dirs=[
        os.path.join(project_root, 'ffi', 'c'),
        'src'
    ],
    extra_compile_args=['-O2', '-Wall'] if sys.platform != 'win32' else ['/O2'],
    language='c'
)

setup(
    name='uor-runtime',
    version='1.0.0',
    description='UOR Prime Structure Runtime - Enhanced Python bindings',
    long_description="""
    Enhanced Python bindings for the UOR Prime Structure FFI.
    
    This package provides a rich, Pythonic API with comprehensive types,
    error handling, and convenience methods built on top of the minimal
    C wrapper implementation.
    
    Features:
    - PhiCoordinate class for coordinate management
    - ResonanceClass for R96 classification
    - Comprehensive error handling
    - Iterator support for structure traversal
    - Property-based access patterns
    """,
    author='UOR Project',
    packages=find_packages('src'),
    package_dir={'': 'src'},
    ext_modules=[uor_runtime],
    python_requires='>=3.7',
    classifiers=[
        'Development Status :: 4 - Beta',
        'Intended Audience :: Developers',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.7',
        'Programming Language :: Python :: 3.8',
        'Programming Language :: Python :: 3.9',
        'Programming Language :: Python :: 3.10',
        'Programming Language :: Python :: 3.11',
    ],
    test_suite='test',
)