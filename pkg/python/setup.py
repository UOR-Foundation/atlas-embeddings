"""
Setup script for UOR Python FFI bindings
"""

from setuptools import setup, find_packages
from pathlib import Path

# Read README
readme_path = Path(__file__).parent.parent.parent / "README.md"
if readme_path.exists():
    long_description = readme_path.read_text()
else:
    long_description = "Python bindings for UOR Prime Structure FFI"

setup(
    name="uor-ffi",
    version="1.0.0",
    author="UOR Contributors",
    description="Python bindings for UOR Prime Structure FFI",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/atlas-12288/uor",
    packages=find_packages(where="src"),
    package_dir={"": "src"},
    python_requires=">=3.7",
    install_requires=[],
    extras_require={
        "test": ["pytest>=6.0"],
        "benchmark": ["timeit"],
    },
    classifiers=[
        "Development Status :: 4 - Beta",
        "Intended Audience :: Developers",
        "Intended Audience :: Science/Research",
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.7",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Topic :: Scientific/Engineering :: Mathematics",
    ],
)