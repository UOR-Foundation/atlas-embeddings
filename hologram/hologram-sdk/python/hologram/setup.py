"""
Hologram Python Bindings

Pythonic wrapper around hologram-ffi providing:
- Automatic resource management (context managers)
- Zero-copy buffer operations
- NumPy integration
- Backend selection (CPU/Metal/CUDA)
"""

from setuptools import setup, find_packages

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

setup(
    name="hologram",
    version="0.1.0",
    author="Hologram Team",
    author_email="team@hologram.ai",
    description="Pythonic bindings for Hologram compute acceleration",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/your-org/hologram-sdk",
    packages=find_packages(),
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Developers",
        "Intended Audience :: Science/Research",
        "Topic :: Scientific/Engineering",
        "Topic :: Scientific/Engineering :: Artificial Intelligence",
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Programming Language :: Python :: 3.12",
    ],
    python_requires=">=3.8",
    install_requires=[
        "numpy>=1.20.0",
    ],
    extras_require={
        "dev": [
            "pytest>=7.0.0",
            "pytest-benchmark>=4.0.0",
            "black>=23.0.0",
            "mypy>=1.0.0",
            "ruff>=0.1.0",
        ],
    },
    package_data={
        "hologram": ["py.typed"],
    },
)
