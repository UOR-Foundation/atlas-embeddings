---
layout: default
title: Installation Guide
sidebar: guides
---

# Installation Guide

This guide provides comprehensive installation instructions for the UOR Prime Structure FFI across all supported platforms and languages.

## Prerequisites

### All Platforms
- **Lean 4** (stable release) - For building from source
- **C compiler** (GCC, Clang, or MSVC)
- **GNU Make** or compatible build system
- **Git** - For cloning the repository

### Language-Specific Requirements

#### Go
- **Go 1.19+** with CGO support
- **C compiler** for CGO bindings

#### Python
- **Python 3.8+**
- **pip** package manager
- **Development headers** (`python3-dev` on Ubuntu, `python-devel` on RHEL)

#### Rust
- **Rust 1.70+** with Cargo
- **bindgen** dependencies (libclang)

#### Node.js
- **Node.js 16+** with npm
- **node-gyp** build tools
- **Platform-specific build tools** (see Node.js section)

## Platform-Specific Setup

### Linux (Ubuntu/Debian)

#### System Dependencies
```bash
# Update package list
sudo apt update

# Install basic build tools
sudo apt install build-essential git curl

# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile
elan install stable
elan default stable

# Install language-specific dependencies
sudo apt install golang-go python3 python3-pip python3-dev nodejs npm
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

#### Installing Lean Dependencies
```bash
# Install required libraries
sudo apt install libc6-dev libgmp-dev

# For development
sudo apt install liblua5.3-dev
```

### Linux (RHEL/CentOS/Fedora)

#### System Dependencies
```bash
# Install basic build tools
sudo dnf install gcc gcc-c++ make git curl

# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile
elan install stable
elan default stable

# Install language dependencies
sudo dnf install golang python3 python3-pip python3-devel nodejs npm
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

### macOS

#### Using Homebrew
```bash
# Install Homebrew if not already installed
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"

# Install basic tools
brew install git make

# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile
elan install stable
elan default stable

# Install languages
brew install go python3 node rust
```

#### Xcode Command Line Tools
```bash
# Install Xcode command line tools (required for compilation)
xcode-select --install
```

### Windows

#### Using MSYS2 (Recommended)
```bash
# Install MSYS2 from https://www.msys2.org/

# Update package database
pacman -Syu

# Install build tools
pacman -S mingw-w64-x86_64-gcc mingw-w64-x86_64-make git

# Install Lean 4 (in PowerShell)
Invoke-RestMethod https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | Invoke-Expression
elan install stable
elan default stable
```

#### Language Installation
```powershell
# Install languages using chocolatey or official installers
# Go: https://golang.org/dl/
# Python: https://python.org/downloads/
# Node.js: https://nodejs.org/
# Rust: https://rustup.rs/
```

## Installation Methods

### Method 1: Package Manager Installation (Recommended)

#### Go
```bash
go get github.com/atlas-12288/uor-prime-structure
```

#### Python
```bash
pip install uor-prime-structure

# Or with conda
conda install -c conda-forge uor-prime-structure
```

#### Rust
```bash
cargo add uor-prime-structure
```

#### Node.js
```bash
npm install uor-prime-structure
```

### Method 2: Building from Source

#### Clone the Repository
```bash
git clone https://github.com/atlas-12288/uor-prime-structure.git
cd uor-prime-structure
```

#### Full Build (All Components)
```bash
# Build everything
make all

# Run tests to verify build
make test

# Install system-wide (optional)
sudo make install
```

#### Language-Specific Builds

##### Go Only
```bash
# Build basic Go bindings
make -C pkg/go all

# Build enhanced Go runtime
make -C runtime/go all

# Test Go bindings
make -C pkg/go test
make -C runtime/go test
```

##### Python Only
```bash
# Build basic Python bindings
make -C pkg/python all

# Build enhanced Python runtime
make -C runtime/python all

# Test Python bindings
make -C pkg/python test
make -C runtime/python test
```

##### Rust Only
```bash
# Build basic Rust bindings
make -C pkg/rust all

# Build enhanced Rust runtime
make -C runtime/rust all

# Test Rust bindings
make -C pkg/rust test
make -C runtime/rust test
```

##### Node.js Only
```bash
# Install Node.js build dependencies
npm install -g node-gyp

# Build basic Node.js bindings
make -C pkg/node all

# Build enhanced Node.js runtime
make -C runtime/node all

# Test Node.js bindings
make -C pkg/node test
make -C runtime/node test
```

### Method 3: Development Installation

For contributors and developers who need the latest features:

```bash
# Clone with development branch
git clone -b develop https://github.com/atlas-12288/uor-prime-structure.git
cd uor-prime-structure

# Install development dependencies
make dev-deps

# Build with debug information
make BUILD_TYPE=debug all

# Run extended test suite
make test-all
```

## Verifying Installation

### Basic Verification
```bash
# Quick system check
make check

# Verify Lean library
.lake/build/bin/uor-verify
echo $?  # Should print 0
```

### Language-Specific Verification

#### Go
```bash
cd tests/go
go run verify.go
```

#### Python
```bash
python3 -c "
import uor
print('UOR installed successfully')
print(f'Pages: {uor.get_pages()}')
print(f'ABI Version: {uor.get_abi_version()}')
"
```

#### Rust
```bash
cd tests/rust
cargo run --bin verify
```

#### Node.js
```bash
node -e "
const uor = require('uor-prime-structure');
console.log('UOR installed successfully');
console.log('Pages:', uor.getPages());
"
```

#### C
```bash
# Compile and run C test
gcc -I/usr/local/include -L/usr/local/lib tests/c/verify.c -o verify -luor
./verify
```

## Configuration Options

### Build Configuration
```bash
# Debug build
make BUILD_TYPE=debug

# Release build (default)
make BUILD_TYPE=release

# Verbose output
make VERBOSE=1

# Custom installation prefix
make PREFIX=/opt/uor install

# Disable colored output
make NO_COLOR=1
```

### Runtime Configuration

#### Environment Variables
```bash
# Use Lean runtime (default)
export UOR_USE_LEAN=1

# Use pure language implementations
export UOR_USE_LEAN=0

# Enable debug logging
export UOR_DEBUG=1

# Set custom library path
export UOR_LIB_PATH=/path/to/uor/lib
```

#### Configuration Files

Create `~/.uorconfig` for user-specific settings:
```ini
[runtime]
use_lean = true
debug = false

[paths]
lib_path = /usr/local/lib
include_path = /usr/local/include

[logging]
level = info
output = stderr
```

## Troubleshooting Installation

### Common Issues

#### Lean Installation Problems
```bash
# Clear Lean cache
lake clean

# Reinstall Lean toolchain
elan self update
elan install stable
elan default stable

# Rebuild from scratch
rm -rf .lake
lake build
```

#### CGO Build Errors (Go)
```bash
# Verify CGO is enabled
go env CGO_ENABLED  # Should be "1"

# Set compiler explicitly
export CC=gcc  # or CC=clang

# Install development headers
# Ubuntu/Debian:
sudo apt install libc6-dev
# macOS:
xcode-select --install
```

#### Python Build Errors
```bash
# Install Python development headers
# Ubuntu/Debian:
sudo apt install python3-dev
# RHEL/Fedora:
sudo dnf install python3-devel

# Upgrade pip and setuptools
pip install --upgrade pip setuptools wheel

# Use system compiler
export CC=gcc
```

#### Node.js Build Errors
```bash
# Rebuild native modules
npm rebuild

# Clear npm cache
npm cache clean --force

# Install build tools
# Windows:
npm install --global --production windows-build-tools
# macOS:
xcode-select --install
# Linux:
sudo apt install build-essential
```

#### Library Path Issues
```bash
# Add to library path
export LD_LIBRARY_PATH=/usr/local/lib:$LD_LIBRARY_PATH

# Update library cache (Linux)
sudo ldconfig

# Check library dependencies
ldd /usr/local/lib/libuor.so
```

### Getting Help

If you encounter issues not covered here:

1. **Check the [FAQ](../reference/faq)** for common questions
2. **Review [Troubleshooting](../reference/troubleshooting)** for specific error solutions
3. **Search existing issues** on GitHub
4. **Create a new issue** with:
   - Operating system and version
   - Language versions
   - Full error message
   - Steps to reproduce

### Platform-Specific Notes

#### Alpine Linux
```bash
# Install musl development packages
apk add musl-dev gcc

# May need to set RUSTFLAGS for Rust
export RUSTFLAGS="-C target-feature=-crt-static"
```

#### ARM64 (Apple Silicon)
```bash
# May need to install Rosetta for some tools
softwareupdate --install-rosetta --agree-to-license

# Use native builds when available
arch -arm64 brew install [package]
```

#### Windows Subsystem for Linux (WSL)
```bash
# Use Linux installation instructions
# Ensure WSL 2 for better performance
wsl --set-version Ubuntu 2
```

## Next Steps

After successful installation:

1. **[Getting Started](getting-started)** - Your first UOR program
2. **[Architecture](architecture)** - Understanding the system design  
3. **[Examples](../examples/)** - Comprehensive code examples
4. **[API Reference](../api/)** - Detailed function documentation