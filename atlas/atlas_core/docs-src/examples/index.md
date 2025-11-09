---
layout: default
title: Examples Overview
sidebar: examples
---

# Examples Overview

This section provides comprehensive examples of using the UOR Prime Structure FFI across all supported languages. Examples range from basic usage to advanced integration patterns.

## Example Categories

### [Basic Examples](basic)
Simple examples demonstrating core functionality in all languages:
- Getting system constants
- R96 resonance classification
- Φ boundary encoding/decoding
- Truth conservation functions

### Language-Specific Examples

#### [C Examples](c)
- Direct FFI usage
- Memory management
- Error handling
- Performance optimization

#### [Go Examples](go)
- Basic package usage
- Enhanced runtime features
- Concurrent processing
- CGO integration patterns

#### [Python Examples](python)
- Basic and runtime APIs
- NumPy integration
- Pandas compatibility
- Scientific computing workflows

#### [Rust Examples](rust)
- Safe wrapper usage
- Zero-copy operations
- SIMD optimization
- Error handling with Result types

#### [Node.js Examples](node)
- JavaScript and TypeScript usage
- Async/await patterns
- Stream processing
- Web API integration

## Common Use Cases

### Data Processing Pipelines
Examples of processing large datasets efficiently:
- Batch R96 classification
- Stream processing
- Parallel computation
- Memory-efficient algorithms

### Mathematical Applications
Examples demonstrating mathematical applications:
- Holographic boundary calculations
- Conservation law verification
- Resonance pattern analysis
- Prime structure exploration

### Integration Examples
Real-world integration patterns:
- Database storage of UOR data
- Web service APIs
- Message queue processing
- Microservice architectures

## Getting Started

1. **[Basic Examples](basic)** - Start here for simple usage patterns
2. **Language-Specific** - Choose your preferred language for detailed examples
3. **Advanced Patterns** - Explore complex integration scenarios

## Example Code Structure

Each example follows a consistent structure:

```
example-name/
├── README.md           # Description and usage
├── src/               # Source code
│   ├── basic.*        # Basic implementation
│   ├── optimized.*    # Performance-optimized version
│   └── tests.*        # Test cases
├── data/              # Sample data (if needed)
├── Makefile           # Build instructions
└── expected-output.txt # Expected results
```

## Running Examples

### Prerequisites
Ensure UOR Prime Structure FFI is installed for your target language:

```bash
# Go
go get github.com/atlas-12288/uor-prime-structure

# Python  
pip install uor-prime-structure

# Rust
cargo add uor-prime-structure

# Node.js
npm install uor-prime-structure

# C (build from source)
make install
```

### Building and Running

Most examples include both pure and FFI versions:

```bash
# Build specific example
cd examples/go/basic-usage/
make all

# Run with pure implementation
make run-pure

# Run with Lean FFI runtime
make run-ffi

# Run performance comparison
make benchmark
```

## Example Data

Many examples use common test datasets:

- **Small Dataset**: 1KB of sample data for quick testing
- **Medium Dataset**: 1MB for performance testing  
- **Large Dataset**: 100MB for scalability testing
- **Mathematical Fixtures**: Known input/output pairs for verification

## Performance Notes

Each example includes performance characteristics:

| Language | Implementation | Typical Performance |
|----------|----------------|-------------------|
| C Direct | Lean Runtime | ~400 MB/s |
| Go Pure | Lookup Table | ~500 MB/s |
| Go FFI | Lean Runtime | ~70 MB/s |
| Rust Pure | SIMD Optimized | ~800 MB/s |
| Python Pure | NumPy | ~1.2 GB/s |
| Node Pure | V8 Optimized | ~100 MB/s |

*Performance measured on AWS c5.xlarge instance for R96 classification*

## Contributing Examples

To contribute new examples:

1. Follow the standard directory structure
2. Include both pure and FFI versions where applicable
3. Add comprehensive documentation
4. Include test cases and expected outputs
5. Verify performance characteristics
6. Submit via pull request

See the [Contributing Guide](../reference/contributing) for detailed guidelines.

## Example Categories by Complexity

### Beginner
- [Basic Usage](basic) - Core functions in all languages
- [Simple Integration](c) - Straightforward C usage
- [Getting Started](go) - Go package basics

### Intermediate  
- [Batch Processing](python) - Efficient data processing
- [Concurrent Usage](go) - Parallel processing patterns
- [Memory Management](rust) - Zero-copy operations

### Advanced
- [SIMD Optimization](rust) - Vectorized operations
- [Stream Processing](node) - Async data streams
- [Custom Backends](c) - FFI extension patterns

## Cross-Language Examples

Some examples demonstrate cross-language interoperability:
- Go service with Rust computation backend
- Python analysis with C performance kernels  
- Node.js API with Lean verification
- Microservice architectures mixing languages

These examples show how the consistent FFI interface enables seamless integration across language boundaries while maintaining mathematical correctness.

## Next Steps

- Start with [Basic Examples](basic) to understand core concepts
- Choose your language-specific guide for detailed usage
- Explore advanced patterns for production applications
- Review [Best Practices](../guides/best-practices) for optimization tips