---
layout: default
title: Testing Guide
sidebar: guides
---

# Testing Guide

The UOR Prime Structure FFI includes a comprehensive test suite that verifies mathematical correctness, FFI functionality, and language binding reliability across all supported platforms and languages.

## Test Architecture

### Test Hierarchy

```
tests/
├── Makefile              # Test coordination
├── lean/                 # Lean verification tests
├── c/                    # C FFI tests
├── ffi/                  # FFI interface tests
├── integration/          # Cross-language tests
└── performance/          # Benchmark tests
```

### Component Testing Layers

```
┌─────────────────────────────────────────────────────────────┐
│                    Integration Tests                        │
│        (Cross-language compatibility and workflows)        │
└─────────────────────────────────────────────────────────────┘
                                │
                                ▼
┌─────────────────────────────────────────────────────────────┐
│                 Language Binding Tests                     │
│    ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐    │
│    │   Go    │  │  Rust   │  │ Node.js │  │ Python  │    │
│    │  Tests  │  │  Tests  │  │  Tests  │  │  Tests  │    │
│    └─────────┘  └─────────┘  └─────────┘  └─────────┘    │
└─────────────────────────────────────────────────────────────┘
                                │
                                ▼
┌─────────────────────────────────────────────────────────────┐
│                      FFI Tests                             │
│           (C API interface verification)                   │
└─────────────────────────────────────────────────────────────┘
                                │
                                ▼
┌─────────────────────────────────────────────────────────────┐
│                    Lean Verification                       │
│          (Mathematical proofs and properties)              │
└─────────────────────────────────────────────────────────────┘
```

## Running Tests

### Complete Test Suite

```bash
# Run all tests
make test

# Run tests with verbose output
make VERBOSE=1 test

# Run tests in parallel
make -j$(nproc) test
```

### Component-Specific Tests

#### Lean Verification
```bash
# Mathematical verification
make -C lean test

# CLI verification tool
.lake/build/bin/uor-verify

# Specific module tests
lake test UOR.Test.PrimeStructureTest
lake test UOR.Test.FFITest
```

#### C FFI Tests
```bash
# All C tests
make -C tests/c all

# Specific C tests
make -C tests/c test-basic
make -C tests/c test-ffi
make -C tests/c test-memory
```

#### Language Binding Tests

##### Go Tests
```bash
# Basic package tests
make -C pkg/go test

# Enhanced runtime tests
make -C runtime/go test

# Go-specific test commands
cd runtime/go && go test ./...
cd runtime/go && go test -race ./...  # Race condition detection
cd runtime/go && go test -bench=.     # Benchmarks
```

##### Python Tests
```bash
# Basic package tests
make -C pkg/python test

# Enhanced runtime tests
make -C runtime/python test

# Python-specific commands
cd runtime/python && python -m pytest tests/
cd runtime/python && python -m pytest --cov=uor_runtime tests/
```

##### Rust Tests
```bash
# Basic package tests
make -C pkg/rust test

# Enhanced runtime tests
make -C runtime/rust test

# Rust-specific commands
cd runtime/rust && cargo test
cd runtime/rust && cargo test --release
cd runtime/rust && cargo test --features lean-runtime
```

##### Node.js Tests
```bash
# Basic package tests
make -C pkg/node test

# Enhanced runtime tests
make -C runtime/node test

# Node-specific commands
cd runtime/node && npm test
cd runtime/node && npm run test:coverage
```

### Quick Verification

```bash
# Quick mathematical verification
make check

# Quick build and test
make all && make check
```

## Test Categories

### 1. Mathematical Verification Tests

Located in `lean/UOR/Test/`, these tests verify the mathematical foundations:

#### Core Mathematical Properties
```lean
-- Test R96 resonance classifier properties
theorem r96_count_exact : card (range 256).image r96Classify = 96

-- Test Φ encoding/decoding roundtrip
theorem phi_encode_decode (page : Nat) (byte : Nat) :
  phiPage (phiEncode page byte) = page % 48 ∧
  phiByte (phiEncode page byte) = byte % 256

-- Test truth conservation laws
theorem truth_conservation (budget : Int) :
  truthZero budget ↔ budget = 0
```

#### Prime Structure Invariants
```lean
-- Test unity constraint α₄α₅ = 1
theorem unity_constraint : α₄ * α₅ = 1

-- Test 48-page structure
theorem page_structure : pages = 48

-- Test conservation sum
theorem conservation_sum : totalSum = 687.110133
```

### 2. FFI Interface Tests

Located in `tests/c/`, these tests verify the C API:

#### Basic Function Tests
```c
// test_constants.c
void test_constants() {
    assert(lean_uor_pages() == 48);
    assert(lean_uor_bytes() == 256);
    assert(lean_uor_rclasses() == 96);
    assert(lean_uor_abi_version() == 1);
}

// test_r96.c  
void test_r96_classifier() {
    // Test all byte values map to valid classes
    for (int b = 0; b < 256; b++) {
        uint8_t class = lean_uor_r96_classify(b);
        assert(class < 96);
    }
    
    // Test specific known mappings
    assert(lean_uor_r96_classify(0) == 0);
    assert(lean_uor_r96_classify(255) == 47);
}
```

#### Memory Management Tests
```c
// test_memory.c
void test_memory_safety() {
    // Initialize and finalize multiple times
    for (int i = 0; i < 100; i++) {
        assert(lean_uor_initialize() == 0);
        lean_uor_finalize();
    }
}
```

### 3. Language Binding Tests

Each language has comprehensive test suites:

#### Go Test Examples
```go
// Basic functionality tests
func TestConstants(t *testing.T) {
    assert.Equal(t, uint32(48), uor.GetPages())
    assert.Equal(t, uint32(256), uor.GetBytes())
    assert.Equal(t, uint32(96), uor.GetRClasses())
}

// R96 classifier tests
func TestR96Classifier(t *testing.T) {
    for b := 0; b < 256; b++ {
        class := uor.R96Classify(byte(b))
        assert.Less(t, class, byte(96))
    }
}

// Φ encoding roundtrip tests
func TestPhiEncoding(t *testing.T) {
    for page := 0; page < 48; page++ {
        for byteVal := 0; byteVal < 256; byteVal++ {
            encoded := uor.PhiEncode(byte(page), byte(byteVal))
            decodedPage := uor.PhiPage(encoded)
            decodedByte := uor.PhiByte(encoded)
            
            assert.Equal(t, byte(page), decodedPage)
            assert.Equal(t, byte(byteVal), decodedByte)
        }
    }
}
```

#### Python Test Examples
```python
import pytest
import uor

class TestUORBasics:
    def setup_method(self):
        uor.initialize()
    
    def teardown_method(self):
        uor.finalize()
    
    def test_constants(self):
        assert uor.get_pages() == 48
        assert uor.get_bytes() == 256
        assert uor.get_rclasses() == 96
    
    def test_r96_classifier(self):
        for b in range(256):
            class_val = uor.r96_classify(b)
            assert 0 <= class_val < 96
    
    def test_phi_encoding_roundtrip(self):
        for page in range(48):
            for byte_val in range(256):
                encoded = uor.phi_encode(page, byte_val)
                decoded_page = uor.phi_page(encoded)
                decoded_byte = uor.phi_byte(encoded)
                
                assert decoded_page == page
                assert decoded_byte == byte_val
```

### 4. Integration Tests

Cross-language compatibility tests ensure consistent behavior:

```python
# integration_test.py
def test_cross_language_consistency():
    """Verify that all languages produce identical results."""
    
    # Test data
    test_cases = [(page, byte_val) for page in range(48) for byte_val in range(0, 256, 17)]
    
    # Results from each language
    go_results = run_go_test(test_cases)
    python_results = run_python_test(test_cases)
    rust_results = run_rust_test(test_cases)
    node_results = run_node_test(test_cases)
    
    # All results should be identical
    assert go_results == python_results == rust_results == node_results
```

### 5. Performance Tests

Benchmark tests measure performance across languages:

```go
// benchmark_test.go
func BenchmarkR96Classify(b *testing.B) {
    for i := 0; i < b.N; i++ {
        uor.R96Classify(byte(i % 256))
    }
}

func BenchmarkPhiEncode(b *testing.B) {
    for i := 0; i < b.N; i++ {
        uor.PhiEncode(byte(i%48), byte(i%256))
    }
}
```

## Continuous Integration

### GitHub Actions Workflow

```yaml
# .github/workflows/test.yml
name: Test Suite

on: [push, pull_request]

jobs:
  test:
    strategy:
      matrix:
        os: [ubuntu-latest, macos-latest, windows-latest]
        language: [go, rust, python, node]
    
    runs-on: {% raw %}${{ matrix.os }}{% endraw %}
    
    steps:
      - uses: actions/checkout@v3
      
      - name: Setup Lean
        run: |
          curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
          source ~/.profile
      
      - name: Build and Test
        run: |
          make all
          make test
          make -C runtime/{% raw %}${{ matrix.language }}{% endraw %} test
```

### Test Coverage

#### Lean Coverage
- All mathematical theorems must have proofs
- All exported functions must have verification tests
- Edge cases and boundary conditions

#### FFI Coverage
- All C API functions tested
- Memory management scenarios
- Error condition handling
- ABI compatibility verification

#### Language Binding Coverage
- All wrapper functions tested
- Type conversion edge cases
- Error handling paths
- Resource cleanup verification

## Test Data and Fixtures

### Mathematical Test Data

```lean
-- Known R96 classifications for verification
def knownR96Classifications : List (Nat × Nat) :=
  [(0, 0), (1, 1), (2, 2), ..., (255, 47)]

-- Known Φ encoding results  
def knownPhiEncodings : List ((Nat × Nat) × Nat) :=
  [((0, 0), 0), ((0, 1), 1), ((1, 0), 256), ...]
```

### Property-Based Testing

#### Go Property Tests
```go
func TestR96Properties(t *testing.T) {
    property := gopter.NewProperties(nil)
    
    property.Property("R96 classifier bounds", prop.ForAll(
        func(b byte) bool {
            class := uor.R96Classify(b)
            return class < 96
        },
        gen.UInt8(),
    ))
    
    properties.TestingRun(t)
}
```

## Writing New Tests

### Test File Organization

```
tests/
├── component/
│   ├── test_feature.c       # C tests
│   ├── test_feature.go      # Go tests  
│   ├── test_feature.py      # Python tests
│   ├── test_feature.rs      # Rust tests
│   └── test_feature.js      # Node.js tests
└── integration/
    └── cross_language_test.py  # Integration tests
```

### Test Naming Conventions

- **C Tests**: `test_<feature>_<aspect>`
- **Go Tests**: `Test<Feature><Aspect>`
- **Python Tests**: `test_<feature>_<aspect>`
- **Rust Tests**: `test_<feature>_<aspect>`
- **Node.js Tests**: `test <feature> <aspect>`

### Writing Effective Tests

#### 1. Test the Interface, Not Implementation
```go
// Good: Tests the behavior
func TestR96ClassifierRange(t *testing.T) {
    for b := 0; b < 256; b++ {
        class := uor.R96Classify(byte(b))
        assert.Less(t, class, byte(96))
    }
}

// Bad: Tests implementation details
func TestR96ClassifierLookupTable(t *testing.T) {
    // Don't test internal data structures
}
```

#### 2. Test Edge Cases
```python
def test_phi_encoding_edge_cases():
    # Test boundary values
    assert uor.phi_encode(0, 0) == 0
    assert uor.phi_encode(47, 255) == 47 * 256 + 255
    
    # Test wraparound behavior
    assert uor.phi_page(uor.phi_encode(48, 0)) == 0
```

#### 3. Use Property-Based Testing
```rust
#[cfg(test)]
mod properties {
    use proptest::prelude::*;
    
    proptest! {
        #[test]
        fn phi_encode_decode_roundtrip(page in 0u8..48, byte in 0u8..=255) {
            let encoded = uor::phi_encode(page, byte).unwrap();
            let (decoded_page, decoded_byte) = uor::phi_decode(encoded).unwrap();
            prop_assert_eq!(page, decoded_page);
            prop_assert_eq!(byte, decoded_byte);
        }
    }
}
```

## Test Maintenance

### Regular Test Review

- **Monthly**: Review test coverage reports
- **Per Release**: Update test data for new features
- **Per Bug Fix**: Add regression tests

### Performance Test Monitoring

```bash
# Run performance tests and compare
make -C tests/performance baseline  # Establish baseline
make -C tests/performance compare   # Compare against baseline
```

### Test Environment Management

```bash
# Clean test environment
make test-clean

# Reset to known state
make test-reset

# Validate test environment
make test-validate
```

This comprehensive testing framework ensures the mathematical correctness and practical reliability of the UOR Prime Structure FFI across all supported languages and platforms.