# Hologram FFI Update Prompt

This document provides a comprehensive prompt for updating the `hologram-ffi` crate and all its language bindings after changes to the `hologram-core` crate.

## When to Use This Prompt

Use this prompt when:

- `hologram-core` has been updated with new APIs, functions, or breaking changes
- New types, operations, or interfaces have been added to `hologram-core`
- The FFI needs to be synchronized with the latest `hologram-core` changes
- Language bindings (Python, TypeScript, WASM) need to be regenerated

## Complete Update Prompt

```
I need to update the hologram-ffi crate and all its language bindings to reflect recent changes in the hologram-core crate. Please help me with the following comprehensive update process:

## 1. Analyze hologram-core Changes

First, please analyze the current state of hologram-core and identify:
- What new APIs, functions, or types have been added
- What existing APIs have been modified or removed
- What breaking changes have been introduced
- What new dependencies or imports are required

## 2. Update FFI Core Components

Please update the following FFI components:

### A. Update Cargo.toml Dependencies
- Review and update dependencies in `crates/hologram-ffi/Cargo.toml`
- Add any new required dependencies (e.g., atlas-backends, atlas-runtime)
- Update version constraints if needed
- Ensure all hologram-core dependencies are properly specified

### B. Update UDL Interface Definition
- Review `crates/hologram-ffi/src/hologram_ffi.udl`
- Add new functions that correspond to new hologram-core APIs
- Update existing function signatures if they've changed
- Add new types if hologram-core has introduced new types
- Ensure all hologram-core functionality is properly exposed

### C. Update Rust Implementation
- Update `crates/hologram-ffi/src/handles.rs` to implement new functions
- Update `crates/hologram-ffi/src/utils.rs` for utility functions
- Update `crates/hologram-ffi/src/advanced.rs` for advanced operations
- Update `crates/hologram-ffi/src/lib.rs` to export new functions
- Fix any compilation errors due to API changes

### D. Handle Breaking Changes
- Update function signatures to match new hologram-core APIs
- Update error handling if error types have changed
- Update imports to use new module structure
- Handle any changes to executor, buffer, or tensor APIs

## 3. Rebuild and Regenerate Bindings

Please help me rebuild the library and regenerate all language bindings:

### A. Clean and Build
- Clean previous builds: `cargo clean`
- Build the library: `cargo build --release`
- Generate UniFFI bindings: `cargo run --bin generate-bindings`

### B. Update Python Bindings
- Regenerate Python bindings from UDL
- Update `crates/hologram-ffi/interfaces/python/hologram_ffi/` package
- Install updated package: `pip install -e . --force-reinstall`
- Update Python examples if needed
- Update Python tests to match new APIs

### C. Update TypeScript Bindings
- Update `crates/hologram-ffi/interfaces/typescript/src/index.ts` with new function signatures
- Update TypeScript examples in `crates/hologram-ffi/interfaces/typescript/examples/`
- Update TypeScript tests in `crates/hologram-ffi/interfaces/typescript/tests/`
- Ensure mock implementations match new APIs

### D. Update WASM Bindings (if applicable)
- Update WASM interface if WASM support is enabled
- Update `crates/hologram-ffi/interfaces/wasm/` if it exists
- Handle any WASM-specific compilation issues

## 4. Update Tests and Examples

Please update all tests and examples comprehensively:

### A. Rust Tests
Update the following Rust test files:

#### Unit Tests (`crates/hologram-ffi/tests/unit_tests.rs`)
- Update tests for new functions and API changes
- Fix any test failures due to API signature changes
- Add unit tests for new functionality
- Ensure all boolean return value assertions are correct (u8 vs bool)
- Update tests for executor, buffer, tensor, and compiler operations
- Add tests for new Atlas state management functions
- Update error handling tests for new error types

#### Integration Tests (`crates/hologram-ffi/tests/integration_tests.rs`)
- Update integration scenarios for new APIs
- Fix any test failures due to API behavior changes
- Add integration tests for new functionality
- Update memory management tests
- Update tensor operation integration tests
- Update compiler infrastructure integration tests
- Update Atlas state management integration tests

#### Additional Rust Tests
- `crates/hologram-ffi/tests/compile_test.rs` - Ensure compilation works
- `crates/hologram-ffi/tests/minimal_test.rs` - Basic functionality tests
- Any other test files in the `tests/` directory

### B. Python Tests
Update the comprehensive Python test suite:

#### Main Test File (`crates/hologram-ffi/interfaces/python/tests/test_hologram_ffi.py`)
- Update `TestBasicOperations` class for new basic functions
- Update `TestExecutorManagement` class for executor API changes
- Update `TestBufferOperations` class for buffer API changes
- Update `TestTensorOperations` class for tensor API changes
- Update `TestErrorHandling` class for new error types
- Update `TestMemoryManagement` class for memory API changes
- Update `TestPerformance` class for performance testing
- Fix PoisonError handling in setUp methods
- Update boundary buffer allocation tests
- Add tests for new functionality

#### Additional Python Tests
- `crates/hologram-ffi/interfaces/python/tests/memory_leak_detection.py`
- `crates/hologram-ffi/interfaces/python/tests/cross_platform_compatibility.py`
- Any other Python test files

### C. TypeScript Tests
Update the comprehensive TypeScript test suite:

#### Main Test File (`crates/hologram-ffi/interfaces/typescript/tests/hologram_ffi.test.ts`)
- Update `Core Functions` test suite for new basic functions
- Update `Executor Management` test suite for executor API changes
- Update `Buffer Operations` test suite for buffer API changes
- Update `Mathematical Operations` test suite for math API changes
- Update `Tensor Operations` test suite for tensor API changes
- Update `Atlas State Management` test suite for Atlas API changes
- Update `Compiler Infrastructure` test suite for compiler API changes
- Update `Error Handling` test suite for new error types
- Update `Performance` test suite for performance testing
- Update `Memory Management` test suite for memory API changes
- Update mock implementations to match new APIs
- Ensure all 51+ tests pass

#### Performance Tests (`crates/hologram-ffi/interfaces/typescript/examples/performance_benchmarks.ts`)
- Update performance benchmarks for new APIs
- Fix any TypeScript compilation errors
- Update matrix operations benchmarks
- Update memory management benchmarks
- Update compiler infrastructure benchmarks

### D. Examples
Update all example files to demonstrate new functionality:

#### Python Examples (`crates/hologram-ffi/interfaces/python/examples/`)
- `basic_operations.py` - Update for new basic functions
- `executor_management.py` - Update for executor API changes
- `buffer_operations.py` - Update for buffer API changes
- `tensor_operations.py` - Update for tensor API changes
- `error_handling.py` - Update for new error types
- `performance_benchmarks.py` - Update for performance testing
- `simple_executor_example.py` - Update for executor changes
- `simple_tensor_example.py` - Update for tensor changes

#### TypeScript Examples (`crates/hologram-ffi/interfaces/typescript/examples/`)
- `basic_operations.ts` - Update for new basic functions
- `executor_management.ts` - Update for executor API changes
- `buffer_operations.ts` - Update for buffer API changes
- `tensor_operations.ts` - Update for tensor API changes
- `error_handling.ts` - Update for new error types
- `performance_benchmarks.ts` - Update for performance testing
- `integration_tests.ts` - Update for integration scenarios

#### WASM Examples (if applicable)
- Update any WASM examples if WASM support is enabled
- Handle any WASM-specific compilation issues

## 5. Update Documentation

Please update documentation:

### A. Update COMPLETE_COVERAGE_PLAN.md
- Update function counts and coverage percentages
- Mark completed phases as complete
- Add new phases if new functionality has been added
- Update implementation notes

### B. Update README files
- Update `crates/hologram-ffi/interfaces/python/README.md`
- Update `crates/hologram-ffi/interfaces/typescript/README.md`
- Update main `crates/hologram-ffi/README.md` if it exists

### C. Update API Documentation
- Ensure all new functions are properly documented
- Update function signatures in documentation
- Add examples for new functionality

## 6. Verification and Testing

Please help me verify the update comprehensively:

### A. Compilation Verification
- Ensure `cargo check` passes without errors
- Ensure `cargo build --release` succeeds
- Fix any compilation errors
- Verify all test targets compile: `cargo test --no-run`

### B. Test Execution
Run all test suites to ensure they pass:

#### Rust Tests
- Run all Rust tests: `cargo test -- --nocapture --color=always`
- Run specific test suites:
  - `cargo test --test unit_tests -- --nocapture --color=always`
  - `cargo test --test integration_tests -- --nocapture --color=always`
  - `cargo test --test compile_test -- --nocapture --color=always`
  - `cargo test --test minimal_test -- --nocapture --color=always`
- Ensure all tests pass without PoisonError or handle issues
- Fix any test failures due to API changes

#### Python Tests
- Run Python tests: `python -m pytest tests -v`
- Run specific test classes:
  - `python -m pytest tests/test_hologram_ffi.py::TestBasicOperations -v`
  - `python -m pytest tests/test_hologram_ffi.py::TestExecutorManagement -v`
  - `python -m pytest tests/test_hologram_ffi.py::TestBufferOperations -v`
  - `python -m pytest tests/test_hologram_ffi.py::TestTensorOperations -v`
  - `python -m pytest tests/test_hologram_ffi.py::TestErrorHandling -v`
  - `python -m pytest tests/test_hologram_ffi.py::TestMemoryManagement -v`
  - `python -m pytest tests/test_hologram_ffi.py::TestPerformance -v`
- Run additional Python tests:
  - `python -m pytest tests/memory_leak_detection.py -v`
  - `python -m pytest tests/cross_platform_compatibility.py -v`
- Ensure all tests pass without PoisonError issues
- Fix any test failures due to API changes

#### TypeScript Tests
- Run TypeScript tests: `npm test`
- Ensure all 51+ tests pass
- Fix any TypeScript compilation errors
- Update mock implementations if needed
- Verify performance benchmarks compile and run

#### Comprehensive Test Runner
- Use the test runner script: `python run_tests.py` (if available)
- Use the shell test runner: `./scripts/run_tests.sh` (if available)
- Verify all test suites pass across all languages

### C. Example Verification
Run all examples to ensure they work with new APIs:

#### Python Examples
- `python examples/basic_operations.py`
- `python examples/executor_management.py`
- `python examples/buffer_operations.py`
- `python examples/tensor_operations.py`
- `python examples/error_handling.py`
- `python examples/performance_benchmarks.py`
- `python examples/simple_executor_example.py`
- `python examples/simple_tensor_example.py`

#### TypeScript Examples
- `npx ts-node examples/basic_operations.ts`
- `npx ts-node examples/executor_management.ts`
- `npx ts-node examples/buffer_operations.ts`
- `npx ts-node examples/tensor_operations.ts`
- `npx ts-node examples/error_handling.ts`
- `npx ts-node examples/performance_benchmarks.ts`
- `npx ts-node examples/integration_tests.ts`

#### WASM Examples (if applicable)
- Run any WASM examples if WASM support is enabled
- Verify WASM compilation and execution

### D. Performance Verification
- Run performance benchmarks to ensure they still work
- Verify performance hasn't regressed significantly
- Update performance baselines if needed
- Test memory usage and leak detection

## 7. Handle Common Issues

Please help me handle common issues that may arise:

### A. PoisonError Issues
- If Python tests fail with PoisonError, ensure the `lock_registry` function is properly implemented
- Rebuild the library and regenerate Python bindings
- Update Python tests to handle PoisonError gracefully

### B. Compilation Errors
- Fix any import errors due to module structure changes
- Update function signatures to match new APIs
- Handle any breaking changes in dependencies

### C. Test Failures
- Update test expectations to match new API behavior
- Fix any test logic that depends on old API behavior
- Add tests for new functionality

### D. Binding Generation Issues
- Ensure UniFFI can generate bindings for all new types
- Handle any complex types that need special serialization
- Update UDL if new types require special handling

## 8. Final Steps

Please help me complete the update:

### A. Clean Up
- Remove any temporary files created during the update
- Clean up any unused imports or functions
- Ensure code follows project conventions

### B. Update Version
- Update version numbers if this is a significant update
- Update changelog if one exists
- Tag the release if appropriate

### C. Documentation
- Update this PROMPT.md file if new patterns emerge
- Document any new update procedures discovered
- Add notes about any special considerations for future updates

## Expected Outcome

After completing this update process:
- The hologram-ffi crate should compile without errors
- All language bindings (Python, TypeScript, WASM) should be up to date
- All tests should pass
- All examples should work with the new APIs
- Documentation should reflect the current state
- The FFI should provide complete coverage of hologram-core functionality

Please proceed step by step and let me know if you encounter any issues or need clarification on any part of this process.
```

## Usage Instructions

1. **Copy the prompt above** when you need to update the FFI after hologram-core changes
2. **Paste it into your AI assistant** (like Claude, ChatGPT, etc.)
3. **Follow the step-by-step guidance** provided by the assistant
4. **Update this PROMPT.md file** if you discover new patterns or procedures

## Quick Reference Commands

```bash
# Clean and rebuild
cd /workspace/crates/hologram-ffi
cargo clean
cargo build --release
cargo run --bin generate-bindings

# Update Python bindings
cd interfaces/python
pip install -e . --force-reinstall

# Run all tests comprehensively
cargo test -- --nocapture --color=always
python -m pytest tests -v
cd ../typescript && npm test

# Run specific test suites
cargo test --test unit_tests -- --nocapture --color=always
cargo test --test integration_tests -- --nocapture --color=always
cargo test --test compile_test -- --nocapture --color=always
cargo test --test minimal_test -- --nocapture --color=always

# Run Python test classes individually
python -m pytest tests/test_hologram_ffi.py::TestBasicOperations -v
python -m pytest tests/test_hologram_ffi.py::TestExecutorManagement -v
python -m pytest tests/test_hologram_ffi.py::TestBufferOperations -v
python -m pytest tests/test_hologram_ffi.py::TestTensorOperations -v
python -m pytest tests/test_hologram_ffi.py::TestErrorHandling -v
python -m pytest tests/test_hologram_ffi.py::TestMemoryManagement -v
python -m pytest tests/test_hologram_ffi.py::TestPerformance -v

# Run additional Python tests
python -m pytest tests/memory_leak_detection.py -v
python -m pytest tests/cross_platform_compatibility.py -v

# Run examples
python examples/basic_operations.py
python examples/executor_management.py
python examples/buffer_operations.py
python examples/tensor_operations.py
python examples/error_handling.py
python examples/performance_benchmarks.py

# Run TypeScript examples
npx ts-node examples/basic_operations.ts
npx ts-node examples/executor_management.ts
npx ts-node examples/buffer_operations.ts
npx ts-node examples/tensor_operations.ts
npx ts-node examples/error_handling.ts
npx ts-node examples/performance_benchmarks.ts

# Use comprehensive test runners (if available)
python run_tests.py
./scripts/run_tests.sh
```

## Common Issues and Solutions

### PoisonError in Python Tests

- **Cause**: Old compiled library without `lock_registry` function
- **Solution**: Rebuild library and regenerate Python bindings

### Compilation Errors

- **Cause**: API changes in hologram-core
- **Solution**: Update imports, function signatures, and dependencies

### Test Failures

- **Cause**: API behavior changes
- **Solution**: Update test expectations and add tests for new functionality

### Binding Generation Failures

- **Cause**: New types not supported by UniFFI
- **Solution**: Update UDL with proper type definitions

## Test Coverage Overview

This section documents the comprehensive test coverage implemented in the hologram-ffi crate:

### Rust Test Coverage

- **Unit Tests** (`tests/unit_tests.rs`): ~50+ individual function tests
- **Integration Tests** (`tests/integration_tests.rs`): ~15+ integration scenarios
- **Compile Tests** (`tests/compile_test.rs`): Compilation verification
- **Minimal Tests** (`tests/minimal_test.rs`): Basic functionality tests

### Python Test Coverage

- **Main Test Suite** (`tests/test_hologram_ffi.py`): 7 test classes, 22+ test methods
  - `TestBasicOperations`: Version, Atlas phase, resonance
  - `TestExecutorManagement`: Executor creation, phase, resonance, topology
  - `TestBufferOperations`: Buffer creation, operations, properties
  - `TestTensorOperations`: Tensor creation, operations, properties, slicing
  - `TestErrorHandling`: Invalid handles, error conditions
  - `TestMemoryManagement`: Resource cleanup, multiple cleanup
  - `TestPerformance`: Performance benchmarks
- **Additional Tests**:
  - `memory_leak_detection.py`: Memory leak detection
  - `cross_platform_compatibility.py`: Cross-platform compatibility

### TypeScript Test Coverage

- **Main Test Suite** (`tests/hologram_ffi.test.ts`): 51+ tests across 8 test suites
  - Core Functions: Version, phase, advance phase
  - Executor Management: 8 tests for executor operations
  - Buffer Operations: 10 tests for buffer operations
  - Mathematical Operations: 5 tests for math operations
  - Tensor Operations: 12 tests for tensor operations
  - Atlas State Management: 4 tests for Atlas operations
  - Compiler Infrastructure: 3 tests for compiler operations
  - Error Handling: 3 tests for error conditions
  - Performance: 2 tests for performance
  - Memory Management: 2 tests for memory management
- **Performance Tests** (`examples/performance_benchmarks.ts`): Comprehensive benchmarks

### Example Coverage

- **Python Examples**: 8 example files demonstrating all functionality
- **TypeScript Examples**: 7 example files with comprehensive demonstrations
- **WASM Examples**: Mock implementations (WASM support deferred)

### Test Infrastructure

- **Test Runners**: `run_tests.py`, `scripts/run_tests.sh`
- **PoisonError Handling**: Graceful handling of registry poisoning
- **Mock Implementations**: TypeScript mock for development without native FFI
- **Performance Benchmarks**: Comprehensive performance testing across languages

## Common Issues and Solutions

### PoisonError in Python Tests

- **Cause**: Old compiled library without `lock_registry` function
- **Solution**: Rebuild library and regenerate Python bindings
- **Prevention**: Always rebuild after API changes

### Compilation Errors

- **Cause**: API changes in hologram-core
- **Solution**: Update imports, function signatures, and dependencies
- **Common Issues**:
  - Boolean vs u8 return type mismatches
  - Missing dependencies (atlas-backends)
  - Changed function signatures

### Test Failures

- **Cause**: API behavior changes
- **Solution**: Update test expectations and add tests for new functionality
- **Common Issues**:
  - Handle consumption in tensor operations
  - Boundary buffer allocation failures
  - Zero-length buffer restrictions

### Binding Generation Failures

- **Cause**: New types not supported by UniFFI
- **Solution**: Update UDL with proper type definitions
- **Common Issues**:
  - Complex types requiring JSON serialization
  - Optional parameters in UDL
  - Reserved keywords in TypeScript

## Maintenance Notes

- Update this prompt whenever new update patterns are discovered
- Document any special procedures for specific types of changes
- Keep the quick reference commands up to date
- Add new common issues and solutions as they arise
