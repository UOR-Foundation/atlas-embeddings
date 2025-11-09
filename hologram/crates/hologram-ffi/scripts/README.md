# Hologram FFI Test Automation Scripts

This directory contains comprehensive test automation scripts for the hologram-ffi project.

## Scripts Overview

### `run_tests.py`

**Comprehensive Python test runner**

A full-featured test runner that executes all test suites across Rust, Python, and TypeScript interfaces.

**Features:**

- Cross-language test execution
- Coverage report generation
- Performance benchmarking
- Memory leak detection
- Detailed reporting and logging
- Parallel test execution
- JSON report generation

**Usage:**

```bash
# Run all tests
python scripts/run_tests.py

# Run with coverage
python scripts/run_tests.py --coverage

# Run with verbose output
python scripts/run_tests.py --verbose

# Run only specific language tests
python scripts/run_tests.py --rust-only
python scripts/run_tests.py --python-only
python scripts/run_tests.py --typescript-only
```

### `run_tests.sh`

**Comprehensive Shell test runner**

A shell-based test runner with the same functionality as the Python version, optimized for Unix systems.

**Features:**

- Cross-language test execution
- Coverage report generation
- Performance benchmarking
- Memory leak detection
- Colored output and logging
- JSON report generation
- Timeout handling

**Usage:**

```bash
# Run all tests
./scripts/run_tests.sh

# Run with coverage
./scripts/run_tests.sh --coverage

# Run with verbose output
./scripts/run_tests.sh --verbose

# Run only specific language tests
./scripts/run_tests.sh --rust-only
./scripts/run_tests.sh --python-only
./scripts/run_tests.sh --typescript-only
```

### `pre-commit.sh`

**Pre-commit hook script**

Fast pre-commit validation script that runs essential checks before allowing commits. Located in the repository root directory.

**Features:**

- Rust formatting check
- Rust clippy analysis
- Basic unit tests
- Python interface tests
- TypeScript interface tests
- Fast execution (< 2 minutes)

**Usage:**

```bash
# The pre-commit hook is already installed and active
# It will run automatically on every commit

# To run pre-commit checks manually:
.git/hooks/pre-commit

# To reinstall the hook (if needed):
# Copy from crates/hologram-ffi/scripts/pre-commit.sh to .git/hooks/pre-commit
```

## Test Reports

### Report Formats

Both test runners generate comprehensive reports in multiple formats:

#### JSON Report (`test_report_*.json`)

```json
{
  "timestamp": "2024-12-XX XX:XX:XX",
  "total_duration": 123.45,
  "results": {
    "rust_tests": {
      "status": "PASSED",
      "test_count": 46,
      "passed": 46,
      "failed": 0,
      "duration": 12.34
    },
    "python_tests": {
      "status": "PASSED",
      "test_count": 22,
      "passed": 22,
      "failed": 0,
      "duration": 8.76
    }
  },
  "summary": {
    "total_tests": 119,
    "passed_tests": 119,
    "failed_tests": 0,
    "success_rate": 100.0
  }
}
```

#### Log Files (`test_run_*.log`)

Detailed execution logs with timestamps and error details.

### Coverage Reports

When run with `--coverage` flag:

- **Python**: XML and HTML coverage reports
- **TypeScript**: LCOV and HTML coverage reports
- **Rust**: LLVM coverage reports (when available)

## GitHub Actions Integration

The scripts are integrated with GitHub Actions CI/CD pipeline:

### Workflow Triggers

- **Push**: On pushes to `main` and `develop` branches
- **Pull Request**: On PRs targeting `main` and `develop`
- **Schedule**: Nightly tests at 2 AM UTC
- **Manual**: On-demand execution

### Test Matrix

- **Operating Systems**: Ubuntu, macOS, Windows
- **Rust Versions**: Stable, Beta, Nightly
- **Python Versions**: 3.9, 3.10, 3.11, 3.12
- **Node.js Versions**: 18, 20, 21

### Automated Features

- Multi-platform testing
- Coverage reporting to Codecov
- Performance benchmarking
- Security auditing
- Documentation testing
- Artifact uploads

## Test Data and Fixtures

### Test Data (`tests/data/`)

- **Small vectors**: 1-10 elements
- **Medium vectors**: 100-1000 elements
- **Large vectors**: 10K-100K elements
- **Edge cases**: Empty, single element, max size
- **JSON format**: With expected results and test cases

### Test Fixtures (`tests/fixtures/`)

- **Executor fixtures**: Different configurations
- **Buffer fixtures**: Various sizes and types
- **Tensor fixtures**: 1D, 2D, 3D tensors
- **Operation fixtures**: Known inputs/outputs
- **Error fixtures**: Error condition testing
- **Cross-language**: Python, TypeScript, Rust

## Performance Testing

### Benchmarking

- **Rust benchmarks**: Using Criterion
- **Python benchmarks**: Using pytest-benchmark
- **TypeScript benchmarks**: Using Jest
- **Memory usage**: Leak detection and analysis
- **Regression detection**: Automated performance monitoring

### Performance Targets

- **Rust**: < 5% overhead vs direct hologram-core usage
- **Python**: < 10% overhead vs native Python
- **TypeScript**: < 15% overhead vs native JavaScript
- **Memory**: Zero memory leaks confirmed

## Troubleshooting

### Common Issues

#### Test Failures

1. **Check dependencies**: Ensure all language runtimes are installed
2. **Check permissions**: Ensure scripts are executable
3. **Check paths**: Ensure you're in the correct directory
4. **Check logs**: Review detailed log files for specific errors

#### Performance Issues

1. **Check system resources**: Ensure sufficient memory/CPU
2. **Check parallel execution**: Disable if causing issues
3. **Check timeout settings**: Increase if tests are slow
4. **Check baseline**: Verify performance baselines are current

#### Coverage Issues

1. **Check tool installation**: Ensure coverage tools are installed
2. **Check file paths**: Verify coverage file locations
3. **Check permissions**: Ensure write access to output directories
4. **Check format**: Verify coverage report formats are correct

### Debug Mode

Run with verbose output for detailed debugging:

```bash
python scripts/run_tests.py --verbose
./scripts/run_tests.sh --verbose
```

### Log Analysis

Review log files for detailed execution information:

```bash
# View latest log
tail -f test_run_*.log

# Search for errors
grep -i error test_run_*.log

# Search for specific test
grep "test_name" test_run_*.log
```

## Contributing

### Adding New Tests

1. Follow existing test patterns
2. Update test data if needed
3. Add fixtures for reusable components
4. Update documentation

### Modifying Scripts

1. Maintain backward compatibility
2. Update documentation
3. Test on multiple platforms
4. Update CI/CD if needed

### Performance Optimization

1. Profile script execution
2. Optimize slow operations
3. Add parallel execution where possible
4. Update performance baselines

## Support

For issues with test automation:

1. Check this documentation
2. Review log files
3. Check GitHub Actions logs
4. Create an issue with detailed information

## License

These scripts are part of the hologram-ffi project and follow the same license terms.
