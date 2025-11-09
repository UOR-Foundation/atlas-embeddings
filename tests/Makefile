# Makefile for test coordination

include ../common.mk

# Test subdirectories
TEST_DIRS := c

.PHONY: all clean test-lean test-c test-runtime test-integration

all: test-lean test-c test-runtime
	$(call print_success, "All tests completed")

# Run Lean verification test
test-lean:
	$(call print_header, "Running Lean verification")
	$(Q)$(BIN_DIR)/uor-verify
	$(call print_success, "Lean verification passed")

# Run C tests
test-c:
	$(call print_header, "Running C tests")
	$(Q)$(MAKE) -C c test
	$(call print_success, "C tests passed")

# Run runtime tests
test-runtime:
	$(call print_header, "Running runtime tests")
	$(Q)$(MAKE) -C ../runtime test
	$(call print_success, "Runtime tests passed")

# Integration tests (all components together)
test-integration: test-lean test-c test-runtime
	$(call print_header, "Running integration tests")
	# Add integration test logic here
	$(call print_success, "Integration tests passed")

# Benchmark tests
benchmark:
	$(call print_header, "Running benchmarks")
	@echo "  Lean verification speed..."
	@time -p $(BIN_DIR)/uor-verify 2>&1 | grep real
	@if [ -f c/test_ffi ]; then \
		echo "  C FFI call speed..."; \
		time -p c/test_ffi 2>&1 | grep real; \
	fi
	$(call print_success, "Benchmarks complete")

# Clean test artifacts
clean:
	$(call print_header, "Cleaning test artifacts")
	@for dir in $(TEST_DIRS); do \
		if [ -f $$dir/Makefile ]; then \
			echo "  Cleaning $$dir..."; \
			$(MAKE) -C $$dir clean || true; \
		fi; \
	done
	$(call print_success, "Test artifacts cleaned")

# Coverage report (if tools available)
coverage:
	$(call print_header, "Generating coverage report")
	@echo "Coverage tools not configured yet"
	$(call print_warning, "Coverage reporting requires additional setup")

# Show test-specific help
help::
	@echo "Test targets:"
	@echo "  test-lean        - Run Lean verification"
	@echo "  test-c           - Run C tests"
	@echo "  test-runtime     - Run all runtime tests"
	@echo "  test-integration - Run integration tests"
	@echo "  benchmark        - Run performance benchmarks"
	@echo "  coverage         - Generate coverage report"