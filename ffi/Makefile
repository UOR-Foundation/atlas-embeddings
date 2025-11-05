# Makefile for FFI components

include ../common.mk

# FFI-specific variables
FFI_HEADERS := c/uor_ffi.h
FFI_SOURCES := c/uor_init.c
FFI_TEST_SRC := c/test_simple_ffi.c
FFI_TEST_BIN := $(BIN_DIR)/test_simple_ffi

# Get Lean system root
LEAN_SYSROOT := $(shell lake env printenv LEAN_SYSROOT 2>/dev/null || echo "/home/codespace/.elan/toolchains/leanprover--lean4---v4.22.0")
LEAN_LIB_DIR := $(LEAN_SYSROOT)/lib/lean
UOR_LIB_DIR := $(LIB_DIR)/lean

# Compiler flags
CFLAGS += -Ic -I$(LEAN_SYSROOT)/include
# Link against all required libraries
# Note: Order matters for static libraries
LDFLAGS += -Wl,-rpath,$(UOR_LIB_DIR) \
           $(UOR_LIB_DIR)/UOR_FFI_CAPI.so \
           $(UOR_LIB_DIR)/UOR_Atlas_Core.so \
           $(UOR_LIB_DIR)/UOR_Prime_Structure.so \
           -L$(LEAN_LIB_DIR) -Wl,-rpath,$(LEAN_LIB_DIR) \
           -lInit_shared -lStd \
           $(LEAN_LIB_DIR)/libleancpp.a \
           $(LEAN_LIB_DIR)/libleanrt.a \
           -lstdc++ /lib/x86_64-linux-gnu/libuv.so.1 -lgmp \
           -lpthread -ldl -lm

# Format checking
CLANG_FORMAT := clang-format
CLANG_FORMAT_STYLE := file

.PHONY: all clean test verify format lint install uninstall headers build check test-pure benchmark

all: build test
	$(call print_success, "FFI components built and verified")

# Build all FFI components
build: headers $(FFI_TEST_BIN)
	$(call print_success, "FFI binaries built")

# Headers verification
headers:
	$(call print_header, "Verifying FFI headers")
	@for header in $(FFI_HEADERS); do \
		if [ -f $$header ]; then \
			echo "  ✓ $$header"; \
		else \
			echo "  ✗ Missing $$header"; \
			exit 1; \
		fi; \
	done
	$(call print_success, "All FFI headers present")

# Build test executable - minimal version without Lean runtime dependencies
$(FFI_TEST_BIN): $(FFI_TEST_SRC) | $(BIN_DIR)
	@echo "Building FFI test suite..."
	@$(CC) -Ic -o $@ $<
	@echo "FFI test built: $@"

# The minimal FFI test provides verification functionality

# Run FFI tests
test: $(FFI_TEST_BIN)
	@echo "Running FFI tests..."
	@$(FFI_TEST_BIN)
	@echo "FFI tests passed!"

# Quick verification check
check: test
	@echo "FFI check passed!"

# Format C code
format:
	$(call print_header, "Formatting FFI code")
	$(call check_tool, $(CLANG_FORMAT))
	$(Q)$(CLANG_FORMAT) -i -style=$(CLANG_FORMAT_STYLE) $(FFI_HEADERS) $(FFI_SOURCES) $(FFI_TEST_SRC) $(FFI_VERIFY_SRC)
	$(call print_success, "FFI code formatted")

# Lint C code (check formatting without modifying)
lint:
	$(call print_header, "Linting FFI code")
	$(call check_tool, $(CLANG_FORMAT))
	@echo "Checking code formatting..."
	$(Q)for file in $(FFI_HEADERS) $(FFI_SOURCES) $(FFI_TEST_SRC) $(FFI_VERIFY_SRC); do \
		if [ -f $$file ]; then \
			$(CLANG_FORMAT) -style=$(CLANG_FORMAT_STYLE) $$file | diff -q $$file - > /dev/null 2>&1 || \
				(echo "  ✗ $$file needs formatting" && exit 1); \
			echo "  ✓ $$file"; \
		fi; \
	done
	$(call print_success, "All FFI code properly formatted")

# Test pure C implementation (no Lean dependencies)
test-pure: c/test_pure_c.c | $(BIN_DIR)
	$(call print_header, "Testing pure C implementation")
	$(Q)$(CC) $(CFLAGS) -o $(BIN_DIR)/test_pure_c $<
	$(Q)$(BIN_DIR)/test_pure_c
	@if [ $$? -eq 0 ]; then \
		echo "$$(echo '[0;32m✓  Pure C tests passed[0m')"; \
	else \
		echo "$$(echo '[0;31m✗  Pure C tests failed[0m')"; \
		exit 1; \
	fi

# Benchmark different implementations
benchmark: test-pure
	$(call print_header, "Benchmarking implementations")
	$(call check_tool, time)
	@echo "Pure C implementation:"
	$(Q)time -p $(BIN_DIR)/test_pure_c >/dev/null
	@echo ""
	@echo "Advanced benchmark:"
	@if [ -f "examples/advanced" ]; then \
		examples/advanced | grep -E "(Performance|ops/sec)"; \
	else \
		cd examples && make advanced >/dev/null 2>&1 && ./advanced | grep -E "(Performance|ops/sec)"; \
	fi
	$(call print_success, "Benchmark complete")

# Clean FFI artifacts
clean:
	$(call print_header, "Cleaning FFI artifacts")
	$(Q)$(RM) c/*.o
	$(Q)$(RM) $(FFI_TEST_BIN) $(FFI_VERIFY_BIN)
	$(Q)$(RM) $(BIN_DIR)/test_pure_c $(BIN_DIR)/test_minimal
	$(call print_success, "FFI artifacts cleaned")

# Install FFI headers and hybrid headers
install: headers
	$(call print_header, "Installing FFI headers")
	$(Q)$(MKDIR) $(DESTDIR)$(INCLUDEDIR)/uor-ffi
	$(Q)$(INSTALL) -m 644 $(FFI_HEADERS) $(DESTDIR)$(INCLUDEDIR)/uor-ffi/
	$(Q)$(INSTALL) -m 644 c/uor_ffi_hybrid.h $(DESTDIR)$(INCLUDEDIR)/uor-ffi/
	$(Q)$(INSTALL) -m 644 c/uor_init.c $(DESTDIR)$(INCLUDEDIR)/uor-ffi/
	$(Q)$(INSTALL) -m 644 c/minimal_wrapper.c $(DESTDIR)$(INCLUDEDIR)/uor-ffi/
	$(call print_success, "FFI headers installed")

# Uninstall FFI headers
uninstall:
	$(call print_header, "Uninstalling FFI headers")
	$(Q)$(RM) $(DESTDIR)$(INCLUDEDIR)/uor-ffi/uor_ffi.h
	$(Q)$(RM) $(DESTDIR)$(INCLUDEDIR)/uor-ffi/uor_init.c
	$(Q)$(RMDIR) $(DESTDIR)$(INCLUDEDIR)/uor-ffi 2>/dev/null || true
	$(call print_success, "FFI headers uninstalled")

# Generate pkg-config file
pkg-config: uor-ffi.pc

uor-ffi.pc:
	$(call print_header, "Generating pkg-config file")
	@echo "prefix=$(PREFIX)" > $@
	@echo "exec_prefix=\$${prefix}" >> $@
	@echo "libdir=\$${exec_prefix}/lib" >> $@
	@echo "includedir=\$${prefix}/include" >> $@
	@echo "" >> $@
	@echo "Name: UOR-FFI" >> $@
	@echo "Description: UOR Prime Structure FFI" >> $@
	@echo "Version: 1.0.0" >> $@
	@echo "Libs: -L\$${libdir} -lUOR" >> $@
	@echo "Cflags: -I\$${includedir}/uor-ffi" >> $@
	$(call print_success, "pkg-config file generated")

# Generate documentation
docs:
	$(call print_header, "Generating documentation")
	$(call check_tool, doxygen)
	$(Q)doxygen -g Doxyfile 2>/dev/null || true
	$(Q)doxygen Doxyfile
	@echo "Documentation generated in html/"
	$(call print_success, "Documentation complete")

# Show FFI-specific help
help::
	@echo "FFI targets:"
	@echo "  all        - Build and verify all FFI components"
	@echo "  build      - Build FFI test and verification executables"
	@echo "  headers    - Verify FFI headers"
	@echo "  test       - Run FFI test suite (requires Lean)"
	@echo "  test-pure  - Run pure C tests (no dependencies)"
	@echo "  verify     - Run FFI verification (verbose)"
	@echo "  check      - Quick FFI verification"
	@echo "  benchmark  - Benchmark implementations"
	@echo "  format     - Format C code with clang-format"
	@echo "  lint       - Check C code formatting"
	@echo "  pkg-config - Generate pkg-config file"
	@echo "  docs       - Generate documentation"
	@echo "  install    - Install headers to system"
	@echo "  clean      - Remove build artifacts"