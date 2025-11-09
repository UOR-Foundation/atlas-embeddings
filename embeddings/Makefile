# UOR-FFI Root Makefile
# Coordinates builds across all subdirectories

include common.mk

# Subdirectories with their own Makefiles
SUBDIRS := lean ffi runtime tests pkg

# Main targets
.PHONY: all clean test install uninstall lean ffi runtime tests check format


dockerup:
	$(call print_header, "Starting Docker container")
	$(Q)docker-compose up -d
	$(call print_success, "Docker container started")

dockerdown:
	$(call print_header, "Stopping Docker container")
	$(Q)docker-compose down
	$(call print_success, "Docker container stopped")

all: lean ffi runtime
	$(call print_success, "Build complete")

# Build Lean library first (dependency for everything else)
lean:
	$(call print_header, "Building Lean library")
	$(Q)$(MAKE) -C lean all

# Build FFI components (depends on Lean)
ffi: lean
	$(call print_header, "Building FFI components")
	$(Q)$(MAKE) -C ffi all

# Build runtime wrappers (depends on lean and ffi)
runtime: lean ffi
	$(call print_header, "Building runtime wrappers")
	$(Q)$(MAKE) -C runtime all

# Run all tests
test: all
	$(call print_header, "Running all tests")
	$(Q)$(MAKE) -C tests all
	$(call print_success, "All tests passed")

# Quick check - just run lean verification
check: lean
	$(call print_header, "Running quick verification")
	$(Q)$(BIN_DIR)/uor-verify
	$(call print_success, "Verification passed")

# Clean all subdirectories
clean:
	$(call print_header, "Cleaning all build artifacts")
	@for dir in $(SUBDIRS); do \
		if [ -f $$dir/Makefile ]; then \
			echo "  Cleaning $$dir..."; \
			$(MAKE) -C $$dir clean || exit 1; \
		fi; \
	done
	$(Q)$(RMDIR) $(BUILD_DIR)
	$(call print_success, "Clean complete")

# Install everything
install: all
	$(call print_header, "Installing UOR-FFI")
	$(Q)$(MAKE) -C lean install
	$(Q)$(MAKE) -C ffi install
	$(Q)$(MAKE) -C pkg install
	$(call print_success, "Installation complete")

# Uninstall everything
uninstall:
	$(call print_header, "Uninstalling UOR-FFI")
	$(Q)$(MAKE) -C lean uninstall
	$(Q)$(MAKE) -C ffi uninstall
	$(Q)$(MAKE) -C pkg uninstall
	$(call print_success, "Uninstallation complete")

# Format code (if formatters are available)
format:
	$(call print_header, "Formatting code")
	@which lean4-format >/dev/null 2>&1 && find lean -name "*.lean" -exec lean4-format -i {} \; || true
	@which clang-format >/dev/null 2>&1 && find ffi tests -name "*.[ch]" -exec clang-format -i {} \; || true
	@which gofmt >/dev/null 2>&1 && find runtime/go -name "*.go" -exec gofmt -w {} \; || true
	@which rustfmt >/dev/null 2>&1 && cd runtime/rust && cargo fmt || true
	$(call print_success, "Formatting complete")

# Build documentation
docs:
	$(call print_header, "Building documentation")
	$(Q)$(MAKE) -C docs-src clean build

# Show help
help::
	@echo "UOR-FFI Build System"
	@echo "===================="
	@echo ""
	@echo "Main targets:"
	@echo "  make all      - Build everything (lean, ffi, runtime)"
	@echo "  make lean     - Build Lean library only"
	@echo "  make ffi      - Build FFI components"
	@echo "  make runtime  - Build all language wrappers"
	@echo "  make test     - Run all tests"
	@echo "  make check    - Quick verification test"
	@echo "  make clean    - Remove all build artifacts"
	@echo "  make install  - Install libraries and headers"
	@echo "  make format   - Format source code"
	@echo "  make docs     - Build documentation"
	@echo ""
	@echo "Subdirectory targets:"
	@echo "  make -C lean all    - Build Lean components"
	@echo "  make -C runtime/go  - Build Go wrapper"
	@echo "  make -C runtime/rust - Build Rust wrapper"
	@echo "  make -C runtime/node - Build Node wrapper"
	@echo "  make -C tests all   - Run all tests"
	@echo ""

# Dependency graph visualization (requires graphviz)
depgraph:
	@echo "digraph dependencies {" > deps.dot
	@echo "  lean -> ffi;" >> deps.dot
	@echo "  lean -> runtime;" >> deps.dot
	@echo "  ffi -> runtime;" >> deps.dot
	@echo "  runtime -> tests;" >> deps.dot
	@echo "}" >> deps.dot
	@dot -Tpng deps.dot -o dependencies.png 2>/dev/null && \
		echo "Dependency graph saved to dependencies.png" || \
		echo "Install graphviz to generate dependency graph"
	@rm -f deps.dot

.PHONY: depgraph docs