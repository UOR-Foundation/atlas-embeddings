# Makefile for runtime wrappers

include ../common.mk

# Subdirectories for each language runtime
RUNTIME_DIRS := go rust node python

.PHONY: all clean test install $(RUNTIME_DIRS)

all: $(RUNTIME_DIRS)
	$(call print_success, "All runtime wrappers built")

# Build Go wrapper
go:
	$(call print_header, "Building Go wrapper")
	@if which go >/dev/null 2>&1; then \
		$(MAKE) -C go all; \
	else \
		echo "Error: Go not found. Install Go toolchain." && exit 1; \
	fi

# Build Rust wrapper
rust:
	$(call print_header, "Building Rust wrapper")
	@if [ -f "$$HOME/.cargo/env" ]; then . "$$HOME/.cargo/env"; fi; \
	if which cargo >/dev/null 2>&1; then \
		$(MAKE) -C rust all; \
	else \
		echo "Error: Cargo not found. Install Rust toolchain." && exit 1; \
	fi

# Build Node.js wrapper
node:
	$(call print_header, "Building Node.js wrapper")
	@if which npm >/dev/null 2>&1; then \
		$(MAKE) -C node all; \
	else \
		echo "Error: npm not found. Install Node.js and npm." && exit 1; \
	fi

# Build Python wrapper
python:
	$(call print_header, "Building Python wrapper")
	@if which python3 >/dev/null 2>&1; then \
		$(MAKE) -C python all; \
	else \
		echo "Error: Python 3 not found. Install Python 3." && exit 1; \
	fi

# Run tests for all wrappers
test:
	$(call print_header, "Testing runtime wrappers")
	@for dir in $(RUNTIME_DIRS); do \
		if [ -f $$dir/Makefile ]; then \
			echo "  Testing $$dir wrapper..."; \
			if [ "$$dir" = "rust" ] && [ -f "$$HOME/.cargo/env" ]; then \
				. "$$HOME/.cargo/env"; \
			fi; \
			$(MAKE) -C $$dir test || exit 1; \
		fi; \
	done
	$(call print_success, "All runtime tests passed")

# Clean all runtime artifacts
clean:
	$(call print_header, "Cleaning runtime artifacts")
	@for dir in $(RUNTIME_DIRS); do \
		if [ -f $$dir/Makefile ]; then \
			echo "  Cleaning $$dir..."; \
			$(MAKE) -C $$dir clean || true; \
		fi; \
	done
	$(call print_success, "Runtime artifacts cleaned")

# Install runtime components (mainly documentation)
install:
	$(call print_header, "Installing runtime documentation")
	# Runtime wrappers are typically not installed system-wide
	# They're used as libraries in their respective ecosystems
	$(call print_success, "Runtime installation complete")

# Show runtime-specific help
help::
	@echo "Runtime targets:"
	@echo "  go        - Build Go wrapper"
	@echo "  rust      - Build Rust wrapper"
	@echo "  node      - Build Node.js wrapper"
	@echo "  python    - Build Python wrapper"
	@echo "  test      - Run all runtime tests"