# Makefile for Rust wrapper

include ../../common.mk

# Rust-specific variables
CARGO_FLAGS := 
ifeq ($(BUILD_TYPE),debug)
	CARGO_FLAGS := 
else
	CARGO_FLAGS := --release
endif

.PHONY: all clean test build fmt clippy doc

all: build test
	$(call print_success, "Rust wrapper ready")

# Build Rust wrapper
build:
	$(call print_header, "Building Rust wrapper")
	@if [ -f "$$HOME/.cargo/env" ]; then . "$$HOME/.cargo/env"; fi; \
	which cargo >/dev/null 2>&1 || (echo "Error: Cargo not found. Install Rust toolchain." && exit 1)
	@if [ -f "$$HOME/.cargo/env" ]; then . "$$HOME/.cargo/env"; fi; \
	cargo build $(CARGO_FLAGS)
	$(call print_success, "Rust wrapper built")

# Run Rust tests
test: build
	$(call print_header, "Testing Rust wrapper")
	@if [ -f "$$HOME/.cargo/env" ]; then . "$$HOME/.cargo/env"; fi; \
	cargo test $(CARGO_FLAGS)
	$(call print_success, "Rust tests passed")

# Format Rust code
fmt:
	$(call print_header, "Formatting Rust code")
	$(Q)cargo fmt
	$(call print_success, "Rust code formatted")

# Run clippy linter
clippy:
	$(call print_header, "Running clippy")
	$(Q)cargo clippy -- -D warnings
	$(call print_success, "Clippy passed")

# Build documentation
doc:
	$(call print_header, "Building Rust documentation")
	$(Q)cargo doc --no-deps
	$(call print_success, "Documentation built in target/doc")

# Clean Rust artifacts
clean:
	$(call print_header, "Cleaning Rust artifacts")
	$(Q)cargo clean
	$(call print_success, "Rust artifacts cleaned")

# Show Rust-specific help
help::
	@echo "Rust wrapper targets:"
	@echo "  build     - Build Rust wrapper"
	@echo "  test      - Run Rust tests"
	@echo "  fmt       - Format Rust code"
	@echo "  clippy    - Run clippy linter"
	@echo "  doc       - Build documentation"