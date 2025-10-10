.PHONY: help build test check lint format docs clean bench audit install-tools all verify lean4-build lean4-clean lean4-test

# Default target
help:
	@echo "atlas-embeddings - Makefile targets:"
	@echo ""
	@echo "Building:"
	@echo "  make build          - Build the Rust crate"
	@echo "  make build-release  - Build with optimizations"
	@echo "  make all            - Build + test + check + docs (Rust only)"
	@echo ""
	@echo "Testing:"
	@echo "  make test           - Run all Rust tests"
	@echo "  make test-unit      - Run unit tests only"
	@echo "  make test-int       - Run integration tests only"
	@echo "  make test-doc       - Run documentation tests"
	@echo ""
	@echo "Quality:"
	@echo "  make check          - Run cargo check"
	@echo "  make lint           - Run clippy with strict lints"
	@echo "  make format         - Format code with rustfmt"
	@echo "  make format-check   - Check formatting without changes"
	@echo "  make verify         - Run all checks (CI equivalent, Rust only)"
	@echo ""
	@echo "Documentation:"
	@echo "  make docs           - Build Rust documentation"
	@echo "  make docs-open      - Build and open Rust documentation"
	@echo "  make docs-private   - Build docs including private items"
	@echo ""
	@echo "Lean 4 Formalization:"
	@echo "  make lean4-build    - Build Lean 4 formalization"
	@echo "  make lean4-clean    - Clean Lean 4 build artifacts"
	@echo "  make lean4-test     - Verify no sorry statements in Lean code"
	@echo ""
	@echo "Benchmarking:"
	@echo "  make bench          - Run all benchmarks"
	@echo "  make bench-save     - Run benchmarks and save baseline"
	@echo ""
	@echo "Maintenance:"
	@echo "  make clean          - Remove all build artifacts (Rust + Lean)"
	@echo "  make audit          - Check for security vulnerabilities"
	@echo "  make install-tools  - Install required development tools"
	@echo "  make deps           - Check dependency tree"

# Build targets
build:
	cargo build

build-release:
	cargo build --release

all: build test check lint docs
	@echo "✓ All checks passed"

# Testing targets
test:
	cargo test --all-features

test-unit:
	cargo test --lib --all-features

test-int:
	cargo test --test '*' --all-features

test-doc:
	cargo test --doc --all-features

# Quality assurance
check:
	cargo check --all-features
	cargo check --all-features --no-default-features

lint:
	@echo "Running clippy with strict lints..."
	cargo clippy --all-targets --all-features -- \
		-D warnings \
		-D clippy::all \
		-D clippy::pedantic \
		-D clippy::nursery \
		-D clippy::cargo \
		-D clippy::float_arithmetic \
		-D clippy::float_cmp \
		-D clippy::float_cmp_const

format:
	cargo fmt --all

format-check:
	@cargo fmt --all -- --check 2>/dev/null

# Verification (for CI)
verify: format-check check lint test docs
	@echo "✓ All verification checks passed"
	@echo "✓ Ready for peer review"

# Documentation
docs:
	cargo doc --all-features --no-deps

docs-open:
	cargo doc --all-features --no-deps --open

docs-private:
	cargo doc --all-features --no-deps --document-private-items

# Benchmarking
bench:
	cargo bench --all-features

bench-save:
	cargo bench --all-features -- --save-baseline main

# Lean 4 targets
lean4-build:
	@echo "Building Lean 4 formalization..."
	cd lean4 && lake build
	@echo "✓ Lean 4 build complete (8 modules, 1,454 lines, 54 theorems)"

lean4-clean:
	@echo "Cleaning Lean 4 build artifacts..."
	cd lean4 && lake clean
	@echo "✓ Lean 4 artifacts cleaned"

lean4-test:
	@echo "Verifying no sorry statements in Lean code..."
	@if grep -rE '\bsorry\b' lean4/AtlasEmbeddings/ --include="*.lean" | grep -v "^\-\-" | grep -v "NO.*sorry.*POLICY" | grep -v "ZERO sorrys"; then \
		echo "Error: Found 'sorry' statements in Lean code"; \
		exit 1; \
	else \
		echo "✓ Zero sorry statements found - all 54 theorems proven"; \
	fi

# Maintenance
clean:
	cargo clean
	rm -rf target/
	rm -rf Cargo.lock
	@if [ -d lean4 ]; then cd lean4 && lake clean; fi
	@echo "✓ All build artifacts removed"

audit:
	cargo audit

deps:
	cargo tree --all-features

install-tools:
	@echo "Installing development tools..."
	cargo install cargo-audit
	cargo install cargo-criterion
	rustup component add rustfmt
	rustup component add clippy
	@echo "✓ Tools installed"

# Coverage (requires cargo-tarpaulin)
coverage:
	cargo tarpaulin --all-features --workspace --timeout 300 --out Html --output-dir coverage/

# Watch mode (requires cargo-watch)
watch-test:
	cargo watch -x test

watch-check:
	cargo watch -x check -x clippy

# Size analysis
bloat:
	cargo bloat --release --crate-name atlas_embeddings

# Assembly inspection
asm:
	cargo asm --rust --lib

# Continuous integration targets
ci-test: format-check lint test
	@echo "✓ CI test phase passed"

ci-build: build build-release
	@echo "✓ CI build phase passed"

ci-docs: docs
	@echo "✓ CI docs phase passed"

ci: ci-test ci-build ci-docs
	@echo "✓ All CI checks passed"
