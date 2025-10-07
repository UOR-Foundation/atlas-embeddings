.PHONY: help build test check lint format docs clean bench audit install-tools all verify

# Default target
help:
	@echo "atlas-embeddings - Makefile targets:"
	@echo ""
	@echo "Building:"
	@echo "  make build          - Build the crate"
	@echo "  make build-release  - Build with optimizations"
	@echo "  make all            - Build + test + check + docs"
	@echo ""
	@echo "Testing:"
	@echo "  make test           - Run all tests"
	@echo "  make test-unit      - Run unit tests only"
	@echo "  make test-int       - Run integration tests only"
	@echo "  make test-doc       - Run documentation tests"
	@echo ""
	@echo "Quality:"
	@echo "  make check          - Run cargo check"
	@echo "  make lint           - Run clippy with strict lints"
	@echo "  make format         - Format code with rustfmt"
	@echo "  make format-check   - Check formatting without changes"
	@echo "  make verify         - Run all checks (CI equivalent)"
	@echo ""
	@echo "Documentation:"
	@echo "  make docs           - Build documentation"
	@echo "  make docs-open      - Build and open documentation"
	@echo "  make docs-private   - Build docs including private items"
	@echo ""
	@echo "Benchmarking:"
	@echo "  make bench          - Run all benchmarks"
	@echo "  make bench-save     - Run benchmarks and save baseline"
	@echo ""
	@echo "Maintenance:"
	@echo "  make clean          - Remove build artifacts"
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
	cargo fmt --all -- --check

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

# Maintenance
clean:
	cargo clean
	rm -rf target/
	rm -rf Cargo.lock

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
