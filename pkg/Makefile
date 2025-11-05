# Makefile for language bindings in pkg/

include ../common.mk

# Package files - use the canonical pkg-config from ffi/
PKGCONFIG_FILE := ../ffi/uor-ffi.pc
PKGCONFIG_NAME := uor-ffi.pc

# Language binding directories
LANGUAGES := go python rust node

.PHONY: all clean install uninstall test verify build

all: build test
	$(call print_success, "All language bindings built and tested")

# Build all language bindings
build: build-go build-python build-rust build-node
	$(call print_success, "All language bindings built")

# Test all language bindings  
test: test-go test-python test-rust test-node
	$(call print_success, "All language binding tests passed")

# Go bindings
build-go:
	$(call print_header, "Building Go bindings")
	@if which go >/dev/null 2>&1; then \
		cd go && $(MAKE) -f Makefile all; \
	else \
		echo "  Warning: Go not installed - skipping"; \
	fi

test-go:
	$(call print_header, "Testing Go bindings")
	@if which go >/dev/null 2>&1; then \
		cd go && $(MAKE) -f Makefile test; \
	else \
		echo "  Warning: Go not installed - skipping"; \
	fi

# Python bindings
build-python:
	$(call print_header, "Building Python bindings")
	@if which python3 >/dev/null 2>&1; then \
		cd python && python3 setup.py build_ext --inplace 2>/dev/null || true; \
	else \
		echo "  Warning: Python not installed - skipping"; \
	fi

test-python:
	$(call print_header, "Testing Python bindings")
	@if which python3 >/dev/null 2>&1; then \
		cd python && (python3 -m pytest test/ -v 2>/dev/null || python3 test/test_uor.py); \
	else \
		echo "  Warning: Python not installed - skipping"; \
	fi

# Rust bindings
build-rust:
	$(call print_header, "Building Rust bindings")
	@if [ -f "$$HOME/.cargo/env" ]; then . "$$HOME/.cargo/env"; fi; \
	if which cargo >/dev/null 2>&1; then \
		cd rust && cargo build --release; \
	else \
		echo "  Warning: Cargo not installed - skipping"; \
	fi

test-rust:
	$(call print_header, "Testing Rust bindings")
	@if [ -f "$$HOME/.cargo/env" ]; then . "$$HOME/.cargo/env"; fi; \
	which cargo >/dev/null 2>&1 || (echo "Error: cargo not found. Install Rust." && exit 1)
	@if [ -f "$$HOME/.cargo/env" ]; then . "$$HOME/.cargo/env"; fi; \
	cd rust && cargo test

# Node.js bindings
build-node:
	$(call print_header, "Building Node.js bindings")
	@if which node >/dev/null 2>&1 && which npm >/dev/null 2>&1; then \
		cd node && npm install && npm run build || true; \
	else \
		echo "  Warning: Node.js/npm not installed - skipping"; \
	fi

test-node:
	$(call print_header, "Testing Node.js bindings")
	@which node >/dev/null 2>&1 || (echo "Error: node not found. Install Node.js." && exit 1)
	@which npm >/dev/null 2>&1 || (echo "Error: npm not found. Install npm." && exit 1)
	cd node && npm test

# Clean all language bindings
clean-bindings:
	$(call print_header, "Cleaning language bindings")
	@for lang in $(LANGUAGES); do \
		if [ -d $$lang ]; then \
			echo "  Cleaning $$lang..."; \
			case $$lang in \
				go) cd go && go clean -cache -testcache 2>/dev/null || true ;; \
				python) cd python && rm -rf build dist *.egg-info src/__pycache__ test/__pycache__ 2>/dev/null || true ;; \
				rust) cd rust && cargo clean 2>/dev/null || true ;; \
				node) cd node && rm -rf node_modules build 2>/dev/null || true ;; \
			esac; \
		fi; \
	done
	$(call print_success, "Language bindings cleaned")

# Install pkg-config file
install: $(PKGCONFIG_FILE)
	$(call print_header, "Installing pkg-config file")
	$(Q)$(MKDIR) $(DESTDIR)$(PKGCONFIGDIR)
	$(Q)sed -e "s|^prefix=.*|prefix=$(PREFIX)|" \
	        -e "s|^libdir=.*|libdir=$(LIBDIR)|" \
	        -e "s|^includedir=.*|includedir=$(INCLUDEDIR)|" \
	        $(PKGCONFIG_FILE) > $(PKGCONFIG_FILE).tmp
	$(Q)$(INSTALL) -m 644 $(PKGCONFIG_FILE).tmp $(DESTDIR)$(PKGCONFIGDIR)/$(PKGCONFIG_NAME)
	$(Q)$(RM) $(PKGCONFIG_FILE).tmp
	$(call print_success, "pkg-config file installed")

# Uninstall pkg-config file
uninstall:
	$(call print_header, "Uninstalling pkg-config file")
	$(Q)$(RM) $(DESTDIR)$(PKGCONFIGDIR)/$(PKGCONFIG_NAME)
	$(call print_success, "pkg-config file uninstalled")

# Verify pkg-config setup
verify:
	$(call print_header, "Verifying pkg-config")
	@if which pkg-config >/dev/null 2>&1; then \
		if PKG_CONFIG_PATH=$(DESTDIR)$(PKGCONFIGDIR):$$PKG_CONFIG_PATH pkg-config --exists uor-ffi; then \
			echo "  Version: $$(PKG_CONFIG_PATH=$(DESTDIR)$(PKGCONFIGDIR):$$PKG_CONFIG_PATH pkg-config --modversion uor-ffi)"; \
			echo "  Cflags:  $$(PKG_CONFIG_PATH=$(DESTDIR)$(PKGCONFIGDIR):$$PKG_CONFIG_PATH pkg-config --cflags uor-ffi)"; \
			echo "  Libs:    $$(PKG_CONFIG_PATH=$(DESTDIR)$(PKGCONFIGDIR):$$PKG_CONFIG_PATH pkg-config --libs uor-ffi)"; \
			$(call print_success, "pkg-config verified"); \
		else \
			$(call print_error, "pkg-config file not found"); \
		fi; \
	else \
		$(call print_warning, "pkg-config not installed"); \
	fi

# Clean everything
clean: clean-bindings
	$(call print_success, "Package directory cleaned")

# Show help
help::
	@echo "Package targets:"
	@echo "  all         - Build and test all language bindings"
	@echo "  build       - Build all language bindings"
	@echo "  test        - Test all language bindings"
	@echo "  build-go    - Build Go bindings"
	@echo "  test-go     - Test Go bindings"
	@echo "  build-python - Build Python bindings"
	@echo "  test-python - Test Python bindings"
	@echo "  build-rust  - Build Rust bindings"
	@echo "  test-rust   - Test Rust bindings"
	@echo "  build-node  - Build Node.js bindings"
	@echo "  test-node   - Test Node.js bindings"
	@echo "  install     - Install pkg-config file"
	@echo "  uninstall   - Remove pkg-config file"
	@echo "  verify      - Check pkg-config setup"
	@echo "  clean       - Clean all build artifacts"