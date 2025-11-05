# Makefile for Lean components

include ../common.mk

# Lean-specific variables
LEAN_LIB_SO := $(LIB_DIR)/libUOR.so
LEAN_LIB_A := $(LIB_DIR)/libUOR.a
LEAN_BIN := $(BIN_DIR)/uor-verify
LEAN_SOURCES := $(wildcard *.lean UOR/*.lean UOR/*/*.lean)

.PHONY: all clean test install uninstall lib exe

all: lib exe
	$(call print_success, "Lean build complete")

# Build the library (both shared and static)
lib: lib-shared lib-static
	$(call print_success, "Both library types built")

# Build shared library
lib-shared:
	$(call print_header, "Building Lean shared library")
	$(call check_tool, $(LAKE))
	$(Q)cd $(PROJECT_ROOT) && $(LAKE) build UOR $(LEAN_OPTS)
	$(call print_success, "Shared library built: $(LEAN_LIB_SO)")

# Build static library
lib-static: lib-shared
	$(call print_header, "Building Lean static library")
	$(Q)cd $(PROJECT_ROOT) && $(LAKE) build UOR:static $(LEAN_OPTS)
	$(call print_success, "Static library built: $(LEAN_LIB_A)")

# Build the executable
exe: lib
	$(call print_header, "Building verification executable")
	$(Q)cd $(PROJECT_ROOT) && $(LAKE) build uor-verify $(LEAN_OPTS)
	$(call print_success, "Executable built: $(LEAN_BIN)")

# Run lean tests
test: exe test-suite
	$(call print_header, "Testing Lean components")
	$(Q)$(LEAN_BIN)
	@if [ $$? -eq 0 ]; then \
		echo "$$(echo '[0;32m✓  Lean verification passed[0m')"; \
	else \
		echo "$$(echo '[0;31m✗  Lean verification failed[0m')"; \
		exit 1; \
	fi
	$(Q)$(BIN_DIR)/uor-test
	@if [ $$? -eq 0 ]; then \
		echo "$$(echo '[0;32m✓  All Lean tests passed[0m')"; \
	else \
		echo "$$(echo '[0;31m✗  Some Lean tests failed[0m')"; \
		exit 1; \
	fi

# Build test suite
test-suite:
	$(call print_header, "Building test suite")
	$(Q)cd $(PROJECT_ROOT) && $(LAKE) build uor-test $(LEAN_OPTS)
	$(call print_success, "Test suite built")

# Clean Lean build artifacts
clean:
	$(call print_header, "Cleaning Lean artifacts")
	$(Q)cd $(PROJECT_ROOT) && $(LAKE) clean
	$(call print_success, "Lean artifacts cleaned")

# Install Lean library and executable
install: all
	$(call print_header, "Installing Lean components")
	$(Q)$(MKDIR) $(DESTDIR)$(LIBDIR)
	$(Q)$(MKDIR) $(DESTDIR)$(BINDIR)
	$(Q)$(INSTALL) -m 644 $(LEAN_LIB_SO) $(DESTDIR)$(LIBDIR)/
	$(Q)$(INSTALL) -m 644 $(LEAN_LIB_A) $(DESTDIR)$(LIBDIR)/
	$(Q)$(INSTALL) -m 755 $(LEAN_BIN) $(DESTDIR)$(BINDIR)/
	$(call print_success, "Lean components installed")

# Uninstall Lean components
uninstall:
	$(call print_header, "Uninstalling Lean components")
	$(Q)$(RM) $(DESTDIR)$(LIBDIR)/libUOR.so
	$(Q)$(RM) $(DESTDIR)$(LIBDIR)/libUOR.a
	$(Q)$(RM) $(DESTDIR)$(BINDIR)/uor-verify
	$(call print_success, "Lean components uninstalled")

# Show Lean-specific help
help::
	@echo "Lean targets:"
	@echo "  lib         - Build both shared and static libraries"
	@echo "  lib-shared  - Build shared library (.so)"
	@echo "  lib-static  - Build static library (.a)"
	@echo "  exe         - Build verification executable"
	@echo "  test        - Run Lean tests"