# Common variables and rules for UOR-FFI build system
# This file is included by all Makefiles in the project

# Project root directory (relative to including Makefile)
PROJECT_ROOT ?= $(shell git rev-parse --show-toplevel 2>/dev/null || pwd)

# Build configuration
BUILD_TYPE ?= release
VERBOSE ?= 0

# Color output
NO_COLOR ?= 0
ifeq ($(NO_COLOR),0)
	RED := \033[0;31m
	GREEN := \033[0;32m
	YELLOW := \033[0;33m
	BLUE := \033[0;34m
	NC := \033[0m # No Color
else
	RED :=
	GREEN :=
	BLUE :=
	YELLOW :=
	NC :=
endif

# Build directories
BUILD_DIR := $(PROJECT_ROOT)/.lake/build
LIB_DIR := $(BUILD_DIR)/lib
BIN_DIR := $(BUILD_DIR)/bin
IR_DIR := $(BUILD_DIR)/ir

# Installation directories (default to user directory to avoid permission issues)
PREFIX ?= $(HOME)/.local
EXEC_PREFIX ?= $(PREFIX)
LIBDIR ?= $(EXEC_PREFIX)/lib
INCLUDEDIR ?= $(PREFIX)/include
BINDIR ?= $(EXEC_PREFIX)/bin
PKGCONFIGDIR ?= $(LIBDIR)/pkgconfig

# Tools
LAKE ?= lake
CC ?= cc
CXX ?= c++
GO ?= go
CARGO ?= cargo
NPM ?= npm
INSTALL ?= install
MKDIR ?= mkdir -p
RM ?= rm -f
RMDIR ?= rm -rf

# Lean configuration
LEAN_OPTS ?= 
# TODO: add `--debug` flag back in
# ifeq ($(BUILD_TYPE),debug)
# 	LEAN_OPTS += --debug
# endif

# C/C++ flags
CFLAGS ?= -O2 -g
CXXFLAGS ?= -O2 -g
LDFLAGS ?= -L$(LIB_DIR)
LIBS ?= -lUOR -lLean -lpthread -ldl

# Include paths
INCLUDES := -I$(PROJECT_ROOT)/ffi/c

# Common rules
.PHONY: all clean test install uninstall help

# Default verbosity rules
ifeq ($(VERBOSE),0)
	Q := @
	ECHO := @echo
else
	Q :=
	ECHO := @:
endif

# Utility functions
define print_header
	@echo "$(BLUE)==> $(1)$(NC)"
endef

define print_success
	@echo "$(GREEN)✓ $(1)$(NC)"
endef

define print_error
	@echo "$(RED)✗ $(1)$(NC)"
endef

define print_warning
	@echo "$(YELLOW)⚠ $(1)$(NC)"
endef

# Check for required tools
define check_tool
	@which $(1) > /dev/null 2>&1 || (echo "$(RED)Error: $(1) not found in PATH$(NC)" && exit 1)
endef

# Common targets that subdirectories can override
help::
	@echo "Common targets:"
	@echo "  all       - Build everything"
	@echo "  clean     - Remove build artifacts"
	@echo "  test      - Run tests"
	@echo "  install   - Install to system"
	@echo "  uninstall - Remove from system"
	@echo ""
	@echo "Variables:"
	@echo "  BUILD_TYPE=$(BUILD_TYPE) (release|debug)"
	@echo "  VERBOSE=$(VERBOSE) (0|1)"
	@echo "  PREFIX=$(PREFIX)"
	@echo "  NO_COLOR=$(NO_COLOR) (0|1)"