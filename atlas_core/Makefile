# atlas_core/Makefile
# Atlas Bridge Context API v0.5
# Build system with BLAS acceleration support

# Compiler settings
CC ?= gcc
CFLAGS = -O2 -Wall -Wextra -fPIC -std=c11
LDFLAGS = -lm

# Directories
SRC_DIR = src
INC_DIR = include
LIB_DIR = lib
BUILD_DIR = build

# Detect BLAS availability
USE_BLAS ?= auto

ifeq ($(USE_BLAS),auto)
    # Try to detect OpenBLAS via pkg-config
    OPENBLAS_CFLAGS := $(shell pkg-config --cflags openblas 2>/dev/null)
    OPENBLAS_LIBS := $(shell pkg-config --libs openblas 2>/dev/null)
    
    ifneq ($(OPENBLAS_CFLAGS),)
        $(info [INFO] Found OpenBLAS via pkg-config)
        CFLAGS += -DUSE_BLAS $(OPENBLAS_CFLAGS)
        LDFLAGS += $(OPENBLAS_LIBS)
        BLAS_DETECTED = openblas
    else
        # Try cblas headers
        CBLAS_H := $(shell echo '\#include <cblas.h>' | $(CC) -E - >/dev/null 2>&1 && echo yes)
        ifeq ($(CBLAS_H),yes)
            $(info [INFO] Found CBLAS headers)
            CFLAGS += -DUSE_BLAS
            LDFLAGS += -lcblas -lblas
            BLAS_DETECTED = cblas
        else
            $(info [WARN] BLAS not detected, using fallback naive loops)
            BLAS_DETECTED = none
        endif
    endif
else ifeq ($(USE_BLAS),yes)
    # Force BLAS usage
    CFLAGS += -DUSE_BLAS
    LDFLAGS += -lcblas -lblas
    BLAS_DETECTED = forced
else
    # Explicitly disable BLAS
    BLAS_DETECTED = disabled
endif

# Detect AVX2 support
AVX2_SUPPORT := $(shell grep -q avx2 /proc/cpuinfo 2>/dev/null && echo yes)
ifeq ($(AVX2_SUPPORT),yes)
    $(info [INFO] AVX2 support detected, enabling SIMD acceleration)
    CFLAGS += -mavx2
else
    $(info [WARN] AVX2 not available, using scalar fallback)
endif

# Library targets
LIBRARY = $(LIB_DIR)/libatlas_bridge_ctx.so
LIBRARY_STATIC = $(LIB_DIR)/libatlas_bridge_ctx.a

# Source files
SOURCES = $(SRC_DIR)/atlas_bridge_ctx.c
OBJECTS = $(BUILD_DIR)/atlas_bridge_ctx.o

# Phony targets
.PHONY: all clean install uninstall test help

# Default target
all: $(LIBRARY)

# Create directories
$(LIB_DIR) $(BUILD_DIR):
	mkdir -p $@

# Compile object files
$(BUILD_DIR)/%.o: $(SRC_DIR)/%.c | $(BUILD_DIR)
	@echo "[CC] $<"
	$(CC) $(CFLAGS) -I$(INC_DIR) -c $< -o $@

# Link shared library
$(LIBRARY): $(OBJECTS) | $(LIB_DIR)
	@echo "[LD] $@"
	$(CC) -shared -o $@ $(OBJECTS) $(LDFLAGS)
	@echo "[OK] Built $@ (BLAS: $(BLAS_DETECTED))"

# Build static library
static: $(LIBRARY_STATIC)

$(LIBRARY_STATIC): $(OBJECTS) | $(LIB_DIR)
	@echo "[AR] $@"
	ar rcs $@ $(OBJECTS)
	@echo "[OK] Built $@"

# Clean build artifacts
clean:
	@echo "[CLEAN] Removing build artifacts"
	rm -rf $(BUILD_DIR) $(LIB_DIR)

# Install library and headers
PREFIX ?= /usr/local
INSTALL_LIB_DIR = $(PREFIX)/lib
INSTALL_INC_DIR = $(PREFIX)/include/atlas_bridge

install: $(LIBRARY)
	@echo "[INSTALL] Installing to $(PREFIX)"
	install -d $(INSTALL_LIB_DIR)
	install -d $(INSTALL_INC_DIR)
	install -m 755 $(LIBRARY) $(INSTALL_LIB_DIR)
	install -m 644 $(INC_DIR)/atlas_bridge_ctx.h $(INSTALL_INC_DIR)
	@echo "[OK] Installation complete"

# Uninstall library and headers
uninstall:
	@echo "[UNINSTALL] Removing from $(PREFIX)"
	rm -f $(INSTALL_LIB_DIR)/libatlas_bridge_ctx.so
	rm -rf $(INSTALL_INC_DIR)
	@echo "[OK] Uninstallation complete"

# Run tests (requires test executables to be built separately)
test: $(LIBRARY)
	@echo "[TEST] Run 'bash ../tools/verify_bridge.sh' for full test suite"

# Help message
help:
	@echo "Atlas Bridge Context API v0.5 - Build System"
	@echo ""
	@echo "Targets:"
	@echo "  all         - Build shared library (default)"
	@echo "  static      - Build static library"
	@echo "  clean       - Remove build artifacts"
	@echo "  install     - Install library and headers (requires sudo)"
	@echo "  uninstall   - Remove installed files (requires sudo)"
	@echo "  test        - Run verification suite"
	@echo "  help        - Show this message"
	@echo ""
	@echo "Variables:"
	@echo "  CC          - C compiler (default: gcc)"
	@echo "  PREFIX      - Install prefix (default: /usr/local)"
	@echo "  USE_BLAS    - BLAS usage: auto|yes|no (default: auto)"
	@echo ""
	@echo "Examples:"
	@echo "  make                    # Build with auto-detected BLAS"
	@echo "  make USE_BLAS=no        # Build without BLAS"
	@echo "  make USE_BLAS=yes       # Force BLAS (may fail if not available)"
	@echo "  make install PREFIX=~/.local  # Install to user directory"
	@echo ""
	@echo "BLAS Detection:"
	@echo "  Tries pkg-config for OpenBLAS first, then falls back to cblas.h"
	@echo "  If BLAS not found, uses naive loop fallback (slower but portable)"
	@echo ""
