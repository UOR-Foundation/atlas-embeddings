# Makefile for C tests

include ../../common.mk

# C test variables
TEST_PROG := test_ffi
TEST_SOURCES := test_ffi.c
TEST_OBJS := $(TEST_SOURCES:.c=.o)
TEST_CFLAGS := $(CFLAGS) -I$(PROJECT_ROOT)/ffi/c
TEST_LDFLAGS := $(LDFLAGS)
TEST_LIBS := $(LIBS)

.PHONY: all clean test build run

all: build test
	$(call print_success, "C tests ready")

# Build test program
build: $(TEST_PROG)
	$(call print_success, "C test program built")

$(TEST_PROG): $(TEST_SOURCES)
	$(call print_header, "Compiling C test")
	@$(CC) -I$(PROJECT_ROOT)/ffi/c -o $(TEST_PROG) $(TEST_SOURCES)

# Run C tests
test: build
	$(call print_header, "Running C tests")
	$(Q)./$(TEST_PROG)
	$(call print_success, "C tests passed")

# Just run without building
run:
	$(Q)./$(TEST_PROG)

# Clean C test artifacts
clean:
	$(call print_header, "Cleaning C test artifacts")
	$(Q)$(RM) $(TEST_PROG) $(TEST_OBJS)
	$(call print_success, "C test artifacts cleaned")

# Valgrind memory check (if available)
memcheck: build
	$(call print_header, "Running memory check")
	@if which valgrind >/dev/null 2>&1; then \
		valgrind --leak-check=full --error-exitcode=1 ./$(TEST_PROG); \
		$(call print_success, "Memory check passed"); \
	else \
		$(call print_warning, "Valgrind not found, skipping memory check"); \
	fi

# Show C test help
help::
	@echo "C test targets:"
	@echo "  build     - Build test program"
	@echo "  test      - Build and run tests"
	@echo "  run       - Run tests without building"
	@echo "  memcheck  - Run with valgrind"