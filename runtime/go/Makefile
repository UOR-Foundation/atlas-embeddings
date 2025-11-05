# Makefile for Go wrapper

include ../../common.mk

# Go-specific variables
GO_PACKAGE := uorffi
GO_SOURCES := $(wildcard $(GO_PACKAGE)/*.go)
GO_TEST_FLAGS := -v

.PHONY: all clean test build fmt vet

all: build test
	$(call print_success, "Go wrapper ready")

# Build Go wrapper (compile check)
build:
	$(call print_header, "Building Go wrapper")
	@which go >/dev/null 2>&1 || (echo "Error: Go not found. Install Go toolchain." && exit 1)
	$(Q)go build ./$(GO_PACKAGE)
	$(call print_success, "Go wrapper compiled")

# Run Go tests
test: build
	$(call print_header, "Testing Go wrapper")
	$(Q)CGO_LDFLAGS="-L$(LIB_DIR)" go test $(GO_TEST_FLAGS) ./$(GO_PACKAGE)
	$(call print_success, "Go tests passed")

# Format Go code
fmt:
	$(call print_header, "Formatting Go code")
	$(Q)go fmt ./$(GO_PACKAGE)
	$(call print_success, "Go code formatted")

# Run Go vet
vet:
	$(call print_header, "Running go vet")
	$(Q)go vet ./$(GO_PACKAGE)
	$(call print_success, "Go vet passed")

# Clean Go artifacts
clean:
	$(call print_header, "Cleaning Go artifacts")
	$(Q)go clean
	$(Q)$(RM) -rf vendor/
	$(call print_success, "Go artifacts cleaned")

# Show Go-specific help
help::
	@echo "Go wrapper targets:"
	@echo "  build     - Compile Go wrapper"
	@echo "  test      - Run Go tests"
	@echo "  fmt       - Format Go code"
	@echo "  vet       - Run go vet"