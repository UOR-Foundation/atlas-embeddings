# Makefile for Node.js wrapper

include ../../common.mk

# Node-specific variables
NPM_FLAGS := --silent

.PHONY: all clean test build install-deps rebuild

all: install-deps build test
	$(call print_success, "Node wrapper ready")

# Install Node dependencies and build native addon
install-deps:
	$(call print_header, "Installing Node dependencies")
	@which npm >/dev/null 2>&1 || (echo "Error: npm not found. Install Node.js and npm." && exit 1)
	@which node >/dev/null 2>&1 || (echo "Error: node not found. Install Node.js and npm." && exit 1)
	$(Q)npm install $(NPM_FLAGS)
	$(call print_success, "Node dependencies installed")

# Build native addon
build: install-deps
	$(call print_header, "Building Node native addon")
	$(Q)npm run rebuild $(NPM_FLAGS)
	$(call print_success, "Native addon built")

# Rebuild native addon
rebuild:
	$(call print_header, "Rebuilding Node native addon")
	$(Q)npm run rebuild $(NPM_FLAGS)
	$(call print_success, "Native addon rebuilt")

# Run Node tests
test: build
	$(call print_header, "Testing Node wrapper")
	$(Q)npm test $(NPM_FLAGS)
	$(call print_success, "Node tests passed")

# Clean Node artifacts
clean:
	$(call print_header, "Cleaning Node artifacts")
	$(Q)npm run clean 2>/dev/null || true
	$(Q)$(RM) -rf node_modules/
	$(Q)$(RM) package-lock.json
	$(call print_success, "Node artifacts cleaned")

# Show Node-specific help
help::
	@echo "Node wrapper targets:"
	@echo "  install-deps - Install npm dependencies"
	@echo "  build        - Compile TypeScript"
	@echo "  test         - Run Node tests"
	@echo "  lint         - Lint TypeScript code"