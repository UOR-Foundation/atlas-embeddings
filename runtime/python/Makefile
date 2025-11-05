# Makefile for Python runtime bindings

include ../../common.mk

PYTHON := python3
PIP := pip3

.PHONY: all build test clean install dev-install

all: build test
	$(call print_success, "Python runtime built and tested")

build:
	$(call print_header, "Building Python runtime extension")
	$(Q)$(PYTHON) setup.py build_ext --inplace
	$(call print_success, "Python runtime extension built")

test: build
	$(call print_header, "Testing Python runtime")
	$(Q)$(PYTHON) -m unittest discover -s test -p "test*.py" -v
	$(call print_success, "Python runtime tests passed")

install: build
	$(call print_header, "Installing Python runtime")
	$(Q)$(PIP) install .
	$(call print_success, "Python runtime installed")

dev-install:
	$(call print_header, "Installing Python runtime in development mode")
	$(Q)$(PIP) install -e .
	$(call print_success, "Python runtime installed (dev mode)")

clean:
	$(call print_header, "Cleaning Python runtime artifacts")
	$(Q)$(RM) -r build dist *.egg-info
	$(Q)$(RM) -r src/*.egg-info src/uor_runtime/*.egg-info
	$(Q)$(RM) -r src/uor_runtime/__pycache__ test/__pycache__
	$(Q)$(RM) src/uor_runtime/_core*.so src/uor_runtime/_core*.pyd
	$(Q)find . -name "*.pyc" -delete
	$(Q)find . -name "*.pyo" -delete
	$(call print_success, "Python runtime cleaned")

help::
	@echo "Python runtime targets:"
	@echo "  all         - Build and test"
	@echo "  build       - Build extension module"
	@echo "  test        - Run tests"
	@echo "  install     - Install package"
	@echo "  dev-install - Install in development mode"
	@echo "  clean       - Remove build artifacts"