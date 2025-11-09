# Makefile for building GitHub Pages documentation

# Directories
DOCS_SRC := .
DOCS_OUT := ../docs
API_DIR := $(DOCS_SRC)/api
GUIDES_DIR := $(DOCS_SRC)/guides

# Files
MD_FILES := $(shell find $(DOCS_SRC) -name "*.md" 2>/dev/null)
HTML_FILES := $(patsubst $(DOCS_SRC)/%.md,$(DOCS_OUT)/%.html,$(MD_FILES))

# Tools
PANDOC := pandoc
MKDIR := mkdir -p
CP := cp -r
RM := rm -rf

# Pandoc options
PANDOC_OPTS := --standalone \
               --metadata title="UOR Prime Structure FFI" \
               --toc \
               --toc-depth=3

.PHONY: all build clean serve install-deps

all: build

# Build documentation
build: $(DOCS_OUT) copy-markdown
	@echo "Documentation built in $(DOCS_OUT)/"

# Create output directory
$(DOCS_OUT):
	$(MKDIR) $(DOCS_OUT)
	$(MKDIR) $(DOCS_OUT)/api
	$(MKDIR) $(DOCS_OUT)/guides

# For GitHub Pages, we'll use markdown directly
copy-markdown: $(DOCS_OUT)
	@echo "Copying markdown files for GitHub Pages"
	@find $(DOCS_SRC) -name "*.md" -exec cp --parents {} $(DOCS_OUT)/ \;
	@echo "Creating Jekyll config"
	@echo "theme: jekyll-theme-cayman" > $(DOCS_OUT)/_config.yml
	@echo "title: UOR Prime Structure FFI" >> $(DOCS_OUT)/_config.yml
	@echo "description: Mathematical framework for 12,288-element holographic structure" >> $(DOCS_OUT)/_config.yml

# Clean generated files
clean:
	$(RM) $(DOCS_OUT)

# Serve documentation locally (requires Python)
serve: build
	@echo "Serving documentation at http://localhost:8000"
	@cd $(DOCS_OUT) && python3 -m http.server 8000

# Help
help:
	@echo "Documentation build targets:"
	@echo "  build       - Build documentation for GitHub Pages"
	@echo "  clean       - Remove generated files"
	@echo "  serve       - Serve docs locally (port 8000)"