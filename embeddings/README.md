# Embeddings Component

The Embeddings component maps structured or unstructured inputs into Atlas spaces.

## Overview

Capabilities:
- Dataset adapters to Atlas-compatible tensors
- Feature heads producing 12,288-length vectors
- Optional 8-lift bridge mode support
- Training/eval loops for consistency checks

## Workflow

1. Prepare data adapter producing (page, byte) views or raw vectors
2. Encode to 12,288 dimensions
3. Run P_class/P_299 consistency checks
4. Optional: Lift to bridge mode and evaluate metrics

## Directory Structure

- `src/` - Core embedding implementations
- `tests/` - Embedding tests
- `examples/` - Usage examples
- `docs/` - Detailed documentation

## Status

🚧 Planned component - Stubs created for future development

