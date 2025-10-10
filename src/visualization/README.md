# Visualization Module

This module provides visualization capabilities for the Atlas of Resonance Classes, exceptional Lie groups, and their relationships.

## Overview

The visualization module enables understanding of the Atlas → E₈ embedding and the emergence of exceptional groups through visual representations. This is critical for communicating the **Golden Seed Vector** and the universal mathematical language it represents.

## Components

### 1. Atlas Graph Visualizer (`atlas_graph.rs`)

Visualizes the 96-vertex Atlas graph with its distinctive properties:
- Bimodal degree distribution (64 vertices of degree-5, 32 of degree-6)
- Mirror symmetry τ (involution pairing)
- Hamming-1 adjacency structure

**Exports:**
- GraphML (for Gephi, Cytoscape, NetworkX)
- JSON (for D3.js, vis.js)
- DOT (for Graphviz)
- CSV (nodes and edges)

### 2. Dynkin Diagram Generator (`dynkin.rs`)

Generates SVG visualizations of Dynkin diagrams for all five exceptional groups:
- G₂ (rank 2, triple bond)
- F₄ (rank 4, double bond)
- E₆ (rank 6, simply-laced)
- E₇ (rank 7, simply-laced)
- E₈ (rank 8, simply-laced)

**Output:** Scalable SVG files

### 3. E₈ Root Projector (`e8_roots.rs`)

Projects the 240 E₈ roots into 2D and 3D for visualization:
- Coxeter plane projection (most symmetric 2D view)
- Principal component projections (3D)
- Simple coordinate plane projections

**Exports:** CSV coordinates for external visualization tools

### 4. Golden Seed Vector Visualizer (`embedding.rs`)

**This is the central visualization** - shows the Golden Seed Vector, the 96-dimensional Atlas embedding within E₈:
- 96 Atlas vertices highlighted within 240 E₈ roots
- Adjacency preservation verification
- Mirror pair relationships
- Full E₈ context

**Exports:**
- CSV coordinates
- JSON with E₈ context
- Adjacency preservation data

### 5. Export Utilities (`export.rs`)

Common export functionality supporting:
- GraphML
- JSON
- CSV
- DOT
- SVG

## Usage

### Quick Start

```rust
use atlas_embeddings::Atlas;
use atlas_embeddings::visualization::atlas_graph::AtlasGraphVisualizer;

let atlas = Atlas::new();
let visualizer = AtlasGraphVisualizer::new(&atlas);

// Export to GraphML
let graphml = visualizer.to_graphml();
std::fs::write("atlas.graphml", graphml)?;
```

### Generate All Visualizations

```bash
# Using Makefile
make vis-all

# Or individually
make vis-atlas        # Atlas graph
make vis-dynkin       # Dynkin diagrams
make vis-golden-seed  # Golden Seed Vector
```

### Using Examples

```bash
# Atlas graph
cargo run --example generate_atlas_graph --features visualization

# Dynkin diagrams
cargo run --example generate_dynkin_diagrams --features visualization

# Golden Seed Vector
cargo run --example export_golden_seed_vector --features visualization
```

## Output Files

### Atlas Graph
- `atlas_graph.graphml` - For graph analysis tools
- `atlas_graph.json` - For web visualizations
- `atlas_graph.dot` - For Graphviz
- `atlas_nodes.csv` - Node attributes
- `atlas_edges.csv` - Edge list

### Dynkin Diagrams
- `g2_dynkin.svg`
- `f4_dynkin.svg`
- `e6_dynkin.svg`
- `e7_dynkin.svg`
- `e8_dynkin.svg`

### Golden Seed Vector
- `golden_seed_vector.csv` - 96 Atlas coordinates in E₈
- `golden_seed_context.json` - Full E₈ context
- `adjacency_preservation.csv` - Verification data

## Design Principles

1. **Exact Arithmetic**: All computations use exact rational arithmetic
2. **Standard Formats**: Export to widely-supported formats
3. **Reproducible**: Same input always produces identical output
4. **Well-Documented**: Comprehensive documentation and examples
5. **Type-Safe**: Compile-time guarantees where possible

## Feature Flag

The visualization module is controlled by the `visualization` feature flag:

```toml
[dependencies]
atlas-embeddings = { version = "0.1", features = ["visualization"] }
```

This feature is enabled by default.

## Implementation Status

### Completed
- Module structure and API design
- Comprehensive documentation
- Integration tests
- Example programs
- Makefile targets

### To Be Implemented
- GraphML export implementation
- JSON export implementation
- DOT export implementation
- CSV export implementation
- SVG generation for Dynkin diagrams
- E₈ projection algorithms
- Golden Seed Vector export implementation

Each TODO item is marked in the source code and can be implemented incrementally while maintaining API stability.

## Testing

```bash
# Run visualization tests
cargo test --features visualization visualization

# Run integration tests
cargo test --test visualization_test --features visualization
```

## Visualization Tools

### Recommended Tools for Viewing Exports

**Graph Analysis:**
- Gephi (GraphML)
- Cytoscape (GraphML)
- NetworkX (Python, GraphML/JSON)

**Web Visualization:**
- D3.js (JSON)
- vis.js (JSON)
- Three.js (JSON coordinates)

**Vector Graphics:**
- Inkscape (SVG)
- Adobe Illustrator (SVG)
- Web browsers (SVG)

**Data Analysis:**
- Python (pandas, numpy)
- R
- Mathematica
- MATLAB

## Contributing

When implementing visualization features:

1. Maintain exact arithmetic (no floating point)
2. Add comprehensive tests
3. Document export format specifications
4. Provide usage examples
5. Update this README

## References

- GraphML Specification: http://graphml.graphdrawing.org/
- SVG Specification: https://www.w3.org/TR/SVG/
- JSON Schema: https://json-schema.org/
- DOT Language: https://graphviz.org/doc/info/lang.html
