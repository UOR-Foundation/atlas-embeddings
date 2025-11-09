# Atlas Bridge v0.5 - Language Bindings

This directory contains language bindings for the Atlas Bridge Context API v0.5.

## Available Bindings

### Python (`python/atlas_bridge/`)
- **Context API**: `_native_ctx.py` (recommended, v0.5)
- **Legacy API**: `_native.py` (deprecated, will be removed in v0.6)
- **Installation**: Uses ctypes, no build required
- **Usage**: See `MIGRATION_v0.5.md`

```python
from bindings.python.atlas_bridge._native_ctx import AtlasContext
ctx = AtlasContext()
```

### Rust (`rust/atlas_bridge/`)
- **Version**: 0.5.0
- **Crate**: `atlas_bridge`
- **Build**: `cargo build --release`
- **Documentation**: `cargo doc --open`

```rust
use atlas_bridge::AtlasContext;
let ctx = AtlasContext::new_default()?;
```

### Node.js (`node/atlas_bridge/`)
- **Package**: `@atlas/bridge`
- **Version**: 0.5.0
- **Build**: `npm install`
- **Dependencies**: `ffi-napi`, `ref-napi`

```javascript
const { AtlasContext } = require('@atlas/bridge');
const ctx = new AtlasContext();
```

### Go (`go/atlas_bridge/`)
- **Package**: `github.com/CitizenGardens-org/atlas-hologram/bindings/go/atlas_bridge`
- **Version**: 0.5.0
- **Build**: `go build`
- **CGO**: Required

```go
import "github.com/CitizenGardens-org/atlas-hologram/bindings/go/atlas_bridge"
ctx, _ := atlas_bridge.NewAtlasContext(nil)
```

## Prerequisites

All bindings require the Atlas Bridge C library to be built:

```bash
cd ../atlas
make
```

Set library path:
```bash
export LD_LIBRARY_PATH="${PWD}/../atlas/lib:$LD_LIBRARY_PATH"
```

## Features

All v0.5 bindings provide:
- Context-based API for resource management
- Artifact loading (lift_forms.hex, P_299_matrix.bin, co1_gates.txt)
- Projector operations (P_class, P_299)
- Certificate emission
- Full error handling
- Thread-safe context lifecycle

## Deprecation Notice

⚠️ **Legacy non-context APIs are deprecated in v0.5 and will be removed in v0.6.**

Please migrate to the context-based API:

**OLD (Python):**
```python
from atlas_bridge._native import lib
lib.e_apply(state, x, z)
```

**NEW (Python):**
```python
from atlas_bridge._native_ctx import AtlasContext
ctx = AtlasContext()
ctx.apply_pauli_x(x, state)
```

## Documentation

- **Build Instructions**: `../BUILD_INSTRUCTIONS.md`
- **Migration Guide**: `../MIGRATION_v0.5.md`
- **API Documentation**: `../atlas/README_v04.md`
- **C Header**: `../atlas/include/atlas_bridge_ctx.h`

## Examples

### Complete Example (Python)

```python
from bindings.python.atlas_bridge._native_ctx import AtlasContext

# Create context
ctx = AtlasContext()

# Load artifacts
ctx.load_lift_forms('lift_forms.hex')
ctx.load_p299_matrix('P_299_matrix.bin')  # optional
ctx.load_co1_gates('co1_gates.txt')  # optional

# Perform operations
state = [0.0] * ctx.block_size
ctx.apply_p_class(state)
ctx.apply_p_299(state)

# Emit certificate
ctx.emit_certificate('bridge_cert.json', 'example')
```

### Complete Example (Rust)

```rust
use atlas_bridge::AtlasContext;

fn main() -> Result<(), String> {
    // Create context
    let ctx = AtlasContext::new_default()?;
    
    // Load artifacts
    ctx.load_lift_forms("lift_forms.hex")?;
    ctx.load_p299_matrix("P_299_matrix.bin").ok();
    ctx.load_co1_gates("co1_gates.txt").ok();
    
    // Perform operations
    let mut state = vec![0.0; ctx.block_size()];
    ctx.apply_p_class(&mut state)?;
    ctx.apply_p_299(&mut state)?;
    
    // Emit certificate
    ctx.emit_certificate("bridge_cert.json", "example")?;
    
    Ok(())
}
```

## Testing

Each binding can be tested independently:

```bash
# Python
python3 -c "from bindings.python.atlas_bridge._native_ctx import AtlasContext; print('OK')"

# Rust
cd rust/atlas_bridge && cargo test

# Node.js
cd node/atlas_bridge && npm test

# Go
cd go/atlas_bridge && go test
```

## Support

For issues with bindings:
1. Ensure C library is built: `cd ../atlas && make`
2. Check library path is set correctly
3. Review language-specific build requirements
4. Consult `../MIGRATION_v0.5.md` for examples

## Version Compatibility

| Binding Version | C Library Version | Status |
|----------------|-------------------|---------|
| 0.5.0 | 0.5.0 | Current |
| 0.4.x | 0.4.0 | Supported |
| 0.3.x | 0.3.0 | Deprecated |
| < 0.3 | < 0.3.0 | Unsupported |

## License

MIT (matches main repository license)
