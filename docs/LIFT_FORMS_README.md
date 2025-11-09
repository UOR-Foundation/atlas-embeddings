# Custom Lift Forms Configuration

## Overview

Atlas Bridge Context API v0.3 supports runtime loading of custom lift linear forms for the 2^{1+24} extraspecial group embedding. This allows researchers to swap in alternative embeddings without recompiling.

## File Format: lift_forms.hex

Place a file named `lift_forms.hex` at the repository root to provide custom lift forms. The file should contain hexadecimal-encoded binary data representing the lift form coefficients.

### Format Specification

- **Encoding**: Hexadecimal (0-9, a-f, A-F)
- **Structure**: Raw binary data encoded as hex pairs
- **Whitespace**: Spaces, tabs, and newlines are ignored
- **Example**:
  ```hex
  deadbeef0123456789abcdef
  fedcba9876543210
  ```

### Minimal Example

Create `lift_forms.hex` in the repository root:

```hex
# Custom lift forms for 2^{1+24} embedding
0102 0304 0506 0708 090a 0b0c 0d0e 0f10
1112 1314 1516 1718 191a 1b1c 1d1e 1f20
```

Lines starting with `#` are treated as comments (ignored during parsing).

## Usage

### C API

```c
#include "atlas/include/atlas_bridge_ctx.h"

// Create context
AtlasBridgeContext* ctx = atlas_ctx_new_default();

// Load custom lift forms from file
int result = atlas_ctx_load_lift_forms(ctx, "lift_forms.hex");
if (result == 0) {
    printf("Custom lift forms loaded successfully\n");
} else {
    printf("Failed to load lift forms, using defaults\n");
}

// Or set lift forms from hex string directly
const char* hex_data = "deadbeef0123456789abcdef";
atlas_ctx_set_lift_forms_hex(ctx, hex_data, strlen(hex_data));

// Retrieve current lift forms
char* current_hex = atlas_ctx_get_lift_forms_hex(ctx);
if (current_hex) {
    printf("Current lift forms: %s\n", current_hex);
    free(current_hex);
}

atlas_ctx_free(ctx);
```

### Python Bindings (future)

```python
from atlas_bridge import AtlasBridgeContext

ctx = AtlasBridgeContext()

# Load from file
ctx.load_lift_forms("lift_forms.hex")

# Or set directly
ctx.set_lift_forms_hex("deadbeef0123456789abcdef")

# Get current forms
hex_data = ctx.get_lift_forms_hex()
print(f"Lift forms: {hex_data}")
```

## Generating Lift Forms

Use the Sage/Atlas bridge in the `sigmatics/` directory to generate valid lift forms:

```sage
# In Sage environment
load('sigmatics/generate_lift_forms.sage')

# Generate default forms
forms = generate_e_group_lift_forms()

# Export to hex
export_lift_forms_hex(forms, 'lift_forms.hex')
```

## Validation

The API performs basic validation:
- ✓ File exists and is readable
- ✓ Hex encoding is valid (only 0-9, a-f, A-F)
- ✓ Even number of hex characters (complete bytes)
- ✓ File size is reasonable (< 1MB)

Invalid files will cause the loader to return an error code (-1) and the context will retain its previous lift forms (or defaults if none were set).

## Certificate Integration

When lift forms are loaded, they are included in JSON certificates emitted by `atlas_ctx_emit_certificate()`:

```json
{
  "version": "0.3.0",
  "mode": "spinlift",
  "lift_forms": "deadbeef0123456789abcdef...",
  "diagnostics": { ... }
}
```

This ensures reproducibility: certificates record which lift forms were active during computation.

## Advanced: Runtime Swap

For experiments requiring multiple lift form configurations:

```c
// Experiment 1: Default forms
AtlasBridgeContext* ctx = atlas_ctx_new_default();
run_experiment(ctx);

// Experiment 2: Custom forms
atlas_ctx_load_lift_forms(ctx, "alternative_lift_forms.hex");
run_experiment(ctx);

// Experiment 3: Another variant
atlas_ctx_set_lift_forms_hex(ctx, "0123456789abcdef", 16);
run_experiment(ctx);
```

Each configuration can produce a separate certificate for comparison.

## Security Notes

- Lift form files are parsed but not executed as code
- File size is capped at 1MB to prevent memory exhaustion
- Invalid hex data is rejected without crashing
- No external network access during loading

## Troubleshooting

### "Failed to load lift forms"

**Cause**: File not found, invalid hex encoding, or file too large.

**Solution**:
1. Check file exists: `ls -l lift_forms.hex`
2. Verify hex encoding: `cat lift_forms.hex` should show only hex characters
3. Check file size: `wc -c lift_forms.hex` should be < 1MB
4. Remove comments/whitespace if causing issues

### "Lift forms don't affect results"

**Cause**: Lift operations not enabled in context flags.

**Solution**: Enable lift operations when creating context:
```c
AtlasContextConfig cfg;
atlas_ctx_config_default(&cfg);
cfg.flags |= ATLAS_CTX_ENABLE_LIFT;
AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
```

## References

- [Atlas Bridge Context API Documentation](atlas/README_CONTEXT_API.md)
- [Sigmatics Lift Form Generators](sigmatics/README.md)
- [v0.3 Release Notes](CHANGELOG.md)
