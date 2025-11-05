# API Documentation

Complete API reference for all UOR Prime Structure language bindings.

## Language Bindings

### Core API
- [**C API**](c-api.md) - FFI layer and minimal wrapper

### Basic Bindings (pkg/)
- [**Go API**](go-api.md) - Basic Go interface
- [**Python API**](python-api.md) - Basic Python interface
- [**Rust API**](rust-api.md) - Basic Rust interface
- [**Node.js API**](node-api.md) - Basic Node.js interface

### Enhanced Bindings (runtime/)
Enhanced runtime APIs are documented in the respective language sections above.

## Common Functions

All language bindings provide these core functions:

| Function | Description | Returns |
|----------|-------------|---------|
| `pages()` | Get number of pages | 48 |
| `bytes()` | Get bytes per page | 256 |
| `rclasses()` | Get resonance classes | 96 |
| `r96_classify(b)` | Classify byte to resonance | [0-95] |
| `phi_encode(p, b)` | Encode coordinates | uint32 |
| `phi_page(code)` | Extract page | [0-47] |
| `phi_byte(code)` | Extract byte | [0-255] |
| `truth_zero(budget)` | Check conservation | bool |
| `truth_add(a, b)` | Check sum conservation | bool |

## Type Mappings

| C Type | Go | Python | Rust | Node.js |
|--------|-----|--------|------|---------|
| `uint32_t` | `uint32` | `int` | `u32` | `number` |
| `uint8_t` | `byte/uint8` | `int` | `u8` | `number` |
| `int32_t` | `int32` | `int` | `i32` | `number` |
| `bool` (0/1) | `bool` | `bool` | `bool` | `boolean` |

## Error Handling

### C
Returns fixed values, no error handling needed for pure functions.

### Go
Returns values directly, panics on initialization failure.

### Python
Raises `ValueError` for invalid inputs in enhanced runtime.

### Rust
Returns `Result<T, E>` for fallible operations in enhanced runtime.

### Node.js
Throws exceptions for invalid inputs in enhanced runtime.

## Performance

All bindings use the same minimal C wrapper, ensuring consistent performance:

- **Pages/Bytes/RClasses**: O(1) constant time
- **R96 Classification**: O(1) lookup
- **Phi Encoding/Decoding**: O(1) bit operations
- **Truth Functions**: O(1) comparisons

## Thread Safety

The minimal C implementation is thread-safe as all functions are pure and stateless. Language-specific considerations:

- **Go**: Safe for concurrent use
- **Python**: GIL ensures thread safety
- **Rust**: Safe, implements `Send` and `Sync`
- **Node.js**: Single-threaded by default