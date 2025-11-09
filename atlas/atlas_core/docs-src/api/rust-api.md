# Rust API Reference

## Crate: `uor_ffi`

### Functions

- `pages() -> u32` - Returns 48
- `bytes() -> u32` - Returns 256
- `rclasses() -> u32` - Returns 96
- `r96_classify(b: u8) -> u8` - Classify byte to resonance class
- `phi_encode(page: u8, byte: u8) -> u32` - Encode coordinates
- `phi_page(code: u32) -> u8` - Extract page from code
- `phi_byte(code: u32) -> u8` - Extract byte from code
- `truth_zero(budget: i32) -> bool` - Check if budget is zero
- `truth_add(a: i32, b: i32) -> bool` - Check if sum is zero
