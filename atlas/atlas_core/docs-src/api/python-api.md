# Python API Reference

## Module: `uor`

### Functions

- `pages() -> int` - Returns 48
- `bytes() -> int` - Returns 256
- `rclasses() -> int` - Returns 96
- `r96_classify(b: int) -> int` - Classify byte to resonance class
- `phi_encode(page: int, byte: int) -> int` - Encode coordinates
- `phi_page(code: int) -> int` - Extract page from code
- `phi_byte(code: int) -> int` - Extract byte from code
- `truth_zero(budget: int) -> bool` - Check if budget is zero
- `truth_add(a: int, b: int) -> bool` - Check if sum is zero
