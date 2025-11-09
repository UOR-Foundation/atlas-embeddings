# Node.js API Reference

## Module: `uor-ffi`

### Functions

- `pages(): number` - Returns 48
- `bytes(): number` - Returns 256
- `rclasses(): number` - Returns 96
- `r96Classify(b: number): number` - Classify byte to resonance class
- `phiEncode(page: number, byte: number): number` - Encode coordinates
- `phiPage(code: number): number` - Extract page from code
- `phiByte(code: number): number` - Extract byte from code
- `truthZero(budget: number): boolean` - Check if budget is zero
- `truthAdd(a: number, b: number): boolean` - Check if sum is zero
