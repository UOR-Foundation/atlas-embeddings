# Go API Reference

## Package: `github.com/atlas-12288/uor`

### Functions

- `Initialize()` - Initialize the UOR system
- `Finalize()` - Clean up resources
- `GetPages() uint32` - Returns 48
- `GetBytes() uint32` - Returns 256
- `GetRClasses() uint32` - Returns 96
- `R96Classify(b byte) byte` - Classify byte to resonance class
- `PhiEncode(page, byte byte) uint32` - Encode coordinates
- `PhiPage(code uint32) byte` - Extract page from code
- `PhiByte(code uint32) byte` - Extract byte from code
- `TruthZero(budget int32) bool` - Check if budget is zero
- `TruthAdd(a, b int32) bool` - Check if sum is zero
