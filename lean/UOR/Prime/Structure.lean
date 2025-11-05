/-!
# Prime Structure Core Module

This module defines the fundamental constants and operations for the Prime Structure,
a mathematical framework based on the 12,288-element structure (48×256) with resonance
compression to 96 classes.

## Key Invariants
- Total elements: 12,288 = 48 × 256 = 2^12 × 3
- Resonance classes: 96 = 3 × 2^5
- Compression ratio: 96/256 = 3/8
-/

namespace UOR.Prime

/-- Number of pages in the boundary structure.
    48 = 3 × 16 = 3 × 2^4 emerges from the unity constraint α₄α₅ = 1. -/
def Pages  : Nat := 48

/-- Number of bytes per page.
    256 = 2^8 provides the full byte space. -/
def Bytes  : Nat := 256

/-- Number of resonance classes after compression.
    96 = 3 × 32 = 3 × 2^5 achieves optimal 3/8 compression. -/
def R96    : Nat := 96

/-- R96 classifier maps bytes to resonance classes.
    
    This function implements the resonance classification that compresses
    256 byte values into 96 distinct resonance classes, achieving the
    theoretical 3/8 compression bound.
    
    Properties:
    - Surjective onto [0, 95]
    - Periodic with period 96
    - Preserves modular arithmetic structure
    
    @param b The byte to classify
    @return Resonance class in range [0, 95]
-/
def classifyByte (b : UInt8) : UInt8 :=
  UInt8.ofNat (b.toNat % R96)

end UOR.Prime