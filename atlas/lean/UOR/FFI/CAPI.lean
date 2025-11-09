import UOR.Prime.Structure
import UOR.Atlas.Core

/-!
# FFI C API Module

Provides Foreign Function Interface exports for interoperability with C, Go, Rust,
Node.js, and other languages. All functions are exported with stable C ABI.

## Exported Functions
- Constants: Pages, Bytes, R96, ABI version
- R96 classifier: Byte → resonance class mapping
- Φ encoding: Page/byte coordinate packing
- Truth/conservation: Budget semantics where truth ≡ zero deficit

## ABI Stability
The ABI version (currently 1) ensures compatibility. Breaking changes increment
the version number.
-/

namespace UOR.FFI

open UOR.Prime
open UOR.Atlas

/-- ABI version for compatibility tracking.
    Increment on breaking changes to function signatures or semantics. -/
def abiVersion : UInt32 := 1

/-- Pack (page, byte) coordinates into a 32-bit code.
    Encoding: (page << 8) | byte
    This provides efficient coordinate representation for boundary indices. -/
@[inline] def phiEncode (page : UInt8) (byte : UInt8) : UInt32 :=
  UInt32.ofNat ((page.toNat <<< 8) + byte.toNat)

/-- Extract page coordinate from encoded value.
    Applies modulo 48 to ensure valid page index. -/
@[inline] def phiPage (code : UInt32) : UInt8 :=
  UInt8.ofNat ((code.toNat >>> 8) % Pages)

/-- Extract byte coordinate from encoded value.
    Returns the lowest 8 bits. -/
@[inline] def phiByte (code : UInt32) : UInt8 :=
  UInt8.ofNat (code.toNat % Bytes)

/-- Truth equivalence with conservation.
    In the Prime Structure, truth is defined as zero budget (no deficit).
    This implements the fundamental principle: truth ≙ conservation. -/
@[inline] def truth (β : UInt32) : Bool := β == 0

/-- Truth addition law for budget composition.
    Truth(a + b) ↔ (Truth a ∧ Truth b)
    This captures the additive nature of conservation in the budget semantics. -/
@[inline] def truthAdd (a b : UInt32) : Bool := (a + b == 0)

/-! ### EXPORTS (C ABI)
All exported symbols are prefixed `lean_` to align with Lean's default toolchain conventions.
-/

/-- ABI version. -/
@[export lean_uor_abi_version]
def c_abiVersion : UInt32 := abiVersion

/-- Constants (Pages, Bytes, R96). -/
@[export lean_uor_pages]   def c_pages   : UInt32 := UInt32.ofNat Pages
@[export lean_uor_bytes]   def c_bytes   : UInt32 := UInt32.ofNat Bytes
@[export lean_uor_rclasses] def c_rclasses : UInt32 := UInt32.ofNat R96

/-- R96 classifier: byte → class in [0,95]. -/
@[export lean_uor_r96_classify]
def c_r96 (b : @& UInt8) : UInt8 := classifyByte b

/-- Pack/unpack boundary codes. -/
@[export lean_uor_phi_encode]
def c_phiEncode (page : @& UInt8) (byte : @& UInt8) : UInt32 := phiEncode page byte

@[export lean_uor_phi_page]
def c_phiPage (code : @& UInt32) : UInt8 := phiPage code

@[export lean_uor_phi_byte]
def c_phiByte (code : @& UInt32) : UInt8 := phiByte code

/-- Truth & budget helpers. -/
@[export lean_uor_truth_zero]
def c_truthZero (β : @& UInt32) : UInt8 := if truth β then (1 : UInt8) else 0

@[export lean_uor_truth_add]
def c_truthAdd (a : @& UInt32) (b : @& UInt32) : UInt8 :=
  if truthAdd a b then (1 : UInt8) else 0

end UOR.FFI