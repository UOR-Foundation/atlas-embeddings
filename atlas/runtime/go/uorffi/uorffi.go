package uorffi

/*
#cgo CFLAGS: -I${SRCDIR}/../../../ffi/c
#cgo LDFLAGS: -L${SRCDIR}/../../../ffi/c -Wl,-rpath,${SRCDIR}/../../../ffi/c
#include "minimal_wrapper.c"
*/
import "C"
import (
	"fmt"
	"sync"
)

var initOnce sync.Once

// Initialize the UOR runtime (no-op for minimal wrapper)
func Init() {
	initOnce.Do(func() {
		C.lean_initialize_uor_minimal(0)
	})
}

// Constants from the UOR Prime Structure
const (
	Pages         = 48
	Bytes         = 256
	RClasses      = 96
	TotalElements = Pages * Bytes // 12,288
)

// CompressionRatio represents the R96 compression ratio (3/8)
const CompressionRatio = float64(RClasses) / float64(Bytes)

// Basic UOR functions
func GetPages() uint32    { Init(); return uint32(C.lean_uor_pages_minimal()) }
func GetBytes() uint32    { Init(); return uint32(C.lean_uor_bytes_minimal()) }
func GetRClasses() uint32 { Init(); return uint32(C.lean_uor_rclasses_minimal()) }

// R96Classify maps a byte to one of 96 resonance classes
func R96Classify(b byte) byte {
	Init()
	return byte(C.lean_uor_r96_classify_minimal(C.uint8_t(b)))
}

// PhiEncode encodes page and byte coordinates into a 32-bit code
func PhiEncode(page, by byte) uint32 {
	Init()
	return uint32(C.lean_uor_phi_encode_minimal(C.uint8_t(page), C.uint8_t(by)))
}

// PhiPage extracts the page component from a Phi code
func PhiPage(code uint32) byte {
	Init()
	return byte(C.lean_uor_phi_page_minimal(C.uint32_t(code)))
}

// PhiByte extracts the byte component from a Phi code
func PhiByte(code uint32) byte {
	Init()
	return byte(C.lean_uor_phi_byte_minimal(C.uint32_t(code)))
}

// TruthZero checks if a budget value represents truth (conservation)
func TruthZero(budget uint32) bool {
	Init()
	return C.lean_uor_truth_zero_minimal(C.uint32_t(budget)) == 1
}

// TruthAdd checks if the sum of two values represents truth
func TruthAdd(a, b uint32) bool {
	Init()
	return C.lean_uor_truth_add_minimal(C.uint32_t(a), C.uint32_t(b)) == 1
}

// Runtime Types and Higher-Level API

// PhiCoordinate represents a coordinate in the Phi-Atlas boundary encoding
type PhiCoordinate struct {
	Page byte
	Byte byte
}

// NewPhiCoordinate creates a new PhiCoordinate
func NewPhiCoordinate(page, b byte) PhiCoordinate {
	return PhiCoordinate{Page: page % Pages, Byte: b}
}

// Encode returns the 32-bit Phi code for this coordinate
func (pc PhiCoordinate) Encode() uint32 {
	return PhiEncode(pc.Page, pc.Byte)
}

// DecodePhiCoordinate creates a PhiCoordinate from a 32-bit code
func DecodePhiCoordinate(code uint32) PhiCoordinate {
	return PhiCoordinate{
		Page: PhiPage(code),
		Byte: PhiByte(code),
	}
}

// String returns a string representation of the coordinate
func (pc PhiCoordinate) String() string {
	return fmt.Sprintf("Φ(%d,%d)", pc.Page, pc.Byte)
}

// ResonanceClass represents a resonance class value
type ResonanceClass struct {
	Value byte
}

// ClassifyResonance creates a ResonanceClass from a byte value
func ClassifyResonance(b byte) ResonanceClass {
	return ResonanceClass{Value: R96Classify(b)}
}

// String returns a string representation of the resonance class
func (rc ResonanceClass) String() string {
	return fmt.Sprintf("R96[%d]", rc.Value)
}

// Conservation provides conservation checking utilities
type Conservation struct{}

// IsZero checks if a value conserves truth (equals zero)
func (Conservation) IsZero(value uint32) bool {
	return TruthZero(value)
}

// SumIsZero checks if a sum conserves truth (equals zero)
func (Conservation) SumIsZero(a, b uint32) bool {
	return TruthAdd(a, b)
}
