// Package uor provides Go bindings for the UOR Prime Structure FFI
package uor

/*
#cgo CFLAGS: -I../../../ffi/c
#include <stdint.h>

// Forward declarations of minimal wrapper functions
uint32_t lean_uor_pages_minimal(void);
uint32_t lean_uor_bytes_minimal(void);
uint32_t lean_uor_rclasses_minimal(void);
uint8_t lean_uor_r96_classify_minimal(uint8_t b);
uint32_t lean_uor_phi_encode_minimal(uint8_t page, uint8_t byte);
uint8_t lean_uor_phi_page_minimal(uint32_t code);
uint8_t lean_uor_phi_byte_minimal(uint32_t code);
uint8_t lean_uor_truth_zero_minimal(uint32_t budget);
uint8_t lean_uor_truth_add_minimal(uint32_t a, uint32_t b);
void lean_initialize_uor_minimal(uintptr_t resv);
void lean_finalize_uor_minimal(void);

// Include the implementation
#include "../../../ffi/c/minimal_wrapper.c"
*/
import "C"
import "fmt"

// Constants from the Prime Structure
const (
	Pages    = 48  // Number of pages in the structure
	Bytes    = 256 // Bytes per page
	RClasses = 96  // Number of resonance classes
)

// Initialize initializes the UOR library (no-op in pure C mode)
func Initialize() {
	C.lean_initialize_uor_minimal(0)
}

// Finalize cleans up the UOR library (no-op in pure C mode)
func Finalize() {
	C.lean_finalize_uor_minimal()
}

// GetPages returns the number of pages (48)
func GetPages() uint32 {
	return uint32(C.lean_uor_pages_minimal())
}

// GetBytes returns the number of bytes per page (256)
func GetBytes() uint32 {
	return uint32(C.lean_uor_bytes_minimal())
}

// GetRClasses returns the number of resonance classes (96)
func GetRClasses() uint32 {
	return uint32(C.lean_uor_rclasses_minimal())
}

// R96Classify classifies a byte into one of 96 resonance classes
func R96Classify(b byte) byte {
	return byte(C.lean_uor_r96_classify_minimal(C.uint8_t(b)))
}

// PhiEncode encodes page and byte coordinates into a 32-bit code
func PhiEncode(page, b byte) uint32 {
	return uint32(C.lean_uor_phi_encode_minimal(C.uint8_t(page), C.uint8_t(b)))
}

// PhiPage extracts the page component from a Phi code
func PhiPage(code uint32) byte {
	return byte(C.lean_uor_phi_page_minimal(C.uint32_t(code)))
}

// PhiByte extracts the byte component from a Phi code
func PhiByte(code uint32) byte {
	return byte(C.lean_uor_phi_byte_minimal(C.uint32_t(code)))
}

// TruthZero checks if a budget value represents truth (conservation)
func TruthZero(budget uint32) bool {
	return C.lean_uor_truth_zero_minimal(C.uint32_t(budget)) != 0
}

// TruthAdd checks if the sum of two values represents truth
func TruthAdd(a, b uint32) bool {
	return C.lean_uor_truth_add_minimal(C.uint32_t(a), C.uint32_t(b)) != 0
}

// PhiCoordinate represents a coordinate in the Phi-Atlas
type PhiCoordinate struct {
	Page byte
	Byte byte
}

// Encode encodes the coordinate to a 32-bit code
func (c PhiCoordinate) Encode() uint32 {
	return PhiEncode(c.Page, c.Byte)
}

// DecodePhiCoordinate decodes a 32-bit code to a PhiCoordinate
func DecodePhiCoordinate(code uint32) PhiCoordinate {
	return PhiCoordinate{
		Page: PhiPage(code),
		Byte: PhiByte(code),
	}
}

// String returns a string representation of the coordinate
func (c PhiCoordinate) String() string {
	return fmt.Sprintf("Φ(%d,%d)", c.Page, c.Byte)
}

// ResonanceClass represents a resonance classification result
type ResonanceClass byte

// Classify creates a ResonanceClass from a byte value
func Classify(b byte) ResonanceClass {
	return ResonanceClass(R96Classify(b))
}

// CompressionRatio returns the compression ratio (3/8)
func CompressionRatio() float64 {
	return float64(RClasses) / float64(Bytes)
}

// TotalElements returns the total number of elements (12,288)
func TotalElements() uint32 {
	return Pages * Bytes
}