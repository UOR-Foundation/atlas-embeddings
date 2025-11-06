// Package atlas_bridge provides Go bindings for Atlas Bridge Context API v0.5
//
// v0.5 Features:
//   - BLAS-accelerated matrix-vector operations
//   - Real artifact integration (lift_forms.hex, P_299_matrix.bin, co1_gates.txt)
//   - Safe Go API wrapping the C library
//
// ⚠️ DEPRECATION WARNING:
// Legacy non-context API has been deprecated in v0.5 and will be removed in v0.6.
// Please migrate all code to use the context-based API.
//
// Example:
//
//	ctx, err := NewAtlasContext(nil)
//	if err != nil {
//	    log.Fatal(err)
//	}
//	defer ctx.Free()
//
//	// Load artifacts
//	ctx.LoadLiftForms("lift_forms.hex")
//	ctx.LoadP299Matrix("P_299_matrix.bin") // optional
//	ctx.LoadCo1Gates("co1_gates.txt")      // optional
//
//	// Perform operations
//	state := make([]float64, ctx.BlockSize())
//	ctx.ApplyPClass(state)
//	ctx.ApplyP299(state)
//	ctx.EmitCertificate("bridge_cert.json", "test")
package atlas_bridge

/*
#cgo CFLAGS: -I../../../atlas_core/include
#cgo LDFLAGS: -L../../../atlas_core/lib -latlas_bridge_ctx -lm

#include <stdlib.h>
#include "atlas_bridge_ctx.h"
*/
import "C"
import (
	"errors"
	"unsafe"
)

// AtlasContext wraps the Atlas Bridge Context API
type AtlasContext struct {
	ctx *C.AtlasBridgeContext
}

// AtlasConfig represents configuration for Atlas Bridge Context
type AtlasConfig struct {
	Flags      uint32
	BlockSize  uint32
	NQubits    uint32
	TwirlGens  uint32
	Epsilon    float64
	NQbits     uint32
}

// DefaultConfig returns the default configuration
func DefaultConfig() AtlasConfig {
	return AtlasConfig{
		Flags:     0,
		BlockSize: 12288,
		NQubits:   8,
		TwirlGens: 16,
		Epsilon:   1e-10,
		NQbits:    8,
	}
}

// NewAtlasContext creates a new Atlas Bridge context
// Pass nil for config to use default configuration
func NewAtlasContext(config *AtlasConfig) (*AtlasContext, error) {
	var ctx *C.AtlasBridgeContext

	if config == nil {
		ctx = C.atlas_ctx_new_default()
	} else {
		cfg := C.AtlasContextConfig{
			flags:      C.uint(config.Flags),
			block_size: C.uint(config.BlockSize),
			n_qubits:   C.uint(config.NQubits),
			twirl_gens: C.uint(config.TwirlGens),
			epsilon:    C.double(config.Epsilon),
			n_qbits:    C.uint(config.NQbits),
		}
		ctx = C.atlas_ctx_new(&cfg)
	}

	if ctx == nil {
		return nil, errors.New("failed to create Atlas context")
	}

	return &AtlasContext{ctx: ctx}, nil
}

// Free releases resources associated with the context
func (a *AtlasContext) Free() {
	if a.ctx != nil {
		C.atlas_ctx_free(a.ctx)
		a.ctx = nil
	}
}

// LoadLiftForms loads lift forms from hex file
func (a *AtlasContext) LoadLiftForms(filepath string) error {
	cPath := C.CString(filepath)
	defer C.free(unsafe.Pointer(cPath))

	result := C.atlas_ctx_load_lift_forms(a.ctx, cPath)
	if result != 0 {
		return errors.New("failed to load lift forms")
	}
	return nil
}

// LoadP299Matrix loads P_299 matrix from binary file (optional)
// Returns error if file cannot be loaded, but fallback logic will be used
func (a *AtlasContext) LoadP299Matrix(filepath string) error {
	cPath := C.CString(filepath)
	defer C.free(unsafe.Pointer(cPath))

	result := C.atlas_ctx_load_p299_matrix(a.ctx, cPath)
	if result != 0 {
		return errors.New("failed to load P_299 matrix (using fallback)")
	}
	return nil
}

// LoadCo1Gates loads Co1 gates from text file (optional)
func (a *AtlasContext) LoadCo1Gates(filepath string) error {
	cPath := C.CString(filepath)
	defer C.free(unsafe.Pointer(cPath))

	result := C.atlas_ctx_load_co1_gates(a.ctx, cPath)
	if result != 0 {
		return errors.New("failed to load Co1 gates")
	}
	return nil
}

// ApplyPClass applies P_class projector to state vector
func (a *AtlasContext) ApplyPClass(state []float64) error {
	if len(state) != int(a.BlockSize()) {
		return errors.New("state vector size mismatch")
	}

	result := C.atlas_ctx_apply_p_class(a.ctx, (*C.double)(&state[0]))
	if result != 0 {
		return errors.New("failed to apply P_class")
	}
	return nil
}

// ApplyP299 applies P_299 projector to state vector
func (a *AtlasContext) ApplyP299(state []float64) error {
	if len(state) != int(a.BlockSize()) {
		return errors.New("state vector size mismatch")
	}

	result := C.atlas_ctx_apply_p_299(a.ctx, (*C.double)(&state[0]))
	if result != 0 {
		return errors.New("failed to apply P_299")
	}
	return nil
}

// BlockSize returns the block size for this context
func (a *AtlasContext) BlockSize() uint32 {
	return uint32(C.atlas_ctx_get_block_size(a.ctx))
}

// NQubits returns the number of qubits for this context
func (a *AtlasContext) NQubits() uint32 {
	return uint32(C.atlas_ctx_get_n_qubits(a.ctx))
}

// EmitCertificate emits JSON certificate to file
func (a *AtlasContext) EmitCertificate(filepath, mode string) error {
	cPath := C.CString(filepath)
	defer C.free(unsafe.Pointer(cPath))
	cMode := C.CString(mode)
	defer C.free(unsafe.Pointer(cMode))

	result := C.atlas_ctx_emit_certificate(a.ctx, cPath, cMode)
	if result != 0 {
		return errors.New("failed to emit certificate")
	}
	return nil
}

// Version returns the library version
func Version() string {
	return C.GoString(C.atlas_ctx_version())
}
