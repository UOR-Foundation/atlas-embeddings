package uor

import (
	"testing"
)

func TestConstants(t *testing.T) {
	Initialize()
	defer Finalize()
	
	if got := GetPages(); got != 48 {
		t.Errorf("GetPages() = %d, want 48", got)
	}
	if got := GetBytes(); got != 256 {
		t.Errorf("GetBytes() = %d, want 256", got)
	}
	if got := GetRClasses(); got != 96 {
		t.Errorf("GetRClasses() = %d, want 96", got)
	}
	if got := TotalElements(); got != 12288 {
		t.Errorf("TotalElements() = %d, want 12288", got)
	}
}

func TestR96Classifier(t *testing.T) {
	Initialize()
	defer Finalize()
	
	// Test specific values
	tests := []struct {
		input byte
		want  byte
	}{
		{0, 0},
		{95, 95},
		{96, 0},
		{255, 63},
	}
	
	for _, tt := range tests {
		if got := R96Classify(tt.input); got != tt.want {
			t.Errorf("R96Classify(%d) = %d, want %d", tt.input, got, tt.want)
		}
	}
	
	// Test range
	for i := 0; i < 256; i++ {
		cls := R96Classify(byte(i))
		if cls >= 96 {
			t.Errorf("R96Classify(%d) = %d, should be < 96", i, cls)
		}
	}
	
	// Test periodicity
	for i := 0; i < 96; i++ {
		cls1 := R96Classify(byte(i))
		cls2 := R96Classify(byte(i + 96))
		if cls1 != cls2 {
			t.Errorf("R96 not periodic: R96(%d) = %d, R96(%d) = %d", i, cls1, i+96, cls2)
		}
	}
}

func TestPhiEncoding(t *testing.T) {
	Initialize()
	defer Finalize()
	
	// Test round-trip
	for page := byte(0); page < 48; page++ {
		for b := 0; b < 256; b += 17 {
			bb := byte(b)
			code := PhiEncode(page, bb)
			if gotPage := PhiPage(code); gotPage != page {
				t.Errorf("PhiPage round-trip failed: page %d -> %d", page, gotPage)
			}
			if gotByte := PhiByte(code); gotByte != bb {
				t.Errorf("PhiByte round-trip failed: byte %d -> %d", bb, gotByte)
			}
		}
	}
	
	// Test coordinate type
	coord := PhiCoordinate{Page: 3, Byte: 16}
	code := coord.Encode()
	decoded := DecodePhiCoordinate(code)
	
	if decoded.Page != coord.Page || decoded.Byte != coord.Byte {
		t.Errorf("PhiCoordinate round-trip failed: %v -> %v", coord, decoded)
	}
	
	if str := coord.String(); str != "Φ(3,16)" {
		t.Errorf("PhiCoordinate.String() = %s, want Φ(3,16)", str)
	}
}

func TestTruthConservation(t *testing.T) {
	Initialize()
	defer Finalize()
	
	// Test truth zero
	if !TruthZero(0) {
		t.Error("TruthZero(0) should be true")
	}
	if TruthZero(1) {
		t.Error("TruthZero(1) should be false")
	}
	if TruthZero(100) {
		t.Error("TruthZero(100) should be false")
	}
	
	// Test truth add
	if !TruthAdd(0, 0) {
		t.Error("TruthAdd(0, 0) should be true")
	}
	if TruthAdd(1, 0) {
		t.Error("TruthAdd(1, 0) should be false")
	}
	if TruthAdd(5, 10) {
		t.Error("TruthAdd(5, 10) should be false")
	}
	
	// Test overflow wrapping
	if !TruthAdd(0xFFFFFFFF, 1) {
		t.Error("TruthAdd(MAX, 1) should wrap to 0 (true)")
	}
}

func TestCompressionRatio(t *testing.T) {
	ratio := CompressionRatio()
	expected := 3.0 / 8.0
	if ratio != expected {
		t.Errorf("CompressionRatio() = %f, want %f", ratio, expected)
	}
}

func TestResonanceClass(t *testing.T) {
	Initialize()
	defer Finalize()
	
	rc := Classify(100)
	if rc != 4 {
		t.Errorf("Classify(100) = %d, want 4", rc)
	}
	
	// Verify all classes are produced
	classMap := make(map[ResonanceClass]bool)
	for i := 0; i < 256; i++ {
		classMap[Classify(byte(i))] = true
	}
	if len(classMap) != 96 {
		t.Errorf("Should produce all 96 classes, got %d", len(classMap))
	}
}

func BenchmarkR96Classify(b *testing.B) {
	Initialize()
	defer Finalize()
	
	for i := 0; i < b.N; i++ {
		_ = R96Classify(byte(i & 0xFF))
	}
}

func BenchmarkPhiEncode(b *testing.B) {
	Initialize()
	defer Finalize()
	
	for i := 0; i < b.N; i++ {
		_ = PhiEncode(byte(i&0x2F), byte(i&0xFF))
	}
}

func BenchmarkPhiDecode(b *testing.B) {
	Initialize()
	defer Finalize()
	
	for i := 0; i < b.N; i++ {
		code := uint32(i)
		_ = PhiPage(code)
		_ = PhiByte(code)
	}
}