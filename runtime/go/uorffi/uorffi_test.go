package uorffi

import (
	"fmt"
	"testing"
)

func TestConstants(t *testing.T) {
	if GetPages() != 48 {
		t.Errorf("GetPages() = %d, want 48", GetPages())
	}
	if GetBytes() != 256 {
		t.Errorf("GetBytes() = %d, want 256", GetBytes())
	}
	if GetRClasses() != 96 {
		t.Errorf("GetRClasses() = %d, want 96", GetRClasses())
	}

	// Test constants
	if Pages != 48 {
		t.Errorf("Pages = %d, want 48", Pages)
	}
	if Bytes != 256 {
		t.Errorf("Bytes = %d, want 256", Bytes)
	}
	if RClasses != 96 {
		t.Errorf("RClasses = %d, want 96", RClasses)
	}
	if TotalElements != 12288 {
		t.Errorf("TotalElements = %d, want 12288", TotalElements)
	}
	if CompressionRatio != 0.375 {
		t.Errorf("CompressionRatio = %f, want 0.375", CompressionRatio)
	}
}

func TestR96Classifier(t *testing.T) {
	// Test that R96Classify returns values in range [0, 95]
	for i := 0; i < 256; i++ {
		result := R96Classify(byte(i))
		if result >= 96 {
			t.Errorf("R96Classify(%d) = %d, want < 96", i, result)
		}
	}

	// Test specific known values
	if R96Classify(0) != 0 {
		t.Errorf("R96Classify(0) = %d, want 0", R96Classify(0))
	}
	if R96Classify(95) != 95 {
		t.Errorf("R96Classify(95) = %d, want 95", R96Classify(95))
	}
	if R96Classify(96) != 0 {
		t.Errorf("R96Classify(96) = %d, want 0", R96Classify(96))
	}
}

func TestPhiEncoding(t *testing.T) {
	// Test encoding and decoding
	testCases := []struct {
		page, bt byte
	}{
		{0, 0},
		{3, 16},
		{47, 255},
		{10, 100},
	}

	for _, tc := range testCases {
		code := PhiEncode(tc.page, tc.bt)
		gotPage := PhiPage(code)
		gotByte := PhiByte(code)

		if gotPage != tc.page {
			t.Errorf("PhiPage(PhiEncode(%d, %d)) = %d, want %d",
				tc.page, tc.bt, gotPage, tc.page)
		}
		if gotByte != tc.bt {
			t.Errorf("PhiByte(PhiEncode(%d, %d)) = %d, want %d",
				tc.page, tc.bt, gotByte, tc.bt)
		}
	}
}

func TestTruth(t *testing.T) {
	if !TruthZero(0) {
		t.Error("TruthZero(0) = false, want true")
	}
	if TruthZero(1) {
		t.Error("TruthZero(1) = true, want false")
	}
	if !TruthAdd(0, 0) {
		t.Error("TruthAdd(0, 0) = false, want true")
	}
	if TruthAdd(1, 0) {
		t.Error("TruthAdd(1, 0) = true, want false")
	}
	if TruthAdd(1, 1) {
		t.Error("TruthAdd(1, 1) = true, want false")
	}
}

// Runtime Types Tests

func TestPhiCoordinate(t *testing.T) {
	// Test coordinate creation and encoding
	coord := NewPhiCoordinate(3, 16)
	if coord.Page != 3 || coord.Byte != 16 {
		t.Errorf("NewPhiCoordinate(3, 16) = {%d, %d}, want {3, 16}", coord.Page, coord.Byte)
	}

	// Test encoding and decoding
	code := coord.Encode()
	decoded := DecodePhiCoordinate(code)
	if decoded.Page != coord.Page || decoded.Byte != coord.Byte {
		t.Errorf("DecodePhiCoordinate(coord.Encode()) = {%d, %d}, want {%d, %d}",
			decoded.Page, decoded.Byte, coord.Page, coord.Byte)
	}

	// Test string representation
	str := coord.String()
	expected := "Φ(3,16)"
	if str != expected {
		t.Errorf("coord.String() = %s, want %s", str, expected)
	}

	// Test modulo behavior
	coord2 := NewPhiCoordinate(51, 44) // 300 & 0xFF = 44
	if coord2.Page != 3 {              // 51 % 48 = 3
		t.Errorf("NewPhiCoordinate(51, 44).Page = %d, want 3", coord2.Page)
	}
	if coord2.Byte != 44 {
		t.Errorf("NewPhiCoordinate(51, 44).Byte = %d, want 44", coord2.Byte)
	}
}

func TestResonanceClass(t *testing.T) {
	rc := ClassifyResonance(100)
	expected := R96Classify(100)
	if rc.Value != expected {
		t.Errorf("ClassifyResonance(100).Value = %d, want %d", rc.Value, expected)
	}

	str := rc.String()
	expectedStr := fmt.Sprintf("R96[%d]", expected)
	if str != expectedStr {
		t.Errorf("rc.String() = %s, want %s", str, expectedStr)
	}
}

func TestConservation(t *testing.T) {
	c := Conservation{}

	if !c.IsZero(0) {
		t.Error("Conservation.IsZero(0) = false, want true")
	}
	if c.IsZero(42) {
		t.Error("Conservation.IsZero(42) = true, want false")
	}
	if !c.SumIsZero(0, 0) {
		t.Error("Conservation.SumIsZero(0, 0) = false, want true")
	}
	if c.SumIsZero(1, 2) {
		t.Error("Conservation.SumIsZero(1, 2) = true, want false")
	}
}
