import UOR.Test.TestFramework
import UOR.FFI.CAPI

/-!
# FFI Export Tests

Tests for FFI C API exports and functionality.
-/

namespace UOR.Test.FFI

open UOR.Test
open UOR.FFI
open UOR.Prime

/-- Test FFI constants -/
def testFFIConstants : List TestResult := [
  assertEqual "ABI version is 1" abiVersion 1,
  assertEqual "c_pages matches Pages" c_pages.toNat Pages,
  assertEqual "c_bytes matches Bytes" c_bytes.toNat Bytes,
  assertEqual "c_rclasses matches R96" c_rclasses.toNat R96,
  
  -- Verify exported values
  assertTrue "Exported pages = 48"
    (c_pages = 48)
    "Should export correct page count",
  assertTrue "Exported bytes = 256"
    (c_bytes = 256)
    "Should export correct byte count",
  assertTrue "Exported rclasses = 96"
    (c_rclasses = 96)
    "Should export correct class count"
]

/-- Test Phi encoding/decoding -/
def testPhiEncoding : List TestResult := 
  let testCases := [
    (0, 0, 0),           -- Min values
    (47, 255, 12287),    -- Max values
    (3, 16, 784),        -- Example from docs
    (10, 100, 2660),     -- Random values
    (0, 255, 255),       -- Edge case
    (47, 0, 12032)       -- Edge case
  ]
  
  testCases.map (fun (page, byte, expected) =>
    let pageU8 := UInt8.ofNat page
    let byteU8 := UInt8.ofNat byte
    let encoded := phiEncode pageU8 byteU8
    let decodedPage := phiPage encoded
    let decodedByte := phiByte encoded
    
    assertTrue s!"Phi encode/decode ({page},{byte})"
      (encoded.toNat = expected && 
       decodedPage = pageU8 && 
       decodedByte = byteU8)
      s!"Encoding or decoding failed"
  )

/-- Test R96 classification via FFI -/
def testFFIR96 : List TestResult := 
  let testValues := [0, 1, 95, 96, 97, 191, 192, 255]
  
  testValues.map (fun val =>
    let input := UInt8.ofNat val
    let result := c_r96 input
    let expected := classifyByte input
    
    assertEqual s!"FFI R96({val})" result expected
  )

/-- Test truth/conservation helpers -/
def testTruthHelpers : List TestResult := [
  -- Truth zero tests
  assertEqual "truth(0) = true" (truth 0) true,
  assertEqual "truth(1) = false" (truth 1) false,
  assertEqual "truth(100) = false" (truth 100) false,
  
  assertEqual "c_truthZero(0) = 1" (c_truthZero 0) 1,
  assertEqual "c_truthZero(1) = 0" (c_truthZero 1) 0,
  
  -- Truth addition tests
  assertEqual "truthAdd(0,0) = true" (truthAdd 0 0) true,
  assertEqual "truthAdd(1,0) = false" (truthAdd 1 0) false,
  assertEqual "truthAdd(1,1) = false" (truthAdd 1 1) false,
  
  assertEqual "c_truthAdd(0,0) = 1" (c_truthAdd 0 0) 1,
  assertEqual "c_truthAdd(1,0) = 0" (c_truthAdd 1 0) 0,
  assertEqual "c_truthAdd(5,5) = 0" (c_truthAdd 5 5) 0,
  
  -- Conservation law: only (0,0) gives truth
  assertTrue "Only (0,0) conserves"
    (c_truthAdd 0 0 = 1 && c_truthAdd 0 1 = 0)
    "Conservation should only hold for (0,0)"
]

/-- Test boundary conditions for FFI -/
def testFFIBoundaries : List TestResult := [
  -- Test page boundaries (mod 48)
  assertEqual "phiPage handles overflow"
    (phiPage (phiEncode 50 0)) 
    (UInt8.ofNat (50 % 48)),
    
  -- Test byte extraction
  assertEqual "phiByte extracts low 8 bits"
    (phiByte 0x1234) 
    (UInt8.ofNat 0x34),
    
  -- Test max values
  assertTrue "Max encoding fits in UInt32"
    ((phiEncode 47 255).toNat < UInt32.size)
    "Should not overflow UInt32"
]

/-- Test FFI export attributes -/
def testExportConsistency : List TestResult := [
  -- Verify that FFI exports match internal functions
  assertTrue "c_r96 matches classifyByte"
    ((List.range 256).all (fun i => 
      let b := UInt8.ofNat i
      c_r96 b = classifyByte b))
    "FFI and internal should match",
    
  -- Verify encoding consistency
  assertTrue "Phi encoding is bijective"
    ((List.range 48).all (fun p =>
      (List.range 256).all (fun b =>
        let pu := UInt8.ofNat p
        let bu := UInt8.ofNat b
        let code := c_phiEncode pu bu
        c_phiPage code = pu && c_phiByte code = bu)))
    "Should be able to round-trip encode/decode"
]

/-- Run all FFI tests -/
def runAllTests : IO UInt32 := do
  let allTests := 
    testFFIConstants ++
    testPhiEncoding ++
    testFFIR96 ++
    testTruthHelpers ++
    testFFIBoundaries ++
    testExportConsistency
    
  runTestSuite "FFI Export Tests" allTests

end UOR.Test.FFI