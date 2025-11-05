import UOR.Test.TestFramework
import UOR.Atlas.Core

/-!
# Atlas Core Tests

Tests for the Φ-Atlas-12288 core structure.
-/

namespace UOR.Test.AtlasCore

open UOR.Test
open UOR.Atlas
open UOR.Prime

/-- Test Atlas Core structure initialization -/
def testAtlasStructure : List TestResult := [
  assertEqual "Atlas pages match Prime pages" 
    phiAtlas12288.pages Pages,
  assertEqual "Atlas bytes match Prime bytes" 
    phiAtlas12288.bytes Bytes,
  assertEqual "Atlas rclasses match R96" 
    phiAtlas12288.rclasses R96,
  
  -- Test derived properties
  assertTrue "Total elements = 12288"
    (phiAtlas12288.pages * phiAtlas12288.bytes = 12288)
    "Should have 12288 boundary elements",
    
  assertTrue "Resonance compression = 3/8"
    (phiAtlas12288.rclasses * 8 = phiAtlas12288.bytes * 3)
    "Should achieve 3/8 compression"
]

/-- Test Φ-Atlas invariants -/
def testPhiInvariants : List TestResult := [
  -- Structural invariants
  assertTrue "Atlas is properly initialized"
    (phiAtlas12288.pages > 0 && phiAtlas12288.bytes > 0)
    "Dimensions should be positive",
    
  assertTrue "R96 < Bytes"
    (phiAtlas12288.rclasses < phiAtlas12288.bytes)
    "Resonance classes should compress byte space",
    
  -- Mathematical relationships
  assertTrue "Pages divides 12288"
    (12288 % phiAtlas12288.pages = 0)
    "Pages should divide total elements",
    
  assertTrue "Bytes is power of 2"
    (phiAtlas12288.bytes = 256 && 256 = 2^8)
    "Bytes should be 2^8"
]

/-- Test the canonical instance properties -/
def testCanonicalInstance : List TestResult := [
  -- Verify the singleton nature
  assertEqual "Canonical instance pages" 
    phiAtlas12288.pages 48,
  assertEqual "Canonical instance bytes" 
    phiAtlas12288.bytes 256,
  assertEqual "Canonical instance rclasses" 
    phiAtlas12288.rclasses 96,
    
  -- Test that default construction matches canonical  
  assertEqual "Default matches canonical (pages)"
    (@Core.mk Pages Bytes R96).pages phiAtlas12288.pages,
  assertEqual "Default matches canonical (bytes)"
    (@Core.mk Pages Bytes R96).bytes phiAtlas12288.bytes,
  assertEqual "Default matches canonical (rclasses)"
    (@Core.mk Pages Bytes R96).rclasses phiAtlas12288.rclasses
]

/-- Test mathematical consistency -/
def testMathematicalConsistency : List TestResult := [
  -- Verify key mathematical facts
  assertTrue "48 = 3 * 16"
    (48 = 3 * 16)
    "Page count factorization",
    
  assertTrue "96 = 3 * 32"
    (96 = 3 * 32)
    "Resonance class factorization",
    
  assertTrue "gcd(48, 256) = 16"
    (Nat.gcd 48 256 = 16)
    "GCD of pages and bytes",
    
  assertTrue "lcm(48, 96) = 96"
    (Nat.lcm 48 96 = 96)
    "LCM of pages and rclasses"
]

/-- Run all Atlas Core tests -/
def runAllTests : IO UInt32 := do
  let allTests := 
    testAtlasStructure ++
    testPhiInvariants ++
    testCanonicalInstance ++
    testMathematicalConsistency
    
  runTestSuite "Atlas Core Tests" allTests

end UOR.Test.AtlasCore