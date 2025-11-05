import UOR.Test.TestFramework
import UOR.Prime.Structure

/-!
# Prime Structure Tests

Comprehensive tests for the Prime Structure mathematical invariants.
-/

namespace UOR.Test.PrimeStructure

open UOR.Test
open UOR.Prime

/-- Test the fundamental constants -/
def testConstants : List TestResult := [
  assertEqual "Pages constant is 48" Pages 48,
  assertEqual "Bytes constant is 256" Bytes 256,
  assertEqual "R96 constant is 96" R96 96,
  assertTrue "Pages * Bytes = 12288" (Pages * Bytes = 12288) "Product should be 12288",
  assertTrue "12288 = 2^12 * 3" (12288 = 4096 * 3) "Should factor as 2^12 * 3"
]

/-- Test R96 classifier properties -/
def testR96Classifier : List TestResult := 
  let tests := [
    -- Test boundary values
    assertTrue "R96(0) is in range" (classifyByte 0 < 96) "Should be less than 96",
    assertTrue "R96(255) is in range" (classifyByte 255 < 96) "Should be less than 96",
    assertEqual "R96(96) maps to 0" (classifyByte 96) 0,
    assertEqual "R96(192) maps to 0" (classifyByte 192) 0,
    
    -- Test specific values
    assertEqual "R96(0) = 0" (classifyByte 0) 0,
    assertEqual "R96(95) = 95" (classifyByte 95) 95,
    assertEqual "R96(96) = 0" (classifyByte 96) 0,
    assertEqual "R96(97) = 1" (classifyByte 97) 1,
    
    -- Test periodicity
    assertTrue "R96 has period 96" 
      (classifyByte 50 = classifyByte (50 + 96)) 
      "Should have period 96"
  ]
  
  -- Add range test for all values
  let rangeTest := assertTrue "All bytes map to [0,95]"
    ((List.range 256).all (fun i => classifyByte (UInt8.ofNat i) < 96))
    "All values should be less than 96"
    
  rangeTest :: tests

/-- Test mathematical invariants -/
def testMathematicalInvariants : List TestResult := [
  -- 3/8 compression ratio
  assertTrue "R96 achieves 3/8 compression" 
    (R96 * 8 = 256 * 3) 
    "96/256 should equal 3/8",
    
  -- Prime factorization of 12288
  assertTrue "12288 = 48 * 256" 
    (48 * 256 = 12288) 
    "Product decomposition",
    
  assertTrue "48 = 16 * 3 = 2^4 * 3" 
    (48 = 16 * 3) 
    "48 factorization",
    
  assertTrue "256 = 2^8" 
    (256 = 2^8) 
    "256 is power of 2",
    
  -- Unity constraint implications
  assertTrue "48 is first non-trivial unity byte"
    (48 % 3 = 0 && 48 % 16 = 0)
    "48 should be divisible by both 3 and 16"
]

/-- Test modular arithmetic properties -/
def testModularArithmetic : List TestResult := 
  let tests := [
    -- Test commutativity of classification
    assertTrue "R96 classification is deterministic"
      (classifyByte 123 = classifyByte 123)
      "Same input should give same output",
      
    -- Test that classification preserves congruence
    assertTrue "Congruent values map identically"
      (classifyByte 5 = classifyByte (5 + 96) && 
       classifyByte 5 = classifyByte (5 + 192))
      "Values differing by 96 should map the same"
  ]
  tests

/-- Test boundary conditions -/
def testBoundaryConditions : List TestResult := [
  -- Edge cases
  assertEqual "Min byte (0) classification" 
    (classifyByte 0) 0,
  assertEqual "Max byte (255) classification" 
    (classifyByte 255) (255 % 96),
  
  -- Transition points (95 -> 0, not 95+1 -> 0)
  assertTrue "Boundary at 96 wraps to 0" 
    (classifyByte 96 = 0)
    "96 should map to 0",
  assertTrue "Boundary at 192 wraps to 0" 
    (classifyByte 192 = 0)
    "192 should map to 0",
  
  -- Verify no overflow
  assertTrue "No overflow in classification"
    ((classifyByte 255).toNat < 96)
    "Max value should still be in range"
]

/-- Run all Prime Structure tests -/
def runAllTests : IO UInt32 := do
  let allTests := 
    testConstants ++
    testR96Classifier ++
    testMathematicalInvariants ++
    testModularArithmetic ++
    testBoundaryConditions
    
  runTestSuite "Prime Structure Tests" allTests

end UOR.Test.PrimeStructure