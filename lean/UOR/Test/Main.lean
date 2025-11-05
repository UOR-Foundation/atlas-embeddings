import UOR.Test.PrimeStructureTest
import UOR.Test.AtlasCoreTest
import UOR.Test.FFITest

/-!
# Main Test Runner

Runs all test suites and reports comprehensive results.
-/

/-- Main test entry point -/
def main (_args : List String) : IO UInt32 := do
  IO.println "═══════════════════════════════════════"
  IO.println "    UOR Prime Structure Test Suite"
  IO.println "═══════════════════════════════════════"
  IO.println ""
  
  let mut exitCode : UInt32 := 0
  
  -- Run Prime Structure tests
  IO.println "▶ Prime Structure Tests"
  let primeResult ← UOR.Test.PrimeStructure.runAllTests
  if primeResult ≠ 0 then exitCode := 1
  IO.println ""
  
  -- Run Atlas Core tests
  IO.println "▶ Atlas Core Tests"
  let atlasResult ← UOR.Test.AtlasCore.runAllTests
  if atlasResult ≠ 0 then exitCode := 1
  IO.println ""
  
  -- Run FFI tests
  IO.println "▶ FFI Export Tests"
  let ffiResult ← UOR.Test.FFI.runAllTests
  if ffiResult ≠ 0 then exitCode := 1
  IO.println ""
  
  -- Final summary
  IO.println "═══════════════════════════════════════"
  if exitCode = 0 then
    IO.println "✅ ALL TEST SUITES PASSED"
  else
    IO.println "❌ SOME TESTS FAILED"
  IO.println "═══════════════════════════════════════"
  
  pure exitCode