import UOR.Prime.Structure
import UOR.Atlas.Core
import UOR.FFI.CAPI

/-!
# UOR Test Framework

This module provides comprehensive testing for the Prime Structure FFI implementation.
It validates all mathematical invariants, FFI exports, and core functionality.
-/

namespace UOR.Test

open UOR.Prime
open UOR.Atlas
open UOR.FFI

/-- Test result type -/
inductive TestResult
  | pass : String → TestResult
  | fail : String → String → TestResult
  deriving Repr

/-- Run a test and return the result -/
def runTest (name : String) (test : Bool) (msg : String := "") : TestResult :=
  if test then
    TestResult.pass name
  else
    TestResult.fail name msg

/-- Assert equality with descriptive error -/
def assertEqual {α : Type} [BEq α] [Repr α] (name : String) (expected : α) (actual : α) : TestResult :=
  if expected == actual then
    TestResult.pass name
  else
    TestResult.fail name s!"Expected {repr expected}, got {repr actual}"

/-- Assert a condition is true -/
def assertTrue (name : String) (condition : Bool) (msg : String := "Condition was false") : TestResult :=
  runTest name condition msg

/-- Assert a condition is false -/
def assertFalse (name : String) (condition : Bool) (msg : String := "Condition was true") : TestResult :=
  runTest name (!condition) msg

/-- Test suite runner -/
def runTestSuite (suiteName : String) (tests : List TestResult) : IO UInt32 := do
  IO.println s!"Running test suite: {suiteName}"
  IO.println "=" 
  
  let mut failures : List String := []
  let mut passCount := 0
  let mut failCount := 0
  
  for test in tests do
    match test with
    | TestResult.pass name => 
      IO.println s!"  ✓ {name}"
      passCount := passCount + 1
    | TestResult.fail name msg =>
      IO.println s!"  ✗ {name}: {msg}"
      failures := name :: failures
      failCount := failCount + 1
  
  IO.println ""
  IO.println s!"Results: {passCount} passed, {failCount} failed"
  
  if failCount > 0 then
    IO.println "\nFailed tests:"
    for failure in failures do
      IO.println s!"  - {failure}"
    pure 1
  else
    IO.println s!"✓ All tests passed!"
    pure 0

end UOR.Test