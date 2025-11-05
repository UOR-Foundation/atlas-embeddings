import UOR.FFI.CAPI
open UOR.FFI

def main (_args : List String) : IO UInt32 := do
  -- Smoke-test the exported functions without leaving Lean.
  let ok1 := (c_pages == 48) && (c_bytes == 256) && (c_rclasses == 96)
  let ok2 := (c_r96 0xFF) ≤ 95
  let code := c_phiEncode 3 0x10
  let pg := c_phiPage code
  let bt := c_phiByte code
  let ok3 := (pg == 3) && (bt == 0x10)
  let ok4 := (c_truthZero 0 == 1) && (c_truthAdd 0 0 == 1) && (c_truthAdd 1 0 == 0)
  pure (if ok1 && ok2 && ok3 && ok4 then 0 else 1)