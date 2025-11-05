import Lake
open Lake DSL

package «uor-ffi» where
  -- Build as a library that other languages link against.
  -- Compile with C code generation for FFI
  moreServerOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  -- Build native code
  buildType := .release
  moreLinkArgs := #[
    "-L.lake/build/lib",
    "-Wl,-rpath,.lake/build/lib"
  ]

@[default_target]
lean_lib UOR where
  -- Root namespace for the Lean library
  roots := #[`UOR]
  srcDir := "lean"
  -- Build native code for FFI
  precompileModules := true
  -- Build type
  buildType := .release

lean_exe «uor-verify» where
  root := `UOR.Verify.CLI
  srcDir := "lean"

lean_exe «uor-test» where
  root := `UOR.Test.Main
  srcDir := "lean"