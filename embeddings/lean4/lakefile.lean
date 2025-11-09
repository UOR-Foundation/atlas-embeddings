import Lake
open Lake DSL

package «AtlasEmbeddings» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «AtlasEmbeddings» where
  globs := #[.submodules `AtlasEmbeddings]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.23.0"

lean_exe «atlas-embeddings» where
  root := `Main
  supportInterpreter := true
