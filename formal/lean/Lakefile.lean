import Lake
open Lake DSL

package «formal» where
  moreLeanArgs := #["-DsynthInstance.maxHeartbeats=2000000"]

@[default_target] lean_lib «Formal»
