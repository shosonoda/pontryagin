import Lake
open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.32.0"

/- Path dependency on the parent package, so the blueprint chapters can
`import Pontryagin.Duality` etc. and `(lean := "…")` references resolve against
the real declarations. -/
require pontryagin from ".."

package PontryaginBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib PontryaginBlueprint where
