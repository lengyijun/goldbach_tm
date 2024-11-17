import Lake
open Lake DSL

package "goldbach_tm" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «GoldbachTm» where
  -- add any library configuration options here

lean_exe «sim31» where
  root := `GoldbachTm.Tm31.Sim31

lean_exe «sim25» where
  root := `GoldbachTm.Tm25.Sim25

lean_exe «SearchUnvisitedBranch» where
  root := `GoldbachTm.Tm25.SearchUnvisitedBranch
