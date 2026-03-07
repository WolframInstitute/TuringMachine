import Lake
open Lake DSL

package «OneSidedTM» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «OneSidedTM» where
  srcDir := "."
  roots := #[`OneSidedTM.Basic, `OneSidedTM.PlusOne, `OneSidedTM.Decide, `OneSidedTM.Equiv]
