import Lake
open Lake DSL

package «OneSidedTM» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «OneSidedTM» where
  srcDir := "."
  roots := #[`TM.Defs, `TagSystem.Basic, `TagSystem.TagToCTS, `OneSidedTM.Basic, `OneSidedTM.PlusOne, `OneSidedTM.ClassC, `OneSidedTM.ClassW, `OneSidedTM.ClassSX, `OneSidedTM.ClassWL, `OneSidedTM.Decide, `OneSidedTM.Equiv, `OneSidedTM.AllPlusOne, `OneSidedTM.NearMiss, `BiTM.Basic, `BiTM.CockeMinsky]
