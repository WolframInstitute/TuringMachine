import Lake
open Lake DSL

-- The Verso blueprint (Blueprint.lean, BlueprintMain.lean, Blueprint/) is not
-- built while verso-blueprint has no v4.36 branch; it returns as its own
-- `require VersoBlueprint ... @ "v4.36.0"` and `lean_lib Blueprint` then.
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.36.0"

package «OneSidedTM» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «OneSidedTM» where
  srcDir := "."
  roots := #[`Wolfram23, `OneSidedTM.Basic, `OneSidedTM.PlusOne, `OneSidedTM.ClassC, `OneSidedTM.ClassW, `OneSidedTM.ClassB, `OneSidedTM.ClassR, `OneSidedTM.ClassS, `OneSidedTM.ClassSB, `OneSidedTM.ClassSX, `OneSidedTM.ClassWL, `OneSidedTM.ClassD, `OneSidedTM.ThreeState, `OneSidedTM.Decide, `OneSidedTM.Equiv, `OneSidedTM.AllPlusOne, `OneSidedTM.NearMiss]

/-- Optional corollaries outside the headline theorems' imports: T5
    (loop-freeness of the lookahead systems and of wolfram23) and the
    closed-form initial conditions of milestone M9 (`wolfram23_universal_ic`,
    `wolfram23_infinite_ic`). `lake build Extras`. -/
lean_lib Extras where
  srcDir := "."
  roots := #[`Extras.LoopFree, `Extras.RunBounds, `Extras.ClosedForm, `Extras.TagBounds,
    `Extras.UniversalityClosed, `Extras.InfiniteClosed]

/-- The regression vectors: runs of every system checked by `decide` and by
    kernel reduction, and the vectors that `scripts/ExportVectors.lean` exports
    for the paclet's tests. `lake build Vectors`. -/
lean_lib Vectors where
  srcDir := "."
  roots := #[`Vectors.SmithVectors, `Vectors.TMToCTSVectors, `Vectors.InfiniteVectors, `Vectors.ClosedFormVectors]
