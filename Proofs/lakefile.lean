import Lake
open Lake DSL

-- VersoBlueprint first and Mathlib last, so that Mathlib's versions of the
-- shared dependencies (proofwidgets, plausible) take precedence and its
-- cache applies.
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint" @ "v4.34.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"

package «OneSidedTM» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «OneSidedTM» where
  srcDir := "."
  roots := #[`TM.Defs, `TagSystem.Basic, `TagSystem.TagToCTS, `TagSystem.HaltsEmpty, `TagSystem.TagRounds, `TagSystem.CockeMinsky, `TagSystem.TMToCTS, `TagSystem.TagBounds, `BiTM.HaltInduction, `BiTM.Wolfram23Valid, `BiTM.XorMerge, `BiTM.System5, `BiTM.System4, `BiTM.System5ToSystem4, `BiTM.CTSToSystem5, `Smith.Simulation, `Smith.Doubling, `Smith.Represents, `Smith.System5Runs, `Smith.Conjecture5, `Smith.ConjectureFive, `Smith.System4Runs, `Smith.Conjecture4, `Smith.Lookahead, `Smith.Systems123, `Smith.LoopFree, `Smith.Wolfram23Bridge, `Smith.ParityBlocks, `Smith.System3Runs, `Smith.Conjecture3, `Smith.Conjecture0, `Smith.Guards, `Smith.Universality, `Smith.Infinite, `Smith.RunBounds, `Smith.ClosedForm, `Vectors.SmithVectors, `Vectors.TMToCTSVectors, `Vectors.InfiniteVectors, `Vectors.ClosedFormVectors, `OneSidedTM.Basic, `OneSidedTM.PlusOne, `OneSidedTM.ClassC, `OneSidedTM.ClassW, `OneSidedTM.ClassB, `OneSidedTM.ClassR, `OneSidedTM.ClassS, `OneSidedTM.ClassSB, `OneSidedTM.ClassSX, `OneSidedTM.ClassWL, `OneSidedTM.ClassD, `OneSidedTM.ThreeState, `OneSidedTM.Decide, `OneSidedTM.Equiv, `OneSidedTM.AllPlusOne, `OneSidedTM.NearMiss, `BiTM.Basic]

/-- The Verso blueprint: one chapter module per link of the chain, the
    top-level document `Blueprint`, rendered by `lake exe vbp build`
    (entry point `BlueprintMain.lean`) to `_out/site/html-multi`. -/
lean_lib Blueprint where
  srcDir := "."
  roots := #[`Blueprint]
  globs := #[.andSubmodules `Blueprint]
  leanOptions := #[⟨`experimental.module, true⟩]
