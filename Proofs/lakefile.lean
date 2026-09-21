import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.32.2"

package «OneSidedTM» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «OneSidedTM» where
  srcDir := "."
  roots := #[`TM.Defs, `TagSystem.Basic, `TagSystem.TagToCTS, `TagSystem.HaltsEmpty, `BiTM.HaltInduction, `BiTM.Wolfram23Valid, `BiTM.XorMerge, `BiTM.System5, `BiTM.System4, `BiTM.System5ToSystem4, `BiTM.CTSToSystem5, `Smith.Simulation, `Smith.Doubling, `Smith.Represents, `Smith.System5Runs, `Smith.Conjecture5, `Smith.ConjectureFive, `Smith.System4Runs, `Smith.Conjecture4, `Smith.Lookahead, `Smith.Systems123, `Smith.LoopFree, `Smith.Wolfram23Bridge, `Tests.SmithVectors, `OneSidedTM.Basic, `OneSidedTM.PlusOne, `OneSidedTM.ClassC, `OneSidedTM.ClassW, `OneSidedTM.ClassB, `OneSidedTM.ClassR, `OneSidedTM.ClassS, `OneSidedTM.ClassSB, `OneSidedTM.ClassSX, `OneSidedTM.ClassWL, `OneSidedTM.ClassD, `OneSidedTM.ThreeState, `OneSidedTM.Decide, `OneSidedTM.Equiv, `OneSidedTM.AllPlusOne, `OneSidedTM.NearMiss, `BiTM.Basic]
