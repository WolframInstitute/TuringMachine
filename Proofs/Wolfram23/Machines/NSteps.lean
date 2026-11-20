/-
  Wolfram23.Machines.NSteps

  The algebra of `nSteps` for the bi-infinite Turing machine model.

  Contents: `BiTM_nSteps_succ_unfold`, `nSteps_one`, `nSteps_add`,
  `BiTM_nSteps_some_compose`.
-/

import Wolfram23.Machines.BiTM
import Wolfram23.Machines.TagCTS
import Wolfram23.TagToCTS.Cook

namespace BiTM

open TM
open TagSystem

/-- Helper: `BiTM.nSteps tm cfg (n+1)` unfolds to the match. -/
theorem BiTM_nSteps_succ_unfold (tm : Machine) (cfg : Config) (n : Nat) :
    nSteps tm cfg (n + 1)
    = match step tm cfg with
      | none => none
      | some cfg' => nSteps tm cfg' n := by
  show (tmSys tm).nSteps cfg (n + 1) = _
  rw [Smith.StepSys.nSteps_succ_left]
  show ((step tm cfg).bind fun c => (tmSys tm).nSteps c n) = _
  cases step tm cfg <;> rfl

/-- One step is `step`. -/
theorem nSteps_one (tm : Machine) (cfg : Config) : nSteps tm cfg 1 = step tm cfg :=
  Smith.StepSys.nSteps_one _ _

/-- Steps add. -/
theorem nSteps_add (tm : Machine) (cfg : Config) (n m : Nat) :
    nSteps tm cfg (n + m) = (nSteps tm cfg n).bind (fun c => nSteps tm c m) :=
  Smith.StepSys.nSteps_add _ _ _ _

-- ============================================================================
-- BiTM halt-related nSteps cluster
-- ============================================================================

/-- **BiTM `nSteps` compose**: BiTM analogue of `CTS_nSteps_some_compose`. -/
theorem BiTM_nSteps_some_compose (tm : Machine) (cfg mid : Config)
    (n m : Nat) (result : Config)
    (h_n : nSteps tm cfg n = some mid)
    (h_m : nSteps tm mid m = some result) :
    nSteps tm cfg (n + m) = some result := by
  rw [nSteps_add, h_n]
  exact h_m

