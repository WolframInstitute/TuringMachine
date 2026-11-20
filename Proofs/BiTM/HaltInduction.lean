/-
  BiTM.HaltInduction

  The algebra of `nSteps` for the bi-infinite Turing machine model.

  Contents: `BiTM_nSteps_succ_unfold`, `nSteps_one`, `nSteps_add`,
  `BiTM_nSteps_some_compose`.
-/

import BiTM.Basic
import TagSystem.Basic
import TagSystem.TagToCTS

namespace BiTM

open TM
open TagSystem

/-- Helper: `BiTM.nSteps tm cfg (n+1)` unfolds to the match. -/
theorem BiTM_nSteps_succ_unfold (tm : Machine) (cfg : Config) (n : Nat) :
    nSteps tm cfg (n + 1)
    = match step tm cfg with
      | none => none
      | some cfg' => nSteps tm cfg' n := rfl

/-- BiTM analog of `tagNSteps_one`: one step is `step`. -/
theorem nSteps_one (tm : Machine) (cfg : Config) :
    nSteps tm cfg 1 = step tm cfg := by
  show (match step tm cfg with
        | none => none
        | some cfg' => nSteps tm cfg' 0) = step tm cfg
  cases step tm cfg <;> rfl

/-- BiTM analog of `tagNSteps_add`: nSteps composes additively. -/
theorem nSteps_add (tm : Machine) (cfg : Config) (n m : Nat) :
    nSteps tm cfg (n + m) = (nSteps tm cfg n).bind (fun c => nSteps tm c m) := by
  induction n generalizing cfg with
  | zero =>
    rw [Nat.zero_add]
    simp [nSteps]
  | succ n ih =>
    rw [Nat.succ_add]
    show (match step tm cfg with
          | none => none
          | some cfg' => nSteps tm cfg' (n + m))
        = (match step tm cfg with
            | none => none
            | some cfg' => nSteps tm cfg' n).bind
          (fun c => nSteps tm c m)
    cases step tm cfg with
    | none => rfl
    | some c => exact ih c

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

