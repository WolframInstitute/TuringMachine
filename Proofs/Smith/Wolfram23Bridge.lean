/-
  Smith.Wolfram23Bridge

  System 0 of `Smith.Lookahead` is Wolfram's (2,3) machine `BiTM.wolfram23`
  on a finite tape.  `toBi` reads a System 0 configuration as a
  `BiTM.Config` (state A is 1, B is 2, the zipper is the same zipper); a
  System 0 step is a `wolfram23` step (`toBi_step`), and where System 0
  leaves its tape `wolfram23` steps onto a blank cell and its explicit
  tape grows by one (`toBi_exit`).  Every valid `wolfram23` configuration
  is `toBi` of a System 0 configuration (`toBi_ofBi`, in `Smith.LoopFree`,
  where T5 for Wolfram's machine is proved).
-/

import Smith.Systems123
import BiTM.Wolfram23Valid

namespace Smith

open TM
open BiTM
open LState

/-- States: A is 1, B is 2 (and C, never reached, is 3). -/
def stateNat : LState → Nat
  | A => 1
  | B => 2
  | C => 3

/-- A System 0 configuration as a `wolfram23` configuration. -/
def toBi (c : LConfig) : BiTM.Config :=
  ⟨stateNat c.state, c.left.map Fin.val, c.head.val, c.right.map Fin.val⟩

/-- The number of explicit cells of a `BiTM.Config`. -/
def biSize (cfg : BiTM.Config) : Nat := cfg.left.length + 1 + cfg.right.length

theorem biSize_toBi (c : LConfig) : biSize (toBi c) = c.toList.length := by
  simp [biSize, toBi, LConfig.toList]
  omega

/-- A run never changes the length of the tape. -/
theorem lnSteps_length (M : LMachine) (c : LConfig) (n : Nat) (c' : LConfig)
    (h : lnSteps M c n = some c') : c'.toList.length = c.toList.length := by
  induction n generalizing c with
  | zero => rw [lnSteps_zero] at h; obtain rfl := Option.some.inj h; rfl
  | succ n ih =>
    rw [lnSteps_succ] at h
    cases hs : lstep M c with
    | none => rw [hs] at h; simp at h
    | some c1 =>
      rw [hs, Option.bind_some] at h
      rw [ih c1 h, lstep_length M c c1 hs]

/-- System 0 never enters state C from A or B. -/
theorem sys0_state (c c' : LConfig) (hst : c.state ≠ C) (h : lstep sys0 c = some c') :
    c'.state ≠ C := by
  obtain ⟨L, a, R, st⟩ := c
  rcases R with _ | ⟨b, R'⟩ <;> rcases L with _ | ⟨x, L'⟩ <;> cases st
  all_goals (try exact absurd rfl hst)
  all_goals fin_cases a
  all_goals (simp [lstep, sys0] at h)
  all_goals (subst h; simp)

/-- A System 0 step is a `wolfram23` step. -/
theorem toBi_step (c c' : LConfig) (hst : c.state ≠ C) (h : lstep sys0 c = some c') :
    BiTM.step wolfram23 (toBi c) = some (toBi c') := by
  obtain ⟨L, a, R, st⟩ := c
  rcases R with _ | ⟨b, R'⟩ <;> rcases L with _ | ⟨x, L'⟩ <;> cases st
  all_goals (try exact absurd rfl hst)
  all_goals fin_cases a
  all_goals (simp [lstep, sys0] at h)
  all_goals (subst h; simp [BiTM.step, wolfram23, toBi, stateNat, BiTM.readHead])

/-- Where System 0 leaves its tape, `wolfram23` steps onto a blank and its
    explicit tape grows by one cell. -/
theorem toBi_exit (c : LConfig) (hst : c.state ≠ C) (h : lstep sys0 c = none) :
    ∃ cfg', BiTM.step wolfram23 (toBi c) = some cfg' ∧ biSize cfg' = biSize (toBi c) + 1 := by
  obtain ⟨L, a, R, st⟩ := c
  rcases R with _ | ⟨b, R'⟩ <;> rcases L with _ | ⟨x, L'⟩ <;> cases st
  all_goals (try exact absurd rfl hst)
  all_goals fin_cases a
  all_goals (simp [lstep, sys0] at h)
  all_goals (refine ⟨_, rfl, ?_⟩; simp [biSize, toBi] <;> omega)

/-- A System 0 run is a `wolfram23` run. -/
theorem toBi_run (c : LConfig) (hst : c.state ≠ C) (n : Nat) (c' : LConfig)
    (h : lnSteps sys0 c n = some c') :
    BiTM.nSteps wolfram23 (toBi c) n = some (toBi c') ∧ c'.state ≠ C := by
  induction n generalizing c with
  | zero =>
    rw [lnSteps_zero] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, hst⟩
  | succ n ih =>
    rw [lnSteps_succ] at h
    cases hs : lstep sys0 c with
    | none => rw [hs] at h; simp at h
    | some c1 =>
      rw [hs, Option.bind_some] at h
      obtain ⟨h1, hst1⟩ := ih c1 (sys0_state c c1 hst hs) h
      refine ⟨?_, hst1⟩
      show (match BiTM.step wolfram23 (toBi c) with
            | none => none
            | some cfg' => BiTM.nSteps wolfram23 cfg' n) = some (toBi c')
      rw [toBi_step c c1 hst hs]
      exact h1

theorem biNSteps_add (tm : Machine) (cfg : BiTM.Config) (n m : Nat) :
    BiTM.nSteps tm cfg (n + m) = (BiTM.nSteps tm cfg n).bind fun c => BiTM.nSteps tm c m := by
  induction n generalizing cfg with
  | zero => simp [BiTM.nSteps]
  | succ n ih =>
    rw [Nat.succ_add]
    show (match BiTM.step tm cfg with
          | none => none
          | some c => BiTM.nSteps tm c (n + m))
        = (match BiTM.step tm cfg with
            | none => none
            | some c => BiTM.nSteps tm c n).bind fun c => BiTM.nSteps tm c m
    cases BiTM.step tm cfg with
    | none => rfl
    | some c => exact ih c

end Smith
