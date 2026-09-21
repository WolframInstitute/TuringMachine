/-
  Smith.Wolfram23Bridge

  System 0 of `Smith.Lookahead` is Wolfram's (2,3) machine `BiTM.wolfram23`
  on a finite tape.  `toBi` reads a System 0 configuration as a
  `BiTM.Config` (state A is 1, B is 2, the zipper is the same zipper); a
  System 0 step is a `wolfram23` step (`toBi_step`), and where System 0
  leaves its tape `wolfram23` steps onto a blank cell and its explicit
  tape grows by one (`toBi_exit`).  Every valid `wolfram23` configuration
  is `toBi` of a System 0 configuration (`toBi_ofBi`).

  T5 for Wolfram's machine follows from `Smith.LoopFree`: from every valid
  configuration the head eventually leaves the explicit tape
  (`wolfram23_leaves`), and no valid configuration is periodic
  (`wolfram23_not_periodic`).  This is the formal refutation of the
  step-faithful predicates REVIEW.md section 4.1 records, which required a
  periodic configuration.
-/

import Smith.LoopFree
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

/-- A run that ends has a last configuration. -/
theorem lnSteps_none_decompose (M : LMachine) (c : LConfig) (n : Nat) (h : lnSteps M c n = none) :
    ∃ m c1, lnSteps M c m = some c1 ∧ lstep M c1 = none := by
  induction n generalizing c with
  | zero => simp at h
  | succ n ih =>
    rw [lnSteps_succ] at h
    cases hs : lstep M c with
    | none => exact ⟨0, c, rfl, hs⟩
    | some c1 =>
      rw [hs, Option.bind_some] at h
      obtain ⟨m, c2, hm, hc2⟩ := ih c1 h
      exact ⟨m + 1, c2, by rw [lnSteps_succ, hs, Option.bind_some, hm], hc2⟩

/-- Read a valid `wolfram23` configuration as a System 0 configuration. -/
def toFin (k : Nat) : Fin 3 := ⟨k % 3, Nat.mod_lt _ (by decide)⟩

/-- The inverse of `toBi` on valid configurations. -/
def ofBi (cfg : BiTM.Config) : LConfig :=
  ⟨cfg.left.map toFin, toFin cfg.head, cfg.right.map toFin, if cfg.state = 1 then A else B⟩

theorem map_val_toFin (l : List Nat) (h : ∀ x ∈ l, x < 3) : (l.map toFin).map Fin.val = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  simp [toFin, Nat.mod_eq_of_lt (h x hx)]

theorem toBi_ofBi (cfg : BiTM.Config) (hv : IsValidWolfram23Cfg cfg) : toBi (ofBi cfg) = cfg := by
  obtain ⟨hs, hh, hl, hr⟩ := hv
  obtain ⟨st, L, a, R⟩ := cfg
  simp only [toBi, ofBi, BiTM.Config.mk.injEq]
  refine ⟨?_, map_val_toFin L hl, ?_, map_val_toFin R hr⟩
  · rcases hs with rfl | rfl <;> simp [stateNat]
  · simp [toFin, Nat.mod_eq_of_lt hh]

theorem ofBi_state (cfg : BiTM.Config) : (ofBi cfg).state ≠ C := by
  simp only [ofBi]
  split_ifs <;> decide

/-! ## T5 for Wolfram's machine -/

/-- Every step of a `BiTM` machine keeps or grows the explicit tape. -/
theorem biSize_step (tm : Machine) (cfg cfg' : BiTM.Config) (h : BiTM.step tm cfg = some cfg') :
    biSize cfg ≤ biSize cfg' := by
  obtain ⟨st, L, a, R⟩ := cfg
  by_cases hs : st = 0
  · subst hs
    simp [BiTM.step] at h
  · simp only [BiTM.step, beq_iff_eq, hs, if_false] at h
    cases hd : (tm.transition st a).dir <;> rw [hd] at h
    · cases L <;> simp [BiTM.readHead] at h <;> subst h <;> simp [biSize]
      all_goals omega
    · cases R <;> simp [BiTM.readHead] at h <;> subst h <;> simp [biSize]
      all_goals omega

theorem biSize_nSteps (tm : Machine) (cfg cfg' : BiTM.Config) (n : Nat)
    (h : BiTM.nSteps tm cfg n = some cfg') : biSize cfg ≤ biSize cfg' := by
  induction n generalizing cfg with
  | zero => obtain rfl := Option.some.inj h; exact le_refl _
  | succ n ih =>
    change (match BiTM.step tm cfg with
            | none => none
            | some c => BiTM.nSteps tm c n) = some cfg' at h
    cases hs : BiTM.step tm cfg with
    | none => rw [hs] at h; cases h
    | some c1 =>
      rw [hs] at h
      exact le_trans (biSize_step tm cfg c1 hs) (ih c1 h)

/-- T5 (PLAN.md), the head leaves every finite interval: from every valid
    configuration of Wolfram's (2,3) machine the run reaches a configuration
    with one more explicit cell, that is, the head has stepped off the
    initial finite tape. -/
theorem wolfram23_leaves (cfg : BiTM.Config) (hv : IsValidWolfram23Cfg cfg) :
    ∃ n cfg', BiTM.nSteps wolfram23 cfg n = some cfg' ∧ biSize cfg' = biSize cfg + 1 := by
  obtain ⟨n, hn⟩ := sys0_leaves (ofBi cfg) (ofBi_state cfg)
  obtain ⟨m, c1, hm, hc1⟩ := lnSteps_none_decompose sys0 (ofBi cfg) n hn
  obtain ⟨hrun, hst1⟩ := toBi_run (ofBi cfg) (ofBi_state cfg) m c1 hm
  obtain ⟨cfg', hstep, hsize⟩ := toBi_exit c1 hst1 hc1
  rw [toBi_ofBi cfg hv] at hrun
  refine ⟨m + 1, cfg', ?_, ?_⟩
  · refine BiTM_nSteps_some_compose wolfram23 cfg (toBi c1) m 1 cfg' hrun ?_
    show (match BiTM.step wolfram23 (toBi c1) with
          | none => none
          | some c => BiTM.nSteps wolfram23 c 0) = some cfg'
    rw [hstep]
    rfl
  · have : biSize (toBi c1) = biSize cfg := by
      rw [biSize_toBi, lnSteps_length sys0 _ _ _ hm, ← biSize_toBi, toBi_ofBi cfg hv]
    omega

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

/-- No valid configuration of Wolfram's (2,3) machine is periodic: the
    explicit tape never shrinks and eventually grows. -/
theorem wolfram23_not_periodic (cfg : BiTM.Config) (hv : IsValidWolfram23Cfg cfg) (p : Nat)
    (hp : 1 ≤ p) : BiTM.nSteps wolfram23 cfg p ≠ some cfg := by
  intro hper
  obtain ⟨n, cfg', hn, hsize⟩ := wolfram23_leaves cfg hv
  have hiter : ∀ k, BiTM.nSteps wolfram23 cfg (k * p) = some cfg := by
    intro k
    induction k with
    | zero => rw [Nat.zero_mul]; rfl
    | succ k ih => rw [Nat.succ_mul]; exact BiTM_nSteps_some_compose _ _ _ _ _ _ ih hper
  have h1 := hiter (n + 1)
  have hle : n + 1 ≤ (n + 1) * p := Nat.le_mul_of_pos_right (n + 1) hp
  rw [show (n + 1) * p = n + ((n + 1) * p - n) by omega, biNSteps_add, hn, Option.bind_some] at h1
  have := biSize_nSteps wolfram23 cfg' cfg _ h1
  omega

end Smith
