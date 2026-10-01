/-
  Smith.Systems123

  The equivalences of Conjectures 0, 1, 2 and 3 (TM23Proof.pdf p. 3-5) as
  forward simulations in the calculus of `Smith.Simulation`, from each
  system down to the next:

    * System 1 -> System 0: the same configurations; a `B2x` step of
      System 1 is one (`B20`) or three (`B21`, `B22`) steps of System 0,
      every other rule is the same rule (`sys1_sys0_forwardSim`).
    * System 2 -> System 1: `phi2` sends a state C configuration to state B
      with the active cell swapped (`1 <-> 2`), one step to one step
      (`sys2_sys1_forwardSim`).
    * System 3 -> System 2: `phi3` swaps every cell left of the active one,
      and the active one in state A, one step to one step
      (`sys3_sys2_forwardSim`).
    * `sys3_sys0_forwardSim`: the composite, System 3 down to System 0.

  Contents:
    * `sw`, `phi2`, `phi3`.
    * `sys0_B2_three`: the three System 0 steps behind `B21` and `B22`.
    * `phi2_step`, `phi3_step`: the one-step commutations, by case analysis
      over the rule tables.
    * The three forward simulations and their composite, plus `decide`
      checks of the correspondences on every three-cell tape.
-/

import Smith.Lookahead
import Smith.ConjectureFive
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

namespace Smith

open TM
open LState

/-- Swap the symbols 1 and 2, fix 0 (Smith's "subtracted from 3 (mod 3)"). -/
def sw : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1

@[simp] theorem sw_sw (a : Fin 3) : sw (sw a) = a := by fin_cases a <;> rfl
@[simp] theorem sw_zero : sw 0 = 0 := rfl
@[simp] theorem sw_one : sw 1 = 2 := rfl
@[simp] theorem sw_two : sw 2 = 1 := rfl

/-- The System 2 -> System 1 relabeling of p. 4: state C is state B with
    the active element swapped. -/
def phi2 : LConfig → LConfig
  | ⟨L, a, R, C⟩ => ⟨L, sw a, R, B⟩
  | c => c

@[simp] theorem phi2_A (L : List (Fin 3)) (a : Fin 3) (R : List (Fin 3)) :
    phi2 ⟨L, a, R, A⟩ = ⟨L, a, R, A⟩ := rfl
@[simp] theorem phi2_B (L : List (Fin 3)) (a : Fin 3) (R : List (Fin 3)) :
    phi2 ⟨L, a, R, B⟩ = ⟨L, a, R, B⟩ := rfl
@[simp] theorem phi2_C (L : List (Fin 3)) (a : Fin 3) (R : List (Fin 3)) :
    phi2 ⟨L, a, R, C⟩ = ⟨L, sw a, R, B⟩ := rfl

/-- The System 3 -> System 2 relabeling of p. 5: swap every cell left of
    the active one, and the active one itself in state A. -/
def phi3 : LConfig → LConfig
  | ⟨L, a, R, A⟩ => ⟨L.map sw, sw a, R, A⟩
  | ⟨L, a, R, st⟩ => ⟨L.map sw, a, R, st⟩

@[simp] theorem phi3_A (L : List (Fin 3)) (a : Fin 3) (R : List (Fin 3)) :
    phi3 ⟨L, a, R, A⟩ = ⟨L.map sw, sw a, R, A⟩ := rfl
@[simp] theorem phi3_B (L : List (Fin 3)) (a : Fin 3) (R : List (Fin 3)) :
    phi3 ⟨L, a, R, B⟩ = ⟨L.map sw, a, R, B⟩ := rfl
@[simp] theorem phi3_C (L : List (Fin 3)) (a : Fin 3) (R : List (Fin 3)) :
    phi3 ⟨L, a, R, C⟩ = ⟨L.map sw, a, R, C⟩ := rfl

/-! ## System 1 to System 0 -/

/-- `B21` and `B22` of System 1 are three steps of System 0: `B2 -> A0>`,
    then `A1 -> A2<` or `A2 -> A1<`, then `A0 -> B1>` (p. 4). -/
theorem sys0_B2_three (L : List (Fin 3)) (b : Fin 3) (R : List (Fin 3)) (hb : b = 1 ∨ b = 2) :
    lnSteps sys0 ⟨L, 2, b :: R, B⟩ 3 = some ⟨1 :: L, sw b, R, B⟩ := by
  rcases hb with rfl | rfl <;> cases R <;> simp [lnSteps_succ, lstep, sys0]

/-- A System 1 step is one or three System 0 steps on the same tape. -/
theorem sys1_sys0_step (c c' : LConfig) (h : lstep sys1 c = some c') :
    ∃ k, 1 ≤ k ∧ lnSteps sys0 c k = some c' := by
  obtain ⟨L, a, R, st⟩ := c
  cases R with
  | nil =>
    refine ⟨1, Nat.le_refl 1, ?_⟩
    rw [lnSteps_one]
    cases st <;> fin_cases a <;> cases L <;> simp [lstep, sys0, sys1] at h ⊢ <;> exact h
  | cons b R' =>
    cases st <;> fin_cases a <;> fin_cases b
    all_goals first
      | (refine ⟨1, Nat.le_refl 1, ?_⟩
         rw [lnSteps_one]
         cases L <;> simp [lstep, sys0, sys1] at h ⊢ <;> exact h)
      | skip
    · -- B21
      simp only [lstep, sys1, Option.some.injEq] at h
      subst h
      exact ⟨3, by omega, by simpa using sys0_B2_three L 1 R' (Or.inl rfl)⟩
    · -- B22
      simp only [lstep, sys1, Option.some.injEq] at h
      subst h
      exact ⟨3, by omega, by simpa using sys0_B2_three L 2 R' (Or.inr rfl)⟩

/-- Conjectures 0 and 1 are equivalent (p. 4), the direction the chain
    uses: System 0 emulates System 1 on the same configurations, one step
    of System 1 being one or three steps of System 0. -/
theorem sys1_sys0_forwardSim : ForwardSim (lsys sys1) (lsys sys0) (fun c c' => c' = c) := by
  rintro c t hR c' hstep
  subst t
  obtain ⟨k, hk, hrun⟩ := sys1_sys0_step c c' hstep
  exact ⟨k, hk, c', hrun, rfl⟩

/-! ## System 2 to System 1 -/

/-- One step of System 2 is one step of System 1 through `phi2`. -/
theorem phi2_step (c : LConfig) : lstep sys1 (phi2 c) = (lstep sys2 c).map phi2 := by
  obtain ⟨L, a, R, st⟩ := c
  cases R with
  | nil => cases st <;> fin_cases a <;> cases L <;> simp [lstep, sys1, sys2]
  | cons b R' => cases st <;> fin_cases a <;> fin_cases b <;> cases L <;> simp [lstep, sys1, sys2]

/-- Conjectures 1 and 2 are equivalent (p. 4), the direction the chain uses. -/
theorem sys2_sys1_forwardSim : ForwardSim (lsys sys2) (lsys sys1) (fun c c' => c' = phi2 c) := by
  rintro c t hR c' hstep
  subst t
  refine ⟨1, Nat.le_refl 1, phi2 c', ?_, rfl⟩
  rw [StepSys.nSteps_one, lsys_step, phi2_step]
  rw [lsys_step] at hstep
  rw [hstep]
  rfl

/-! ## System 3 to System 2 -/

/-- One step of System 3 is one step of System 2 through `phi3`. -/
theorem phi3_step (c : LConfig) : lstep sys2 (phi3 c) = (lstep sys3 c).map phi3 := by
  obtain ⟨L, a, R, st⟩ := c
  cases R with
  | nil => cases st <;> fin_cases a <;> cases L <;> simp [lstep, sys2, sys3]
  | cons b R' => cases st <;> fin_cases a <;> fin_cases b <;> cases L <;> simp [lstep, sys2, sys3]

/-- Conjectures 2 and 3 are equivalent (p. 5), the direction the chain uses. -/
theorem sys3_sys2_forwardSim : ForwardSim (lsys sys3) (lsys sys2) (fun c c' => c' = phi3 c) := by
  rintro c t hR c' hstep
  subst t
  refine ⟨1, Nat.le_refl 1, phi3 c', ?_, rfl⟩
  rw [StepSys.nSteps_one, lsys_step, phi3_step]
  rw [lsys_step] at hstep
  rw [hstep]
  rfl

/-! ## System 3 to System 0 -/

/-- Conjecture 3 implies Conjecture 0 (p. 3-5): System 0 emulates System 3
    through `phi2 ∘ phi3`, one step of System 3 being one or three steps of
    System 0. -/
theorem sys3_sys0_forwardSim :
    ForwardSim (lsys sys3) (lsys sys0) (fun c c' => c' = phi2 (phi3 c)) := by
  refine ForwardSim_congr
    (ForwardSim_comp (ForwardSim_comp sys3_sys2_forwardSim sys2_sys1_forwardSim) sys1_sys0_forwardSim)
    (fun c c' => ⟨fun h => ⟨phi2 (phi3 c), ⟨phi3 c, rfl, rfl⟩, h⟩, ?_⟩)
  rintro ⟨_, ⟨_, rfl, rfl⟩, h⟩
  exact h

/-! ## Checks -/

/-- The 1-or-3 correspondence on every two-cell tape, by `decide`. -/
example : ∀ (st : LState) (x a b : Fin 3),
    (lstep sys1 ⟨[x], a, [b], st⟩).all (fun c' =>
      decide (lnSteps sys0 ⟨[x], a, [b], st⟩ 1 = some c' ∨ lnSteps sys0 ⟨[x], a, [b], st⟩ 3 = some c'))
      = true := by
  decide

/-- The two relabelings on every three-cell tape, by `decide`. -/
example : ∀ (st : LState) (x a b : Fin 3),
    lstep sys1 (phi2 ⟨[x], a, [b], st⟩) = (lstep sys2 ⟨[x], a, [b], st⟩).map phi2 := by
  decide

example : ∀ (st : LState) (x a b : Fin 3),
    lstep sys2 (phi3 ⟨[x], a, [b], st⟩) = (lstep sys3 ⟨[x], a, [b], st⟩).map phi3 := by
  decide

/-- The relabelings are real: `phi3` moves a System 3 configuration that
    System 2 would treat differently. -/
example : lstep sys2 ⟨[0], 1, [0], A⟩ ≠ (lstep sys3 ⟨[0], 1, [0], A⟩).map phi3 := by decide

example : lstep sys1 ⟨[0], 1, [0], C⟩ ≠ (lstep sys2 ⟨[0], 1, [0], C⟩).map phi2 := by decide

end Smith
