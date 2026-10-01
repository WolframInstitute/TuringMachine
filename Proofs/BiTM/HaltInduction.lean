/-
  BiTM.HaltInduction

  Halting infrastructure for the bi-infinite Turing machine model: the
  step/halted dichotomy, the algebra of `nSteps`, and the bridge between
  `nSteps` (exact step count, `none` on halt) and `Halts` (fuel-based
  `eval`).

  Contents:
    * `step_some_of_active`, `step_none_iff_halted`, `step_active_state`:
      a step succeeds exactly on a config in an active state.
    * `nSteps_one`, `nSteps_add`, `BiTM_nSteps_succ_unfold`,
      `BiTM_nSteps_some_compose`: composition algebra for `nSteps`.
    * `nSteps_none_imp_halts`, `halts_imp_nSteps_none` and the
      `Halts`-iff-`nSteps` characterisations in both directions.
-/

import BiTM.Basic
import TagSystem.Basic
import TagSystem.HaltsEmpty

namespace BiTM

open TM
open TagSystem

theorem step_some_of_active (tm : Machine) (cfg : Config) (h : cfg.state ≠ 0) :
    ∃ cfg', step tm cfg = some cfg' := by
  have h_neq : ¬ ((cfg.state == 0) = true) := by simp [h]
  cases h_dir : (tm.transition cfg.state cfg.head).dir with
  | L =>
    cases h_l : readHead cfg.left with
    | mk newHead newLeft =>
      refine ⟨{ state := (tm.transition cfg.state cfg.head).nextState,
                left := newLeft, head := newHead,
                right := (tm.transition cfg.state cfg.head).write :: cfg.right },
              ?_⟩
      unfold step
      rw [ite_eq_right h_neq]
      dsimp only []
      rw [h_dir, h_l]
  | R =>
    cases h_r : readHead cfg.right with
    | mk newHead newRight =>
      refine ⟨{ state := (tm.transition cfg.state cfg.head).nextState,
                left := (tm.transition cfg.state cfg.head).write :: cfg.left,
                head := newHead, right := newRight },
              ?_⟩
      unfold step
      rw [ite_eq_right h_neq]
      dsimp only []
      rw [h_dir, h_r]

/-- `step` returns `none` exactly when the config is halted. -/
theorem step_none_iff_halted (tm : Machine) (cfg : Config) :
    step tm cfg = none ↔ cfg.state = 0 := by
  constructor
  · intro h_none
    by_cases h : cfg.state = 0
    · exact h
    · exfalso
      obtain ⟨cfg', h_some⟩ := step_some_of_active tm cfg h
      rw [h_some] at h_none
      contradiction
  · intro h_zero
    unfold step
    simp [h_zero]

/-- For an active config (state not 0), a successful step's resulting
    state matches the transition's `nextState`. -/
theorem step_active_state (tm : Machine) (cfg cfg' : Config)
    (h_step : step tm cfg = some cfg') :
    cfg'.state = (tm.transition cfg.state cfg.head).nextState := by
  have h_state_neq : ¬ ((cfg.state == 0) = true) := by
    intro h
    simp [step, h] at h_step
  cases h_dir : (tm.transition cfg.state cfg.head).dir with
  | L =>
    cases h_l : readHead cfg.left with
    | mk newHead newLeft =>
      have h_eval : step tm cfg = some
          { state := (tm.transition cfg.state cfg.head).nextState,
            left := newLeft, head := newHead,
            right := (tm.transition cfg.state cfg.head).write :: cfg.right } := by
        unfold step
        rw [ite_eq_right h_state_neq]
        dsimp only []
        rw [h_dir, h_l]
      rw [h_eval] at h_step
      injection h_step with h_eq
      subst h_eq
      rfl
  | R =>
    cases h_r : readHead cfg.right with
    | mk newHead newRight =>
      have h_eval : step tm cfg = some
          { state := (tm.transition cfg.state cfg.head).nextState,
            left := (tm.transition cfg.state cfg.head).write :: cfg.left,
            head := newHead, right := newRight } := by
        unfold step
        rw [ite_eq_right h_state_neq]
        dsimp only []
        rw [h_dir, h_r]
      rw [h_eval] at h_step
      injection h_step with h_eq
      subst h_eq
      rfl

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

/-- **Bridge**: nSteps-halting implies eval-halting (`BiTM.Halts`).  This
    is the implication we need to feed nSteps-style halting facts (which
    the System 5 to System 0 chain produces) into the eval-style
    `BiTM.Halts` predicate that `smith_reduces` consumes. -/
theorem nSteps_none_imp_halts (tm : Machine) (cfg : Config) :
    (∃ n, nSteps tm cfg n = none) → Halts tm cfg := by
  rintro ⟨n, h⟩
  induction n generalizing cfg with
  | zero => simp [nSteps] at h
  | succ n ih =>
    rw [BiTM_nSteps_succ_unfold] at h
    cases h_step : step tm cfg with
    | none =>
      have h_state := (step_none_iff_halted tm cfg).mp h_step
      refine ⟨0, cfg, ?_⟩
      simp [eval, halted, h_state]
    | some cfg' =>
      rw [h_step] at h
      simp at h
      obtain ⟨fuel, result, h_eval⟩ := ih cfg' h
      refine ⟨fuel + 1, result, ?_⟩
      have h_state_nz : cfg.state ≠ 0 := by
        intro h_z
        rw [(step_none_iff_halted tm cfg).mpr h_z] at h_step
        nomatch h_step
      have h_not_halted : (halted cfg) = false := by
        simp [halted, h_state_nz]
      show eval tm cfg (fuel + 1) = some result
      simp [eval, h_not_halted, h_step, h_eval]

/-- **Converse bridge**: eval-style `BiTM.Halts` implies nSteps-style
    halting.  Together with `nSteps_none_imp_halts`, this gives a full
    equivalence between the two halting predicates. -/
theorem halts_imp_nSteps_none (tm : Machine) (cfg : Config) :
    Halts tm cfg → (∃ n, nSteps tm cfg n = none) := by
  rintro ⟨fuel, result, h_eval⟩
  induction fuel generalizing cfg with
  | zero =>
    cases h_halt : halted cfg with
    | true =>
      have h_state : cfg.state = 0 := by simp [halted] at h_halt; exact h_halt
      refine ⟨1, ?_⟩
      rw [BiTM_nSteps_succ_unfold, (step_none_iff_halted tm cfg).mpr h_state]
    | false =>
      simp [eval, h_halt] at h_eval
  | succ fuel ih =>
    cases h_halt : halted cfg with
    | true =>
      have h_state : cfg.state = 0 := by simp [halted] at h_halt; exact h_halt
      refine ⟨1, ?_⟩
      rw [BiTM_nSteps_succ_unfold, (step_none_iff_halted tm cfg).mpr h_state]
    | false =>
      simp [eval, h_halt] at h_eval
      cases h_step : step tm cfg with
      | none =>
        have h_state : cfg.state = 0 := (step_none_iff_halted _ _).mp h_step
        have h_halt' : halted cfg = true := by simp [halted, h_state]
        rw [h_halt'] at h_halt
        exact Bool.noConfusion h_halt
      | some cfg' =>
        rw [h_step] at h_eval
        obtain ⟨n, hn⟩ := ih cfg' h_eval
        refine ⟨n + 1, ?_⟩
        rw [BiTM_nSteps_succ_unfold, h_step]
        exact hn

-- ============================================================================
-- BiTM halt-related nSteps cluster
-- ============================================================================

/-- BiTM analog of `ctsHalted_nSteps_succ_eq_none`: once a TM halts
    (state = 0), `nSteps tm cfg (n+1) = none`. -/
theorem BiTM_halted_nSteps_succ_eq_none (tm : Machine) (cfg : Config) (n : Nat)
    (h : halted cfg = true) :
    nSteps tm cfg (n + 1) = none := by
  rw [BiTM_nSteps_succ_unfold]
  have h_state : cfg.state = 0 := by simp [halted] at h; exact h
  have h_step : step tm cfg = none := (step_none_iff_halted tm cfg).mpr h_state
  rw [h_step]

theorem BiTM_halted_nSteps_eq_none (tm : Machine) (cfg : Config) (n : Nat)
    (h_halt : halted cfg = true) (h_n : 1 ≤ n) :
    nSteps tm cfg n = none := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact BiTM_halted_nSteps_succ_eq_none tm cfg m h_halt

/-- BiTM analog of `CTS_nSteps_none_decompose`: if `nSteps tm cfg n = none`,
    then some intermediate state at step `k < n` is halted (state = 0). -/
theorem BiTM_nSteps_none_decompose (tm : Machine) (cfg : Config) (n : Nat)
    (h : nSteps tm cfg n = none) :
    ∃ k < n, ∃ cfg', nSteps tm cfg k = some cfg' ∧ halted cfg' = true := by
  induction n generalizing cfg with
  | zero => simp [nSteps] at h
  | succ m ih =>
    rw [BiTM_nSteps_succ_unfold] at h
    by_cases h_halt_cfg : halted cfg = true
    · refine ⟨0, by omega, cfg, ?_, h_halt_cfg⟩
      rfl
    · have h_state_nz : cfg.state ≠ 0 := by
        intro h_z
        exact h_halt_cfg (by simp [halted, h_z])
      obtain ⟨cfg', h_step_eq⟩ := step_some_of_active tm cfg h_state_nz
      rw [h_step_eq] at h
      simp at h
      obtain ⟨k', h_k', cfg_h, h_n', h_halt⟩ := ih cfg' h
      refine ⟨k' + 1, by omega, cfg_h, ?_, h_halt⟩
      rw [BiTM_nSteps_succ_unfold, h_step_eq]
      exact h_n'

/-- BiTM reverse direction: reaching a halted state at step k implies
    `nSteps tm cfg (k+1) = none`. -/
theorem BiTM_nSteps_none_of_reaches_halted
    (tm : Machine) (cfg cfg' : Config) (k : Nat)
    (h_n : nSteps tm cfg k = some cfg') (h_halt : halted cfg' = true) :
    nSteps tm cfg (k + 1) = none := by
  rw [nSteps_add, h_n]
  show nSteps tm cfg' 1 = none
  exact BiTM_halted_nSteps_succ_eq_none tm cfg' 0 h_halt

/-- BiTM analog of `CTS_nSteps_halts_iff_reaches_halted`. -/
theorem BiTM_nSteps_halts_iff_reaches_halted (tm : Machine) (cfg : Config) :
    (∃ n, nSteps tm cfg n = none) ↔
    ∃ k cfg', nSteps tm cfg k = some cfg' ∧ halted cfg' = true := by
  constructor
  · intro ⟨n, h⟩
    obtain ⟨k, _, cfg', h_n, h_halt⟩ := BiTM_nSteps_none_decompose tm cfg n h
    exact ⟨k, cfg', h_n, h_halt⟩
  · intro ⟨k, cfg', h_n, h_halt⟩
    exact ⟨k + 1, BiTM_nSteps_none_of_reaches_halted tm cfg cfg' k h_n h_halt⟩

/-- `Halts` iff `nSteps` reaches a halted state.  Chains the
    `nSteps_none_imp_halts` and `halts_imp_nSteps_none` bridges with
    `BiTM_nSteps_halts_iff_reaches_halted`. -/
theorem BiTM_Halts_iff_nSteps_reaches_halted (tm : Machine) (cfg : Config) :
    Halts tm cfg ↔ ∃ k cfg', nSteps tm cfg k = some cfg' ∧ halted cfg' = true := by
  constructor
  · intro h_halts
    exact (BiTM_nSteps_halts_iff_reaches_halted tm cfg).mp
      (halts_imp_nSteps_none tm cfg h_halts)
  · intro ⟨k, cfg', h_n, h_halt⟩
    apply nSteps_none_imp_halts
    exact (BiTM_nSteps_halts_iff_reaches_halted tm cfg).mpr ⟨k, cfg', h_n, h_halt⟩

/-- **BiTM `Halts` step-predecessor**: if `step tm cfg = some cfg'`
    and `Halts tm cfg'`, then `Halts tm cfg`. -/
theorem BiTM_Halts_step_pred
    (tm : Machine) (cfg cfg' : Config) (h_step : step tm cfg = some cfg')
    (h : Halts tm cfg') :
    Halts tm cfg := by
  obtain ⟨fuel, res, h_eval⟩ := h
  refine ⟨fuel + 1, res, ?_⟩
  by_cases h_halt : halted cfg = true
  · simp [eval, h_halt]
    exfalso
    have h_state : cfg.state = 0 := by
      unfold halted at h_halt
      exact (beq_iff_eq).mp h_halt
    have := (step_none_iff_halted tm cfg).mpr h_state
    rw [this] at h_step
    cases h_step
  · simp [eval, h_halt, h_step]
    exact h_eval

/-- **BiTM `Halts` predecessor under nSteps**. -/
theorem BiTM_Halts_nSteps_pred
    (tm : Machine) (cfg : Config) (n : Nat) (result : Config)
    (h_n : nSteps tm cfg n = some result) (h : Halts tm result) :
    Halts tm cfg := by
  induction n generalizing cfg with
  | zero =>
    simp [nSteps] at h_n
    rw [h_n]
    exact h
  | succ k ih =>
    rw [BiTM_nSteps_succ_unfold] at h_n
    cases h_step : step tm cfg with
    | none => rw [h_step] at h_n; cases h_n
    | some cfg₁ =>
      rw [h_step] at h_n
      have h_halts₁ := ih cfg₁ h_n
      exact BiTM_Halts_step_pred tm cfg cfg₁ h_step h_halts₁

/-- **BiTM `nSteps` compose**: BiTM analogue of `CTS_nSteps_some_compose`. -/
theorem BiTM_nSteps_some_compose (tm : Machine) (cfg mid : Config)
    (n m : Nat) (result : Config)
    (h_n : nSteps tm cfg n = some mid)
    (h_m : nSteps tm mid m = some result) :
    nSteps tm cfg (n + m) = some result := by
  rw [nSteps_add, h_n]
  exact h_m

/-- **BiTM nSteps past halt yields none**. -/
theorem BiTM_nSteps_past_halt_eq_none
    (tm : Machine) (cfg : Config) (n : Nat) (result : Config)
    (h_n : nSteps tm cfg n = some result) (h_halt : halted result = true)
    (k : Nat) (h_k : k ≥ 1) :
    nSteps tm cfg (n + k) = none := by
  rw [nSteps_add, h_n]
  exact BiTM_halted_nSteps_eq_none tm result k h_halt h_k

/-- **BiTM not-Halts iff nSteps always some**. -/
theorem BiTM_not_Halts_iff_nSteps_always_some
    (tm : Machine) (cfg : Config) :
    ¬ Halts tm cfg ↔ ∀ n, ∃ result, nSteps tm cfg n = some result := by
  constructor
  · intro h_not_halts n
    cases h_n : nSteps tm cfg n with
    | none =>
      exfalso
      exact h_not_halts (nSteps_none_imp_halts tm cfg ⟨n, h_n⟩)
    | some r => exact ⟨r, rfl⟩
  · intro h_all h_halts
    rw [BiTM_Halts_iff_nSteps_reaches_halted] at h_halts
    obtain ⟨k, r, h_k, h_halt_r⟩ := h_halts
    obtain ⟨r', h_r'⟩ := h_all (k + 1)
    rw [BiTM_nSteps_past_halt_eq_none tm cfg k r h_k h_halt_r 1 (by omega)] at h_r'
    cases h_r'

