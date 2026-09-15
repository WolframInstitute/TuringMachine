/-
  TagSystem.HaltsEmpty

  Halting infrastructure for tag systems and cyclic tag systems: the two
  strong induction principles and the bridge between `CTS.nSteps` (exact
  step count, `none` on halt) and `CTS.Halts` (fuel-based `eval`).

  Contents:
    * `Tag_HaltsEmpty_induction`, `CTS_Halts_induction`: backward strong
      induction along single steps within a halting run.
    * `CTS_step_none_iff_halted`, `CTS_nSteps_succ_unfold` and the
      `nSteps`/`Halts` bridges in both directions.
    * `find_min_or_none`: bounded search for a least witness.

  All declarations live in the `TagSystem` namespace.
-/

import TagSystem.Basic
import TagSystem.TagToCTS

namespace TagSystem

open TagSystem

/-- Strong induction on `HaltsEmpty`: any property `P` that holds for `[]`
    and propagates backwards along single `step`s (within `HaltsEmpty`
    configs) holds for every `HaltsEmpty` config.  Proved by induction on
    the fuel witnessing `HaltsEmpty cfg`. -/
theorem Tag_HaltsEmpty_induction {k : Nat} (ts : Tag k)
    (P : TagConfig k → Prop)
    (h_nil : P [])
    (h_back : ∀ cfg cfg', ts.step cfg = some cfg' →
              ts.HaltsEmpty cfg' → P cfg' → P cfg)
    (cfg : TagConfig k) (h : ts.HaltsEmpty cfg) : P cfg := by
  obtain ⟨fuel, h_eval⟩ := h
  induction fuel generalizing cfg with
  | zero =>
    -- eval cfg 0 = if tagHalted cfg then some cfg else none
    -- so result `some []` forces tagHalted and cfg = []
    by_cases h_halt : tagHalted cfg = true
    · rw [Tag.eval_halted ts cfg 0 h_halt] at h_eval
      injection h_eval with h_eq; rw [h_eq]; exact h_nil
    · simp [Tag.eval] at h_eval
      simp [h_halt] at h_eval
  | succ n ih =>
    by_cases h_halt : tagHalted cfg = true
    · rw [Tag.eval_halted ts cfg (n+1) h_halt] at h_eval
      injection h_eval with h_eq; rw [h_eq]; exact h_nil
    · have h_nh : tagHalted cfg = false := by
        cases h_eq : tagHalted cfg with
        | true => exact absurd h_eq h_halt
        | false => rfl
      cases h_step : ts.step cfg with
      | none =>
        -- impossible: step = none iff halted, contradicting h_nh
        have h_halt_true := (Tag.step_none_iff_halted ts cfg).mp h_step
        rw [h_halt_true] at h_nh; cases h_nh
      | some cfg' =>
        rw [Tag.eval_step ts cfg cfg' n h_nh h_step] at h_eval
        have h_he' : ts.HaltsEmpty cfg' := ⟨n, h_eval⟩
        exact h_back cfg cfg' h_step h_he' (ih cfg' h_eval)

/-- CTS analog of `Tag.step_none_iff_halted`: no step exactly when halted. -/
theorem CTS_step_none_iff_halted (cts : CTS) (cfg : CTSConfig) :
    cts.step cfg = none ↔ ctsHalted cfg = true := by
  cases h_data : cfg.data with
  | nil => simp [CTS.step, h_data, ctsHalted, List.isEmpty]
  | cons head rest => simp [CTS.step, h_data, ctsHalted, List.isEmpty]

/-- CTS analog of `Tag_HaltsEmpty_induction`:
    strong induction principle over halting CTS configs.  Any
    property `P` that holds on halted configs (data = []) and is
    preserved backwards through one step holds on every halting
    cfg.  Proof: induction on the fuel witnessing `cts.Halts cfg`,
    using `CTS_step_none_iff_halted` to dispatch the dead
    `step = none` branch. -/
theorem CTS_Halts_induction (cts : CTS) (P : CTSConfig → Prop)
    (h_halt : ∀ cfg, ctsHalted cfg = true → P cfg)
    (h_back : ∀ cfg cfg', cts.step cfg = some cfg' →
              cts.Halts cfg' → P cfg' → P cfg)
    (cfg : CTSConfig) (h : cts.Halts cfg) : P cfg := by
  obtain ⟨fuel, result, h_eval⟩ := h
  induction fuel generalizing cfg with
  | zero =>
    simp [CTS.eval] at h_eval
    obtain ⟨h_halted, _⟩ := h_eval
    exact h_halt cfg h_halted
  | succ m ih =>
    by_cases h_halted : ctsHalted cfg = true
    · exact h_halt cfg h_halted
    · have h_nh : ctsHalted cfg = false := by
        cases h_eq : ctsHalted cfg with
        | true => exact absurd h_eq h_halted
        | false => rfl
      cases h_step : cts.step cfg with
      | none =>
        have h_halt_true := (CTS_step_none_iff_halted cts cfg).mp h_step
        rw [h_halt_true] at h_nh; cases h_nh
      | some cfg' =>
        have h_eval_step :
            cts.eval cfg (m + 1) = cts.eval cfg' m := by
          show (if ctsHalted cfg then some cfg
                else match cts.step cfg with
                  | none => some cfg
                  | some c' => cts.eval c' m) = cts.eval cfg' m
          rw [if_neg (by rw [h_nh]; decide), h_step]
        rw [h_eval_step] at h_eval
        have h_he' : cts.Halts cfg' := ⟨m, result, h_eval⟩
        exact h_back cfg cfg' h_step h_he' (ih cfg' h_eval)

-- ============================================================================
-- CTS nSteps succ unfold/decompose
-- ============================================================================

/-- Helper: `CTS.nSteps cts cfg (n+1)` unfolds to the match. -/
theorem CTS_nSteps_succ_unfold (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    cts.nSteps cfg (n + 1)
    = match cts.step cfg with
      | none => none
      | some cfg' => cts.nSteps cfg' n := rfl

/-- Once halted, CTS stays halted: `nSteps cfg (n+1) = none` for any
    halted `cfg` (since `step cfg = none` and propagates). -/
theorem ctsHalted_nSteps_succ_eq_none (cts : CTS) (cfg : CTSConfig) (n : Nat)
    (h : ctsHalted cfg = true) :
    cts.nSteps cfg (n + 1) = none := by
  rw [CTS_nSteps_succ_unfold]
  have h_step : cts.step cfg = none := (CTS_step_none_iff_halted cts cfg).mpr h
  rw [h_step]

/-- **Halt-decomposition**: if `cts.nSteps cfg n = none`, then some
    intermediate state at step `k < n` is halted.  Useful for connecting
    "CTS halts" to "CTS reaches a halted intermediate state", which in
    turn is needed for halting-preservation arguments through the
    encoder. -/
theorem CTS_nSteps_none_decompose (cts : CTS) (cfg : CTSConfig) (n : Nat)
    (h : cts.nSteps cfg n = none) :
    ∃ k < n, ∃ cfg', cts.nSteps cfg k = some cfg' ∧ ctsHalted cfg' = true := by
  induction n generalizing cfg with
  | zero => simp [CTS.nSteps] at h
  | succ m ih =>
    rw [CTS_nSteps_succ_unfold] at h
    by_cases h_halt_cfg : ctsHalted cfg = true
    · refine ⟨0, by omega, cfg, ?_, h_halt_cfg⟩
      rfl
    · have h_step_some : ∃ cfg', cts.step cfg = some cfg' := by
        cases h_step : cts.step cfg with
        | none =>
          exact absurd ((CTS_step_none_iff_halted cts cfg).mp h_step) h_halt_cfg
        | some cfg' => exact ⟨cfg', rfl⟩
      obtain ⟨cfg', h_step_eq⟩ := h_step_some
      rw [h_step_eq] at h
      simp at h
      obtain ⟨k', h_k', cfg_h, h_n', h_halt⟩ := ih cfg' h
      refine ⟨k' + 1, by omega, cfg_h, ?_, h_halt⟩
      rw [CTS_nSteps_succ_unfold, h_step_eq]
      exact h_n'

/-- **Reverse direction**: if CTS reaches a halted intermediate state at
    step `k`, then `nSteps cfg (k+1) = none`. -/
theorem CTS_nSteps_none_of_reaches_halted
    (cts : CTS) (cfg cfg' : CTSConfig) (k : Nat)
    (h_n : cts.nSteps cfg k = some cfg') (h_halt : ctsHalted cfg' = true) :
    cts.nSteps cfg (k + 1) = none := by
  rw [← CTS.nSteps_add cts cfg cfg' k 1 h_n]
  exact ctsHalted_nSteps_succ_eq_none cts cfg' 0 h_halt

/-- A CTS halts exactly when some exact-step run reaches a halted config. -/
theorem CTS_nSteps_halts_iff_reaches_halted (cts : CTS) (cfg : CTSConfig) :
    (∃ n, cts.nSteps cfg n = none) ↔
    ∃ k cfg', cts.nSteps cfg k = some cfg' ∧ ctsHalted cfg' = true := by
  constructor
  · intro ⟨n, h⟩
    obtain ⟨k, _, cfg', h_n, h_halt⟩ := CTS_nSteps_none_decompose cts cfg n h
    exact ⟨k, cfg', h_n, h_halt⟩
  · intro ⟨k, cfg', h_n, h_halt⟩
    exact ⟨k + 1, CTS_nSteps_none_of_reaches_halted cts cfg cfg' k h_n h_halt⟩

/-- Bridge from `nSteps` to `Halts`: analog of `nSteps_none_imp_halts` for
    `CTS`.  Same structure: induction on n, use `CTS_step_none_iff_halted`
    to extract halted-ness when `step = none`. -/
theorem CTS_nSteps_none_imp_halts (cts : CTS) (cfg : CTSConfig) :
    (∃ n, cts.nSteps cfg n = none) → cts.Halts cfg := by
  rintro ⟨n, h⟩
  induction n generalizing cfg with
  | zero => simp [CTS.nSteps] at h
  | succ n ih =>
    rw [CTS_nSteps_succ_unfold] at h
    cases h_step : cts.step cfg with
    | none =>
      have h_halt := (CTS_step_none_iff_halted cts cfg).mp h_step
      refine ⟨0, cfg, ?_⟩
      simp [CTS.eval, h_halt]
    | some cfg' =>
      rw [h_step] at h
      simp at h
      obtain ⟨fuel, result, h_eval⟩ := ih cfg' h
      refine ⟨fuel + 1, result, ?_⟩
      have h_not_halt : ctsHalted cfg = false :=
        cts_step_some_not_halted cts cfg cfg' h_step
      simp [CTS.eval, h_not_halt, h_step, h_eval]

/-- Bridge from `Halts` to `nSteps`: converse of `CTS_nSteps_none_imp_halts`. -/
theorem CTS_halts_imp_nSteps_none (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg → (∃ n, cts.nSteps cfg n = none) := by
  rintro ⟨fuel, result, h_eval⟩
  induction fuel generalizing cfg with
  | zero =>
    cases h_halt : ctsHalted cfg with
    | true =>
      refine ⟨1, ?_⟩
      rw [CTS_nSteps_succ_unfold, (CTS_step_none_iff_halted cts cfg).mpr h_halt]
    | false =>
      simp [CTS.eval, h_halt] at h_eval
  | succ fuel ih =>
    cases h_halt : ctsHalted cfg with
    | true =>
      refine ⟨1, ?_⟩
      rw [CTS_nSteps_succ_unfold, (CTS_step_none_iff_halted cts cfg).mpr h_halt]
    | false =>
      simp [CTS.eval, h_halt] at h_eval
      cases h_step : cts.step cfg with
      | none =>
        have h_halt' : ctsHalted cfg = true := (CTS_step_none_iff_halted cts cfg).mp h_step
        rw [h_halt'] at h_halt
        exact Bool.noConfusion h_halt
      | some cfg' =>
        rw [h_step] at h_eval
        obtain ⟨n, hn⟩ := ih cfg' h_eval
        refine ⟨n + 1, ?_⟩
        rw [CTS_nSteps_succ_unfold, h_step]
        exact hn

-- ============================================================================
-- CTS exact-step-form theorems
-- ============================================================================

/-- **`cts.Halts` iff `nSteps` reaches a halted state**. -/
theorem CTS_Halts_iff_nSteps_reaches_halted (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ∃ k cfg', cts.nSteps cfg k = some cfg' ∧ ctsHalted cfg' = true := by
  constructor
  · intro h_halts
    exact (CTS_nSteps_halts_iff_reaches_halted cts cfg).mp
      (CTS_halts_imp_nSteps_none cts cfg h_halts)
  · intro ⟨k, cfg', h_n, h_halt⟩
    apply CTS_nSteps_none_imp_halts
    exact (CTS_nSteps_halts_iff_reaches_halted cts cfg).mpr ⟨k, cfg', h_n, h_halt⟩

/-- **Bounded minimum-finder**: given a decidable predicate on
    `Nat`, either there is a least `k <= n` satisfying P (with
    minimality below k), or no `m <= n` satisfies P.  Replacement
    for `Nat.find` (not available without mathlib). -/
theorem find_min_or_none (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    (∃ k, k ≤ n ∧ P k ∧ ∀ m < k, ¬ P m) ∨ (∀ m ≤ n, ¬ P m) := by
  induction n with
  | zero =>
    by_cases h : P 0
    · exact Or.inl ⟨0, Nat.le_refl _, h,
        fun _ h_lt => absurd h_lt (Nat.not_lt_zero _)⟩
    · exact Or.inr (fun m h_le => by
        obtain rfl := Nat.le_zero.mp h_le; exact h)
  | succ n ih =>
    rcases ih with ⟨k, h_le, h_pk, h_min⟩ | h_none
    · exact Or.inl ⟨k, Nat.le_succ_of_le h_le, h_pk, h_min⟩
    · by_cases h : P (n + 1)
      · refine Or.inl ⟨n + 1, Nat.le_refl _, h, fun m h_lt => ?_⟩
        exact h_none m (Nat.le_of_lt_succ h_lt)
      · refine Or.inr (fun m h_le => ?_)
        rcases Nat.lt_or_eq_of_le h_le with h_lt | h_eq
        · exact h_none m (Nat.le_of_lt_succ h_lt)
        · subst h_eq; exact h

