/-
  BiTM.HaltInduction

  BiTM-side halt-induction infrastructure extracted from
  `BiTM.CockeMinskyConstruction`.

  Contents:
    * `step_some_of_active`, `step_none_iff_halted` —
      basic step/halted dichotomy lemmas
    * `BiTM_Halts_induction` (iter 546) — strong induction over
      halting BiTM configs
    * `Halts_imp_nSteps_eventually_none` (iter 549) — consumer
    * `CTS_Halts_imp_nSteps_eventually_none` (iter 550) — CTS analog

  Depends on `TagSystem.HaltsEmpty` for `CTS_Halts_induction`.
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
      rw [if_neg h_neq]
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
      rw [if_neg h_neq]
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

/-- For an active config (`cfg.state ≠ 0`), a successful step's resulting
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
        rw [if_neg h_state_neq]
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
        rw [if_neg h_state_neq]
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

/-- **`BiTM_Halts_induction` (iter 546)**: BiTM analog of iter
    528/545 — strong induction principle over halting BiTM configs.
    Any `P` holding on halted configs (state = 0) with backwards-
    step preservation propagates to all halting cfgs.  Completes
    the induction-principle family across Tag/CTS/BiTM. -/
theorem BiTM_Halts_induction (tm : Machine) (P : Config → Prop)
    (h_halt : ∀ cfg, cfg.state = 0 → P cfg)
    (h_back : ∀ cfg cfg', step tm cfg = some cfg' →
              Halts tm cfg' → P cfg' → P cfg)
    (cfg : Config) (h : Halts tm cfg) : P cfg := by
  obtain ⟨fuel, result, h_eval⟩ := h
  induction fuel generalizing cfg with
  | zero =>
    simp [eval] at h_eval
    obtain ⟨h_halted, _⟩ := h_eval
    have h_state : cfg.state = 0 := by
      simp [halted] at h_halted; exact h_halted
    exact h_halt cfg h_state
  | succ m ih =>
    by_cases h_halted : halted cfg = true
    · have h_state : cfg.state = 0 := by
        simp [halted] at h_halted; exact h_halted
      exact h_halt cfg h_state
    · have h_nh : halted cfg = false := by
        cases h_eq : halted cfg with
        | true => exact absurd h_eq h_halted
        | false => rfl
      cases h_step : step tm cfg with
      | none =>
        have h_state : cfg.state = 0 := (step_none_iff_halted tm cfg).mp h_step
        have h_halt_true : halted cfg = true := by simp [halted, h_state]
        rw [h_halt_true] at h_nh; cases h_nh
      | some cfg' =>
        have h_eval_step :
            eval tm cfg (m + 1) = eval tm cfg' m := by
          show (if halted cfg then some cfg
                else match step tm cfg with
                  | none => some cfg
                  | some c' => eval tm c' m) = eval tm cfg' m
          rw [if_neg (by rw [h_nh]; decide), h_step]
        rw [h_eval_step] at h_eval
        have h_he' : Halts tm cfg' := ⟨m, result, h_eval⟩
        exact h_back cfg cfg' h_step h_he' (ih cfg' h_eval)
/-- **`Halts_imp_nSteps_eventually_none` (iter 549)**: a consumer
    of `BiTM_Halts_induction` (iter 546).  Any halting cfg has some
    bound `N` past which `nSteps tm cfg k = none` for all `k > N`.
    Captures the "trajectory eventually dies" intuition.
    Proof: induction via iter 546 with `P cfg = ∃ N, ∀ k > N,
    nSteps tm cfg k = none`. -/
theorem Halts_imp_nSteps_eventually_none (tm : Machine) (cfg : Config)
    (h : Halts tm cfg) :
    ∃ N, ∀ k, k > N → nSteps tm cfg k = none := by
  refine BiTM_Halts_induction tm
    (fun cfg => ∃ N, ∀ k, k > N → nSteps tm cfg k = none) ?_ ?_ cfg h
  · -- Halted cfg: state = 0, step = none, so nSteps cfg (m+1) = none
    intro c h_state
    refine ⟨0, ?_⟩
    intro k h_k
    cases k with
    | zero => omega
    | succ m =>
      show (match step tm c with | none => none | some c' => nSteps tm c' m) = none
      have h_step : step tm c = none := (step_none_iff_halted tm c).mpr h_state
      rw [h_step]
  · -- Backwards: cfg → cfg', P cfg' ⟹ P cfg
    intro c c' h_step _ ⟨N', h_N'⟩
    refine ⟨N' + 1, ?_⟩
    intro k h_k
    cases k with
    | zero => omega
    | succ m =>
      show (match step tm c with | none => none | some c'' => nSteps tm c'' m) = none
      rw [h_step]
      exact h_N' m (by omega)

/-- **`CTS_Halts_imp_nSteps_eventually_none` (iter 550)**: CTS
    analog of iter 549 — consumer of `CTS_Halts_induction`.  Any
    halting CTS cfg has a bound `N` past which `cts.nSteps cfg k =
    none` for all `k > N`.  Proof: induction via iter 545 with the
    same `P` shape as iter 549. -/
theorem CTS_Halts_imp_nSteps_eventually_none (cts : CTS) (cfg : CTSConfig)
    (h : cts.Halts cfg) :
    ∃ N, ∀ k, k > N → cts.nSteps cfg k = none := by
  refine CTS_Halts_induction cts
    (fun cfg => ∃ N, ∀ k, k > N → cts.nSteps cfg k = none) ?_ ?_ cfg h
  · -- Halted cfg: step = none, so nSteps cfg (m+1) = none
    intro c h_halted
    refine ⟨0, ?_⟩
    intro k h_k
    cases k with
    | zero => omega
    | succ m =>
      show (match cts.step c with | none => none | some c' => cts.nSteps c' m) = none
      have h_step : cts.step c = none := (CTS_step_none_iff_halted cts c).mpr h_halted
      rw [h_step]
  · -- Backwards
    intro c c' h_step _ ⟨N', h_N'⟩
    refine ⟨N' + 1, ?_⟩
    intro k h_k
    cases k with
    | zero => omega
    | succ m =>
      show (match cts.step c with | none => none | some c'' => cts.nSteps c'' m) = none
      rw [h_step]
      exact h_N' m (by omega)

-- ============================================================================
-- nSteps ↔ Halts bridges (extracted in refactor)
-- ============================================================================

/-- **Bridge**: nSteps-halting implies eval-halting (`BiTM.Halts`).  This
    is the implication we need to feed nSteps-style halting facts (which
    the System 5 → 4 → 3 → 2 → 1 → 0 chain produces) into the eval-style
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
-- BiTM halt-related nSteps cluster (extracted in refactor)
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

-- ============================================================================
-- BiTM exact-step-form theorems (iters 553/556/558; extracted in refactor)
-- ============================================================================

/-- **`Halts_exact_step_form` (iter 553)**: packaging — for any
    halting BiTM cfg, there's an exact step `N` reaching a halt
    state, and beyond `N` all `nSteps` return `none`.  Combines
    `BiTM_Halts_iff_nSteps_reaches_halted` (existence of N) with
    `BiTM_halted_nSteps_eq_none` (post-halt is none) via
    `nSteps_add`. -/
theorem Halts_exact_step_form (tm : Machine) (cfg : Config) (h : Halts tm cfg) :
    ∃ N result, nSteps tm cfg N = some result ∧ result.state = 0 ∧
                ∀ k, k > N → nSteps tm cfg k = none := by
  obtain ⟨N, result, h_n, h_halt⟩ :=
    (BiTM_nSteps_halts_iff_reaches_halted tm cfg).mp (halts_imp_nSteps_none tm cfg h)
  have h_state : result.state = 0 := by
    simp [halted] at h_halt; exact h_halt
  refine ⟨N, result, h_n, h_state, ?_⟩
  intro k h_k
  have h_split : k = N + (k - N) := by omega
  rw [h_split, nSteps_add, h_n]
  show nSteps tm result (k - N) = none
  exact BiTM_halted_nSteps_eq_none tm result (k - N) h_halt (by omega)

/-- **`Halts_exact_step_form_unique` (iter 556)**: the exact halt
    step `N` from iter 553 is unique. -/
theorem Halts_exact_step_form_unique (tm : Machine) (cfg : Config)
    (N₁ N₂ : Nat) (result₁ result₂ : Config)
    (h₁_n : nSteps tm cfg N₁ = some result₁)
    (h₁_eventual : ∀ k, k > N₁ → nSteps tm cfg k = none)
    (h₂_n : nSteps tm cfg N₂ = some result₂)
    (h₂_eventual : ∀ k, k > N₂ → nSteps tm cfg k = none) :
    N₁ = N₂ := by
  rcases Nat.lt_or_ge N₁ N₂ with h_lt | h_ge
  · have h_none := h₁_eventual N₂ h_lt
    rw [h_none] at h₂_n; cases h₂_n
  · rcases Nat.lt_or_ge N₂ N₁ with h_lt' | h_ge'
    · have h_none := h₂_eventual N₁ h_lt'
      rw [h_none] at h₁_n; cases h₁_n
    · omega

/-- **`Halts_iff_exact_step_witness` (iter 558)**: biconditional
    packaging — `Halts tm cfg` is equivalent to the existence of an
    exact halt-step witness (state-0 reach + eventually-none). -/
theorem Halts_iff_exact_step_witness (tm : Machine) (cfg : Config) :
    Halts tm cfg ↔
    ∃ N result, nSteps tm cfg N = some result ∧ result.state = 0 ∧
                ∀ k, k > N → nSteps tm cfg k = none := by
  constructor
  · exact Halts_exact_step_form tm cfg
  · rintro ⟨N, result, h_n, h_state, _⟩
    have h_halted : halted result = true := by simp [halted, h_state]
    exact nSteps_none_imp_halts tm cfg
      ⟨N + 1, BiTM_nSteps_none_of_reaches_halted tm cfg result N h_n h_halted⟩

-- ============================================================================
-- BiTM misc halt-trivial lemmas (extracted in refactor)
-- ============================================================================

/-- **`halted` iff `state = 0`**: the def `halted cfg := cfg.state ==
    0` reduces directly to `cfg.state = 0` via `beq_iff_eq`. -/
theorem halted_iff_state_zero (cfg : Config) :
    halted cfg = true ↔ cfg.state = 0 := by
  unfold halted
  exact beq_iff_eq

/-- **BiTM `Halts` on state-0 config**: any cfg with `state = 0`
    halts (already halted). -/
theorem BiTM_Halts_state_zero (tm : Machine) (left : List Nat) (head : Nat)
    (right : List Nat) :
    Halts tm { state := 0, left := left, head := head, right := right } := by
  refine ⟨0, { state := 0, left := left, head := head, right := right }, ?_⟩
  simp [eval, halted]

/-- **BiTM `Halts` iff `nSteps` reaches a halted state** (analogue of
    iter 369).  Chains BiTM's `nSteps_none_imp_halts` /
    `halts_imp_nSteps_none` bridges with `BiTM_nSteps_halts_iff_
    reaches_halted`. -/
theorem BiTM_Halts_iff_nSteps_reaches_halted (tm : Machine) (cfg : Config) :
    Halts tm cfg ↔ ∃ k cfg', nSteps tm cfg k = some cfg' ∧ halted cfg' = true := by
  constructor
  · intro h_halts
    exact (BiTM_nSteps_halts_iff_reaches_halted tm cfg).mp
      (halts_imp_nSteps_none tm cfg h_halts)
  · intro ⟨k, cfg', h_n, h_halt⟩
    apply nSteps_none_imp_halts
    exact (BiTM_nSteps_halts_iff_reaches_halted tm cfg).mpr ⟨k, cfg', h_n, h_halt⟩

/-- **`BiTM_eval_some_imp_nSteps_le` (iter 564)**: BiTM analog of
    iter 563.  An eval-success witness `eval tm cfg fuel = some
    result` extracts a discrete-step witness at some `n ≤ fuel`
    that reaches the same result.  Direct fuel induction with
    case-split on `halted cfg`. -/
theorem BiTM_eval_some_imp_nSteps_le (tm : Machine) (cfg : Config) (fuel : Nat)
    (result : Config) (h : eval tm cfg fuel = some result) :
    ∃ n, n ≤ fuel ∧ nSteps tm cfg n = some result := by
  induction fuel generalizing cfg with
  | zero =>
    simp [eval] at h
    obtain ⟨_, h_eq⟩ := h
    refine ⟨0, Nat.le_refl 0, ?_⟩
    show some cfg = some result
    rw [h_eq]
  | succ m ih =>
    by_cases h_halt : halted cfg = true
    · simp [eval, h_halt] at h
      refine ⟨0, Nat.zero_le _, ?_⟩
      show some cfg = some result
      rw [h]
    · have h_nh : halted cfg = false := by
        cases h_eq : halted cfg with
        | true => exact absurd h_eq h_halt
        | false => rfl
      cases h_step : step tm cfg with
      | none =>
        have h_state := (step_none_iff_halted tm cfg).mp h_step
        have h_h : halted cfg = true := by simp [halted, h_state]
        rw [h_h] at h_nh; cases h_nh
      | some cfg' =>
        have h_eval' : eval tm cfg' m = some result := by
          simp [eval, h_nh, h_step] at h
          exact h
        obtain ⟨n', h_le, h_n'⟩ := ih cfg' h_eval'
        refine ⟨n' + 1, by omega, ?_⟩
        rw [BiTM_nSteps_succ_unfold, h_step]
        exact h_n'

-- ============================================================================
-- BiTM Halts step/nSteps propagation cluster (extracted in refactor)
-- ============================================================================

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

/-- **BiTM `Halts` step-successor**. -/
theorem BiTM_Halts_step_succ
    (tm : Machine) (cfg cfg' : Config) (h_step : step tm cfg = some cfg')
    (h : Halts tm cfg) :
    Halts tm cfg' := by
  obtain ⟨fuel, res, h_eval⟩ := h
  have h_not_halt : halted cfg ≠ true := by
    intro h_halt
    have h_state : cfg.state = 0 := by
      unfold halted at h_halt
      exact (beq_iff_eq).mp h_halt
    have := (step_none_iff_halted tm cfg).mpr h_state
    rw [this] at h_step
    cases h_step
  cases fuel with
  | zero =>
    simp [eval] at h_eval
    obtain ⟨h_halt, _⟩ := h_eval
    exact absurd h_halt h_not_halt
  | succ k =>
    simp [eval, h_not_halt, h_step] at h_eval
    exact ⟨k, res, h_eval⟩

/-- **BiTM `Halts` step iff**. -/
theorem BiTM_Halts_step_iff
    (tm : Machine) (cfg cfg' : Config) (h_step : step tm cfg = some cfg') :
    Halts tm cfg ↔ Halts tm cfg' :=
  ⟨BiTM_Halts_step_succ tm cfg cfg' h_step,
   BiTM_Halts_step_pred tm cfg cfg' h_step⟩

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

/-- **BiTM `Halts` propagates under nSteps**. -/
theorem BiTM_Halts_nSteps_succ
    (tm : Machine) (cfg : Config) (n : Nat) (h : Halts tm cfg)
    (result : Config) (h_n : nSteps tm cfg n = some result) :
    Halts tm result := by
  induction n generalizing cfg with
  | zero =>
    simp [nSteps] at h_n
    rw [← h_n]
    exact h
  | succ k ih =>
    rw [BiTM_nSteps_succ_unfold] at h_n
    cases h_step : step tm cfg with
    | none => rw [h_step] at h_n; cases h_n
    | some cfg₁ =>
      rw [h_step] at h_n
      have h_halts₁ := BiTM_Halts_step_succ tm cfg cfg₁ h_step h
      exact ih cfg₁ h_halts₁ h_n

/-- **BiTM `Halts` iff under nSteps**. -/
theorem BiTM_Halts_nSteps_iff
    (tm : Machine) (cfg : Config) (n : Nat) (result : Config)
    (h_n : nSteps tm cfg n = some result) :
    Halts tm cfg ↔ Halts tm result :=
  ⟨fun h => BiTM_Halts_nSteps_succ tm cfg n h result h_n,
   BiTM_Halts_nSteps_pred tm cfg n result h_n⟩

-- ============================================================================
-- BiTM eval-side lemmas (extracted in refactor)
-- ============================================================================

/-- **BiTM `eval` returns `some` only with halted result**.  When
    `eval tm cfg fuel = some result`, `halted result = true`. -/
theorem BiTM_eval_some_imp_halted (tm : Machine) (cfg : Config)
    (fuel : Nat) (result : Config)
    (h : eval tm cfg fuel = some result) :
    halted result = true := by
  induction fuel generalizing cfg with
  | zero =>
    simp [eval] at h
    obtain ⟨h_halt, h_eq⟩ := h
    rw [← h_eq]; exact h_halt
  | succ k ih =>
    simp [eval] at h
    by_cases h_halt : halted cfg = true
    · rw [if_pos h_halt] at h
      injection h with h_eq
      rw [← h_eq]; exact h_halt
    · rw [if_neg h_halt] at h
      cases h_step : step tm cfg with
      | none =>
        rw [h_step] at h
        simp at h
        rw [← h]
        have h_state : cfg.state = 0 := (step_none_iff_halted tm cfg).mp h_step
        unfold halted
        rw [h_state]
        rfl
      | some cfg' =>
        rw [h_step] at h
        simp at h
        exact ih cfg' h

/-- **BiTM `eval` returns `some result` only with `state = 0`**. -/
theorem BiTM_eval_some_state_zero (tm : Machine) (cfg : Config)
    (fuel : Nat) (result : Config)
    (h : eval tm cfg fuel = some result) :
    result.state = 0 := by
  have h_halt := BiTM_eval_some_imp_halted tm cfg fuel result h
  unfold halted at h_halt
  exact (beq_iff_eq).mp h_halt

/-- **BiTM `eval` on a halted cfg returns the cfg itself**. -/
theorem BiTM_eval_halted_self (tm : Machine) (cfg : Config)
    (h : halted cfg = true) (fuel : Nat) :
    eval tm cfg fuel = some cfg := by
  cases fuel with
  | zero => simp [eval, h]
  | succ k => simp [eval, h]

/-- **BiTM `eval` fuel-succ monotonicity**. -/
theorem BiTM_eval_fuel_succ (tm : Machine) (cfg : Config) (fuel : Nat)
    (result : Config) (h : eval tm cfg fuel = some result) :
    eval tm cfg (fuel + 1) = some result := by
  induction fuel generalizing cfg with
  | zero =>
    simp [eval] at h
    obtain ⟨h_halt, h_eq⟩ := h
    rw [← h_eq]
    exact BiTM_eval_halted_self tm cfg h_halt 1
  | succ k ih =>
    by_cases h_halt : halted cfg = true
    · simp [eval, h_halt] at h
      rw [← h]
      exact BiTM_eval_halted_self tm cfg h_halt _
    · simp [eval, h_halt] at h
      cases h_step : step tm cfg with
      | none =>
        rw [h_step] at h
        simp at h
        rw [← h]
        have h_state : cfg.state = 0 := (step_none_iff_halted tm cfg).mp h_step
        have h_halt_cfg : halted cfg = true := by
          unfold halted; rw [h_state]; rfl
        exact absurd h_halt_cfg h_halt
      | some cfg' =>
        rw [h_step] at h
        simp [eval, h_halt, h_step]
        exact ih cfg' h

/-- **BiTM `eval` fuel monotonicity (multi-step)**. -/
theorem BiTM_eval_fuel_le (tm : Machine) (cfg : Config)
    (fuel fuel' : Nat) (h_le : fuel ≤ fuel') (result : Config)
    (h : eval tm cfg fuel = some result) :
    eval tm cfg fuel' = some result := by
  obtain ⟨k, h_k⟩ : ∃ k, fuel' = fuel + k := ⟨fuel' - fuel, by omega⟩
  rw [h_k]
  clear h_k h_le fuel'
  induction k with
  | zero => exact h
  | succ j ih =>
    rw [show fuel + (j + 1) = (fuel + j) + 1 from by omega]
    exact BiTM_eval_fuel_succ tm cfg (fuel + j) result ih

/-- **BiTM Halts implies eval stabilizes**. -/
theorem BiTM_Halts_eval_stable (tm : Machine) (cfg : Config)
    (h : Halts tm cfg) :
    ∃ fuel result, ∀ fuel' ≥ fuel, eval tm cfg fuel' = some result := by
  obtain ⟨fuel, result, h_eval⟩ := h
  exact ⟨fuel, result, fun fuel' h_le =>
    BiTM_eval_fuel_le tm cfg fuel fuel' h_le result h_eval⟩

/-- **BiTM `nSteps` reaching a halted state produces matching `eval`**. -/
theorem BiTM_nSteps_some_halted_imp_eval
    (tm : Machine) (cfg : Config) (n : Nat) (result : Config)
    (h_n : nSteps tm cfg n = some result) (h_halt : halted result = true) :
    eval tm cfg n = some result := by
  induction n generalizing cfg with
  | zero =>
    simp [nSteps] at h_n
    rw [← h_n]
    rw [← h_n] at h_halt
    exact BiTM_eval_halted_self tm cfg h_halt 0
  | succ k ih =>
    rw [BiTM_nSteps_succ_unfold] at h_n
    cases h_step : step tm cfg with
    | none => rw [h_step] at h_n; cases h_n
    | some cfg₁ =>
      rw [h_step] at h_n
      have h_not_halt : halted cfg ≠ true := by
        intro h_halt_cfg
        have h_state : cfg.state = 0 := by
          unfold halted at h_halt_cfg
          exact (beq_iff_eq).mp h_halt_cfg
        have := (step_none_iff_halted tm cfg).mpr h_state
        rw [this] at h_step
        cases h_step
      simp [eval, h_not_halt, h_step]
      exact ih cfg₁ h_n

/-- **BiTM `eval` produces an exact `nSteps` witness**: BiTM analogue of
    `CTS_eval_some_imp_exists_nSteps`. -/
theorem BiTM_eval_some_imp_exists_nSteps
    (tm : Machine) (cfg : Config) (fuel : Nat) (result : Config)
    (h : eval tm cfg fuel = some result) :
    ∃ k, k ≤ fuel ∧ nSteps tm cfg k = some result ∧ halted result = true := by
  induction fuel generalizing cfg with
  | zero =>
    cases h_halt : halted cfg with
    | true =>
      simp [eval, h_halt] at h
      refine ⟨0, Nat.le_refl _, ?_, ?_⟩
      · simp [nSteps]; exact h
      · rw [← h]; exact h_halt
    | false =>
      simp [eval, h_halt] at h
  | succ fuel ih =>
    cases h_halt : halted cfg with
    | true =>
      simp [eval, h_halt] at h
      refine ⟨0, Nat.zero_le _, ?_, ?_⟩
      · simp [nSteps]; exact h
      · rw [← h]; exact h_halt
    | false =>
      cases h_step : step tm cfg with
      | none =>
        have h_state : cfg.state = 0 := (step_none_iff_halted tm cfg).mp h_step
        have h_h : halted cfg = true := by simp [halted, h_state]
        rw [h_h] at h_halt
        exact Bool.noConfusion h_halt
      | some cfg' =>
        simp [eval, h_halt, h_step] at h
        obtain ⟨k, h_le, h_n, h_halt_r⟩ := ih cfg' h
        refine ⟨k + 1, Nat.succ_le_succ h_le, ?_, h_halt_r⟩
        rw [BiTM_nSteps_succ_unfold, h_step]
        exact h_n

/-- **BiTM `nSteps`-witness gives `eval`**. -/
theorem BiTM_exists_nSteps_some_imp_eval
    (tm : Machine) (cfg : Config) (fuel : Nat) (result : Config)
    (h : ∃ k, k ≤ fuel ∧ nSteps tm cfg k = some result ∧ halted result = true) :
    eval tm cfg fuel = some result := by
  obtain ⟨k, h_le, h_n, h_halt⟩ := h
  have h_eval := BiTM_nSteps_some_halted_imp_eval tm cfg k result h_n h_halt
  exact BiTM_eval_fuel_le tm cfg k fuel h_le result h_eval

/-- **BiTM `eval`/`nSteps` biconditional**. -/
theorem BiTM_eval_some_iff_exists_nSteps
    (tm : Machine) (cfg : Config) (fuel : Nat) (result : Config) :
    eval tm cfg fuel = some result ↔
    ∃ k, k ≤ fuel ∧ nSteps tm cfg k = some result ∧ halted result = true :=
  ⟨BiTM_eval_some_imp_exists_nSteps tm cfg fuel result,
   BiTM_exists_nSteps_some_imp_eval tm cfg fuel result⟩

/-- **BiTM Halts iff `eval` succeeds with `state = 0`**. -/
theorem BiTM_Halts_iff_eval_state_zero (tm : Machine) (cfg : Config) :
    Halts tm cfg ↔ ∃ fuel result, eval tm cfg fuel = some result
                                  ∧ result.state = 0 := by
  constructor
  · intro ⟨fuel, result, h_eval⟩
    exact ⟨fuel, result, h_eval, BiTM_eval_some_state_zero tm cfg fuel result h_eval⟩
  · intro ⟨fuel, result, h_eval, _⟩
    exact ⟨fuel, result, h_eval⟩

/-- **`BiTM_eval_result_unique` (iter 568)**: any two eval witnesses
    for the same cfg agree on the result.  Proof: extend both
    witnesses to `max f₁ f₂` via `BiTM_eval_fuel_le` (iter 384);
    they then equal `some` of the same value.  Justifies the
    informal "halt result of a halting cfg" terminology. -/
theorem BiTM_eval_result_unique (tm : Machine) (cfg : Config)
    (f₁ f₂ : Nat) (r₁ r₂ : Config)
    (h₁ : eval tm cfg f₁ = some r₁) (h₂ : eval tm cfg f₂ = some r₂) :
    r₁ = r₂ := by
  have h_le1 : f₁ ≤ max f₁ f₂ := Nat.le_max_left f₁ f₂
  have h_le2 : f₂ ≤ max f₁ f₂ := Nat.le_max_right f₁ f₂
  have h₁' := BiTM_eval_fuel_le tm cfg f₁ (max f₁ f₂) h_le1 r₁ h₁
  have h₂' := BiTM_eval_fuel_le tm cfg f₂ (max f₁ f₂) h_le2 r₂ h₂
  rw [h₁'] at h₂'
  injection h₂'

/-- **BiTM `nSteps` split**: BiTM analogue of `CTS_nSteps_some_split`. -/
theorem BiTM_nSteps_some_split (tm : Machine) (cfg : Config)
    (n m : Nat) (result : Config)
    (h : nSteps tm cfg (n + m) = some result) :
    ∃ mid, nSteps tm cfg n = some mid ∧ nSteps tm mid m = some result := by
  induction n generalizing cfg with
  | zero =>
    rw [Nat.zero_add] at h
    exact ⟨cfg, rfl, h⟩
  | succ n ih =>
    rw [Nat.succ_add, BiTM_nSteps_succ_unfold] at h
    cases h_step : step tm cfg with
    | none => rw [h_step] at h; cases h
    | some cfg₁ =>
      rw [h_step] at h
      obtain ⟨mid, h_mid, h_rest⟩ := ih cfg₁ h
      refine ⟨mid, ?_, h_rest⟩
      rw [BiTM_nSteps_succ_unfold, h_step]
      exact h_mid

/-- **BiTM `nSteps` compose**: BiTM analogue of `CTS_nSteps_some_compose`. -/
theorem BiTM_nSteps_some_compose (tm : Machine) (cfg mid : Config)
    (n m : Nat) (result : Config)
    (h_n : nSteps tm cfg n = some mid)
    (h_m : nSteps tm mid m = some result) :
    nSteps tm cfg (n + m) = some result := by
  rw [nSteps_add, h_n]
  exact h_m

/-- **Either halted or steppable**: any TM cfg either is at state 0
    (halted) or admits a step.  Direct dichotomy from
    `step_none_iff_halted`. -/
theorem step_or_halted (tm : Machine) (cfg : Config) :
    cfg.state = 0 ∨ ∃ cfg', step tm cfg = some cfg' := by
  by_cases h : cfg.state = 0
  · left; exact h
  · right
    cases h_step : step tm cfg with
    | none =>
      exfalso
      exact h ((step_none_iff_halted tm cfg).mp h_step)
    | some cfg' => exact ⟨cfg', rfl⟩

/-- **`Halts` step decomposition**: any halting cfg is either at
    state 0 or steps to another halting cfg. -/
theorem Halts_step_decompose
    (tm : Machine) (cfg : Config) (h : Halts tm cfg) :
    cfg.state = 0 ∨ ∃ cfg', step tm cfg = some cfg' ∧ Halts tm cfg' := by
  rcases step_or_halted tm cfg with h_state | ⟨cfg', h_step⟩
  · left; exact h_state
  · right
    exact ⟨cfg', h_step, (BiTM_Halts_step_iff tm cfg cfg' h_step).mp h⟩

/-- **`Halts` step decomposition active version**: when cfg is
    active (state ≠ 0), the step branch is forced. -/
theorem Halts_step_decompose_active
    (tm : Machine) (cfg : Config) (h_active : cfg.state ≠ 0)
    (h_halts : Halts tm cfg) :
    ∃ cfg', step tm cfg = some cfg' ∧ Halts tm cfg' := by
  rcases Halts_step_decompose tm cfg h_halts with h_state | h_step
  · exact absurd h_state h_active
  · exact h_step

/-- **`BiTM_Halts_iff_step_or_zero` (iter 570)**: BiTM analog of
    iter 540 (Tag).  `Halts tm cfg ↔ cfg.state = 0 ∨ (∃ cfg', step
    tm cfg = some cfg' ∧ Halts tm cfg')`. -/
theorem BiTM_Halts_iff_step_or_zero (tm : Machine) (cfg : Config) :
    Halts tm cfg ↔ cfg.state = 0 ∨
                  ∃ cfg', step tm cfg = some cfg' ∧ Halts tm cfg' := by
  constructor
  · exact Halts_step_decompose tm cfg
  · rintro (h_state | ⟨cfg', h_step, h_halts⟩)
    · have : cfg = { state := 0, left := cfg.left, head := cfg.head,
                     right := cfg.right } := by
        cases cfg
        simp
        exact h_state
      rw [this]
      exact BiTM_Halts_state_zero tm cfg.left cfg.head cfg.right
    · exact BiTM_Halts_step_pred tm cfg cfg' h_step h_halts

/-- **BiTM step preserves not-Halts**. -/
theorem BiTM_not_Halts_step_succ
    (tm : Machine) (cfg cfg' : Config)
    (h_step : step tm cfg = some cfg') (h : ¬ Halts tm cfg) :
    ¬ Halts tm cfg' :=
  fun h_halt' => h (BiTM_Halts_step_pred tm cfg cfg' h_step h_halt')

/-- **BiTM nSteps preserves not-Halts**. -/
theorem BiTM_not_Halts_nSteps_succ
    (tm : Machine) (cfg : Config) (n : Nat) (r : Config)
    (h_n : nSteps tm cfg n = some r) (h : ¬ Halts tm cfg) :
    ¬ Halts tm r :=
  fun h_halt' => h (BiTM_Halts_nSteps_pred tm cfg n r h_n h_halt')

/-- **BiTM `nSteps`-none succ propagation**. -/
theorem BiTM_nSteps_none_succ
    (tm : Machine) (cfg : Config) (n : Nat)
    (h : nSteps tm cfg n = none) :
    nSteps tm cfg (n + 1) = none := by
  rw [nSteps_add tm cfg n 1, h]
  rfl

/-- **BiTM `nSteps`-none monotone propagation**. -/
theorem BiTM_nSteps_none_propagate
    (tm : Machine) (cfg : Config) (n m : Nat)
    (h_le : n ≤ m) (h_n : nSteps tm cfg n = none) :
    nSteps tm cfg m = none := by
  obtain ⟨k, h_k⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  rw [h_k]
  clear h_k h_le m
  induction k with
  | zero => exact h_n
  | succ j ih =>
    rw [show n + (j + 1) = (n + j) + 1 from by omega]
    exact BiTM_nSteps_none_succ tm cfg (n + j) ih

/-- **BiTM `nSteps`-some monotonicity**. -/
theorem BiTM_nSteps_some_le
    (tm : Machine) (cfg : Config) (k n : Nat) (h_le : k ≤ n)
    (result : Config) (h : nSteps tm cfg n = some result) :
    ∃ intermediate, nSteps tm cfg k = some intermediate := by
  cases h_k : nSteps tm cfg k with
  | none =>
    have h_n := BiTM_nSteps_none_propagate tm cfg k n h_le h_k
    rw [h_n] at h
    cases h
  | some intermediate => exact ⟨intermediate, rfl⟩

/-- **BiTM nSteps past halt yields none**. -/
theorem BiTM_nSteps_past_halt_eq_none
    (tm : Machine) (cfg : Config) (n : Nat) (result : Config)
    (h_n : nSteps tm cfg n = some result) (h_halt : halted result = true)
    (k : Nat) (h_k : k ≥ 1) :
    nSteps tm cfg (n + k) = none := by
  rw [nSteps_add, h_n]
  exact BiTM_halted_nSteps_eq_none tm result k h_halt h_k

/-- **BiTM halt-point uniqueness**. -/
theorem BiTM_nSteps_halt_unique
    (tm : Machine) (cfg : Config) (n₁ n₂ : Nat) (r₁ r₂ : Config)
    (h₁ : nSteps tm cfg n₁ = some r₁) (h_halt₁ : halted r₁ = true)
    (h₂ : nSteps tm cfg n₂ = some r₂) (h_halt₂ : halted r₂ = true) :
    n₁ = n₂ ∧ r₁ = r₂ := by
  rcases Nat.lt_or_ge n₁ n₂ with h_lt | h_ge
  · obtain ⟨k, hk_pos, rfl⟩ : ∃ k, k ≥ 1 ∧ n₂ = n₁ + k :=
      ⟨n₂ - n₁, by omega, by omega⟩
    rw [BiTM_nSteps_past_halt_eq_none tm cfg n₁ r₁ h₁ h_halt₁ k hk_pos] at h₂
    cases h₂
  · rcases Nat.lt_or_eq_of_le h_ge with h_lt | h_eq
    · obtain ⟨k, hk_pos, rfl⟩ : ∃ k, k ≥ 1 ∧ n₁ = n₂ + k :=
        ⟨n₁ - n₂, by omega, by omega⟩
      rw [BiTM_nSteps_past_halt_eq_none tm cfg n₂ r₂ h₂ h_halt₂ k hk_pos] at h₁
      cases h₁
    · subst h_eq
      rw [h₁] at h₂
      injection h₂ with h_r
      exact ⟨rfl, h_r⟩

/-- **BiTM intermediate-state retrieval**. -/
theorem BiTM_nSteps_intermediate
    (tm : Machine) (cfg r₁ r₂ : Config) (n₁ n₂ : Nat) (h_le : n₁ ≤ n₂)
    (h₁ : nSteps tm cfg n₁ = some r₁) (h₂ : nSteps tm cfg n₂ = some r₂) :
    nSteps tm r₁ (n₂ - n₁) = some r₂ := by
  have h_sum : n₁ + (n₂ - n₁) = n₂ := by omega
  rw [← h_sum, nSteps_add, h₁] at h₂
  exact h₂

/-- **`halted` implies `Halts`**. -/
theorem halted_imp_Halts (tm : Machine) (cfg : Config)
    (h : halted cfg = true) :
    Halts tm cfg := by
  refine ⟨0, cfg, ?_⟩
  simp [eval, h]

/-- **BiTM intermediate-state Halts retrieval**. -/
theorem BiTM_nSteps_intermediate_Halts
    (tm : Machine) (cfg r₁ r₂ : Config) (n₁ n₂ : Nat) (h_le : n₁ ≤ n₂)
    (h₁ : nSteps tm cfg n₁ = some r₁)
    (h₂ : nSteps tm cfg n₂ = some r₂) (h_halt₂ : halted r₂ = true) :
    Halts tm r₁ :=
  BiTM_Halts_nSteps_pred tm r₁ (n₂ - n₁) r₂
    (BiTM_nSteps_intermediate tm cfg r₁ r₂ n₁ n₂ h_le h₁ h₂)
    (halted_imp_Halts tm r₂ h_halt₂)

/-- **BiTM Halts iff exists nSteps none**. -/
theorem BiTM_Halts_iff_exists_nSteps_none
    (tm : Machine) (cfg : Config) :
    Halts tm cfg ↔ ∃ n, nSteps tm cfg n = none :=
  ⟨halts_imp_nSteps_none tm cfg, nSteps_none_imp_halts tm cfg⟩

/-- **BiTM first nSteps-none**. -/
theorem BiTM_Halts_first_none
    (tm : Machine) (cfg : Config) (h : Halts tm cfg) :
    ∃ n, nSteps tm cfg n = none ∧ ∀ m < n, nSteps tm cfg m ≠ none := by
  obtain ⟨N, hN⟩ := (BiTM_Halts_iff_exists_nSteps_none tm cfg).mp h
  rcases find_min_or_none (fun n => nSteps tm cfg n = none) N with
    ⟨k, _h_le, h_pk, h_min⟩ | h_none
  · exact ⟨k, h_pk, h_min⟩
  · exact absurd hN (h_none N (Nat.le_refl _))

/-- **BiTM first-none predecessor halts**. -/
theorem BiTM_first_none_predecessor_halts
    (tm : Machine) (cfg : Config) (N : Nat)
    (hN : nSteps tm cfg N = none) (h_min : ∀ m < N, nSteps tm cfg m ≠ none) :
    ∃ k, N = k + 1 ∧ ∃ r, nSteps tm cfg k = some r ∧ halted r = true := by
  cases N with
  | zero =>
    simp [nSteps] at hN
  | succ k =>
    refine ⟨k, rfl, ?_⟩
    cases h_k : nSteps tm cfg k with
    | none => exact absurd h_k (h_min k (Nat.lt_succ_self k))
    | some r =>
      refine ⟨r, rfl, ?_⟩
      have h_one : nSteps tm r 1 = none := by
        rw [nSteps_add, h_k] at hN
        exact hN
      rw [nSteps_one] at h_one
      have h_state : r.state = 0 := (step_none_iff_halted tm r).mp h_one
      simp [halted, h_state]

/-- **BiTM halt-time extractor**. -/
theorem BiTM_Halts_extract_halt_time
    (tm : Machine) (cfg : Config) (h : Halts tm cfg) :
    ∃ k r, nSteps tm cfg k = some r ∧ halted r = true ∧
           ∀ m < k, ∀ r', nSteps tm cfg m = some r' → halted r' = false := by
  obtain ⟨N, hN, h_min⟩ := BiTM_Halts_first_none tm cfg h
  obtain ⟨k, _h_N_eq, r, h_step, h_halt⟩ :=
    BiTM_first_none_predecessor_halts tm cfg N hN h_min
  refine ⟨k, r, h_step, h_halt, ?_⟩
  intro m h_lt r' h_m
  cases h_halt'_b : halted r' with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨h_eq_mn, _⟩ := BiTM_nSteps_halt_unique tm cfg m k r' r
                            h_m h_halt'_b h_step h_halt
    omega

/-- **BiTM Halts eval at halt time**. -/
theorem BiTM_Halts_eval_at_halt_time
    (tm : Machine) (cfg : Config) (h : Halts tm cfg) :
    ∃ k r, eval tm cfg k = some r ∧ nSteps tm cfg k = some r
           ∧ halted r = true
           ∧ ∀ m < k, ∀ r', nSteps tm cfg m = some r' → halted r' = false := by
  obtain ⟨k, r, h_step, h_halt, h_min⟩ := BiTM_Halts_extract_halt_time tm cfg h
  exact ⟨k, r,
    BiTM_nSteps_some_halted_imp_eval tm cfg k r h_step h_halt,
    h_step, h_halt, h_min⟩

/-- **BiTM step-some implies not halted**. -/
theorem BiTM_step_some_not_halted (tm : Machine) (cfg cfg' : Config)
    (h : step tm cfg = some cfg') :
    halted cfg = false := by
  cases h_halted : halted cfg with
  | true =>
    exfalso
    have h_state : cfg.state = 0 := by simp [halted] at h_halted; exact h_halted
    rw [(step_none_iff_halted tm cfg).mpr h_state] at h
    cases h
  | false => rfl

/-- **BiTM self-loop nSteps stays at cfg**. -/
theorem BiTM_self_loop_nSteps_self
    (tm : Machine) (cfg : Config) (h_self : step tm cfg = some cfg) (n : Nat) :
    nSteps tm cfg n = some cfg := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [BiTM_nSteps_succ_unfold, h_self]
    exact ih

/-- **BiTM self-loop does not halt**. -/
theorem BiTM_self_loop_not_halts
    (tm : Machine) (cfg : Config) (h_self : step tm cfg = some cfg) :
    ¬ Halts tm cfg := by
  intro h_halts
  rw [BiTM_Halts_iff_nSteps_reaches_halted] at h_halts
  obtain ⟨k, r, h_n, h_halt_r⟩ := h_halts
  rw [BiTM_self_loop_nSteps_self tm cfg h_self k] at h_n
  injection h_n with h_eq
  rw [← h_eq] at h_halt_r
  have h_not_halted : halted cfg = false :=
    BiTM_step_some_not_halted tm cfg cfg h_self
  rw [h_halt_r] at h_not_halted
  exact Bool.noConfusion h_not_halted

/-- **BiTM periodic-orbit nSteps stays at cfg modulo k iterations**. -/
theorem BiTM_periodic_nSteps_iter
    (tm : Machine) (cfg : Config) (p : Nat)
    (h_period : nSteps tm cfg p = some cfg) (k : Nat) :
    nSteps tm cfg (k * p) = some cfg := by
  induction k with
  | zero => rw [Nat.zero_mul]; rfl
  | succ k ih =>
    rw [Nat.succ_mul, nSteps_add, ih]
    exact h_period

/-- **BiTM periodic orbit ⇒ not halts**. -/
theorem BiTM_periodic_not_halts
    (tm : Machine) (cfg : Config) (p : Nat) (h_pos : p ≥ 1)
    (h_period : nSteps tm cfg p = some cfg) :
    ¬ Halts tm cfg := by
  intro h_halts
  rw [BiTM_Halts_iff_nSteps_reaches_halted] at h_halts
  obtain ⟨N, r, h_n, h_halt_r⟩ := h_halts
  have h_iter := BiTM_periodic_nSteps_iter tm cfg p h_period (N + 1)
  have h_ge : (N + 1) * p ≥ N + 1 := by
    have : (N + 1) * 1 ≤ (N + 1) * p := Nat.mul_le_mul_left _ h_pos
    omega
  obtain ⟨j, hj_pos, h_eq⟩ : ∃ j, j ≥ 1 ∧ (N + 1) * p = N + j :=
    ⟨(N + 1) * p - N, by omega, by omega⟩
  rw [h_eq] at h_iter
  rw [BiTM_nSteps_past_halt_eq_none tm cfg N r h_n h_halt_r j hj_pos] at h_iter
  cases h_iter

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

/-- **BiTM Halts ⇒ no period**. -/
theorem BiTM_Halts_no_period
    (tm : Machine) (cfg : Config) (h : Halts tm cfg)
    (p : Nat) (h_pos : p ≥ 1) :
    nSteps tm cfg p ≠ some cfg :=
  fun h_period => BiTM_periodic_not_halts tm cfg p h_pos h_period h

/-- **`Halts_eval_exact_step_form`**: an `eval`-success witness with
    fuel `f` produces a full exact-step witness with `N ≤ f`.
    Combines `BiTM_eval_some_imp_nSteps_le` with
    `BiTM_eval_some_imp_halted` and `BiTM_halted_nSteps_eq_none`. -/
theorem Halts_eval_exact_step_form (tm : Machine) (cfg : Config) (fuel : Nat)
    (result : Config) (h : eval tm cfg fuel = some result) :
    ∃ N, N ≤ fuel ∧ nSteps tm cfg N = some result ∧ result.state = 0 ∧
         ∀ k, k > N → nSteps tm cfg k = none := by
  obtain ⟨N, h_le, h_n⟩ := BiTM_eval_some_imp_nSteps_le tm cfg fuel result h
  have h_halted : halted result = true := BiTM_eval_some_imp_halted tm cfg fuel result h
  have h_state : result.state = 0 := by simp [halted] at h_halted; exact h_halted
  refine ⟨N, h_le, h_n, h_state, ?_⟩
  intro k h_k
  have h_split : k = N + (k - N) := by omega
  rw [h_split, nSteps_add, h_n]
  show nSteps tm result (k - N) = none
  exact BiTM_halted_nSteps_eq_none tm result (k - N) h_halted (by omega)

private theorem readHead_snd_length_ge (l : List Nat) :
    (readHead l).snd.length + 1 ≥ l.length := by
  cases l with
  | nil => simp [readHead]
  | cons h t => simp [readHead]

/-- Total tape length is **non-decreasing** under any TM step.  Per step
    the head moves onto one side and writes onto the other; the moved-onto
    side either pops one element (if non-empty) or contributes 0 (empty),
    while the written-onto side gains one element.  So total either stays
    or grows by 1.

    Useful smith-side invariant: rules out periodic returns that would
    require shrinking the tape. -/
theorem step_total_length_nondecreasing (tm : Machine) (cfg cfg' : Config)
    (h_active : cfg.state ≠ 0) (h_step : step tm cfg = some cfg') :
    cfg.left.length + cfg.right.length ≤ cfg'.left.length + cfg'.right.length := by
  have h_state_neq : ¬ ((cfg.state == 0) = true) := by simp [h_active]
  unfold step at h_step
  rw [if_neg h_state_neq] at h_step
  dsimp only at h_step
  generalize h_d : (tm.transition cfg.state cfg.head).dir = d at h_step
  cases d with
  | L =>
    cases h_l_eq : (readHead cfg.left) with
    | mk newHead newLeft =>
      rw [h_l_eq] at h_step
      dsimp at h_step
      injection h_step with h_inj
      rw [← h_inj]
      simp only [List.length_cons]
      have h_left : newLeft = (readHead cfg.left).snd := by rw [h_l_eq]
      have h_left_len : newLeft.length + 1 ≥ cfg.left.length := by
        rw [h_left]; exact readHead_snd_length_ge cfg.left
      omega
  | R =>
    cases h_r_eq : (readHead cfg.right) with
    | mk newHead newRight =>
      rw [h_r_eq] at h_step
      dsimp at h_step
      injection h_step with h_inj
      rw [← h_inj]
      simp only [List.length_cons]
      have h_right : newRight = (readHead cfg.right).snd := by rw [h_r_eq]
      have h_right_len : newRight.length + 1 ≥ cfg.right.length := by
        rw [h_right]; exact readHead_snd_length_ge cfg.right
      omega

/-- Every TM step writes a symbol on one side of the head, so the resulting
    cfg's `left` or `right` list is one element longer than the original's.
    This is a structural property of any TM (not just wolfram23). -/
theorem step_grows_some_side (tm : Machine) (cfg cfg' : Config)
    (h_active : cfg.state ≠ 0) (h_step : step tm cfg = some cfg') :
    cfg'.right.length = cfg.right.length + 1 ∨
    cfg'.left.length = cfg.left.length + 1 := by
  have h_state_neq : ¬ ((cfg.state == 0) = true) := by simp [h_active]
  unfold step at h_step
  rw [if_neg h_state_neq] at h_step
  dsimp only at h_step
  generalize h_d : (tm.transition cfg.state cfg.head).dir = d at h_step
  cases d with
  | L =>
    cases h_l : readHead cfg.left with
    | mk newHead newLeft =>
      rw [h_l] at h_step
      dsimp at h_step
      injection h_step with h_eq
      left
      rw [← h_eq]
      simp
  | R =>
    cases h_r : readHead cfg.right with
    | mk newHead newRight =>
      rw [h_r] at h_step
      dsimp at h_step
      injection h_step with h_eq
      right
      rw [← h_eq]
      simp

/-- **Strict-growth** lemma: when a TM step reads from an empty side, the
    total tape length grows by exactly 1 (the write goes onto the other
    side, the empty read contributes 0).

    Useful for ruling out periodicity: a periodic cycle requires every
    step to *preserve* total length (since length is non-decreasing and
    must return to the original value), hence no step can read from
    an empty side. -/
theorem step_grows_strict_when_reading_empty (tm : Machine)
    (cfg cfg' : Config) (h_active : cfg.state ≠ 0)
    (h_step : step tm cfg = some cfg')
    (h_empty : ((tm.transition cfg.state cfg.head).dir = Dir.L ∧ cfg.left = []) ∨
               ((tm.transition cfg.state cfg.head).dir = Dir.R ∧ cfg.right = [])) :
    cfg'.left.length + cfg'.right.length = cfg.left.length + cfg.right.length + 1 := by
  have h_state_neq : ¬ ((cfg.state == 0) = true) := by simp [h_active]
  unfold step at h_step
  rw [if_neg h_state_neq] at h_step
  dsimp only at h_step
  generalize h_d : (tm.transition cfg.state cfg.head).dir = d at h_step
  cases d with
  | L =>
    rcases h_empty with ⟨_, h_left⟩ | ⟨h_dir_R, _⟩
    · rw [h_left, readHead] at h_step
      dsimp at h_step
      injection h_step with h_inj
      rw [← h_inj, h_left]
      simp
    · rw [h_d] at h_dir_R; cases h_dir_R
  | R =>
    rcases h_empty with ⟨h_dir_L, _⟩ | ⟨_, h_right⟩
    · rw [h_d] at h_dir_L; cases h_dir_L
    · rw [h_right, readHead] at h_step
      dsimp at h_step
      injection h_step with h_inj
      rw [← h_inj, h_right]
      simp

/-- **`readHead` snd length upper bound**: reading from a list returns
    a tail at most as long as the original. -/
private theorem readHead_snd_length_le (l : List Nat) :
    (readHead l).snd.length ≤ l.length := by
  cases l with
  | nil => simp [readHead]
  | cons _ _ => simp [readHead]

/-- **Step total length upper bound**: each active TM step grows the
    total tape length by at most 1.  Companion to
    `step_total_length_nondecreasing` (lower bound), giving the full
    bound: `cfg.total ≤ cfg'.total ≤ cfg.total + 1`. -/
theorem step_total_length_le_succ (tm : Machine) (cfg cfg' : Config)
    (h_active : cfg.state ≠ 0) (h_step : step tm cfg = some cfg') :
    cfg'.left.length + cfg'.right.length ≤ cfg.left.length + cfg.right.length + 1 := by
  have h_state_neq : ¬ ((cfg.state == 0) = true) := by simp [h_active]
  unfold step at h_step
  rw [if_neg h_state_neq] at h_step
  dsimp only at h_step
  generalize h_d : (tm.transition cfg.state cfg.head).dir = d at h_step
  cases d with
  | L =>
    cases h_l_eq : readHead cfg.left with
    | mk newHead newLeft =>
      rw [h_l_eq] at h_step
      dsimp at h_step
      injection h_step with h_inj
      rw [← h_inj]
      simp only [List.length_cons]
      have h_left_len_le : newLeft.length ≤ cfg.left.length := by
        have h_eq : newLeft = (readHead cfg.left).snd := by rw [h_l_eq]
        rw [h_eq]; exact readHead_snd_length_le cfg.left
      omega
  | R =>
    cases h_r_eq : readHead cfg.right with
    | mk newHead newRight =>
      rw [h_r_eq] at h_step
      dsimp at h_step
      injection h_step with h_inj
      rw [← h_inj]
      simp only [List.length_cons]
      have h_right_len_le : newRight.length ≤ cfg.right.length := by
        have h_eq : newRight = (readHead cfg.right).snd := by rw [h_r_eq]
        rw [h_eq]; exact readHead_snd_length_le cfg.right
      omega

/-- **`nSteps` total length upper bound**: multi-step generalisation —
    `n` steps from any cfg add at most `n` to total tape length.
    Companion to `nSteps_total_length_nondecreasing` (lower bound). -/
theorem nSteps_total_length_le (tm : Machine) :
    ∀ (cfg : Config) (n : Nat) (cfg' : Config),
      nSteps tm cfg n = some cfg' →
      cfg'.left.length + cfg'.right.length ≤ cfg.left.length + cfg.right.length + n := by
  intro cfg n
  induction n generalizing cfg with
  | zero =>
    intro cfg' h
    change some cfg = some cfg' at h
    injection h with h_eq
    rw [h_eq]; omega
  | succ n ih =>
    intro cfg' h
    change (match step tm cfg with
            | none => none
            | some c => nSteps tm c n) = some cfg' at h
    cases h_step : step tm cfg with
    | none => rw [h_step] at h; cases h
    | some c =>
      rw [h_step] at h
      have h_active : cfg.state ≠ 0 := by
        intro h_zero
        have h_step_none : step tm cfg = none :=
          (step_none_iff_halted tm cfg).mpr h_zero
        rw [h_step_none] at h_step
        cases h_step
      have h_one := step_total_length_le_succ tm cfg c h_active h_step
      have h_rest := ih c cfg' h
      omega

/-- Multi-step generalisation: total tape length is non-decreasing across
    any number of TM steps.  Induction on `n` using
    `step_total_length_nondecreasing`. -/
theorem nSteps_total_length_nondecreasing (tm : Machine) :
    ∀ (cfg : Config) (n : Nat) (cfg' : Config),
      nSteps tm cfg n = some cfg' →
      cfg.left.length + cfg.right.length ≤ cfg'.left.length + cfg'.right.length := by
  intro cfg n
  induction n generalizing cfg with
  | zero =>
    intro cfg' h
    change some cfg = some cfg' at h
    injection h with h_eq
    rw [h_eq]; exact Nat.le_refl _
  | succ n ih =>
    intro cfg' h
    change (match step tm cfg with
            | none => none
            | some c => nSteps tm c n) = some cfg' at h
    cases h_step : step tm cfg with
    | none => rw [h_step] at h; cases h
    | some c =>
      rw [h_step] at h
      have h_active : cfg.state ≠ 0 := by
        intro h_z
        have h_n : step tm cfg = none := (step_none_iff_halted tm cfg).mpr h_z
        rw [h_n] at h_step; cases h_step
      have h_one := step_total_length_nondecreasing tm cfg c h_active h_step
      have h_rec := ih c cfg' h
      omega

/-- **`nSteps_total_length_bounds` (iter 636)**: tight two-sided bounds
    on tape length growth — combines the lower bound (non-decreasing)
    with the upper bound (≤ +n) into a single sandwich. -/
theorem nSteps_total_length_bounds (tm : Machine)
    (cfg : Config) (n : Nat) (cfg' : Config)
    (h : nSteps tm cfg n = some cfg') :
    cfg.left.length + cfg.right.length ≤ cfg'.left.length + cfg'.right.length ∧
    cfg'.left.length + cfg'.right.length ≤ cfg.left.length + cfg.right.length + n :=
  ⟨nSteps_total_length_nondecreasing tm cfg n cfg' h,
   nSteps_total_length_le tm cfg n cfg' h⟩

/-- **No TM step preserves cfg-form**: if `step tm cfg = some cfg'`,
    the resulting cfg' differs from cfg in either `left` length or
    `right` length.  Direct re-export of `step_grows_some_side` for
    any active source. -/
theorem step_some_changes_tape_length
    (tm : Machine) (cfg cfg' : Config)
    (h_active : cfg.state ≠ 0) (h_step : step tm cfg = some cfg') :
    cfg'.right.length = cfg.right.length + 1 ∨
    cfg'.left.length = cfg.left.length + 1 :=
  step_grows_some_side tm cfg cfg' h_active h_step

/-- **`nSteps_one_changes_tape_length`**: a single nSteps changes tape
    length on either side. -/
theorem nSteps_one_changes_tape_length
    (tm : Machine) (cfg cfg' : Config)
    (h_active : cfg.state ≠ 0) (h_n : nSteps tm cfg 1 = some cfg') :
    cfg'.right.length = cfg.right.length + 1 ∨
    cfg'.left.length = cfg.left.length + 1 := by
  rw [nSteps_one] at h_n
  exact step_some_changes_tape_length tm cfg cfg' h_active h_n

/-- **`step_total_length_growth_zero_or_one` (iter 638)**: each active
    TM step changes the total tape length by exactly 0 or 1.  Tight
    bound combining `_nondecreasing` (lower) with `_le_succ` (upper). -/
theorem step_total_length_growth_zero_or_one
    (tm : Machine) (cfg cfg' : Config)
    (h_active : cfg.state ≠ 0) (h_step : step tm cfg = some cfg') :
    ∃ b, b ≤ 1 ∧ cfg'.left.length + cfg'.right.length =
      cfg.left.length + cfg.right.length + b := by
  have h_lo := step_total_length_nondecreasing tm cfg cfg' h_active h_step
  have h_hi := step_total_length_le_succ tm cfg cfg' h_active h_step
  refine ⟨cfg'.left.length + cfg'.right.length -
          (cfg.left.length + cfg.right.length), ?_, ?_⟩ <;> omega

/-- **`periodic_orbit_constant_total_length` (iter 641)**: along any
    periodic orbit, every intermediate cfg has the same total tape
    length as the source.  Sandwich argument using nondecreasing
    (lower) on `[0..k]` and on `[k..p]` (forced by `BiTM_nSteps_
    intermediate`). -/
theorem periodic_orbit_constant_total_length
    (tm : Machine) (cfg : Config) (p : Nat) (h_period : nSteps tm cfg p = some cfg)
    (k : Nat) (cfg_k : Config) (h_le : k ≤ p) (h_k : nSteps tm cfg k = some cfg_k) :
    cfg_k.left.length + cfg_k.right.length = cfg.left.length + cfg.right.length := by
  have h_lo := nSteps_total_length_nondecreasing tm cfg k cfg_k h_k
  have h_inter := BiTM_nSteps_intermediate tm cfg cfg_k cfg k p h_le h_k h_period
  have h_hi := nSteps_total_length_nondecreasing tm cfg_k (p - k) cfg h_inter
  omega

/-- **`periodic_orbit_no_strict_growth` (iter 641)**: contrapositive
    obstruction — if a TM cfg has period `p ≥ 1` AND some intermediate
    step has strictly larger total length than the source, that's a
    contradiction.  Useful for ruling out periodicity by exhibiting a
    growth point. -/
theorem periodic_orbit_no_strict_growth
    (tm : Machine) (cfg : Config) (p : Nat) (h_period : nSteps tm cfg p = some cfg)
    (k : Nat) (h_le : k ≤ p) (cfg_k : Config) (h_k : nSteps tm cfg k = some cfg_k)
    (h_growth : cfg_k.left.length + cfg_k.right.length >
                cfg.left.length + cfg.right.length) :
    False := by
  have h_const := periodic_orbit_constant_total_length tm cfg p h_period k cfg_k h_le h_k
  omega

/-- **Generic per-step → multi-step emulation lifting (iter 397)**:
    iter 395 generalized to any target `tm : Machine`.  Useful for
    intermediate systems in the Smith chain (CTS → System5 → ... →
    wolfram23): each link only needs its per-step emulation
    discharged, and this lemma yields multi-step automatically. -/
theorem step_to_nSteps_emulation_generic
    (cts : CTS) (tm : Machine) (encode : CTSConfig → Config)
    (h_emulate : ∀ ctsCfg ctsCfg',
       cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (encode ctsCfg) n = some (encode ctsCfg'))
    (ctsCfg : CTSConfig) (k : Nat) (result : CTSConfig)
    (h_steps : cts.nSteps ctsCfg k = some result) :
    ∃ m, nSteps tm (encode ctsCfg) m = some (encode result) := by
  induction k generalizing ctsCfg with
  | zero =>
    rw [CTS.nSteps_zero] at h_steps
    injection h_steps with h_eq
    refine ⟨0, ?_⟩
    rw [h_eq]
    rfl
  | succ k ih =>
    rw [CTS_nSteps_succ_unfold] at h_steps
    cases h_step : cts.step ctsCfg with
    | none => rw [h_step] at h_steps; cases h_steps
    | some cfg₁ =>
      rw [h_step] at h_steps
      obtain ⟨n, _hn_pos, h_n⟩ := h_emulate ctsCfg cfg₁ h_step
      obtain ⟨m', h_m'⟩ := ih cfg₁ h_steps
      exact ⟨n + m',
        BiTM_nSteps_some_compose tm (encode ctsCfg) (encode cfg₁)
          n m' (encode result) h_n h_m'⟩

/-- **Generic halt-preservation under step-emulation + per-cfg halt
    encoding (iter 397)**: iter 396 generalized to any target
    `tm : Machine`.  Building block for chaining halt-preservation
    along the Smith reduction tower. -/
theorem ctsHalts_imp_tmHalts_under_step_emulation_generic
    (cts : CTS) (tm : Machine) (encode : CTSConfig → Config)
    (h_step_emulate : ∀ ctsCfg ctsCfg',
       cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (encode ctsCfg) n = some (encode ctsCfg'))
    (h_halt_preserve : ∀ ctsCfg, ctsHalted ctsCfg = true → halted (encode ctsCfg) = true)
    (ctsCfg : CTSConfig) (h : cts.Halts ctsCfg) :
    Halts tm (encode ctsCfg) := by
  rw [CTS_Halts_iff_nSteps_reaches_halted] at h
  obtain ⟨k, result, h_n, h_halt⟩ := h
  obtain ⟨m, h_m⟩ := step_to_nSteps_emulation_generic
    cts tm encode h_step_emulate ctsCfg k result h_n
  rw [BiTM_Halts_iff_nSteps_reaches_halted]
  exact ⟨m, encode result, h_m, h_halt_preserve result h_halt⟩

/-- **TM-to-TM step-to-nSteps emulation lifting (iter 398)**: parallel
    of iter 395/397 for `Machine → Machine` chains.  Useful for
    composing emulations when both source and target are bi-infinite
    TMs (e.g. System1 → wolfram23 in the Smith chain). -/
theorem tm_step_to_nSteps_emulation
    (tm₁ tm₂ : Machine) (encode : Config → Config)
    (h_emulate : ∀ cfg cfg',
       step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₂ (encode cfg) n = some (encode cfg'))
    (cfg : Config) (k : Nat) (result : Config)
    (h_steps : nSteps tm₁ cfg k = some result) :
    ∃ m, nSteps tm₂ (encode cfg) m = some (encode result) := by
  induction k generalizing cfg with
  | zero =>
    simp [nSteps] at h_steps
    refine ⟨0, ?_⟩
    rw [h_steps]
    rfl
  | succ k ih =>
    rw [BiTM_nSteps_succ_unfold] at h_steps
    cases h_step : step tm₁ cfg with
    | none => rw [h_step] at h_steps; cases h_steps
    | some cfg₁ =>
      rw [h_step] at h_steps
      obtain ⟨n, _hn_pos, h_n⟩ := h_emulate cfg cfg₁ h_step
      obtain ⟨m', h_m'⟩ := ih cfg₁ h_steps
      exact ⟨n + m',
        BiTM_nSteps_some_compose tm₂ (encode cfg) (encode cfg₁)
          n m' (encode result) h_n h_m'⟩

/-- **TM-to-TM halt-preservation under step-emulation (iter 398)**:
    parallel of iter 396/397 for `Machine → Machine` chains. -/
theorem tmHalts_imp_tmHalts_under_step_emulation
    (tm₁ tm₂ : Machine) (encode : Config → Config)
    (h_step_emulate : ∀ cfg cfg',
       step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₂ (encode cfg) n = some (encode cfg'))
    (h_halt_preserve : ∀ cfg, halted cfg = true → halted (encode cfg) = true)
    (cfg : Config) (h : Halts tm₁ cfg) :
    Halts tm₂ (encode cfg) := by
  rw [BiTM_Halts_iff_nSteps_reaches_halted] at h
  obtain ⟨k, result, h_n, h_halt⟩ := h
  obtain ⟨m, h_m⟩ := tm_step_to_nSteps_emulation
    tm₁ tm₂ encode h_step_emulate cfg k result h_n
  rw [BiTM_Halts_iff_nSteps_reaches_halted]
  exact ⟨m, encode result, h_m, h_halt_preserve result h_halt⟩

/-- **Composition: halt-preservation across two TM-to-TM emulations
    (iter 399)**: chains iter 398 with itself.  Given encoders
    `enc₁ : tm₁ → tm₂` and `enc₂ : tm₂ → tm₃` each with per-step
    emulation + per-cfg halt encoding, derive halt-preservation
    `tm₁ → tm₃` via `enc₂ ∘ enc₁`.

    Useful for chaining links in the Smith reduction tower (e.g.
    System1 → wolfram23 followed by another bi-infinite link). -/
theorem tmHalts_compose_under_two_emulations
    (tm₁ tm₂ tm₃ : Machine) (enc₁ enc₂ : Config → Config)
    (h₁_step : ∀ cfg cfg', step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₂ (enc₁ cfg) n = some (enc₁ cfg'))
    (h₁_halt : ∀ cfg, halted cfg = true → halted (enc₁ cfg) = true)
    (h₂_step : ∀ cfg cfg', step tm₂ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₃ (enc₂ cfg) n = some (enc₂ cfg'))
    (h₂_halt : ∀ cfg, halted cfg = true → halted (enc₂ cfg) = true)
    (cfg : Config) (h : Halts tm₁ cfg) :
    Halts tm₃ (enc₂ (enc₁ cfg)) :=
  tmHalts_imp_tmHalts_under_step_emulation tm₂ tm₃ enc₂ h₂_step h₂_halt _
    (tmHalts_imp_tmHalts_under_step_emulation tm₁ tm₂ enc₁ h₁_step h₁_halt cfg h)

/-- **Composition: halt-preservation across CTS → tm → tm chain
    (iter 399)**: chains iter 397 + iter 398.  Given encoders
    `enc₁ : CTS → tm₁` and `enc₂ : tm₁ → tm₂` each with per-step
    emulation + per-cfg halt encoding, derive halt-preservation
    `cts.Halts cfg → tm₂.Halts (enc₂ (enc₁ cfg))`. -/
theorem ctsHalts_compose_under_two_emulations
    (cts : CTS) (tm₁ tm₂ : Machine)
    (enc₁ : CTSConfig → Config) (enc₂ : Config → Config)
    (h₁_step : ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₁ (enc₁ ctsCfg) n = some (enc₁ ctsCfg'))
    (h₁_halt : ∀ ctsCfg, ctsHalted ctsCfg = true → halted (enc₁ ctsCfg) = true)
    (h₂_step : ∀ cfg cfg', step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₂ (enc₂ cfg) n = some (enc₂ cfg'))
    (h₂_halt : ∀ cfg, halted cfg = true → halted (enc₂ cfg) = true)
    (ctsCfg : CTSConfig) (h : cts.Halts ctsCfg) :
    Halts tm₂ (enc₂ (enc₁ ctsCfg)) :=
  tmHalts_imp_tmHalts_under_step_emulation tm₁ tm₂ enc₂ h₂_step h₂_halt _
    (ctsHalts_imp_tmHalts_under_step_emulation_generic cts tm₁ enc₁
      h₁_step h₁_halt ctsCfg h)

/-- **`tm_step_to_nSteps_emulation_with_bound` (iter 726)**: refines
    iter 398's `tm_step_to_nSteps_emulation` with a uniform per-step
    budget bound `B`.  If every per-step emulation uses `n ≤ B` target
    steps, then the multi-step total is `m ≤ B * k`.  Useful for
    declaring a concrete System 5 / wolfram23 budget when the per-step
    cost is known a priori (e.g., for AllEmptyAppendants where each
    bit consumes ≤ 6 System 5 steps). -/
theorem tm_step_to_nSteps_emulation_with_bound
    (tm₁ tm₂ : Machine) (encode : Config → Config) (B : Nat)
    (h_emulate : ∀ cfg cfg',
       step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ n ≤ B ∧ nSteps tm₂ (encode cfg) n = some (encode cfg'))
    (cfg : Config) (k : Nat) (result : Config)
    (h_steps : nSteps tm₁ cfg k = some result) :
    ∃ m, nSteps tm₂ (encode cfg) m = some (encode result)
       ∧ m ≤ B * k := by
  induction k generalizing cfg with
  | zero =>
    simp [nSteps] at h_steps
    refine ⟨0, ?_, by omega⟩
    rw [h_steps]; rfl
  | succ k ih =>
    rw [BiTM_nSteps_succ_unfold] at h_steps
    cases h_step : step tm₁ cfg with
    | none => rw [h_step] at h_steps; cases h_steps
    | some cfg₁ =>
      rw [h_step] at h_steps
      obtain ⟨n, _hn_pos, h_n_le, h_n⟩ := h_emulate cfg cfg₁ h_step
      obtain ⟨m', h_m', h_m'_le⟩ := ih cfg₁ h_steps
      refine ⟨n + m',
        BiTM_nSteps_some_compose tm₂ (encode cfg) (encode cfg₁)
          n m' (encode result) h_n h_m', ?_⟩
      rw [Nat.mul_succ]
      omega

/-- **Identity self-emulation, step (iter 400)**: any TM emulates
    itself per-step with budget `n = 1` under the identity encoder.
    Building block for instantiating iter 397/398 with the identity
    encoder and as the trivial base case for emulation chains. -/
theorem tm_self_emulates_step (tm : Machine) :
    ∀ cfg cfg', step tm cfg = some cfg' →
      ∃ n, n ≥ 1 ∧ nSteps tm cfg n = some cfg' := by
  intro cfg cfg' h_step
  refine ⟨1, Nat.le_refl _, ?_⟩
  rw [BiTM_nSteps_succ_unfold, h_step]
  rfl

/-- **Identity self-emulation, halt-preserve (iter 400)**: identity
    encoder preserves halt for any TM trivially. -/
theorem tm_self_halt_preserves (_tm : Machine) :
    ∀ cfg, halted cfg = true → halted ((id : Config → Config) cfg) = true :=
  fun _ h => h

/-- **Smoke test (iter 400)**: instantiating iter 398's halt-preservation
    with the identity encoder and self-emulation gives back the trivial
    `Halts tm cfg → Halts tm cfg`.  Validates the iter 398 framework
    against its degenerate base case. -/
example (tm : Machine) (cfg : Config) (h : Halts tm cfg) : Halts tm cfg :=
  tmHalts_imp_tmHalts_under_step_emulation tm tm id
    (fun cfg cfg' => tm_self_emulates_step tm cfg cfg')
    (tm_self_halt_preserves tm) cfg h

/-- **Trivial halt-collapse encoder fails iter 397's step-emulation
    hypothesis (iter 401)**: documents that iter 397's predicate
    is genuinely stronger than the trivial `smith_reduces` halt-
    collapse closure.  Concretely: if `encode` collapses every
    CTSConfig to wolfram23's halted state-0 cfg, then for any CTS
    with a self-step (e.g. `selfLoopCTS`), the per-step hypothesis
    `∃ n ≥ 1, nSteps wolfram23 (encode cfg) n = some (encode cfg)`
    is unsatisfiable — a halted wolfram23 cfg has no successor steps
    by `step_none_iff_halted`.

    Implication: iter 397 cannot be trivially discharged via the
    halt-collapse witness, unlike `smith_reduces`. -/
theorem trivial_halt_collapse_obstructs_iter397_step_emulation :
    ¬ ∃ n, n ≥ 1 ∧ nSteps wolfram23
        ({ state := 0, left := [], head := 0, right := [] } : Config) n
      = some ({ state := 0, left := [], head := 0, right := [] } : Config) := by
  intro ⟨n, hn_pos, h_n⟩
  have h_step : step wolfram23
      ({ state := 0, left := [], head := 0, right := [] } : Config) = none :=
    (step_none_iff_halted wolfram23 _).mpr rfl
  cases n with
  | zero => omega
  | succ k =>
    rw [BiTM_nSteps_succ_unfold, h_step] at h_n
    cases h_n

/-- **Halted cfg has no step-emulation witness (iter 402)**: abstract
    generalization of iter 401.  For any TM and any state-0 cfg, the
    `∃ n ≥ 1, nSteps tm cfg n = some cfg'` predicate is unsatisfiable
    for ANY target `cfg'`.  Builds on iter 261's
    `BiTM_halted_nSteps_succ_eq_none`.

    Use: any encoding chain link that maps source-cfg to a halted
    target-cfg cannot satisfy the per-step emulation hypothesis when
    the source has any genuine step. -/
theorem halted_cfg_no_step_emulation
    (tm : Machine) (cfg cfg' : Config) (h_halt : cfg.state = 0) :
    ¬ ∃ n, n ≥ 1 ∧ nSteps tm cfg n = some cfg' := by
  intro ⟨n, hn_pos, h_n⟩
  cases n with
  | zero => omega
  | succ k =>
    have h_halt_bool : halted cfg = true := by simp [halted, h_halt]
    rw [BiTM_halted_nSteps_succ_eq_none tm cfg k h_halt_bool] at h_n
    cases h_n

/-- **Strengthened iter 398 with positive lower bound (iter 403)**:
    same as `tm_step_to_nSteps_emulation` but tracks `m ≥ 1` in the
    conclusion when the input `k ≥ 1`.  Required for composing
    per-step emulations along chains. -/
theorem tm_step_to_nSteps_emulation_pos
    (tm₁ tm₂ : Machine) (encode : Config → Config)
    (h_emulate : ∀ cfg cfg', step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₂ (encode cfg) n = some (encode cfg'))
    (cfg : Config) (k : Nat) (result : Config) (h_pos : k ≥ 1)
    (h_steps : nSteps tm₁ cfg k = some result) :
    ∃ m, m ≥ 1 ∧ nSteps tm₂ (encode cfg) m = some (encode result) := by
  cases k with
  | zero => omega
  | succ k =>
    rw [BiTM_nSteps_succ_unfold] at h_steps
    cases h_step : step tm₁ cfg with
    | none => rw [h_step] at h_steps; cases h_steps
    | some cfg₁ =>
      rw [h_step] at h_steps
      obtain ⟨n, hn_pos, h_n⟩ := h_emulate cfg cfg₁ h_step
      obtain ⟨m', h_m'⟩ := tm_step_to_nSteps_emulation
        tm₁ tm₂ encode h_emulate cfg₁ k result h_steps
      exact ⟨n + m', by omega,
        BiTM_nSteps_some_compose tm₂ (encode cfg) (encode cfg₁)
          n m' (encode result) h_n h_m'⟩

/-- **Per-step emulation composes: CTS → tm₁ → tm₂ chain (iter 403)**:
    if every CTS step is mirrored by `≥ 1` tm₁ steps and every tm₁
    step is mirrored by `≥ 1` tm₂ steps, then every CTS step is
    mirrored by `≥ 1` tm₂ steps via the composite encoder.

    Closes the per-step emulation under composition for two-link
    chains starting from CTS.  Useful for building Smith chain links
    that compose at the per-step level (rather than only at the
    halt-preservation level — iter 399). -/
theorem cts_step_emulation_compose
    (cts : CTS) (tm₁ tm₂ : Machine)
    (enc₁ : CTSConfig → Config) (enc₂ : Config → Config)
    (h₁ : ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₁ (enc₁ ctsCfg) n = some (enc₁ ctsCfg'))
    (h₂ : ∀ cfg cfg', step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₂ (enc₂ cfg) n = some (enc₂ cfg')) :
    ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₂ (enc₂ (enc₁ ctsCfg)) n = some (enc₂ (enc₁ ctsCfg')) := by
  intro ctsCfg ctsCfg' h_cts_step
  obtain ⟨k₁, hk₁_pos, h_k₁⟩ := h₁ ctsCfg ctsCfg' h_cts_step
  exact tm_step_to_nSteps_emulation_pos tm₁ tm₂ enc₂ h₂
    (enc₁ ctsCfg) k₁ (enc₁ ctsCfg') hk₁_pos h_k₁

/-- **Per-step emulation composes: tm₁ → tm₂ → tm₃ chain (iter 404)**:
    parallel of iter 403 for `Machine → Machine → Machine` chains.
    Lets per-step emulations be chained along arbitrary-length TM
    sub-chains within the Smith reduction tower.  Together with iter
    403, every per-step emulation chain (starting from CTS or from
    a TM) closes under binary composition. -/
theorem tm_step_emulation_compose
    (tm₁ tm₂ tm₃ : Machine) (enc₁ enc₂ : Config → Config)
    (h₁ : ∀ cfg cfg', step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₂ (enc₁ cfg) n = some (enc₁ cfg'))
    (h₂ : ∀ cfg cfg', step tm₂ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₃ (enc₂ cfg) n = some (enc₂ cfg')) :
    ∀ cfg cfg', step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm₃ (enc₂ (enc₁ cfg)) n = some (enc₂ (enc₁ cfg')) := by
  intro cfg cfg' h_step
  obtain ⟨k₁, hk₁_pos, h_k₁⟩ := h₁ cfg cfg' h_step
  exact tm_step_to_nSteps_emulation_pos tm₂ tm₃ enc₂ h₂
    (enc₁ cfg) k₁ (enc₁ cfg') hk₁_pos h_k₁

/-- **`tmHalts_imp_tmHalts_with_bound` (iter 728)**: refines iter 398's
    halt-preservation with a uniform per-step budget bound `B`.  If
    `tm₁` halts at step `k` and every per-step emulation uses `≤ B`
    target steps, then `tm₂` halts at step `≤ B * k`.  Composes
    iter 726's `_with_bound` with iter 419's
    `BiTM_Halts_iff_nSteps_reaches_halted`.  Quantifies the cost of
    halt preservation under bounded emulation. -/
theorem tmHalts_imp_tmHalts_with_bound
    (tm₁ tm₂ : Machine) (encode : Config → Config) (B : Nat)
    (h_step_emulate : ∀ cfg cfg',
       step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ n ≤ B ∧ nSteps tm₂ (encode cfg) n = some (encode cfg'))
    (h_halt_preserve : ∀ cfg, halted cfg = true → halted (encode cfg) = true)
    (cfg : Config) (k : Nat) (result : Config)
    (h_n : nSteps tm₁ cfg k = some result) (h_halt : halted result = true) :
    ∃ m, nSteps tm₂ (encode cfg) m = some (encode result)
       ∧ halted (encode result) = true ∧ m ≤ B * k := by
  obtain ⟨m, h_m, h_m_le⟩ := tm_step_to_nSteps_emulation_with_bound
    tm₁ tm₂ encode B h_step_emulate cfg k result h_n
  exact ⟨m, h_m, h_halt_preserve result h_halt, h_m_le⟩

/-- **`tm_step_to_nSteps_emulation_pos_with_bound` (iter 730 helper)**:
    combines iter 403's `_pos` with iter 726's `_with_bound`.  When
    `k ≥ 1`, the multi-step lift produces `m` with both `m ≥ 1` and
    `m ≤ B * k`.  Direct induction with both invariants tracked. -/
theorem tm_step_to_nSteps_emulation_pos_with_bound
    (tm₁ tm₂ : Machine) (encode : Config → Config) (B : Nat)
    (h_emulate : ∀ cfg cfg', step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ n ≤ B ∧ nSteps tm₂ (encode cfg) n = some (encode cfg'))
    (cfg : Config) (k : Nat) (result : Config) (h_pos : k ≥ 1)
    (h_steps : nSteps tm₁ cfg k = some result) :
    ∃ m, m ≥ 1 ∧ m ≤ B * k
       ∧ nSteps tm₂ (encode cfg) m = some (encode result) := by
  cases k with
  | zero => omega
  | succ k =>
    rw [BiTM_nSteps_succ_unfold] at h_steps
    cases h_step : step tm₁ cfg with
    | none => rw [h_step] at h_steps; cases h_steps
    | some cfg₁ =>
      rw [h_step] at h_steps
      obtain ⟨n, hn_pos, hn_le, h_n⟩ := h_emulate cfg cfg₁ h_step
      obtain ⟨m', h_m', h_m'_le⟩ := tm_step_to_nSteps_emulation_with_bound
        tm₁ tm₂ encode B (fun a b h => h_emulate a b h) cfg₁ k result h_steps
      refine ⟨n + m', by omega, ?_,
        BiTM_nSteps_some_compose tm₂ (encode cfg) (encode cfg₁)
          n m' (encode result) h_n h_m'⟩
      rw [Nat.mul_succ]
      omega

/-- **`tm_step_emulation_compose_with_bound` (iter 730)**: refines
    iter 404's `tm_step_emulation_compose` with bounded composition.
    If per-step `tm₁ → tm₂` budgets are `≤ B₁` and per-step `tm₂ → tm₃`
    budgets are `≤ B₂`, then the composite `tm₁ → tm₃` per-step
    emulation has budget `≤ B₁ * B₂`.  Useful for Smith-chain budget
    arithmetic when each link has a known per-step cost. -/
theorem tm_step_emulation_compose_with_bound
    (tm₁ tm₂ tm₃ : Machine) (enc₁ enc₂ : Config → Config) (B₁ B₂ : Nat)
    (h₁ : ∀ cfg cfg', step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ n ≤ B₁ ∧ nSteps tm₂ (enc₁ cfg) n = some (enc₁ cfg'))
    (h₂ : ∀ cfg cfg', step tm₂ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ n ≤ B₂ ∧ nSteps tm₃ (enc₂ cfg) n = some (enc₂ cfg')) :
    ∀ cfg cfg', step tm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ n ≤ B₁ * B₂
              ∧ nSteps tm₃ (enc₂ (enc₁ cfg)) n = some (enc₂ (enc₁ cfg')) := by
  intro cfg cfg' h_step
  obtain ⟨k₁, hk₁_pos, hk₁_le, h_k₁⟩ := h₁ cfg cfg' h_step
  obtain ⟨m, hm_pos, hm_le, h_m⟩ := tm_step_to_nSteps_emulation_pos_with_bound
    tm₂ tm₃ enc₂ B₂ h₂ (enc₁ cfg) k₁ (enc₁ cfg') hk₁_pos h_k₁
  refine ⟨m, hm_pos, ?_, h_m⟩
  calc m ≤ B₂ * k₁ := hm_le
    _ ≤ B₂ * B₁ := Nat.mul_le_mul_left B₂ hk₁_le
    _ = B₁ * B₂ := Nat.mul_comm _ _

/-- **Generic step-changes-cfg (iter 476)**: any TM step from an
    active cfg produces a different cfg.  Generalizes
    `step_wolfram23_changes_cfg` (iter ?) from wolfram23 to any
    `Machine`.  Direct via `step_grows_some_side` (private file
    helper). -/
theorem step_changes_cfg_generic (tm : Machine) (cfg cfg' : Config)
    (h_active : cfg.state ≠ 0) (h_step : step tm cfg = some cfg') :
    cfg ≠ cfg' := by
  intro h_eq
  rcases step_grows_some_side tm cfg cfg' h_active h_step with h_r | h_l
  · have : cfg.right.length = cfg.right.length + 1 := by rw [h_eq] at *; exact h_r
    omega
  · have : cfg.left.length = cfg.left.length + 1 := by rw [h_eq] at *; exact h_l
    omega

/-- **No TM has a self-step from an active cfg (iter 476)**:
    contrapositive of iter 476 — `step tm cfg = some cfg` is
    impossible for any active cfg.  Documents that BiTM TMs never
    have period-1 orbits at active states. -/
theorem no_TM_self_step_from_active (tm : Machine) (cfg : Config)
    (h_active : cfg.state ≠ 0) :
    step tm cfg ≠ some cfg := by
  intro h_step
  exact step_changes_cfg_generic tm cfg cfg h_active h_step rfl

/-- **No TM has a self-step at any cfg (iter 477)**: stronger form
    of iter 476 covering both halted and active cases.  At halted
    cfgs, `step = none ≠ some cfg`; at active cfgs, iter 476
    applies.  Direct corollary: no BiTM has any period-1 orbit. -/
theorem no_TM_self_step (tm : Machine) (cfg : Config) :
    step tm cfg ≠ some cfg := by
  by_cases h : cfg.state = 0
  · rw [(step_none_iff_halted tm cfg).mpr h]
    intro h'; cases h'
  · exact no_TM_self_step_from_active tm cfg h

/-- **No TM has a period-1 orbit (iter 477)**: equivalently, there's
    no TM cfg `cfg` with `nSteps tm cfg 1 = some cfg`. -/
theorem no_TM_period_1 (tm : Machine) (cfg : Config) :
    nSteps tm cfg 1 ≠ some cfg := by
  rw [nSteps_one]
  exact no_TM_self_step tm cfg
/-- **`nSteps` from halted cfg returns none for any positive count
    (iter 481)**: contrapositive — if `nSteps tm cfg p = some r`
    with `p ≥ 1`, then `cfg.state ≠ 0` (active source).  Direct from
    iter 7341's `BiTM_halted_nSteps_eq_none`. -/
theorem nSteps_some_imp_active_source
    (tm : Machine) (cfg : Config) (p : Nat) (h_pos : p ≥ 1) (r : Config)
    (h_n : nSteps tm cfg p = some r) :
    cfg.state ≠ 0 := by
  intro h_state
  have h_halt : halted cfg = true := by simp [halted, h_state]
  rw [BiTM_halted_nSteps_eq_none tm cfg p h_halt h_pos] at h_n
  cases h_n

/-- **Periodic source must be active (iter 482)**: if cfg is
    periodic with `nSteps tm cfg p = some cfg` for `p ≥ 1`, then
    cfg is active (state ≠ 0).  Direct from iter 481. -/
theorem periodic_source_active
    (tm : Machine) (cfg : Config) (p : Nat) (h_pos : p ≥ 1)
    (h_period : nSteps tm cfg p = some cfg) :
    cfg.state ≠ 0 :=
  nSteps_some_imp_active_source tm cfg p h_pos cfg h_period

/-- **`TM_period_ge_2` (iter 746)**: any TM period must be ≥ 2.
    Combines iter 477's `no_TM_period_1` (no period-1 orbits) with
    the `p ≥ 1` precondition.  Sharpens periodicity statements
    across the codebase (e.g. periodic-orbit witnesses must have
    period ≥ 2).  Mirrors the wolfram23-specific obstruction
    discovered in iter 479. -/
theorem TM_period_ge_2 (tm : Machine) (cfg : Config) (p : Nat)
    (h_pos : p ≥ 1) (h_period : nSteps tm cfg p = some cfg) :
    p ≥ 2 := by
  rcases Nat.eq_or_lt_of_le h_pos with h_eq | h_lt
  · exfalso
    rw [← h_eq] at h_period
    exact no_TM_period_1 tm cfg h_period
  · omega

/-- **`TM_periodic_iff_periodic_ge_2` (iter 748)**: characterisation
    of TM periodicity — having any positive period is equivalent to
    having a period `≥ 2`.  Forward via iter 746's `TM_period_ge_2`;
    backward by relaxing `2` to `1` via transitivity.  Useful for
    rewriting periodicity statements between the natural `p ≥ 1`
    form (from `nSteps`-some witnesses) and the sharper `p ≥ 2` form
    (forced by no-period-1). -/
theorem TM_periodic_iff_periodic_ge_2 (tm : Machine) (cfg : Config) :
    (∃ p, p ≥ 1 ∧ nSteps tm cfg p = some cfg)
    ↔ (∃ p, p ≥ 2 ∧ nSteps tm cfg p = some cfg) := by
  constructor
  · rintro ⟨p, h_pos, h_period⟩
    exact ⟨p, TM_period_ge_2 tm cfg p h_pos h_period, h_period⟩
  · rintro ⟨p, h_ge2, h_period⟩
    exact ⟨p, by omega, h_period⟩

/-- **`TM_periodic_imp_active_source` (iter 754)**: any periodic TM
    cfg has an active state (state ≠ 0).  Direct from
    `periodic_source_active` extracted to a positive-witness form
    (vs. the explicit `p ≥ 1` argument).  Useful when reasoning about
    periodic orbits without explicitly tracking the period. -/
theorem TM_periodic_imp_active_source
    (tm : Machine) (cfg : Config)
    (h : ∃ p, p ≥ 1 ∧ nSteps tm cfg p = some cfg) :
    cfg.state ≠ 0 := by
  obtain ⟨p, h_pos, h_period⟩ := h
  exact periodic_source_active tm cfg p h_pos h_period

end BiTM
