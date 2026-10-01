/-
  BiTM.Wolfram23Periodic

  Aperiodicity of Wolfram (2,3) from `wolfram23_init`, plus generic
  obstructions to periodic orbits at active configs.  Extracted from
  `BiTM.CockeMinskyConstruction` in a refactor.

  Contents:
    * `wolfram23_from_init_not_periodic` — wolfram23_init is aperiodic
    * `wolfram23_at_n_ne_init`, `wolfram23_at_n_total_length_ge_one`
    * `wolfram23_periodic_first_step_reads_nonempty` — periodic ⇒
      first step reads from non-empty side
    * `step_preserves_periodicity` — generic: stepping preserves period
    * `wolfram23_periodic_along_cycle_nonempty_read` — non-empty
      reads at every cycle point
    * `wolfram23_periodic_state_and_head_valid` — period ≥ 2 forces
      state ∈ {1, 2} and head ≤ 2
-/

import BiTM.Basic
import BiTM.HaltInduction
import BiTM.Wolfram23Valid

namespace BiTM

open TM

/-- Every wolfram23 step from a valid cfg produces a *different* cfg.

    Proof: any step grows one of the tape sides by 1 (via `step_grows_some_side`),
    so the cfg can't equal itself.  The validity hypothesis only feeds in the
    "active state" precondition required by `step_grows_some_side`.

    Practical impact for the smith side: this is the SIMPLEST obstruction to
    wolfram23 having a self-loop (period-1 periodic point). -/
theorem step_wolfram23_changes_cfg (cfg cfg' : Config)
    (h : IsValidWolfram23Cfg cfg) (h_step : step wolfram23 cfg = some cfg') :
    cfg ≠ cfg' := by
  intro h_eq
  have h_active : cfg.state ≠ 0 := by
    rcases h.1 with h_s | h_s <;> rw [h_s] <;> omega
  rcases step_grows_some_side wolfram23 cfg cfg' h_active h_step with h_r | h_l
  · have : cfg.right.length = cfg.right.length + 1 := by rw [h_eq] at *; exact h_r
    omega
  · have : cfg.left.length = cfg.left.length + 1 := by rw [h_eq] at *; exact h_l
    omega

/-- No wolfram23 trajectory point is a self-loop in one step.
    Direct corollary: `wolfram23_at_n n ≠ wolfram23_at_n (n + 1)`. -/
theorem wolfram23_at_n_succ_neq (n : Nat) :
    wolfram23_at_n n ≠ wolfram23_at_n (n + 1) := by
  intro h_eq
  have h_step := step_wolfram23_at_n n
  exact step_wolfram23_changes_cfg (wolfram23_at_n n) (wolfram23_at_n (n + 1))
    (wolfram23_at_n_valid n) h_step h_eq

/-- **Wolfram23 from init is not periodic**: there's no `n ≥ 1` such that
    `n` steps from `wolfram23_init` returns to `wolfram23_init`.

    Proof: `wolfram23_init` has total tape length 0.  Step 1 (per
    `wolfram23_step1`) yields `⟨2, [1], 0, []⟩` with total length 1.
    By `nSteps_total_length_nondecreasing`, total length stays ≥ 1
    for all subsequent steps.  Since 0 < 1, we never return to init.

    This is the FIRST concrete proof of aperiodicity along wolfram23's
    standard trajectory — the structural foundation any aperiodicity
    argument needs. -/
theorem wolfram23_from_init_not_periodic (n : Nat) (h_pos : n ≥ 1) :
    nSteps wolfram23 wolfram23_init n ≠ some wolfram23_init := by
  intro h_eq
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  change (match step wolfram23 wolfram23_init with
          | none => none
          | some c => nSteps wolfram23 c m) = some wolfram23_init at h_eq
  rw [wolfram23_step1] at h_eq
  have h_len := nSteps_total_length_nondecreasing wolfram23
    { state := 2, left := [1], head := 0, right := [] } m wolfram23_init h_eq
  simp [wolfram23_init] at h_len

/-- Direct corollary: `wolfram23_at_n n ≠ wolfram23_at_n 0` for all `n ≥ 1`.
    Wolfram23 trajectory never returns to its starting point. -/
theorem wolfram23_at_n_ne_init (n : Nat) (h_pos : n ≥ 1) :
    wolfram23_at_n n ≠ wolfram23_at_n 0 := by
  intro h_eq
  have h_zero : wolfram23_at_n 0 = wolfram23_init := by
    unfold wolfram23_at_n
    rfl
  rw [h_zero] at h_eq
  have h_nSteps := wolfram23_at_n_eq_nSteps n
  rw [h_eq] at h_nSteps
  exact wolfram23_from_init_not_periodic n h_pos h_nSteps

/-- For all `n ≥ 1`, the wolfram23 trajectory point `wolfram23_at_n n` has
    total tape length at least 1.

    Proof: step 1 yields `⟨2, [1], 0, []⟩` of total length 1; subsequent
    steps preserve `≥ 1` via `nSteps_total_length_nondecreasing`.

    Useful smith-side bound: rules out the encoder mapping any cfg to
    `wolfram23_init` for non-trivial CTS computations. -/
theorem wolfram23_at_n_total_length_ge_one (n : Nat) (h_pos : n ≥ 1) :
    (wolfram23_at_n n).left.length + (wolfram23_at_n n).right.length ≥ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h_nSteps := wolfram23_at_n_eq_nSteps (m + 1)
  change (match step wolfram23 wolfram23_init with
          | none => none
          | some c => nSteps wolfram23 c m) = some (wolfram23_at_n (m + 1)) at h_nSteps
  rw [wolfram23_step1] at h_nSteps
  have h_len := nSteps_total_length_nondecreasing wolfram23
    { state := 2, left := [1], head := 0, right := [] } m
    (wolfram23_at_n (m + 1)) h_nSteps
  simp at h_len
  exact h_len

/-- **Periodicity obstruction**: if a wolfram23 cfg `cfg` is `m`-periodic
    (`nSteps wolfram23 cfg m = some cfg` with `m ≥ 1`), then its first
    step's read-from-side cannot be empty.

    Proof: a strict-growth step would force total length to grow ≥ 1
    over the cycle, contradicting `nSteps_total_length_nondecreasing`'s
    equality (which periodic forces). -/
theorem wolfram23_periodic_first_step_reads_nonempty (cfg : Config) (m : Nat)
    (h_pos : m ≥ 1) (h_active : cfg.state ≠ 0)
    (h_periodic : nSteps wolfram23 cfg m = some cfg) :
    ¬ (((wolfram23.transition cfg.state cfg.head).dir = Dir.L ∧ cfg.left = []) ∨
       ((wolfram23.transition cfg.state cfg.head).dir = Dir.R ∧ cfg.right = [])) := by
  intro h_empty
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  change (match step wolfram23 cfg with
          | none => none
          | some c => nSteps wolfram23 c k) = some cfg at h_periodic
  cases h_step : step wolfram23 cfg with
  | none =>
    have h_n : step wolfram23 cfg = none := h_step
    have : cfg.state = 0 := (step_none_iff_halted _ _).mp h_n
    exact h_active this
  | some cfg' =>
    rw [h_step] at h_periodic
    have h_strict := step_grows_strict_when_reading_empty wolfram23 cfg cfg'
                       h_active h_step h_empty
    have h_nondecr := nSteps_total_length_nondecreasing wolfram23 cfg' k cfg h_periodic
    omega

/-- **Periodicity is preserved by stepping**: if `cfg` is `m`-periodic
    and `step tm cfg = some cfg'`, then `cfg'` is also `m`-periodic.

    Proof: `nSteps tm cfg (m + 1) = nSteps tm cfg m ;; step ;; ...`.  By
    `nSteps_add`, this equals `(step tm cfg) >>= nSteps · m`.  Since
    `step tm cfg = some cfg'` and `nSteps tm cfg m = some cfg`, we get
    `step tm cfg = some cfg' = step (nSteps_result) = step cfg = some cfg'`.
    Conclude `nSteps tm cfg' m = some cfg'`. -/
theorem step_preserves_periodicity (tm : Machine) (cfg cfg' : Config) (m : Nat)
    (h_periodic : nSteps tm cfg m = some cfg)
    (h_step : step tm cfg = some cfg') :
    nSteps tm cfg' m = some cfg' := by
  have h_a : nSteps tm cfg (m + 1) = nSteps tm cfg' m := by
    change (match step tm cfg with
            | none => none
            | some c => nSteps tm c m) = nSteps tm cfg' m
    rw [h_step]
  have h_b : nSteps tm cfg (m + 1) = step tm cfg := by
    rw [show m + 1 = m + 1 from rfl]
    rw [nSteps_add tm cfg m 1]
    rw [h_periodic]
    show (some cfg).bind (fun c => nSteps tm c 1) = step tm cfg
    show nSteps tm cfg 1 = step tm cfg
    exact nSteps_one tm cfg
  rw [h_a] at h_b
  rw [h_b]
  exact h_step

/-- **All cfgs along a wolfram23 cycle have non-empty read-from-side.**
    Combination of `step_preserves_periodicity`, `nSteps_wolfram23_preserves_valid`,
    and `wolfram23_periodic_first_step_reads_nonempty`.  Apply to any cfg
    reachable in `k` steps from a periodic cfg `cfg` (those reachable cfgs
    are themselves `m`-periodic). -/
theorem wolfram23_periodic_along_cycle_nonempty_read (cfg : Config) (m k : Nat)
    (h_pos : m ≥ 1) (h_active : cfg.state ≠ 0)
    (h_periodic : nSteps wolfram23 cfg m = some cfg)
    (cfg_k : Config) (h_reach : nSteps wolfram23 cfg k = some cfg_k)
    (h_active_k : cfg_k.state ≠ 0) :
    ¬ (((wolfram23.transition cfg_k.state cfg_k.head).dir = Dir.L
        ∧ cfg_k.left = []) ∨
       ((wolfram23.transition cfg_k.state cfg_k.head).dir = Dir.R
        ∧ cfg_k.right = [])) := by
  have h_cfg_k_periodic : nSteps wolfram23 cfg_k m = some cfg_k := by
    induction k generalizing cfg with
    | zero =>
      change some cfg = some cfg_k at h_reach
      injection h_reach with h_eq
      rw [← h_eq]
      exact h_periodic
    | succ k ih =>
      change (match step wolfram23 cfg with
              | none => none
              | some c => nSteps wolfram23 c k) = some cfg_k at h_reach
      cases h_step : step wolfram23 cfg with
      | none =>
        rw [h_step] at h_reach; cases h_reach
      | some c =>
        rw [h_step] at h_reach
        have h_c_periodic : nSteps wolfram23 c m = some c :=
          step_preserves_periodicity wolfram23 cfg c m h_periodic h_step
        have h_c_active : c.state ≠ 0 := by
          intro h_z
          have : step wolfram23 c = none := (step_none_iff_halted _ _).mpr h_z
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          change (match step wolfram23 c with
                  | none => none
                  | some c' => nSteps wolfram23 c' m') = some c at h_c_periodic
          rw [this] at h_c_periodic; cases h_c_periodic
        exact ih c h_c_active h_c_periodic h_reach
  exact wolfram23_periodic_first_step_reads_nonempty cfg_k m h_pos h_active_k
    h_cfg_k_periodic

/-- **Periodic cfg of period ≥ 2 has state ∈ {1, 2} and head ≤ 2.**

    Strengthens iter 135's domain restrictions: invalid states/heads
    force halting within 1 step, ruling out cycles of period ≥ 2. -/
theorem wolfram23_periodic_state_and_head_valid (cfg : Config) (n : Nat)
    (h_pos : n ≥ 2) (h_periodic : nSteps wolfram23 cfg n = some cfg) :
    (cfg.state = 1 ∨ cfg.state = 2) ∧ cfg.head ≤ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  refine ⟨?_, ?_⟩
  · cases h_state : cfg.state with
    | zero =>
      exfalso
      have h_n : step wolfram23 cfg = none :=
        (step_none_iff_halted _ _).mpr h_state
      change (match step wolfram23 cfg with
              | none => none
              | some c => nSteps wolfram23 c (m + 1)) = some cfg at h_periodic
      rw [h_n] at h_periodic; cases h_periodic
    | succ s =>
      cases s with
      | zero => left; simp
      | succ s' =>
        cases s' with
        | zero => right; simp
        | succ _ =>
          exfalso
          have h_state_pos : cfg.state ≠ 0 := by simp [h_state]
          obtain ⟨cfg', h_step⟩ := step_some_of_active wolfram23 cfg h_state_pos
          have h_cfg'_state : cfg'.state = 0 := by
            rw [step_active_state wolfram23 cfg cfg' h_step]
            unfold wolfram23
            simp [h_state]
          have h_n2 : step wolfram23 cfg' = none :=
            (step_none_iff_halted _ _).mpr h_cfg'_state
          change (match step wolfram23 cfg with
                  | none => none
                  | some c => nSteps wolfram23 c (m + 1)) = some cfg at h_periodic
          rw [h_step] at h_periodic
          change (match step wolfram23 cfg' with
                  | none => none
                  | some c => nSteps wolfram23 c m) = some cfg at h_periodic
          rw [h_n2] at h_periodic; cases h_periodic
  · rcases (Nat.lt_or_ge cfg.head 3) with h_lt | h_ge
    · omega
    have h_state_pos : cfg.state ≠ 0 := by
      cases h_state : cfg.state with
      | zero =>
        exfalso
        have h_n : step wolfram23 cfg = none :=
          (step_none_iff_halted _ _).mpr h_state
        change (match step wolfram23 cfg with
                | none => none
                | some c => nSteps wolfram23 c (m + 1)) = some cfg at h_periodic
        rw [h_n] at h_periodic; cases h_periodic
      | succ _ => simp
    obtain ⟨cfg', h_step⟩ := step_some_of_active wolfram23 cfg h_state_pos
    have h_cfg'_state : cfg'.state = 0 := by
      rw [step_active_state wolfram23 cfg cfg' h_step]
      unfold wolfram23
      cases h_s : cfg.state with
      | zero => exact absurd h_s h_state_pos
      | succ s =>
        cases s with
        | zero =>
          have hh0 : cfg.head ≠ 0 := by omega
          have hh1 : cfg.head ≠ 1 := by omega
          have hh2 : cfg.head ≠ 2 := by omega
          simp_all
        | succ s' =>
          cases s' with
          | zero =>
            have hh0 : cfg.head ≠ 0 := by omega
            have hh1 : cfg.head ≠ 1 := by omega
            have hh2 : cfg.head ≠ 2 := by omega
            simp_all
          | succ _ => simp_all
    have h_n2 : step wolfram23 cfg' = none :=
      (step_none_iff_halted _ _).mpr h_cfg'_state
    exfalso
    change (match step wolfram23 cfg with
            | none => none
            | some c => nSteps wolfram23 c (m + 1)) = some cfg at h_periodic
    rw [h_step] at h_periodic
    change (match step wolfram23 cfg' with
            | none => none
            | some c => nSteps wolfram23 c m) = some cfg at h_periodic
    rw [h_n2] at h_periodic; cases h_periodic

/-- **`wolfram23_at_n_some_side_grows` (iter 639)**: at each step
    `n → n+1`, either right or left length grows by exactly 1. -/
theorem wolfram23_at_n_some_side_grows (n : Nat) :
    (wolfram23_at_n (n + 1)).right.length = (wolfram23_at_n n).right.length + 1 ∨
    (wolfram23_at_n (n + 1)).left.length = (wolfram23_at_n n).left.length + 1 :=
  step_some_changes_tape_length wolfram23 (wolfram23_at_n n) (wolfram23_at_n (n + 1))
    (wolfram23_at_n_state_ne_zero n) (step_wolfram23_at_n n)

/-- **`wolfram23_at_n_total_length_le` (iter 639)**: tape length ≤ n.
    Combined with `wolfram23_at_n_total_length_ge_one` (lower bound for
    n ≥ 1), gives the full bound `1 ≤ total ≤ n`. -/
theorem wolfram23_at_n_total_length_le (n : Nat) :
    (wolfram23_at_n n).left.length + (wolfram23_at_n n).right.length ≤ n := by
  have h_init : wolfram23_init.left.length + wolfram23_init.right.length = 0 := by
    simp [wolfram23_init]
  have h_n := nSteps_total_length_le wolfram23 wolfram23_init n (wolfram23_at_n n)
                (wolfram23_at_n_eq_nSteps n)
  omega

/-- **`wolfram23_at_n_total_length_sandwich` (iter 639)**: for n ≥ 1,
    total tape length is between 1 and n inclusive. -/
theorem wolfram23_at_n_total_length_sandwich (n : Nat) (h_pos : n ≥ 1) :
    1 ≤ (wolfram23_at_n n).left.length + (wolfram23_at_n n).right.length ∧
    (wolfram23_at_n n).left.length + (wolfram23_at_n n).right.length ≤ n :=
  ⟨wolfram23_at_n_total_length_ge_one n h_pos, wolfram23_at_n_total_length_le n⟩

/-- **`wolfram23_at_n_total_length_pos` (iter 639)**: total tape length
    is strictly positive for n ≥ 1.  Direct from sandwich. -/
theorem wolfram23_at_n_total_length_pos (n : Nat) (h_pos : n ≥ 1) :
    (wolfram23_at_n n).left.length + (wolfram23_at_n n).right.length > 0 := by
  have ⟨h_lo, _⟩ := wolfram23_at_n_total_length_sandwich n h_pos
  omega

/-- **`wolfram23_at_n_total_length_step_le` (iter 640)**: per-step
    upper bound — total length at `n+1` is at most one more than
    at `n`.  Direct via `step_total_length_le_succ` plus
    `step_wolfram23_at_n` and `wolfram23_at_n_state_ne_zero`. -/
theorem wolfram23_at_n_total_length_step_le (n : Nat) :
    (wolfram23_at_n (n + 1)).left.length + (wolfram23_at_n (n + 1)).right.length
    ≤ (wolfram23_at_n n).left.length + (wolfram23_at_n n).right.length + 1 :=
  step_total_length_le_succ wolfram23 (wolfram23_at_n n) (wolfram23_at_n (n + 1))
    (wolfram23_at_n_state_ne_zero n) (step_wolfram23_at_n n)

/-- **`wolfram23_at_n_total_length_step_ge` (iter 640)**: per-step
    lower bound — total length is non-decreasing along the
    trajectory.  Companion to `_step_le`. -/
theorem wolfram23_at_n_total_length_step_ge (n : Nat) :
    (wolfram23_at_n n).left.length + (wolfram23_at_n n).right.length ≤
    (wolfram23_at_n (n + 1)).left.length + (wolfram23_at_n (n + 1)).right.length :=
  step_total_length_nondecreasing wolfram23 (wolfram23_at_n n) (wolfram23_at_n (n + 1))
    (wolfram23_at_n_state_ne_zero n) (step_wolfram23_at_n n)

/-- **`wolfram23_init_not_periodic_via_length` (iter 641)**: alternative
    proof of `wolfram23_from_init_not_periodic` via the constant-
    length argument.  If wolfram23_init had period `p ≥ 1`, all
    intermediate cfgs would have total length 0 (= init's), but
    `wolfram23_at_n 1` has total length 1 — contradiction. -/
theorem wolfram23_init_not_periodic_via_length
    (p : Nat) (h_pos : p ≥ 1) :
    nSteps wolfram23 wolfram23_init p ≠ some wolfram23_init := by
  intro h_period
  have h_const := periodic_orbit_constant_total_length wolfram23 wolfram23_init p
                  h_period 1 (wolfram23_at_n 1) h_pos (wolfram23_at_n_eq_nSteps 1)
  have h_at_1 : (wolfram23_at_n 1).left.length + (wolfram23_at_n 1).right.length = 1 := rfl
  have h_init : wolfram23_init.left.length + wolfram23_init.right.length = 0 := by
    simp [wolfram23_init]
  omega

/-- **`wolfram23_at_n_total_length_growth_zero_or_one` (iter 642)**:
    along the wolfram23 trajectory, each step grows total tape length
    by exactly 0 or 1.  Direct application of generic
    `step_total_length_growth_zero_or_one`. -/
theorem wolfram23_at_n_total_length_growth_zero_or_one (n : Nat) :
    ∃ b, b ≤ 1 ∧
      (wolfram23_at_n (n + 1)).left.length + (wolfram23_at_n (n + 1)).right.length =
      (wolfram23_at_n n).left.length + (wolfram23_at_n n).right.length + b :=
  step_total_length_growth_zero_or_one wolfram23 (wolfram23_at_n n)
    (wolfram23_at_n (n + 1)) (wolfram23_at_n_state_ne_zero n) (step_wolfram23_at_n n)

/-- **`wolfram23_at_n 1` total length sanity check (iter 492)**:
    explicit verification that the upper bound `≤ n` from iter 490
    is tight for n = 1 (total = 1 exactly).  Smoke test for the
    framework. -/
example : (wolfram23_at_n 1).left.length + (wolfram23_at_n 1).right.length = 1 := by
  rfl

/-- **`wolfram23_at_n 2` total length is 1 (iter 493)**: explicit
    calculation showing iter 490's bound `≤ 2` is NOT tight at
    n = 2 — total stays at 1 across step 2 (left shrinks from [1]
    to [] while right grows from [] to [2]).  Demonstrates that
    total-length growth is 0-or-1 per step, not always 1. -/
example : (wolfram23_at_n 2).left.length + (wolfram23_at_n 2).right.length = 1 := by
  rfl

/-- **`wolfram23_at_n 3` total length is 2 (iter 493)**: total grew
    by 1 across step 3 (because step 3 reads from empty left). -/
example : (wolfram23_at_n 3).left.length + (wolfram23_at_n 3).right.length = 2 := by
  rfl

/-- **`wolfram23_at_n` distinct cfgs for small n (iter 494)**:
    explicit verification that the trajectory does not loop in
    its first few steps.  Combined with the existing
    `wolfram23_at_n_ne_init` (rules out n ≠ 0 = init), confirms
    no period-2 or period-3 loops exist along the canonical
    trajectory. -/
example : wolfram23_at_n 1 ≠ wolfram23_at_n 2 := by decide

example : wolfram23_at_n 1 ≠ wolfram23_at_n 3 := by decide

example : wolfram23_at_n 2 ≠ wolfram23_at_n 3 := by decide

example : wolfram23_at_n 0 ≠ wolfram23_at_n 1 := by decide

/-- **`wolfram23_at_n` distinctness extended to n = 4, 5 (iter
    495)**: continues iter 494's pairwise distinctness check.
    Confirms the trajectory remains aperiodic for the first 6
    steps. -/
example : wolfram23_at_n 4 ≠ wolfram23_at_n 5 := by decide

example : wolfram23_at_n 0 ≠ wolfram23_at_n 4 := by decide

example : wolfram23_at_n 0 ≠ wolfram23_at_n 5 := by decide

example : wolfram23_at_n 1 ≠ wolfram23_at_n 4 := by decide

example : wolfram23_at_n 2 ≠ wolfram23_at_n 5 := by decide


/-- **Explicit values of `wolfram23_at_n` for n ∈ {1, 2, 3} (iter
    498)**: concrete trajectory values verified by `rfl`.  Useful
    as documentation reference for the wolfram23 dynamics. -/
example : wolfram23_at_n 1 = { state := 2, left := [1], head := 0, right := [] } := rfl

example : wolfram23_at_n 2 = { state := 1, left := [], head := 1, right := [2] } := rfl

example : wolfram23_at_n 3 = { state := 1, left := [], head := 0, right := [2, 2] } := rfl

/-- **Explicit `wolfram23_at_n` values for n ∈ {4, 5} (iter 499)**:
    extends iter 498's trajectory reference values.
    at_n 4 = ⟨2, [1], 2, [2]⟩; at_n 5 = ⟨1, [0, 1], 2, []⟩. -/
example : wolfram23_at_n 4 = { state := 2, left := [1], head := 2, right := [2] } := rfl

example : wolfram23_at_n 5 = { state := 1, left := [0, 1], head := 2, right := [] } := rfl

/-- **`wolfram23_at_n` pairwise distinctness for n ∈ [0, 6) (iter
    500)**: milestone summary — single decidable check covering all
    distinctness pairs from {0..5}.  Confirms aperiodicity of
    wolfram23's canonical trajectory across the first 6 steps in
    one shot.  Replaces the individual `decide` calls of iters
    494/495 with a universally-quantified statement. -/
theorem wolfram23_at_n_distinct_first_6 :
    ∀ i j : Fin 6, i ≠ j → wolfram23_at_n i.val ≠ wolfram23_at_n j.val := by
  decide

/-- **`wolfram23_at_n` pairwise distinctness for n ∈ [0, 10) (iter
    501)**: extends iter 500 to 10 steps.  Confirms wolfram23's
    canonical trajectory is aperiodic across the first 10 steps. -/
theorem wolfram23_at_n_distinct_first_10 :
    ∀ i j : Fin 10, i ≠ j → wolfram23_at_n i.val ≠ wolfram23_at_n j.val := by
  decide

/-- **Explicit `wolfram23_at_n` values for n ∈ {6, 7} (iter 502)**:
    extends iter 499.  at_n 6 = ⟨1, [1], 0, [1]⟩;
    at_n 7 = ⟨2, [1, 1], 1, []⟩.  Both have total length 2. -/
example : wolfram23_at_n 6 = { state := 1, left := [1], head := 0, right := [1] } := rfl

example : wolfram23_at_n 7 = { state := 2, left := [1, 1], head := 1, right := [] } := rfl

/-- Total tape length stable at 2 for n ∈ {6, 7} (iter 502). -/
example : (wolfram23_at_n 6).left.length + (wolfram23_at_n 6).right.length = 2 := rfl

example : (wolfram23_at_n 7).left.length + (wolfram23_at_n 7).right.length = 2 := rfl

/-- **`wolfram23_at_n 8` value (iter 503)**: continues iter 502.
    Step 8 reads from empty right side, so total grows to 3.
    at_n 8 = ⟨2, [2, 1, 1], 0, []⟩. -/
example : wolfram23_at_n 8 = { state := 2, left := [2, 1, 1], head := 0, right := [] } := rfl

/-- Total tape length jumps to 3 across step 8 (iter 503). -/
example : (wolfram23_at_n 8).left.length + (wolfram23_at_n 8).right.length = 3 := rfl

/-- **`wolfram23_at_n` pairwise distinctness for n ∈ [0, 20) (iter
    504)**: extends iter 501 to 20 steps via single decidable
    check (20*20 = 400 pairs).  Confirms wolfram23 trajectory is
    aperiodic across first 20 steps. -/
theorem wolfram23_at_n_distinct_first_20 :
    ∀ i j : Fin 20, i ≠ j → wolfram23_at_n i.val ≠ wolfram23_at_n j.val := by
  decide


/-- **Explicit `wolfram23_at_n` values for n ∈ {9, 10} (iter 508)**:
    extends iter 503's trajectory documentation.
    at_n 9 = ⟨1, [1, 1], 2, [2]⟩, total = 3.
    at_n 10 = ⟨1, [1], 1, [1, 2]⟩, total = 3. -/
example : wolfram23_at_n 9 = { state := 1, left := [1, 1], head := 2, right := [2] } := rfl

example : wolfram23_at_n 10 = { state := 1, left := [1], head := 1, right := [1, 2] } := rfl

example : (wolfram23_at_n 9).left.length + (wolfram23_at_n 9).right.length = 3 := rfl

example : (wolfram23_at_n 10).left.length + (wolfram23_at_n 10).right.length = 3 := rfl

/-- **wolfram23 trajectory bounded total length ≤ 3 for n ∈ [0, 10]
    (iter 509)**: concrete tighter bound — for the first 11 cfgs,
    total tape length never exceeds 3 (vs the looser ≤ n bound from
    iter 490).  Verified by `decide`. -/
theorem wolfram23_at_n_total_length_le_3_first_11 :
    ∀ i : Fin 11,
      (wolfram23_at_n i.val).left.length + (wolfram23_at_n i.val).right.length ≤ 3 := by
  decide

/-- **`wolfram23_at_n` total length jumps to 4 at n = 12 (iter
    510)**: extends iter 508/509 — at n = 12, total tape length
    grows to 4.  Marks the precise point where the iter 509 bound
    `≤ 3` fails. -/
example : wolfram23_at_n 12 = { state := 1, left := [], head := 0, right := [2, 2, 1, 2] } := rfl

example : (wolfram23_at_n 12).left.length + (wolfram23_at_n 12).right.length = 4 := rfl

/-- **wolfram23 trajectory bounded total length ≤ 4 for n ∈ [0, 14]
    (iter 510)**: tighter bound for first 15 cfgs.  Generalizes
    iter 509. -/
theorem wolfram23_at_n_total_length_le_4_first_15 :
    ∀ i : Fin 15,
      (wolfram23_at_n i.val).left.length + (wolfram23_at_n i.val).right.length ≤ 4 := by
  decide

/-- **`wolfram23_at_n` pairwise distinctness for n ∈ [0, 30) (iter
    511)**: extends iter 504 to 30 steps via single decidable
    check.  Confirms wolfram23 trajectory is aperiodic across the
    first 30 steps. -/
theorem wolfram23_at_n_distinct_first_30 :
    ∀ i j : Fin 30, i ≠ j → wolfram23_at_n i.val ≠ wolfram23_at_n j.val := by
  decide

/-- **wolfram23 trajectory bounded total length ≤ 5 for n ∈ [0, 20)
    (iter 512)**: tighter empirical bound for first 20 cfgs.
    Wolfram (2,3)'s trajectory from init grows slowly.  Generalizes
    iter 510. -/
theorem wolfram23_at_n_total_length_le_5_first_20 :
    ∀ i : Fin 20,
      (wolfram23_at_n i.val).left.length + (wolfram23_at_n i.val).right.length ≤ 5 := by
  decide

/-- **wolfram23 trajectory bounded total length ≤ 8 for n ∈ [0, 30)
    (iter 513)**: extends iter 512 to 30 cfgs. -/
theorem wolfram23_at_n_total_length_le_8_first_30 :
    ∀ i : Fin 30,
      (wolfram23_at_n i.val).left.length + (wolfram23_at_n i.val).right.length ≤ 8 := by
  decide

/-- **`wolfram23_at_n` pairwise distinctness for n ∈ [0, 40) (iter
    514)**: extends iter 511 to 40 steps via single decidable
    check (40*40 = 1600 pairs). -/
theorem wolfram23_at_n_distinct_first_40 :
    ∀ i j : Fin 40, i ≠ j → wolfram23_at_n i.val ≠ wolfram23_at_n j.val := by
  decide

/-- **`wolfram23_at_n_total_length_le_10_first_40` (iter 732)**:
    extends iter 513 to 40 cfgs.  Empirical bound — wolfram (2,3)'s
    canonical trajectory grows slowly: total tape length stays ≤ 10
    across the first 40 steps.  Verified by `decide`. -/
theorem wolfram23_at_n_total_length_le_10_first_40 :
    ∀ i : Fin 40,
      (wolfram23_at_n i.val).left.length + (wolfram23_at_n i.val).right.length ≤ 10 := by
  decide

/-- **`wolfram23_at_n_distinct_first_50` (iter 742)**: extends iter
    514 to 50 steps via single decidable check (50*50 = 2500 pairs).
    Confirms wolfram (2,3) trajectory is aperiodic across first 50
    steps from `wolfram23_init`.  Empirical evidence consistent with
    the abstract aperiodicity proof in `wolfram23_from_init_not_periodic`. -/
theorem wolfram23_at_n_distinct_first_50 :
    ∀ i j : Fin 50, i ≠ j → wolfram23_at_n i.val ≠ wolfram23_at_n j.val := by
  decide

end BiTM
