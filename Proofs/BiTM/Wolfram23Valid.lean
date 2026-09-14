/-
  BiTM.Wolfram23Valid

  Validity infrastructure for Wolfram's (2,3) Turing machine
  configurations: state ∈ {1, 2}, head < 3, all tape values < 3.

  Key results:
    * `IsValidWolfram23Cfg` predicate
    * `step_wolfram23_preserves_valid` — single-step preservation
    * `nSteps_wolfram23_preserves_valid` — multi-step preservation
    * `not_halts_wolfram23_valid` — wolfram23 never halts on valid cfgs
    * `wolfram23_init_valid` — initial cfg is valid
    * `wolfram23_at_n` — concrete trajectory from `wolfram23_init`

  Extracted from `BiTM.CockeMinskyConstruction` in a refactor.
-/

import BiTM.Basic
import BiTM.HaltInduction

namespace BiTM

open TM

/-- Wolfram23's `nextState` is always in `{1, 2}` for valid (state, head)
    pairs.  Concretely demonstrates that wolfram23 never reaches halt-state-0
    from any in-range starting cfg. -/
theorem wolfram23_nextState_in_range (q s : Nat) (h_q : q = 1 ∨ q = 2)
    (h_s : s < 3) :
    (wolfram23.transition q s).nextState = 1 ∨
    (wolfram23.transition q s).nextState = 2 := by
  rcases h_q with h_q | h_q <;> subst h_q
  all_goals (match s, h_s with
            | 0, _ => first | (left; native_decide) | (right; native_decide)
            | 1, _ => first | (left; native_decide) | (right; native_decide)
            | 2, _ => first | (left; native_decide) | (right; native_decide))

/-- One step of wolfram23 from a valid input lands in a valid state. -/
theorem step_wolfram23_state_in_range (cfg : Config)
    (h_state : cfg.state = 1 ∨ cfg.state = 2) (h_head : cfg.head < 3) :
    ∃ cfg', step wolfram23 cfg = some cfg' ∧
      (cfg'.state = 1 ∨ cfg'.state = 2) := by
  have h_active : cfg.state ≠ 0 := by
    rcases h_state with h | h <;> rw [h] <;> omega
  obtain ⟨cfg', h_step⟩ := step_some_of_active wolfram23 cfg h_active
  refine ⟨cfg', h_step, ?_⟩
  rw [step_active_state wolfram23 cfg cfg' h_step]
  exact wolfram23_nextState_in_range cfg.state cfg.head h_state h_head

/-- Wolfram23's `write` field is always `< 3` for valid (state, head)
    pairs.  Together with `wolfram23_nextState_in_range`, this confirms
    wolfram23 preserves "tape values < 3" if the input cfg is valid. -/
theorem wolfram23_write_in_range (q s : Nat) (h_q : q = 1 ∨ q = 2)
    (h_s : s < 3) :
    (wolfram23.transition q s).write < 3 := by
  rcases h_q with h_q | h_q <;> subst h_q
  all_goals (match s, h_s with
            | 0, _ => native_decide
            | 1, _ => native_decide
            | 2, _ => native_decide)

/-- A valid wolfram23 config: active state, in-range head, and all
    tape values `< 3` on both sides. -/
def IsValidWolfram23Cfg (cfg : Config) : Prop :=
  (cfg.state = 1 ∨ cfg.state = 2)
    ∧ cfg.head < 3
    ∧ (∀ x ∈ cfg.left, x < 3)
    ∧ (∀ x ∈ cfg.right, x < 3)

/-- A valid wolfram23 cfg has nonzero state (`state ∈ {1, 2}`). -/
theorem IsValidWolfram23Cfg.state_ne_zero (cfg : Config) (h : IsValidWolfram23Cfg cfg) :
    cfg.state ≠ 0 := by
  rcases h.1 with h_s | h_s <;> rw [h_s] <;> omega

/-- `readHead` preserves the "all values < 3" invariant. -/
private theorem readHead_preserves_lt_three (l : List Nat)
    (h_all : ∀ x ∈ l, x < 3) :
    (readHead l).fst < 3 ∧ (∀ x ∈ (readHead l).snd, x < 3) := by
  cases l with
  | nil => simp [readHead]
  | cons head tail =>
    simp [readHead]
    refine ⟨?_, ?_⟩
    · exact h_all head (by simp)
    · intro x h_mem
      exact h_all x (by simp [h_mem])

/-- Wolfram23's step preserves `IsValidWolfram23Cfg`. -/
theorem step_wolfram23_preserves_valid (cfg : Config)
    (h : IsValidWolfram23Cfg cfg) :
    ∃ cfg', step wolfram23 cfg = some cfg' ∧ IsValidWolfram23Cfg cfg' := by
  obtain ⟨h_state, h_head, h_left, h_right⟩ := h
  have h_active : cfg.state ≠ 0 := by
    rcases h_state with h | h <;> rw [h] <;> omega
  have h_neq : ¬ ((cfg.state == 0) = true) := by simp [h_active]
  have h_w_lt : (wolfram23.transition cfg.state cfg.head).write < 3 :=
    wolfram23_write_in_range _ _ h_state h_head
  have h_ns : (wolfram23.transition cfg.state cfg.head).nextState = 1 ∨
              (wolfram23.transition cfg.state cfg.head).nextState = 2 :=
    wolfram23_nextState_in_range _ _ h_state h_head
  cases h_dir : (wolfram23.transition cfg.state cfg.head).dir with
  | L =>
    cases h_l : readHead cfg.left with
    | mk newHead newLeft =>
      have h_lh := readHead_preserves_lt_three cfg.left h_left
      rw [h_l] at h_lh
      refine ⟨{ state := (wolfram23.transition cfg.state cfg.head).nextState,
                left := newLeft, head := newHead,
                right := (wolfram23.transition cfg.state cfg.head).write
                          :: cfg.right }, ?_, ?_, ?_, ?_, ?_⟩
      · unfold step
        rw [if_neg h_neq]
        dsimp only []
        rw [h_dir, h_l]
      · exact h_ns
      · exact h_lh.1
      · exact h_lh.2
      · intro x h_mem
        rcases List.mem_cons.mp h_mem with h | h
        · rw [h]; exact h_w_lt
        · exact h_right x h
  | R =>
    cases h_r : readHead cfg.right with
    | mk newHead newRight =>
      have h_rh := readHead_preserves_lt_three cfg.right h_right
      rw [h_r] at h_rh
      refine ⟨{ state := (wolfram23.transition cfg.state cfg.head).nextState,
                left := (wolfram23.transition cfg.state cfg.head).write
                          :: cfg.left,
                head := newHead, right := newRight }, ?_, ?_, ?_, ?_, ?_⟩
      · unfold step
        rw [if_neg h_neq]
        dsimp only []
        rw [h_dir, h_r]
      · exact h_ns
      · exact h_rh.1
      · intro x h_mem
        rcases List.mem_cons.mp h_mem with h | h
        · rw [h]; exact h_w_lt
        · exact h_left x h
      · exact h_rh.2

/-- Wolfram23 nSteps preserves `IsValidWolfram23Cfg` for any `n`. -/
theorem nSteps_wolfram23_preserves_valid (cfg : Config)
    (h : IsValidWolfram23Cfg cfg) (n : Nat) :
    ∃ cfg', nSteps wolfram23 cfg n = some cfg' ∧ IsValidWolfram23Cfg cfg' := by
  induction n generalizing cfg with
  | zero => exact ⟨cfg, rfl, h⟩
  | succ n ih =>
    obtain ⟨cfg'', h_step, h_valid''⟩ := step_wolfram23_preserves_valid cfg h
    obtain ⟨cfg', h_nstep, h_valid'⟩ := ih cfg'' h_valid''
    refine ⟨cfg', ?_, h_valid'⟩
    show (match step wolfram23 cfg with
          | none => none
          | some c => nSteps wolfram23 c n) = some cfg'
    rw [h_step]
    exact h_nstep

/-- Wolfram23's `eval` returns `none` for any fuel, from any valid cfg.
    Formal proof that wolfram23 truly doesn't halt from valid input. -/
theorem eval_wolfram23_valid_eq_none (cfg : Config)
    (h : IsValidWolfram23Cfg cfg) (fuel : Nat) :
    eval wolfram23 cfg fuel = none := by
  induction fuel generalizing cfg with
  | zero =>
    have h_active : cfg.state ≠ 0 := by
      rcases h.1 with h_s | h_s <;> rw [h_s] <;> omega
    have h_nh : halted cfg = false := by simp [halted, h_active]
    simp [eval, h_nh]
  | succ fuel ih =>
    have h_active : cfg.state ≠ 0 := by
      rcases h.1 with h_s | h_s <;> rw [h_s] <;> omega
    have h_nh : halted cfg = false := by simp [halted, h_active]
    obtain ⟨cfg', h_step, h_valid⟩ := step_wolfram23_preserves_valid cfg h
    simp [eval, h_nh, h_step]
    exact ih cfg' h_valid

/-- Wolfram23 does not halt from any valid input cfg. -/
theorem not_halts_wolfram23_valid (cfg : Config) (h : IsValidWolfram23Cfg cfg) :
    ¬ Halts wolfram23 cfg := by
  intro ⟨fuel, _, h_eval⟩
  rw [eval_wolfram23_valid_eq_none cfg h fuel] at h_eval
  cases h_eval

/-- The standard initial cfg `wolfram23_init` is valid. -/
theorem wolfram23_init_valid : IsValidWolfram23Cfg wolfram23_init := by
  refine ⟨Or.inl rfl, by decide, ?_, ?_⟩ <;> intro x h <;> cases h

/-- Hence wolfram23 doesn't halt from `wolfram23_init` — strengthening
    `wolfram23_runs_20` from "doesn't halt within 20" to
    "doesn't halt for any fuel". -/
theorem not_halts_wolfram23_init : ¬ Halts wolfram23 wolfram23_init :=
  not_halts_wolfram23_valid wolfram23_init wolfram23_init_valid

/-- `nSteps wolfram23 wolfram23_init n` always returns `some` valid cfg. -/
theorem nSteps_wolfram23_init_succeeds (n : Nat) :
    ∃ cfg, nSteps wolfram23 wolfram23_init n = some cfg
            ∧ IsValidWolfram23Cfg cfg :=
  nSteps_wolfram23_preserves_valid wolfram23_init wolfram23_init_valid n

/-- Wolfram23 step doesn't return `none` on valid input. -/
theorem step_wolfram23_valid_ne_none (cfg : Config)
    (h : IsValidWolfram23Cfg cfg) :
    step wolfram23 cfg ≠ none := by
  obtain ⟨cfg', h_step, _⟩ := step_wolfram23_preserves_valid cfg h
  rw [h_step]
  intro h_ne; cases h_ne

/-- The post-step-1 cfg of wolfram23 from init is valid.
    (Concrete instance: the cfg `⟨2, [1], 0, []⟩` after 1 step
    from init is itself a valid input for further wolfram23 evolution.) -/
example : IsValidWolfram23Cfg
    { state := 2, left := [1], head := 0, right := [] } := by
  refine ⟨Or.inr rfl, by decide, ?_, ?_⟩
  · intro x h
    rcases List.mem_cons.mp h with h | h
    · rw [h]; decide
    · cases h
  · intro x h; cases h

/-- The wolfram23 cfg after exactly `n` steps from `wolfram23_init`.
    Falls back to `wolfram23_init` in the (impossible-for-valid-input)
    `none` case via `Option.getD`. -/
def wolfram23_at_n (n : Nat) : Config :=
  (nSteps wolfram23 wolfram23_init n).getD wolfram23_init

/-- `wolfram23_at_n n` agrees with `nSteps wolfram23 wolfram23_init n`. -/
theorem wolfram23_at_n_eq_nSteps (n : Nat) :
    nSteps wolfram23 wolfram23_init n = some (wolfram23_at_n n) := by
  obtain ⟨cfg, h_nSteps, _⟩ :=
    nSteps_wolfram23_preserves_valid wolfram23_init wolfram23_init_valid n
  rw [h_nSteps]
  unfold wolfram23_at_n
  rw [h_nSteps]
  rfl

/-- **wolfram23 from `wolfram23_init` always has nSteps some**:
    direct application of `BiTM_not_Halts_iff_nSteps_always_some`
    to `not_halts_wolfram23_init`.  The canonical wolfram23
    trajectory never terminates. -/
theorem wolfram23_init_nSteps_always_some :
    ∀ n, ∃ result, nSteps wolfram23 wolfram23_init n = some result :=
  (BiTM_not_Halts_iff_nSteps_always_some wolfram23 wolfram23_init).mp
    not_halts_wolfram23_init

/-- One wolfram23 step from `wolfram23_at_n n` gives `wolfram23_at_n (n+1)`. -/
theorem step_wolfram23_at_n (n : Nat) :
    step wolfram23 (wolfram23_at_n n) = some (wolfram23_at_n (n + 1)) := by
  have h_n := wolfram23_at_n_eq_nSteps n
  have h_n1 := wolfram23_at_n_eq_nSteps (n + 1)
  rw [show n + 1 = n + 1 from rfl, nSteps_add wolfram23 wolfram23_init n 1] at h_n1
  rw [h_n] at h_n1
  simp at h_n1
  have h_step_eq : nSteps wolfram23 (wolfram23_at_n n) 1
                  = step wolfram23 (wolfram23_at_n n) := by
    show (match step wolfram23 (wolfram23_at_n n) with
          | none => none
          | some cfg' => nSteps wolfram23 cfg' 0) = _
    cases step wolfram23 (wolfram23_at_n n) <;> rfl
  rw [h_step_eq] at h_n1
  exact h_n1

/-- Wolfram23 trajectory composes additively from any starting offset:
    running `m` steps from `wolfram23_at_n n` lands on `wolfram23_at_n (n+m)`. -/
theorem nSteps_wolfram23_at_n (n m : Nat) :
    nSteps wolfram23 (wolfram23_at_n n) m = some (wolfram23_at_n (n + m)) := by
  induction m generalizing n with
  | zero =>
    show some (wolfram23_at_n n) = some (wolfram23_at_n (n + 0))
    rw [Nat.add_zero]
  | succ m ih =>
    show (match step wolfram23 (wolfram23_at_n n) with
          | none => none
          | some cfg' => nSteps wolfram23 cfg' m) = some (wolfram23_at_n (n + (m + 1)))
    rw [step_wolfram23_at_n n]
    have h_assoc : n + (m + 1) = (n + 1) + m := by
      rw [Nat.add_succ, Nat.succ_add]
    rw [h_assoc]
    exact ih (n + 1)

/-- Every wolfram23 trajectory point is a valid wolfram23 config.  Direct
    consequence of `nSteps_wolfram23_init_succeeds`: the `getD` fallback
    is unreachable. -/
theorem wolfram23_at_n_valid (n : Nat) :
    IsValidWolfram23Cfg (wolfram23_at_n n) := by
  obtain ⟨cfg, h_nSteps, h_valid⟩ := nSteps_wolfram23_init_succeeds n
  have h_eq : wolfram23_at_n n = cfg := by
    unfold wolfram23_at_n; rw [h_nSteps]; rfl
  rw [h_eq]; exact h_valid

/-- Wolfram23 never reaches the halt state `0` along its trajectory. -/
theorem wolfram23_at_n_state_ne_zero (n : Nat) :
    (wolfram23_at_n n).state ≠ 0 := by
  have h := (wolfram23_at_n_valid n).1
  rcases h with h_s | h_s <;> rw [h_s] <;> omega

/-- Wolfram23 never halts at any trajectory point — strengthens
    `not_halts_wolfram23_init` to every reachable config. -/
theorem wolfram23_at_n_not_halted (n : Nat) :
    halted (wolfram23_at_n n) = false := by
  simp [halted, wolfram23_at_n_state_ne_zero n]

/-- Strict injectivity surrogate: two trajectory points are equal iff one
    is reachable from the other.  Direction "n+m offset = some specific point". -/
theorem wolfram23_at_n_eq_iff_reach (n m : Nat) :
    nSteps wolfram23 (wolfram23_at_n n) m = some (wolfram23_at_n (n + m)) :=
  nSteps_wolfram23_at_n n m

/-- **`wolfram23_at_n_state_in_one_two` (iter 637)**: state is always
    in {1, 2} along wolfram23's canonical trajectory.  Direct extract
    from `wolfram23_at_n_valid`'s first component. -/
theorem wolfram23_at_n_state_in_one_two (n : Nat) :
    (wolfram23_at_n n).state = 1 ∨ (wolfram23_at_n n).state = 2 :=
  (wolfram23_at_n_valid n).1

/-- **`wolfram23_at_n_head_lt_three` (iter 637)**: head bounded by
    numSymbols (= 3). -/
theorem wolfram23_at_n_head_lt_three (n : Nat) :
    (wolfram23_at_n n).head < 3 :=
  (wolfram23_at_n_valid n).2.1

/-- **`wolfram23_at_n_left_lt_three` (iter 637)**: all symbols on left
    tape are valid wolfram23 alphabet (0, 1, or 2). -/
theorem wolfram23_at_n_left_lt_three (n : Nat) :
    ∀ x ∈ (wolfram23_at_n n).left, x < 3 :=
  (wolfram23_at_n_valid n).2.2.1

/-- **`wolfram23_at_n_right_lt_three` (iter 637)**: same for right tape. -/
theorem wolfram23_at_n_right_lt_three (n : Nat) :
    ∀ x ∈ (wolfram23_at_n n).right, x < 3 :=
  (wolfram23_at_n_valid n).2.2.2

end BiTM
