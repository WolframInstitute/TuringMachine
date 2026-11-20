/-
  BiTM.Wolfram23Valid

  Validity infrastructure for Wolfram's (2,3) Turing machine
  configurations: state in {1, 2}, head < 3, all tape values < 3.

  Key results:
    * `IsValidWolfram23Cfg` predicate
    * `step_wolfram23_preserves_valid`: single-step preservation
    * `nSteps_wolfram23_preserves_valid`: multi-step preservation
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
            | 0, _ => decide
            | 1, _ => decide
            | 2, _ => decide)

/-- Wolfram23's `write` field is always `< 3` for valid (state, head)
    pairs.  Together with `wolfram23_nextState_in_range`, this confirms
    wolfram23 preserves "tape values < 3" if the input cfg is valid. -/
theorem wolfram23_write_in_range (q s : Nat) (h_q : q = 1 ∨ q = 2)
    (h_s : s < 3) :
    (wolfram23.transition q s).write < 3 := by
  rcases h_q with h_q | h_q <;> subst h_q
  all_goals (match s, h_s with
            | 0, _ => decide
            | 1, _ => decide
            | 2, _ => decide)

/-- A valid wolfram23 config: active state, in-range head, and all
    tape values `< 3` on both sides. -/
def IsValidWolfram23Cfg (cfg : Config) : Prop :=
  (cfg.state = 1 ∨ cfg.state = 2)
    ∧ cfg.head < 3
    ∧ (∀ x ∈ cfg.left, x < 3)
    ∧ (∀ x ∈ cfg.right, x < 3)

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
        rw [ite_eq_right h_neq]
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
        rw [ite_eq_right h_neq]
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
    rw [BiTM_nSteps_succ_unfold, h_step]
    exact h_nstep

/-- The post-step-1 cfg of wolfram23 from init is valid.
    (Concrete instance: the cfg with state 2, left `[1]`, head 0, right `[]` after 1 step
    from init is itself a valid input for further wolfram23 evolution.) -/
example : IsValidWolfram23Cfg
    { state := 2, left := [1], head := 0, right := [] } := by
  refine ⟨Or.inr rfl, by decide, ?_, ?_⟩
  · intro x h
    rcases List.mem_cons.mp h with h | h
    · rw [h]; decide
    · cases h
  · intro x h; cases h

end BiTM
