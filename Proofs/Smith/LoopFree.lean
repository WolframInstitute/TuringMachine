/-
  Smith.LoopFree

  PLAN.md target T5, loop-freeness (TM23Proof.pdf p. 21-22): a finite
  region of System 0 cannot trap the head.  Smith's argument is made in
  System 1: add up the positions of the 0s in the region; a change of state
  from A to B or from B to A decreases the sum, except that `B20` increases
  it and the `A0` step that must follow decreases it below its old value;
  and without a change of state the head moves monotonically (left in A,
  right in B) and so leaves the region.

  Formally, on the zipper configurations of `Smith.Lookahead`:

    * `V c` is the sum of the positions of the 0s, counted from 1 at the
      left end of the tape.
    * `W c` is `V c` without the contribution of the head cell in state A
      (that contribution is spent by the `A0` step that is bound to come),
      which makes `W` non-increasing on every System 1 step and strictly
      decreasing on every step from state B to state A.
    * `phase c` is the head position in state A and the number of cells to
      the right in state B; it decreases on every step that does not
      decrease `W`.

  The pair `(W, phase)` decreases lexicographically on every step
  (`sys1_measure`), so every System 1 run on a finite tape is finite
  (`sys1_leaves`), and so is every System 0 run through the 1-or-3 step
  correspondence of `Smith.Systems123` (`sys0_leaves`).  No configuration
  of System 0 is periodic (`sys0_not_periodic`).

  Contents: `zeroSumL`, `zeroSumR`, `V`, `W`, `phase`, `sys1_measure`,
  `run_ends_of_measure`, `sys1_leaves`, `sys1_none_sys0`, `sys0_leaves`,
  `sys0_not_periodic`, and `decide` checks of the measure on the p. 47 run.
-/

import Smith.Systems123

namespace Smith

open TM
open LState

/-! ## Smith's zero-position sum -/

/-- The zero-position sum of the cells left of the head, nearest first: the
    cell at distance `d` from the head is at position `|L| - d`, weight
    `|L| - d + 1`. -/
def zeroSumL : List (Fin 3) → Nat
  | [] => 0
  | x :: L' => (if x = 0 then L'.length + 1 else 0) + zeroSumL L'

/-- The zero-position sum of a list whose first cell is at position `i`. -/
def zeroSumR : List (Fin 3) → Nat → Nat
  | [], _ => 0
  | b :: R', i => (if b = 0 then i + 1 else 0) + zeroSumR R' (i + 1)

/-- Smith's sum, p. 22: the positions (from 1) of the 0s of the tape. -/
def V (c : LConfig) : Nat :=
  zeroSumL c.left + (if c.head = 0 then c.left.length + 1 else 0)
    + zeroSumR c.right (c.left.length + 1)

/-- `V` without the head cell in state A. -/
def W (c : LConfig) : Nat :=
  zeroSumL c.left + (if c.state ≠ A ∧ c.head = 0 then c.left.length + 1 else 0)
    + zeroSumR c.right (c.left.length + 1)

/-- The secondary measure: how far the head can still go in its current
    direction before it changes state, plus the tape length in state A so
    that the change from A to B decreases it too. -/
def phase (c : LConfig) : Nat :=
  match c.state with
  | A => c.left.length + 1 + c.right.length + 1 + c.left.length
  | _ => c.right.length

/-- `W` agrees with `V` in state B and discounts the head in state A. -/
theorem W_eq (c : LConfig) :
    W c = V c - (if c.state = A ∧ c.head = 0 then c.left.length + 1 else 0) := by
  unfold W V
  by_cases hs : c.state = A <;> by_cases hh : c.head = 0 <;> simp [hs, hh]
  all_goals omega

/-! ## The measure decreases -/

/-- One step of System 1 from a configuration in state A or B decreases the
    pair `(W, phase)` lexicographically and stays in states A, B. -/
theorem sys1_measure (c c' : LConfig) (hst : c.state ≠ C) (h : lstep sys1 c = some c') :
    (W c' < W c ∨ (W c' = W c ∧ phase c' < phase c)) ∧ c'.state ≠ C := by
  obtain ⟨L, a, R, st⟩ := c
  rcases R with _ | ⟨b, R'⟩ <;> rcases L with _ | ⟨x, L'⟩ <;> cases st
  all_goals (try exact absurd rfl hst)
  all_goals fin_cases a
  all_goals (try fin_cases b)
  all_goals (simp [lstep, sys1] at h)
  all_goals (subst h; simp [W, phase, zeroSumL, zeroSumR])
  all_goals ((try split_ifs) <;> omega)

/-! ## From the measure to the end of the run -/

/-- A lexicographically decreasing measure on a set of configurations
    closed under the step ends every run from the set. -/
theorem run_ends_of_measure (M : LMachine) (P : LConfig → Prop) (W phase : LConfig → Nat)
    (hdec : ∀ c c', P c → lstep M c = some c' →
      (W c' < W c ∨ (W c' = W c ∧ phase c' < phase c)) ∧ P c') :
    ∀ (w f : Nat) (c : LConfig), P c → W c ≤ w → phase c ≤ f → ∃ n, lnSteps M c n = none := by
  intro w
  induction w with
  | zero =>
    intro f
    induction f with
    | zero =>
      intro c hP hW hf
      cases hs : lstep M c with
      | none => exact ⟨1, by rw [lnSteps_one, hs]⟩
      | some c' =>
        obtain ⟨hlt, _⟩ := hdec c c' hP hs
        omega
    | succ f ihf =>
      intro c hP hW hf
      cases hs : lstep M c with
      | none => exact ⟨1, by rw [lnSteps_one, hs]⟩
      | some c' =>
        obtain ⟨hlt, hP'⟩ := hdec c c' hP hs
        obtain ⟨n, hn⟩ := ihf c' hP' (by omega) (by omega)
        exact ⟨n + 1, by rw [lnSteps_succ, hs, Option.bind_some, hn]⟩
  | succ w ihw =>
    intro f
    induction f with
    | zero =>
      intro c hP hW hf
      cases hs : lstep M c with
      | none => exact ⟨1, by rw [lnSteps_one, hs]⟩
      | some c' =>
        obtain ⟨hlt, hP'⟩ := hdec c c' hP hs
        rcases hlt with hlt | ⟨_, hlt⟩
        · obtain ⟨n, hn⟩ := ihw (phase c') c' hP' (by omega) (le_refl _)
          exact ⟨n + 1, by rw [lnSteps_succ, hs, Option.bind_some, hn]⟩
        · omega
    | succ f ihf =>
      intro c hP hW hf
      cases hs : lstep M c with
      | none => exact ⟨1, by rw [lnSteps_one, hs]⟩
      | some c' =>
        obtain ⟨hlt, hP'⟩ := hdec c c' hP hs
        rcases hlt with hlt | ⟨heq, hlt⟩
        · obtain ⟨n, hn⟩ := ihw (phase c') c' hP' (by omega) (le_refl _)
          exact ⟨n + 1, by rw [lnSteps_succ, hs, Option.bind_some, hn]⟩
        · obtain ⟨n, hn⟩ := ihf c' hP' (by omega) (by omega)
          exact ⟨n + 1, by rw [lnSteps_succ, hs, Option.bind_some, hn]⟩

/-- T5 for System 1: every run from a configuration in state A or B leaves
    the tape. -/
theorem sys1_leaves (c : LConfig) (hst : c.state ≠ C) : ∃ n, lnSteps sys1 c n = none :=
  run_ends_of_measure sys1 (fun c => c.state ≠ C) W phase sys1_measure (W c) (phase c) c hst
    (le_refl _) (le_refl _)

/-! ## From System 1 to System 0 -/

/-- Where System 1 is stuck, System 0 is stuck too: the one-cell rules are
    the same, and `B2` at the last cell moves System 0 off the tape. -/
theorem sys1_none_sys0 (c : LConfig) (h : lstep sys1 c = none) : lstep sys0 c = none := by
  obtain ⟨L, a, R, st⟩ := c
  rcases R with _ | ⟨b, R'⟩ <;> rcases L with _ | ⟨x, L'⟩ <;> cases st
  all_goals fin_cases a
  all_goals (try fin_cases b)
  all_goals (simp [lstep, sys0, sys1] at h ⊢)

/-- A run of the target that ends when the source's run ends. -/
theorem run_ends_of_sim (M1 M0 : LMachine)
    (hstep : ∀ c c', lstep M1 c = some c' → ∃ k, 1 ≤ k ∧ lnSteps M0 c k = some c')
    (hnone : ∀ c, lstep M1 c = none → lstep M0 c = none)
    (c : LConfig) (n : Nat) (h : lnSteps M1 c n = none) : ∃ m, lnSteps M0 c m = none := by
  induction n generalizing c with
  | zero => simp at h
  | succ n ih =>
    rw [lnSteps_succ] at h
    cases hs : lstep M1 c with
    | none => exact ⟨1, by rw [lnSteps_one, hnone c hs]⟩
    | some c' =>
      rw [hs, Option.bind_some] at h
      obtain ⟨m, hm⟩ := ih c' h
      obtain ⟨k, _, hk⟩ := hstep c c' hs
      exact ⟨k + m, by rw [lnSteps_add, hk, Option.bind_some, hm]⟩

/-- T5 for System 0, Wolfram's machine on a finite tape: from every
    configuration in state A or B the head leaves the tape. -/
theorem sys0_leaves (c : LConfig) (hst : c.state ≠ C) : ∃ n, lnSteps sys0 c n = none := by
  obtain ⟨n, hn⟩ := sys1_leaves c hst
  exact run_ends_of_sim sys1 sys0 sys1_sys0_step sys1_none_sys0 c n hn

/-- No System 0 configuration in state A or B is periodic. -/
theorem sys0_not_periodic (c : LConfig) (hst : c.state ≠ C) (p : Nat) (hp : 1 ≤ p) :
    lnSteps sys0 c p ≠ some c := by
  intro hper
  obtain ⟨n, hn⟩ := sys0_leaves c hst
  have hiter : ∀ k, lnSteps sys0 c (k * p) = some c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul, lnSteps_add, ih, Option.bind_some, hper]
  have h1 := hiter (n + 1)
  have hle : n + 1 ≤ (n + 1) * p := Nat.le_mul_of_pos_right (n + 1) hp
  rw [show (n + 1) * p = n + ((n + 1) * p - n) by omega, lnSteps_none_add _ _ _ _ hn] at h1
  exact absurd h1 (by simp)

/-! ## Checks -/

/-- Smith's sum on the p. 47 run: `V` is not monotone (System 0 steps
    through `B2`, which System 1 compresses), while `W` never increases
    along the System 1 run of the same tape. -/
example : V cfgP47 = 1 + 2 + 3 + 4 + 5 + 6 + 7 := by decide

/-- The `W` values along the System 1 run of `cfgP47` are non-increasing. -/
def wTrace (c : LConfig) : Nat → List Nat
  | 0 => [W c]
  | n + 1 =>
    match lstep sys1 c with
    | none => [W c]
    | some c' => W c :: wTrace c' n

example : (wTrace cfgP47 40).Pairwise (· ≥ ·) := by decide

/-- `V` increases along the System 0 run (the `B2 -> A0>` steps). -/
def vTrace (c : LConfig) : Nat → List Nat
  | 0 => [V c]
  | n + 1 =>
    match lstep sys0 c with
    | none => [V c]
    | some c' => V c :: vTrace c' n

example : ¬ (vTrace cfgP47 27).Pairwise (· ≥ ·) := by decide

end Smith
