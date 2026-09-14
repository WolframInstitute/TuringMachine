/-
  BiTM.System5

  Smith's "System 5" simulator (PDF `TM23Proof.pdf` p. 30, `system5.pl`):
  a parity-multiset bag plus a queue of integer-list rules.  One step
  decrements every bag element, increments every rule element, and
  either pops a rule (XOR-merging it into the bag) when a `0`
  surfaces, or proceeds without popping otherwise.

  Extracted from `BiTM.CockeMinskyConstruction` in a refactor.

  Contents:
    * `System5Config` structure
    * `System5.step` definition
    * `System5_step_pure_decrement` — no-pop case characterisation
    * `System5_step_none_iff` — halting iff bag or rules empty
    * `System5_step_some_iff` — dual: success iff both nonempty
    * `System5_step_pop_rule` — pop case characterisation
-/

import BiTM.XorMerge
import BiTM.HaltInduction
import TagSystem.HaltsEmpty

namespace BiTM

open TM
open TagSystem

/-- A System 5 configuration: a bag (parity multiset) + a queue of rules. -/
structure System5Config where
  /-- The current bag (parity-mod-2 multiset). -/
  bag : List Int
  /-- The remaining rules; rules are popped (consumed) as `0` ∈ bag triggers. -/
  rules : List (List Int)
  deriving Repr, DecidableEq

/-- One step of System 5 per `TM23Proof.pdf` p. 30, `system5.pl`.
    Returns `none` when the system halts (bag empty or no rules left). -/
def System5.step (cfg : System5Config) : Option System5Config :=
  let decremented := cfg.bag.map (fun x => x - 1)
  let incrementedRules := cfg.rules.map (fun r => r.map (fun x => x + 1))
  if decremented.isEmpty ∨ incrementedRules.isEmpty then
    none
  else if 0 ∈ decremented then
    match incrementedRules with
    | [] => none -- handled above but Lean wants exhaustive match
    | nextRule :: restRules =>
      let bagWithoutZero := decremented.erase 0
      let merged := xorMerge bagWithoutZero nextRule
      some { bag := merged, rules := restRules }
  else
    some { bag := decremented, rules := incrementedRules }

/-- When no `0` survives the decrement (and neither bag nor rules is
    empty), `System5.step` simply decrements the bag and increments
    the rules — no rule pop, no XOR-merge. -/
theorem System5_step_pure_decrement (cfg cfg' : System5Config)
    (h_step : System5.step cfg = some cfg')
    (h_bag : cfg.bag ≠ []) (h_rules : cfg.rules ≠ [])
    (h_zero : 0 ∉ cfg.bag.map (· - 1)) :
    cfg'.bag = cfg.bag.map (· - 1)
    ∧ cfg'.rules = cfg.rules.map (fun r => r.map (· + 1)) := by
  unfold System5.step at h_step
  have h_dec_ne_nil : cfg.bag.map (· - 1) ≠ [] := by
    intro h; rw [List.map_eq_nil_iff] at h; exact h_bag h
  have h_inc_ne_nil : cfg.rules.map (fun r => r.map (· + 1)) ≠ [] := by
    intro h; rw [List.map_eq_nil_iff] at h; exact h_rules h
  have h_first_false :
      (cfg.bag.map (· - 1)).isEmpty = true ∨
      (cfg.rules.map (fun r => r.map (· + 1))).isEmpty = true → False := by
    intro h
    rcases h with h | h
    · exact h_dec_ne_nil (List.isEmpty_iff.mp h)
    · exact h_inc_ne_nil (List.isEmpty_iff.mp h)
  rw [if_neg h_first_false] at h_step
  rw [if_neg h_zero] at h_step
  injection h_step with h_eq
  rw [← h_eq]
  exact ⟨rfl, rfl⟩

/-- **Halting characterisation**: `System5.step cfg = none` iff bag or rules is empty. -/
theorem System5_step_none_iff (cfg : System5Config) :
    System5.step cfg = none ↔ cfg.bag = [] ∨ cfg.rules = [] := by
  unfold System5.step
  constructor
  · intro h
    by_cases h_bag : cfg.bag = []
    · left; exact h_bag
    by_cases h_rules : cfg.rules = []
    · right; exact h_rules
    exfalso
    have h_dec_ne_nil : cfg.bag.map (· - 1) ≠ [] := by
      intro hh; rw [List.map_eq_nil_iff] at hh; exact h_bag hh
    have h_inc_ne_nil : cfg.rules.map (fun r => r.map (· + 1)) ≠ [] := by
      intro hh; rw [List.map_eq_nil_iff] at hh; exact h_rules hh
    have h_first_false :
        (cfg.bag.map (· - 1)).isEmpty = true ∨
        (cfg.rules.map (fun r => r.map (· + 1))).isEmpty = true → False := by
      intro h
      rcases h with h | h
      · exact h_dec_ne_nil (List.isEmpty_iff.mp h)
      · exact h_inc_ne_nil (List.isEmpty_iff.mp h)
    rw [if_neg h_first_false] at h
    by_cases h_zero : 0 ∈ cfg.bag.map (· - 1)
    · rw [if_pos h_zero] at h
      cases h_cfg_rules : cfg.rules with
      | nil => exact h_rules h_cfg_rules
      | cons r rs =>
        rw [h_cfg_rules] at h; cases h
    · rw [if_neg h_zero] at h
      cases h
  · intro h
    rcases h with h | h
    · have : (cfg.bag.map (· - 1)).isEmpty = true := by
        rw [h]; rfl
      rw [if_pos (Or.inl this)]
    · have : (cfg.rules.map (fun r => r.map (· + 1))).isEmpty = true := by
        rw [h]; rfl
      rw [if_pos (Or.inr this)]

/-- Dual of `System5_step_none_iff`: `step` succeeds iff bag and rules are nonempty. -/
theorem System5_step_some_iff (cfg : System5Config) :
    (∃ cfg', System5.step cfg = some cfg') ↔ cfg.bag ≠ [] ∧ cfg.rules ≠ [] := by
  constructor
  · intro ⟨_, h_some⟩
    refine ⟨?_, ?_⟩
    · intro h_empty
      have h_none : System5.step cfg = none :=
        (System5_step_none_iff cfg).mpr (Or.inl h_empty)
      rw [h_none] at h_some; cases h_some
    · intro h_empty
      have h_none : System5.step cfg = none :=
        (System5_step_none_iff cfg).mpr (Or.inr h_empty)
      rw [h_none] at h_some; cases h_some
  · intro ⟨h_bag, h_rules⟩
    cases h_step : System5.step cfg with
    | none =>
      exfalso
      rcases (System5_step_none_iff cfg).mp h_step with h | h
      · exact h_bag h
      · exact h_rules h
    | some cfg' => exact ⟨cfg', rfl⟩

/-- The rule-pop case: when `0` survives the decrement, `System5.step` pops
    the next (incremented) rule and XOR-merges it into the bag minus `0`. -/
theorem System5_step_pop_rule (cfg cfg' : System5Config)
    (h_step : System5.step cfg = some cfg')
    (h_bag : cfg.bag ≠ []) (h_rules : cfg.rules ≠ [])
    (h_zero : 0 ∈ cfg.bag.map (· - 1)) :
    ∃ (nextRule : List Int) (restRules : List (List Int)),
      cfg.rules.map (fun r => r.map (· + 1)) = nextRule :: restRules ∧
      cfg'.bag = xorMerge ((cfg.bag.map (· - 1)).erase 0) nextRule ∧
      cfg'.rules = restRules := by
  unfold System5.step at h_step
  have h_dec_ne_nil : cfg.bag.map (· - 1) ≠ [] := by
    intro h; rw [List.map_eq_nil_iff] at h; exact h_bag h
  have h_inc_ne_nil : cfg.rules.map (fun r => r.map (· + 1)) ≠ [] := by
    intro h; rw [List.map_eq_nil_iff] at h; exact h_rules h
  have h_first_false :
      (cfg.bag.map (· - 1)).isEmpty = true ∨
      (cfg.rules.map (fun r => r.map (· + 1))).isEmpty = true → False := by
    intro h
    rcases h with h | h
    · exact h_dec_ne_nil (List.isEmpty_iff.mp h)
    · exact h_inc_ne_nil (List.isEmpty_iff.mp h)
  rw [if_neg h_first_false] at h_step
  rw [if_pos h_zero] at h_step
  cases h_cfg_rules : cfg.rules with
  | nil => exact absurd h_cfg_rules h_rules
  | cons r rs =>
    rw [h_cfg_rules] at h_step
    injection h_step with h_eq
    refine ⟨r.map (· + 1), rs.map (fun r => r.map (· + 1)), rfl, ?_, ?_⟩ <;>
      (simp [← h_eq])

/-- **Iter 886: rules length strict decrease on P-step**.  When
    `System5.step` is a pop (i.e., `0 ∈ bag.map(·-1)`), the resulting
    rules list has length exactly `cfg.rules.length - 1`. -/
theorem System5_step_rules_length_eq_pop (cfg cfg' : System5Config)
    (h_step : System5.step cfg = some cfg')
    (h_bag : cfg.bag ≠ []) (h_rules : cfg.rules ≠ [])
    (h_zero : 0 ∈ cfg.bag.map (· - 1)) :
    cfg'.rules.length = cfg.rules.length - 1 := by
  obtain ⟨nextRule, restRules, h_inc, h_bag', h_rules'⟩ :=
    System5_step_pop_rule cfg cfg' h_step h_bag h_rules h_zero
  rw [h_rules']
  have : cfg.rules.length = restRules.length + 1 := by
    have h_len : (cfg.rules.map (fun r => r.map (· + 1))).length = cfg.rules.length := by
      simp
    rw [← h_len, h_inc]
    simp
  omega

/-- **Iter 899: explicit P-step characterization**.  When the rules
    head is known (cfg.rules = r1 :: rest) and `0 ∈ cfg.bag.map(·-1)`,
    the System5 step pops r1 (incremented) and merges with bag-after-erase. -/
theorem System5_step_explicit_pop (cfg : System5Config)
    (r1 : List Int) (rest_rules : List (List Int))
    (h_rules : cfg.rules = r1 :: rest_rules)
    (h_bag : cfg.bag ≠ [])
    (h_zero : 0 ∈ cfg.bag.map (· - 1)) :
    System5.step cfg = some
      { bag := xorMerge ((cfg.bag.map (· - 1)).erase 0) (r1.map (· + 1)),
        rules := rest_rules.map (fun r => r.map (· + 1)) } := by
  unfold System5.step
  have h_dec_ne_nil : cfg.bag.map (· - 1) ≠ [] := by
    intro h; rw [List.map_eq_nil_iff] at h; exact h_bag h
  have h_rules_ne : cfg.rules ≠ [] := by rw [h_rules]; simp
  have h_inc_ne_nil : cfg.rules.map (fun r => r.map (· + 1)) ≠ [] := by
    intro h; rw [List.map_eq_nil_iff] at h; exact h_rules_ne h
  have h_first_false :
      (cfg.bag.map (· - 1)).isEmpty = true
      ∨ (cfg.rules.map (fun r => r.map (· + 1))).isEmpty = true → False := by
    intro h
    rcases h with h | h
    · exact h_dec_ne_nil (List.isEmpty_iff.mp h)
    · exact h_inc_ne_nil (List.isEmpty_iff.mp h)
  rw [if_neg h_first_false, if_pos h_zero]
  rw [h_rules]
  rfl

/-- **Iter 887: bridge between `1 ∈ bag` and `0 ∈ bag.map(·-1)`**.
    This is the predicate that distinguishes P-steps from D-steps,
    expressed in the more natural "bag has counter 1" form. -/
theorem System5_one_mem_iff_zero_in_decremented (bag : List Int) :
    (1 : Int) ∈ bag ↔ (0 : Int) ∈ bag.map (· - 1) := by
  rw [List.mem_map]
  constructor
  · intro h_one
    exact ⟨1, h_one, by omega⟩
  · rintro ⟨x, hx_mem, hx_eq⟩
    have : x = 1 := by omega
    rw [this] at hx_mem
    exact hx_mem

/-- **Iter 886: rules length preserved on D-step**.  When
    `System5.step` is a pure decrement (i.e., `0 ∉ bag.map(·-1)`),
    rules length is preserved. -/
theorem System5_step_rules_length_eq_dec (cfg cfg' : System5Config)
    (h_step : System5.step cfg = some cfg')
    (h_bag : cfg.bag ≠ []) (h_rules : cfg.rules ≠ [])
    (h_zero : 0 ∉ cfg.bag.map (· - 1)) :
    cfg'.rules.length = cfg.rules.length := by
  obtain ⟨_, h_rules'⟩ :=
    System5_step_pure_decrement cfg cfg' h_step h_bag h_rules h_zero
  rw [h_rules']
  simp

/-- **Iter 884: rules length monotonicity (single step)**.  Every
    `System5.step` either preserves rules length (D-step / pure
    decrement) or decreases by 1 (P-step / pop rule).  So `cfg'.rules.length
    ≤ cfg.rules.length` always.  Foundational invariant for trajectory
    analysis — see iter 883 closure plan in plan file. -/
theorem System5_step_rules_length_le (cfg cfg' : System5Config)
    (h_step : System5.step cfg = some cfg') :
    cfg'.rules.length ≤ cfg.rules.length := by
  unfold System5.step at h_step
  by_cases h_empty :
      (cfg.bag.map (· - 1)).isEmpty = true
      ∨ (cfg.rules.map (fun r => r.map (· + 1))).isEmpty = true
  · rw [if_pos h_empty] at h_step; cases h_step
  · rw [if_neg h_empty] at h_step
    by_cases h_zero : 0 ∈ cfg.bag.map (· - 1)
    · rw [if_pos h_zero] at h_step
      cases h_rules : cfg.rules with
      | nil =>
        rw [h_rules] at h_step
        simp at h_step
      | cons r rest =>
        rw [h_rules] at h_step
        injection h_step with h_eq
        rw [← h_eq]
        simp
    · rw [if_neg h_zero] at h_step
      injection h_step with h_eq
      rw [← h_eq]
      simp

/-- **Iter 968: single-step P-step rules form**.  Strengthened version
    of `System5_step_rules_drop_inc`: when `0 ∈ bag.map(·-1)` (P-step
    condition), `j = 1` exactly — the rules drop the head and increment.
    Removes the existential to give a direct equality.  Useful for
    chaining 4 P-steps in the false-head trajectory. -/
theorem System5_step_rules_pstep
    (cfg cfg' : System5Config)
    (h : System5.step cfg = some cfg')
    (h_zero : 0 ∈ cfg.bag.map (· - 1)) :
    cfg'.rules = (cfg.rules.drop 1).map (fun r => r.map (· + 1)) := by
  have h_bag : cfg.bag ≠ [] := by
    intro h_empty
    have h_none : System5.step cfg = none :=
      (System5_step_none_iff cfg).mpr (Or.inl h_empty)
    rw [h_none] at h; cases h
  have h_rules : cfg.rules ≠ [] := by
    intro h_empty
    have h_none : System5.step cfg = none :=
      (System5_step_none_iff cfg).mpr (Or.inr h_empty)
    rw [h_none] at h; cases h
  obtain ⟨_, _, h_inc, _, h_rules'⟩ :=
    System5_step_pop_rule cfg cfg' h h_bag h_rules h_zero
  rw [h_rules']
  cases h_cfg_rules : cfg.rules with
  | nil => exact absurd h_cfg_rules h_rules
  | cons r rest =>
    rw [h_cfg_rules] at h_inc
    simp at h_inc
    obtain ⟨_, h_rest⟩ := h_inc
    rw [← h_rest]
    simp [List.drop]

/-- **Iter 956: single-step rules-drop-inc invariant**.  Every successful
    `System5.step` produces rules `(cfg.rules.drop j).map(map(·+1))` for
    some `j ∈ {0, 1}` — `j = 1` on a P-step (rule popped), `j = 0` on a
    D-step (rule retained, just incremented).  Foundational for the
    multi-step trajectory invariant `System5_nSteps_rules_form`. -/
theorem System5_step_rules_drop_inc (cfg cfg' : System5Config)
    (h : System5.step cfg = some cfg') :
    ∃ j, j ≤ 1 ∧ cfg'.rules = (cfg.rules.drop j).map (fun r => r.map (· + 1)) := by
  have h_bag : cfg.bag ≠ [] := by
    intro h_empty
    have h_none : System5.step cfg = none :=
      (System5_step_none_iff cfg).mpr (Or.inl h_empty)
    rw [h_none] at h; cases h
  have h_rules : cfg.rules ≠ [] := by
    intro h_empty
    have h_none : System5.step cfg = none :=
      (System5_step_none_iff cfg).mpr (Or.inr h_empty)
    rw [h_none] at h; cases h
  by_cases h_zero : 0 ∈ cfg.bag.map (· - 1)
  · obtain ⟨nextRule, restRules, h_inc, _, h_rules'⟩ :=
      System5_step_pop_rule cfg cfg' h h_bag h_rules h_zero
    refine ⟨1, Nat.le_refl _, ?_⟩
    rw [h_rules']
    cases h_cfg_rules : cfg.rules with
    | nil => exact absurd h_cfg_rules h_rules
    | cons r rest =>
      rw [h_cfg_rules] at h_inc
      simp at h_inc
      obtain ⟨_, h_rest⟩ := h_inc
      rw [← h_rest]
      simp [List.drop, h_cfg_rules]
  · obtain ⟨_, h_rules'⟩ :=
      System5_step_pure_decrement cfg cfg' h h_bag h_rules h_zero
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [h_rules']
    simp

/-- Run System 5 for exactly `m` steps; halts (returns `none`) if the
    intermediate `System5.step` returns `none`. -/
def System5.nSteps (cfg : System5Config) : Nat → Option System5Config
  | 0 => some cfg
  | m + 1 =>
    match System5.step cfg with
    | none => none
    | some cfg' => System5.nSteps cfg' m

/-- 0-step iteration is the identity. -/
@[simp] theorem System5.nSteps_zero (cfg : System5Config) :
    System5.nSteps cfg 0 = some cfg := rfl

/-- **Iter 885: rules length monotonicity (multi-step)**.  Across any
    `n` System5 steps reaching a `some cfg'`, the rules length only
    decreases.  By induction on `n` using `System5_step_rules_length_le`. -/
theorem System5_nSteps_rules_length_le
    (cfg cfg' : System5Config) (n : Nat)
    (h : System5.nSteps cfg n = some cfg') :
    cfg'.rules.length ≤ cfg.rules.length := by
  induction n generalizing cfg with
  | zero =>
    simp [System5.nSteps] at h
    rw [← h]; exact Nat.le_refl _
  | succ k ih =>
    unfold System5.nSteps at h
    cases h_step : System5.step cfg with
    | none => rw [h_step] at h; cases h
    | some cfg₁ =>
      rw [h_step] at h
      have h_step_le : cfg₁.rules.length ≤ cfg.rules.length :=
        System5_step_rules_length_le cfg cfg₁ h_step
      exact Nat.le_trans (ih cfg₁ h) h_step_le

/-- 1-step iteration is `System5.step`. -/
theorem System5.nSteps_one (cfg : System5Config) :
    System5.nSteps cfg 1 = System5.step cfg := by
  show (match System5.step cfg with
        | none => none
        | some cfg' => System5.nSteps cfg' 0) = System5.step cfg
  cases System5.step cfg <;> rfl

/-- Additive composition: `nSteps cfg (n + m) = nSteps cfg n >>= nSteps · m`. -/
theorem System5.nSteps_add (cfg : System5Config) (n m : Nat) :
    System5.nSteps cfg (n + m)
      = (System5.nSteps cfg n).bind (fun c => System5.nSteps c m) := by
  induction n generalizing cfg with
  | zero => simp [System5.nSteps]
  | succ n ih =>
    rw [Nat.succ_add]
    show (match System5.step cfg with
          | none => none
          | some c => System5.nSteps c (n + m))
        = (match System5.step cfg with
            | none => none
            | some c => System5.nSteps c n).bind
          (fun c => System5.nSteps c m)
    cases System5.step cfg with
    | none => rfl
    | some c => exact ih c

/-- Direct-recursion form: `nSteps cfg (n+1) = step cfg >>= nSteps · n`.
    Definitional, but stated explicitly for ergonomic use. -/
theorem System5.nSteps_succ (cfg : System5Config) (n : Nat) :
    System5.nSteps cfg (n + 1)
      = (System5.step cfg).bind (fun c => System5.nSteps c n) := by
  rw [Nat.add_comm, System5.nSteps_add, System5.nSteps_one]

/-- Shift composition: two `(· + _)` maps compose to a single map of
    the sum.  `(l.map (· + a)).map (· + b) = l.map (· + (a + b))`. -/
theorem List_Int_map_add_compose (l : List Int) (a b : Int) :
    (l.map (· + a)).map (· + b) = l.map (· + (a + b)) := by
  rw [List.map_map]
  congr 1
  funext x
  show (x + a) + b = x + (a + b)
  omega

/-- Dual: two `(· - _)` maps compose to a single map of the sum.
    `(l.map (· - a)).map (· - b) = l.map (· - (a + b))`. -/
theorem List_Int_map_sub_compose (l : List Int) (a b : Int) :
    (l.map (· - a)).map (· - b) = l.map (· - (a + b)) := by
  rw [List.map_map]
  congr 1
  funext x
  show (x - a) - b = x - (a + b)
  omega

/-- Add-then-sub by the same value is the identity: `(l.map (· + k)).map
    (· - k) = l`.  Useful for cancelling out a shift-then-unshift. -/
theorem List_Int_map_add_sub_self (l : List Int) (k : Int) :
    (l.map (· + k)).map (· - k) = l := by
  rw [List.map_map]
  show l.map (fun x => (x + k) - k) = l
  have h : (fun x : Int => (x + k) - k) = id := by
    funext x; show x + k - k = x; omega
  rw [h]
  exact List.map_id l

/-- Sub-then-add by the same value is the identity. -/
theorem List_Int_map_sub_add_self (l : List Int) (k : Int) :
    (l.map (· - k)).map (· + k) = l := by
  rw [List.map_map]
  show l.map (fun x => (x - k) + k) = l
  have h : (fun x : Int => (x - k) + k) = id := by
    funext x; show x - k + k = x; omega
  rw [h]
  exact List.map_id l

/-- Helper: iterated subtraction commutes — `l.map (· - (k+1))`
    equals `l.map (· - k)` then `· - 1`. -/
theorem List_Int_map_sub_succ (l : List Int) (k : Nat) :
    l.map (· - ((k + 1 : Nat) : Int)) = (l.map (· - (k : Int))).map (· - 1) := by
  rw [List.map_map]
  congr 1
  funext x
  show x - ((k + 1 : Nat) : Int) = (x - (k : Int)) - 1
  omega

/-- Helper: iterated addition commutes — `l.map (· + (k+1))`
    equals `l.map (· + k)` then `· + 1`. -/
theorem List_Int_map_add_succ (l : List Int) (k : Nat) :
    l.map (· + ((k + 1 : Nat) : Int)) = (l.map (· + (k : Int))).map (· + 1) := by
  rw [List.map_map]
  congr 1
  funext x
  show x + ((k + 1 : Nat) : Int) = (x + (k : Int)) + 1
  omega

/-- **Iter 956: multi-step rules trajectory invariant**.  After `n`
    successful System5 steps from `cfg`, the resulting rules list is
    `(cfg.rules.drop k).map(map(·+n))` for some `k ≤ n` (the cumulative
    P-step count along the trajectory).  Each of the `k` popped rules
    advances the drop-index by 1; every step (P or D) increments every
    surviving rule by 1, so after `n` steps the cumulative shift is `n`.
    Foundational for the Smith Conjecture 0 false-head closure plan
    (handoff: trajectory invariant gap blocking the 4-step proof). -/
theorem System5_nSteps_rules_form
    (cfg cfg' : System5Config) (n : Nat)
    (h : System5.nSteps cfg n = some cfg') :
    ∃ k, k ≤ n ∧
      cfg'.rules = (cfg.rules.drop k).map (fun r => r.map (· + (n : Int))) := by
  induction n generalizing cfg with
  | zero =>
    simp [System5.nSteps] at h
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [← h]
    simp
  | succ k ih =>
    rw [System5.nSteps_succ] at h
    cases h_step : System5.step cfg with
    | none => rw [h_step] at h; cases h
    | some cfg₁ =>
      rw [h_step] at h
      simp only [Option.bind_some] at h
      obtain ⟨k₁, h_k₁_le, h_rules_k₁⟩ := ih cfg₁ h
      obtain ⟨j, _, h_rules_j⟩ := System5_step_rules_drop_inc cfg cfg₁ h_step
      refine ⟨j + k₁, by omega, ?_⟩
      rw [h_rules_k₁, h_rules_j]
      rw [← List.map_drop, List.drop_drop, List.map_map]
      apply List.map_congr_left
      intro r _
      show (r.map (· + 1)).map (· + (k : Int)) = r.map (· + ((k + 1 : Nat) : Int))
      rw [List_Int_map_add_compose]
      apply List.map_congr_left
      intro x _
      show x + (1 + (k : Int)) = x + ((k + 1 : Nat) : Int)
      push_cast
      omega

/-- **Iter 968: multi-step all-P-step rules form**.  When every
    intermediate System5 step is a P-step (`0 ∈ bag.map(·-1)`), the
    trajectory drops *exactly* `n` rules (i.e., `k = n` in
    `System5_nSteps_rules_form`).  Removes the existential `k`,
    giving the precise per-step relationship: each P-step pops one
    rule, total drop equals total step count. -/
theorem System5_nSteps_rules_pstep
    (cfg cfg' : System5Config) (n : Nat)
    (h : System5.nSteps cfg n = some cfg')
    (h_pstep : ∀ k < n, ∀ cfg_k, System5.nSteps cfg k = some cfg_k
              → 0 ∈ cfg_k.bag.map (· - 1)) :
    cfg'.rules = (cfg.rules.drop n).map (fun r => r.map (· + (n : Int))) := by
  induction n generalizing cfg with
  | zero =>
    simp [System5.nSteps] at h
    rw [← h]; simp
  | succ k ih =>
    rw [System5.nSteps_succ] at h
    cases h_step : System5.step cfg with
    | none => rw [h_step] at h; cases h
    | some cfg₁ =>
      rw [h_step] at h
      simp only [Option.bind_some] at h
      have h_zero_0 : 0 ∈ cfg.bag.map (· - 1) :=
        h_pstep 0 (Nat.zero_lt_succ _) cfg rfl
      have h_rules_step : cfg₁.rules
                        = (cfg.rules.drop 1).map (fun r => r.map (· + 1)) :=
        System5_step_rules_pstep cfg cfg₁ h_step h_zero_0
      have h_pstep' : ∀ j < k, ∀ cfg_j, System5.nSteps cfg₁ j = some cfg_j
                    → 0 ∈ cfg_j.bag.map (· - 1) := by
        intro j h_j cfg_j h_j_eq
        have : System5.nSteps cfg (j + 1) = some cfg_j := by
          rw [System5.nSteps_succ, h_step]
          simp only [Option.bind_some]
          exact h_j_eq
        exact h_pstep (j + 1) (by omega) cfg_j this
      have h_ih := ih cfg₁ h h_pstep'
      rw [h_ih, h_rules_step]
      rw [← List.map_drop, List.drop_drop, List.map_map]
      rw [show 1 + k = k + 1 from Nat.add_comm 1 k]
      apply List.map_congr_left
      intro r _
      show (r.map (· + 1)).map (· + (k : Int))
        = r.map (· + ((k + 1 : Nat) : Int))
      rw [List_Int_map_add_compose]
      apply List.map_congr_left
      intro x _
      show x + (1 + (k : Int)) = x + ((k + 1 : Nat) : Int)
      push_cast
      omega

/-- System 5 analog: once `cfg.bag = []` or `cfg.rules = []`,
    `System5.nSteps cfg (n+1) = none`. -/
theorem System5_halted_nSteps_succ_eq_none (cfg : System5Config) (n : Nat)
    (h : cfg.bag = [] ∨ cfg.rules = []) :
    System5.nSteps cfg (n + 1) = none := by
  rw [System5.nSteps_succ, (System5_step_none_iff cfg).mpr h]
  rfl

/-- Generalisation: for any `n ≥ 1`, `nSteps haltedCfg n = none`. -/
theorem System5_halted_nSteps_eq_none (cfg : System5Config) (n : Nat)
    (h : cfg.bag = [] ∨ cfg.rules = []) (h_n : 1 ≤ n) :
    System5.nSteps cfg n = none := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact System5_halted_nSteps_succ_eq_none cfg m h

/-- System 5 analog of `CTS_nSteps_none_decompose`: if `System5.nSteps
    cfg n = none`, then some intermediate state at step `k < n` is
    halted (`bag = [] ∨ rules = []`). -/
theorem System5_nSteps_none_decompose (cfg : System5Config) (n : Nat)
    (h : System5.nSteps cfg n = none) :
    ∃ k < n, ∃ cfg', System5.nSteps cfg k = some cfg'
                    ∧ (cfg'.bag = [] ∨ cfg'.rules = []) := by
  induction n generalizing cfg with
  | zero => simp [System5.nSteps] at h
  | succ m ih =>
    rw [System5.nSteps_succ] at h
    by_cases h_halt_cfg : cfg.bag = [] ∨ cfg.rules = []
    · refine ⟨0, by omega, cfg, ?_, h_halt_cfg⟩
      rfl
    · have h_step_some : ∃ cfg', System5.step cfg = some cfg' := by
        cases h_step : System5.step cfg with
        | none =>
          exact absurd ((System5_step_none_iff cfg).mp h_step) h_halt_cfg
        | some cfg' => exact ⟨cfg', rfl⟩
      obtain ⟨cfg', h_step_eq⟩ := h_step_some
      rw [h_step_eq] at h
      simp at h
      obtain ⟨k', h_k', cfg_h, h_n', h_halt⟩ := ih cfg' h
      refine ⟨k' + 1, by omega, cfg_h, ?_, h_halt⟩
      rw [System5.nSteps_succ, h_step_eq]
      exact h_n'

/-- System 5 reverse direction: reaching a halted state at step k
    implies `nSteps cfg (k+1) = none`. -/
theorem System5_nSteps_none_of_reaches_halted
    (cfg cfg' : System5Config) (k : Nat)
    (h_n : System5.nSteps cfg k = some cfg')
    (h_halt : cfg'.bag = [] ∨ cfg'.rules = []) :
    System5.nSteps cfg (k + 1) = none := by
  rw [System5.nSteps_add, h_n]
  show System5.nSteps cfg' 1 = none
  exact System5_halted_nSteps_succ_eq_none cfg' 0 h_halt

/-- **System 5 halts ↔ reaches halted**: clean iff form. -/
theorem System5_nSteps_halts_iff_reaches_halted (cfg : System5Config) :
    (∃ n, System5.nSteps cfg n = none) ↔
    ∃ k cfg', System5.nSteps cfg k = some cfg'
              ∧ (cfg'.bag = [] ∨ cfg'.rules = []) := by
  constructor
  · intro ⟨n, h⟩
    obtain ⟨k, _, cfg', h_n, h_halt⟩ := System5_nSteps_none_decompose cfg n h
    exact ⟨k, cfg', h_n, h_halt⟩
  · intro ⟨k, cfg', h_n, h_halt⟩
    exact ⟨k + 1, System5_nSteps_none_of_reaches_halted cfg cfg' k h_n h_halt⟩

/-- A System 5 cfg halts iff `nSteps` returns `none` for some budget. -/
def System5.Halts (cfg : System5Config) : Prop :=
  ∃ n, System5.nSteps cfg n = none

/-- Trivial halting witness: empty bag ⟹ halts in one step. -/
theorem System5.Halts_of_empty_bag (cfg : System5Config) (h : cfg.bag = []) :
    System5.Halts cfg :=
  ⟨1, by rw [System5.nSteps_one]; exact (System5_step_none_iff cfg).mpr (Or.inl h)⟩

/-- Trivial halting witness: empty rules ⟹ halts in one step. -/
theorem System5.Halts_of_empty_rules (cfg : System5Config) (h : cfg.rules = []) :
    System5.Halts cfg :=
  ⟨1, by rw [System5.nSteps_one]; exact (System5_step_none_iff cfg).mpr (Or.inr h)⟩

/-- **System5 Halts step-pred**: backward Halts propagation under
    stepping.  Parallel of `CTS_Halts_step_pred`. -/
theorem System5_Halts_step_pred
    (cfg cfg' : System5Config) (h_step : System5.step cfg = some cfg')
    (h : System5.Halts cfg') :
    System5.Halts cfg := by
  obtain ⟨n, h_n⟩ := h
  refine ⟨n + 1, ?_⟩
  rw [System5.nSteps_succ, h_step]
  exact h_n

/-- **System5 Halts step-succ**: forward Halts propagation under
    stepping.  Parallel of `CTS_Halts_step_succ`. -/
theorem System5_Halts_step_succ
    (cfg cfg' : System5Config) (h_step : System5.step cfg = some cfg')
    (h : System5.Halts cfg) :
    System5.Halts cfg' := by
  obtain ⟨n, h_n⟩ := h
  cases n with
  | zero =>
    simp [System5.nSteps_zero] at h_n
  | succ k =>
    rw [System5.nSteps_succ, h_step] at h_n
    exact ⟨k, h_n⟩

/-- **System5 Halts step-iff**: biconditional combining step-pred
    and step-succ. -/
theorem System5_Halts_step_iff
    (cfg cfg' : System5Config) (h_step : System5.step cfg = some cfg') :
    System5.Halts cfg ↔ System5.Halts cfg' :=
  ⟨System5_Halts_step_succ cfg cfg' h_step, System5_Halts_step_pred cfg cfg' h_step⟩

/-- **System5 Halts nSteps-pred**: backward Halts propagation via
    multi-step. -/
theorem System5_Halts_nSteps_pred
    (cfg : System5Config) (n : Nat) (r : System5Config)
    (h_n : System5.nSteps cfg n = some r) (h : System5.Halts r) :
    System5.Halts cfg := by
  induction n generalizing cfg with
  | zero =>
    rw [System5.nSteps_zero] at h_n
    injection h_n with h_eq
    rw [h_eq]
    exact h
  | succ k ih =>
    rw [System5.nSteps_succ] at h_n
    cases h_step : System5.step cfg with
    | none => rw [h_step] at h_n; cases h_n
    | some cfg₁ =>
      rw [h_step] at h_n
      simp at h_n
      exact System5_Halts_step_pred cfg cfg₁ h_step (ih cfg₁ h_n)

/-- **System5 Halts nSteps-succ**: forward Halts propagation via
    multi-step. -/
theorem System5_Halts_nSteps_succ
    (cfg : System5Config) (n : Nat) (r : System5Config)
    (h_n : System5.nSteps cfg n = some r) (h : System5.Halts cfg) :
    System5.Halts r := by
  induction n generalizing cfg with
  | zero =>
    rw [System5.nSteps_zero] at h_n
    injection h_n with h_eq
    rw [← h_eq]
    exact h
  | succ k ih =>
    rw [System5.nSteps_succ] at h_n
    cases h_step : System5.step cfg with
    | none => rw [h_step] at h_n; cases h_n
    | some cfg₁ =>
      rw [h_step] at h_n
      simp at h_n
      exact ih cfg₁ h_n (System5_Halts_step_succ cfg cfg₁ h_step h)

/-- **System5 Halts nSteps-iff**: biconditional. -/
theorem System5_Halts_nSteps_iff
    (cfg : System5Config) (n : Nat) (r : System5Config)
    (h_n : System5.nSteps cfg n = some r) :
    System5.Halts cfg ↔ System5.Halts r :=
  ⟨System5_Halts_nSteps_succ cfg n r h_n, System5_Halts_nSteps_pred cfg n r h_n⟩

/-- **System5 nSteps compose**: chain `nSteps` trajectories via
    `System5.nSteps_add`. -/
theorem System5_nSteps_some_compose
    (cfg mid : System5Config) (n m : Nat) (result : System5Config)
    (h_n : System5.nSteps cfg n = some mid)
    (h_m : System5.nSteps mid m = some result) :
    System5.nSteps cfg (n + m) = some result := by
  rw [System5.nSteps_add, h_n]
  exact h_m

/-- **`System5_Halts_iff_reaches_halted` (iter 620)**: clean
    `Halts`-form of `System5_nSteps_halts_iff_reaches_halted`.
    `System5.Halts cfg ↔ ∃ k cfg', cfg evolves into cfg' in k
    steps and cfg' is halted (empty bag or empty rules)`.  Direct
    via the def unfold. -/
theorem System5_Halts_iff_reaches_halted (cfg : System5Config) :
    System5.Halts cfg ↔
    ∃ k cfg', System5.nSteps cfg k = some cfg'
              ∧ (cfg'.bag = [] ∨ cfg'.rules = []) :=
  System5_nSteps_halts_iff_reaches_halted cfg

/-- **`System5_not_Halts_imp_step_some` (iter 620)**: contrapositive
    flavour — if `cfg` does NOT halt, then `step cfg` is `some`
    (since `step = none` implies halt in 1 step).  Useful to extract
    a successor cfg in non-halting trajectories. -/
theorem System5_not_Halts_imp_step_some (cfg : System5Config)
    (h : ¬ System5.Halts cfg) :
    ∃ cfg', System5.step cfg = some cfg' := by
  cases h_step : System5.step cfg with
  | none =>
    exfalso
    apply h
    exact ⟨1, by rw [System5.nSteps_one]; exact h_step⟩
  | some cfg' => exact ⟨cfg', rfl⟩

/-- **System5 not-Halts step-succ**: contrapositive of
    `System5_Halts_step_pred`.  Forward non-halt propagation. -/
theorem System5_not_Halts_step_succ
    (cfg cfg' : System5Config) (h_step : System5.step cfg = some cfg')
    (h : ¬ System5.Halts cfg) :
    ¬ System5.Halts cfg' :=
  fun h_halt => h (System5_Halts_step_pred cfg cfg' h_step h_halt)

/-- **System5 not-Halts nSteps-succ**: nSteps version. -/
theorem System5_not_Halts_nSteps_succ
    (cfg : System5Config) (n : Nat) (r : System5Config)
    (h_n : System5.nSteps cfg n = some r) (h : ¬ System5.Halts cfg) :
    ¬ System5.Halts r :=
  fun h_halt => h (System5_Halts_nSteps_pred cfg n r h_n h_halt)

/-- **System5 self-loop nSteps stays at cfg**: if `step cfg = some cfg`,
    then `nSteps cfg n = some cfg` for any n. -/
theorem System5_self_loop_nSteps_self
    (cfg : System5Config) (h_self : System5.step cfg = some cfg) (n : Nat) :
    System5.nSteps cfg n = some cfg := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [System5.nSteps_succ, h_self]
    simpa using ih

/-- **System5 self-loop ⇒ not-Halts**: a System5 cfg with a self-step
    cannot have `System5.Halts`. -/
theorem System5_self_loop_not_halts
    (cfg : System5Config) (h_self : System5.step cfg = some cfg) :
    ¬ System5.Halts cfg := by
  intro ⟨n, h_n⟩
  rw [System5_self_loop_nSteps_self cfg h_self n] at h_n
  cases h_n

/-- **System5 step-none nSteps succ eq none**: `step cfg = none →
    nSteps cfg (n+1) = none`. -/
theorem System5_step_none_nSteps_succ_eq_none
    (cfg : System5Config) (h : System5.step cfg = none) (n : Nat) :
    System5.nSteps cfg (n + 1) = none := by
  rw [System5.nSteps_succ, h]
  rfl

/-- **System5 nSteps past step-none = none**: once a trajectory
    reaches a step-none cfg, any further `k ≥ 1` steps yield `none`. -/
theorem System5_nSteps_past_step_none_eq_none
    (cfg : System5Config) (n : Nat) (result : System5Config)
    (h_n : System5.nSteps cfg n = some result) (h_step : System5.step result = none)
    (k : Nat) (h_k : k ≥ 1) :
    System5.nSteps cfg (n + k) = none := by
  rw [System5.nSteps_add, h_n]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simpa using System5_step_none_nSteps_succ_eq_none result h_step m

/-- **System5 nSteps intermediate retrieval**: given `nSteps` results
    at `n₁ ≤ n₂`, the in-between trajectory is `nSteps r₁ (n₂ - n₁) =
    some r₂`. -/
theorem System5_nSteps_intermediate
    (cfg r₁ r₂ : System5Config) (n₁ n₂ : Nat) (h_le : n₁ ≤ n₂)
    (h₁ : System5.nSteps cfg n₁ = some r₁)
    (h₂ : System5.nSteps cfg n₂ = some r₂) :
    System5.nSteps r₁ (n₂ - n₁) = some r₂ := by
  have h_sum : n₁ + (n₂ - n₁) = n₂ := by omega
  rw [← h_sum, System5.nSteps_add, h₁] at h₂
  exact h₂

/-- **System5 step-none implies Halts**: trivial halt witness via
    `nSteps cfg 1 = step cfg = none`. -/
theorem System5_step_none_imp_Halts (cfg : System5Config)
    (h : System5.step cfg = none) :
    System5.Halts cfg :=
  ⟨1, by rw [System5.nSteps_one]; exact h⟩

/-- **System5 nSteps intermediate Halts retrieval**: if a trajectory
    ends at a step-none cfg, any earlier intermediate also halts. -/
theorem System5_nSteps_intermediate_Halts
    (cfg r₁ r₂ : System5Config) (n₁ n₂ : Nat) (h_le : n₁ ≤ n₂)
    (h₁ : System5.nSteps cfg n₁ = some r₁)
    (h₂ : System5.nSteps cfg n₂ = some r₂) (h_step_r₂ : System5.step r₂ = none) :
    System5.Halts r₁ :=
  System5_Halts_nSteps_pred r₁ (n₂ - n₁) r₂
    (System5_nSteps_intermediate cfg r₁ r₂ n₁ n₂ h_le h₁ h₂)
    (System5_step_none_imp_Halts r₂ h_step_r₂)

/-- **System5 periodic-orbit nSteps stays at cfg modulo k iterations**:
    if `nSteps cfg p = some cfg`, then `nSteps cfg (k * p) = some cfg`
    for all k.  Generalises self-loop to arbitrary period. -/
theorem System5_periodic_nSteps_iter
    (cfg : System5Config) (p : Nat)
    (h_period : System5.nSteps cfg p = some cfg) (k : Nat) :
    System5.nSteps cfg (k * p) = some cfg := by
  induction k with
  | zero => rw [Nat.zero_mul]; rfl
  | succ k ih =>
    rw [Nat.succ_mul, System5.nSteps_add, ih]
    simpa using h_period

/-- **`System5_Halts_of_exists_step_none` (iter 624)**: backward
    direction of the step-none witness characterisation — if some
    intermediate cfg `r` reached after `k` steps has `step r = none`,
    then the original cfg halts.  Composes `nSteps_pred` with
    `step_none_imp_Halts`. -/
theorem System5_Halts_of_exists_step_none
    (cfg : System5Config)
    (h : ∃ k r, System5.nSteps cfg k = some r ∧ System5.step r = none) :
    System5.Halts cfg := by
  obtain ⟨k, r, h_n, h_step⟩ := h
  exact System5_Halts_nSteps_pred cfg k r h_n
    (System5_step_none_imp_Halts r h_step)

/-- **System5 step-none witness extractor**: from `System5.Halts cfg`,
    extract `k`, `r` such that `nSteps cfg k = some r ∧ step r = none`.
    Halt-time extractor; uses `find_min_or_none`. -/
theorem System5_Halts_extract_step_none_witness
    (cfg : System5Config) (h : System5.Halts cfg) :
    ∃ k r, System5.nSteps cfg k = some r ∧ System5.step r = none := by
  obtain ⟨N, hN⟩ := h
  rcases find_min_or_none (fun n => System5.nSteps cfg n = none) N with
    ⟨n, _h_le, h_pn, h_min⟩ | h_none
  · cases n with
    | zero =>
      simp [System5.nSteps_zero] at h_pn
    | succ k =>
      cases h_k : System5.nSteps cfg k with
      | none => exact absurd h_k (h_min k (Nat.lt_succ_self k))
      | some r =>
        refine ⟨k, r, h_k, ?_⟩
        have h_eq : System5.nSteps cfg (k + 1) = System5.step r := by
          rw [System5.nSteps_add, h_k]
          exact System5.nSteps_one r
        rw [h_eq] at h_pn
        exact h_pn
  · exact absurd hN (h_none N (Nat.le_refl _))

/-- **System5 periodic orbit ⇒ not-Halts**: a config with a periodic
    orbit (period ≥ 1) cannot halt.  Uses `System5_Halts_extract_step_
    none_witness` plus `System5_nSteps_past_step_none_eq_none`. -/
theorem System5_periodic_not_halts
    (cfg : System5Config) (p : Nat) (h_pos : p ≥ 1)
    (h_period : System5.nSteps cfg p = some cfg) :
    ¬ System5.Halts cfg := by
  intro h_halts
  obtain ⟨N, r, h_n, h_step_none⟩ := System5_Halts_extract_step_none_witness cfg h_halts
  have h_iter := System5_periodic_nSteps_iter cfg p h_period (N + 1)
  have h_ge : (N + 1) * p ≥ N + 1 := by
    have : (N + 1) * 1 ≤ (N + 1) * p := Nat.mul_le_mul_left _ h_pos
    omega
  obtain ⟨j, hj_pos, h_eq⟩ : ∃ j, j ≥ 1 ∧ (N + 1) * p = N + j :=
    ⟨(N + 1) * p - N, by omega, by omega⟩
  rw [h_eq] at h_iter
  rw [System5_nSteps_past_step_none_eq_none cfg N r h_n h_step_none j hj_pos]
    at h_iter
  cases h_iter

/-- **`System5_Halts_iff_exists_step_none_witness` (iter 626)**:
    biconditional combining iter 624's backward direction with iter
    625's extractor.  `System5.Halts cfg ↔ ∃ k r, nSteps cfg k = some r
    ∧ step r = none`.  The most useful iff form for halt analysis. -/
theorem System5_Halts_iff_exists_step_none_witness (cfg : System5Config) :
    System5.Halts cfg ↔
    ∃ k r, System5.nSteps cfg k = some r ∧ System5.step r = none :=
  ⟨System5_Halts_extract_step_none_witness cfg,
   System5_Halts_of_exists_step_none cfg⟩

/-- **`System5_no_period_of_Halts` (iter 626)**: contrapositive of
    `System5_periodic_not_halts` — halting cfgs have no periodic
    orbit at any positive period.  Useful for ruling out cycles in
    halting trajectories. -/
theorem System5_no_period_of_Halts
    (cfg : System5Config) (h : System5.Halts cfg)
    (p : Nat) (h_pos : p ≥ 1) :
    System5.nSteps cfg p ≠ some cfg :=
  fun h_period => System5_periodic_not_halts cfg p h_pos h_period h

/-- **System5 → BiTM step-to-nSteps emulation lifting**: generic-`tm`
    target version of `step_to_nSteps_emulation_system5_to_system4`.
    Given per-step System5 → tm emulator with `n ≥ 1` budget, lifts
    to multi-step. -/
theorem step_to_nSteps_emulation_system5_to_tm
    (tm : Machine) (encode : System5Config → Config)
    (h_emulate : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (encode cfg) n = some (encode cfg'))
    (cfg : System5Config) (k : Nat) (result : System5Config)
    (h_steps : System5.nSteps cfg k = some result) :
    ∃ m, nSteps tm (encode cfg) m = some (encode result) := by
  induction k generalizing cfg with
  | zero =>
    rw [System5.nSteps_zero] at h_steps
    injection h_steps with h_eq
    refine ⟨0, ?_⟩
    rw [h_eq]
    rfl
  | succ k ih =>
    rw [System5.nSteps_succ] at h_steps
    cases h_step : System5.step cfg with
    | none => rw [h_step] at h_steps; cases h_steps
    | some cfg₁ =>
      rw [h_step] at h_steps
      simp at h_steps
      obtain ⟨n, _hn_pos, h_n⟩ := h_emulate cfg cfg₁ h_step
      obtain ⟨m', h_m'⟩ := ih cfg₁ h_steps
      exact ⟨n + m',
        BiTM_nSteps_some_compose tm (encode cfg) (encode cfg₁)
          n m' (encode result) h_n h_m'⟩

/-- **System5 → BiTM halt-preservation under step emulation**: composes
    iter 433's lifting with the System5 step-none witness extractor +
    `BiTM_Halts_nSteps_pred`. -/
theorem system5Halts_imp_tmHalts_under_step_emulation
    (tm : Machine) (encode : System5Config → Config)
    (h_step_emulate : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (encode cfg) n = some (encode cfg'))
    (h_halt_preserve : ∀ cfg, System5.step cfg = none → Halts tm (encode cfg))
    (cfg : System5Config) (h : System5.Halts cfg) :
    Halts tm (encode cfg) := by
  obtain ⟨k, r, h_n, h_step_none⟩ := System5_Halts_extract_step_none_witness cfg h
  obtain ⟨m, h_m⟩ := step_to_nSteps_emulation_system5_to_tm
    tm encode h_step_emulate cfg k r h_n
  exact BiTM_Halts_nSteps_pred tm (encode cfg) m (encode r) h_m
    (h_halt_preserve r h_step_none)

/-- **`system5_not_Halts_of_tm_not_Halts` (iter 630)**: contrapositive
    of `system5Halts_imp_tmHalts_under_step_emulation` — if the
    encoded tm cfg does NOT halt, then the System5 cfg does NOT halt
    either.  Useful when transferring non-halting facts (e.g.
    `not_halts_wolfram23_init`) backwards through an emulation. -/
theorem system5_not_Halts_of_tm_not_Halts
    (tm : Machine) (encode : System5Config → Config)
    (h_step_emulate : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (encode cfg) n = some (encode cfg'))
    (h_halt_preserve : ∀ cfg, System5.step cfg = none → Halts tm (encode cfg))
    (cfg : System5Config) (h : ¬ Halts tm (encode cfg)) :
    ¬ System5.Halts cfg :=
  fun h_halts => h (system5Halts_imp_tmHalts_under_step_emulation tm encode
    h_step_emulate h_halt_preserve cfg h_halts)

/-- **`System5_step_or_halted` (iter 643)**: every System5 cfg is
    either halted (bag/rules empty) or admits a step.  Direct from
    `System5_step_none_iff`. -/
theorem System5_step_or_halted (cfg : System5Config) :
    (cfg.bag = [] ∨ cfg.rules = []) ∨ ∃ cfg', System5.step cfg = some cfg' := by
  cases h_step : System5.step cfg with
  | none => left; exact (System5_step_none_iff cfg).mp h_step
  | some cfg' => right; exact ⟨cfg', rfl⟩

/-- **`System5_Halts_step_decompose` (iter 643)**: any halting System5
    cfg is either at halt position (bag/rules empty) or steps to
    another halting cfg. -/
theorem System5_Halts_step_decompose
    (cfg : System5Config) (h : System5.Halts cfg) :
    (cfg.bag = [] ∨ cfg.rules = []) ∨
    ∃ cfg', System5.step cfg = some cfg' ∧ System5.Halts cfg' := by
  rcases System5_step_or_halted cfg with h_halt | ⟨cfg', h_step⟩
  · left; exact h_halt
  · right
    exact ⟨cfg', h_step, (System5_Halts_step_iff cfg cfg' h_step).mp h⟩

/-- **`System5_Halts_step_decompose_active` (iter 643)**: when both
    bag and rules are non-empty, the step branch is forced. -/
theorem System5_Halts_step_decompose_active
    (cfg : System5Config) (h_bag : cfg.bag ≠ []) (h_rules : cfg.rules ≠ [])
    (h_halts : System5.Halts cfg) :
    ∃ cfg', System5.step cfg = some cfg' ∧ System5.Halts cfg' := by
  rcases System5_Halts_step_decompose cfg h_halts with h_halt | h_step
  · rcases h_halt with hb | hr
    · exact absurd hb h_bag
    · exact absurd hr h_rules
  · exact h_step

/-- **`System5_Halts_induction` (iter 643)**: strong induction over
    halting System5 cfgs.  Any `P` satisfying the halt-condition base
    (`bag = [] ∨ rules = []`) and backwards-step preservation holds on
    all halting cfgs. -/
theorem System5_Halts_induction (P : System5Config → Prop)
    (h_halt : ∀ cfg, (cfg.bag = [] ∨ cfg.rules = []) → P cfg)
    (h_back : ∀ cfg cfg', System5.step cfg = some cfg' →
              System5.Halts cfg' → P cfg' → P cfg)
    (cfg : System5Config) (h : System5.Halts cfg) : P cfg := by
  obtain ⟨n, h_n⟩ := h
  induction n generalizing cfg with
  | zero => simp [System5.nSteps] at h_n
  | succ m ih =>
    cases h_step : System5.step cfg with
    | none =>
      exact h_halt cfg ((System5_step_none_iff cfg).mp h_step)
    | some cfg' =>
      have h_n' : System5.nSteps cfg' m = none := by
        rw [System5.nSteps_succ, h_step] at h_n
        exact h_n
      have h_he' : System5.Halts cfg' := ⟨m, h_n'⟩
      exact h_back cfg cfg' h_step h_he' (ih cfg' h_n')

/-- **System5 → BiTM step-to-nSteps emulation positive bound**:
    System5 → tm analog of `step_to_nSteps_emulation_system5_to_
    system4_pos`.  Required for BiTM-side chain composition. -/
theorem step_to_nSteps_emulation_system5_to_tm_pos
    (tm : Machine) (encode : System5Config → Config)
    (h_emulate : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (encode cfg) n = some (encode cfg'))
    (cfg : System5Config) (k : Nat) (h_pos : k ≥ 1) (result : System5Config)
    (h_steps : System5.nSteps cfg k = some result) :
    ∃ m, m ≥ 1 ∧ nSteps tm (encode cfg) m = some (encode result) := by
  cases k with
  | zero => omega
  | succ k =>
    rw [System5.nSteps_succ] at h_steps
    cases h_step : System5.step cfg with
    | none => rw [h_step] at h_steps; cases h_steps
    | some cfg₁ =>
      rw [h_step] at h_steps
      simp at h_steps
      obtain ⟨n, hn_pos, h_n⟩ := h_emulate cfg cfg₁ h_step
      obtain ⟨m', h_m'⟩ := step_to_nSteps_emulation_system5_to_tm
        tm encode h_emulate cfg₁ k result h_steps
      exact ⟨n + m', by omega,
        BiTM_nSteps_some_compose tm (encode cfg) (encode cfg₁)
          n m' (encode result) h_n h_m'⟩

/-- **`System5_nSteps_one_pure_decrement` (iter 677)**: nSteps form
    of pure decrement.  Combines `System5.nSteps_one`, `_step_some_iff`,
    and `_step_pure_decrement`. -/
theorem System5_nSteps_one_pure_decrement (cfg : System5Config)
    (h_bag : cfg.bag ≠ []) (h_rules : cfg.rules ≠ [])
    (h_zero : 0 ∉ cfg.bag.map (· - 1)) :
    System5.nSteps cfg 1
      = some { bag := cfg.bag.map (· - 1)
               rules := cfg.rules.map (fun r => r.map (· + 1)) } := by
  rw [System5.nSteps_one]
  obtain ⟨cfg', h_some⟩ := (System5_step_some_iff cfg).mpr ⟨h_bag, h_rules⟩
  obtain ⟨h_b, h_r⟩ := System5_step_pure_decrement cfg cfg' h_some h_bag h_rules h_zero
  rw [h_some]
  show (some ⟨cfg'.bag, cfg'.rules⟩ : Option System5Config) = _
  rw [h_b, h_r]

/-- **`System5_nSteps_one_pop_rule` (iter 677)**: nSteps form of rule
    pop.  When `0 ∈ cfg.bag.map (· - 1)`, `nSteps cfg 1` pops the next
    incremented rule and XOR-merges into `(bag.map (·-1)).erase 0`. -/
theorem System5_nSteps_one_pop_rule (cfg : System5Config)
    (h_bag : cfg.bag ≠ []) (h_rules : cfg.rules ≠ [])
    (h_zero : 0 ∈ cfg.bag.map (· - 1)) :
    ∃ (nextRule : List Int) (restRules : List (List Int)),
      cfg.rules.map (fun r => r.map (· + 1)) = nextRule :: restRules ∧
      System5.nSteps cfg 1
        = some { bag := xorMerge ((cfg.bag.map (· - 1)).erase 0) nextRule
                 rules := restRules } := by
  rw [System5.nSteps_one]
  obtain ⟨cfg', h_some⟩ := (System5_step_some_iff cfg).mpr ⟨h_bag, h_rules⟩
  obtain ⟨nextRule, restRules, h_split, h_b, h_r⟩ :=
    System5_step_pop_rule cfg cfg' h_some h_bag h_rules h_zero
  refine ⟨nextRule, restRules, h_split, ?_⟩
  rw [h_some]
  show (some ⟨cfg'.bag, cfg'.rules⟩ : Option System5Config) = _
  rw [h_b, h_r]

/-- **`System5_nSteps_k_pure_decrement` (iter 677)**: multi-step pure
    decrement.  If no value in `{1, ..., k}` appears in `cfg.bag`, then
    `k` consecutive System 5 steps are pure decrements.  Workhorse for
    `cy2s5.pl`-style System 5 trajectories between successive
    CTS-step encodings. -/
theorem System5_nSteps_k_pure_decrement (cfg : System5Config) (k : Nat)
    (h_bag : cfg.bag ≠ []) (h_rules : cfg.rules ≠ [])
    (h_no_small : ∀ j : Nat, 1 ≤ j → j ≤ k → (↑j : Int) ∉ cfg.bag) :
    ∃ cfg', System5.nSteps cfg k = some cfg'
            ∧ cfg'.bag = cfg.bag.map (· - (k : Int))
            ∧ cfg'.rules = cfg.rules.map (fun r => r.map (· + (k : Int))) := by
  induction k with
  | zero =>
    refine ⟨cfg, System5.nSteps_zero cfg, ?_, ?_⟩
    · simp
    · simp
  | succ k ih =>
    have h_no_small_k : ∀ j : Nat, 1 ≤ j → j ≤ k → (↑j : Int) ∉ cfg.bag :=
      fun j h1 h2 => h_no_small j h1 (Nat.le_succ_of_le h2)
    obtain ⟨cfg_k, h_nsteps_k, h_bag_k, h_rules_k⟩ := ih h_no_small_k
    have h_bag_k_ne : cfg_k.bag ≠ [] := by
      rw [h_bag_k]; intro h; rw [List.map_eq_nil_iff] at h; exact h_bag h
    have h_rules_k_ne : cfg_k.rules ≠ [] := by
      rw [h_rules_k]; intro h; rw [List.map_eq_nil_iff] at h; exact h_rules h
    have h_zero_k : 0 ∉ cfg_k.bag.map (· - 1) := by
      rw [h_bag_k, ← List_Int_map_sub_succ]
      intro h_mem
      rw [List.mem_map] at h_mem
      obtain ⟨x, h_x_mem, h_x_eq⟩ := h_mem
      have h_x : x = ((k + 1 : Nat) : Int) := by omega
      rw [h_x] at h_x_mem
      exact h_no_small (k + 1) (by omega) (by omega) h_x_mem
    have h_one_step :=
      System5_nSteps_one_pure_decrement cfg_k h_bag_k_ne h_rules_k_ne h_zero_k
    refine ⟨⟨cfg_k.bag.map (· - 1), cfg_k.rules.map (fun r => r.map (· + 1))⟩,
            ?_, ?_, ?_⟩
    · rw [System5.nSteps_add, h_nsteps_k]
      exact h_one_step
    · show cfg_k.bag.map (· - 1) = cfg.bag.map (· - ((k + 1 : Nat) : Int))
      rw [h_bag_k, ← List_Int_map_sub_succ]
    · show cfg_k.rules.map (fun r => r.map (· + 1))
        = cfg.rules.map (fun r => r.map (· + ((k + 1 : Nat) : Int)))
      rw [h_rules_k, List.map_map]
      congr 1
      funext r
      simp only [Function.comp]
      rw [← List_Int_map_add_succ]

/-- **`System5_nSteps_one_empty_rule_pop` (iter 678)**: System5 step
    with empty-head rule + `1 ∈ bag` — pure decrement-erase on the bag
    (empty rule contributes nothing via `xorMerge_nil`), advance rules
    to tail (incremented).  Specialises `System5_nSteps_one_pop_rule`
    to the empty-rule case relevant to `AllEmptyAppendants` CTS
    dynamics. -/
theorem System5_nSteps_one_empty_rule_pop
    (cfg : System5Config) (rest : List (List Int))
    (h_rules : cfg.rules = [] :: rest)
    (h_bag : cfg.bag ≠ [])
    (h_zero : 0 ∈ cfg.bag.map (· - 1)) :
    System5.nSteps cfg 1
      = some { bag := (cfg.bag.map (· - 1)).erase 0
               rules := rest.map (fun r => r.map (· + 1)) } := by
  have h_rules_ne : cfg.rules ≠ [] := by rw [h_rules]; simp
  obtain ⟨nextRule, restRules, h_split, h_step⟩ :=
    System5_nSteps_one_pop_rule cfg h_bag h_rules_ne h_zero
  have h_split' : cfg.rules.map (fun r => r.map (· + 1))
                 = ([] : List Int) :: rest.map (fun r => r.map (· + 1)) := by
    rw [h_rules]
    show ([] : List Int).map (· + 1) :: rest.map (fun r => r.map (· + 1))
        = ([] : List Int) :: rest.map (fun r => r.map (· + 1))
    rfl
  rw [h_split'] at h_split
  have h_eq : nextRule = [] ∧ restRules = rest.map (fun r => r.map (· + 1)) := by
    constructor
    · exact (List.cons.injEq _ _ _ _).mp h_split |>.1 |>.symm
    · exact (List.cons.injEq _ _ _ _).mp h_split |>.2 |>.symm
  rw [h_step]
  rw [h_eq.1, h_eq.2]
  show (some { bag := xorMerge ((cfg.bag.map (· - 1)).erase 0) []
               rules := rest.map (fun r => r.map (· + 1)) } : Option System5Config)
      = _
  rw [xorMerge_nil]

/-- **`System5_nSteps_decrement_then_pop` (iter 677)**: full per-step
    emulation primitive — `k` pure decrements followed by one rule pop.
    The single-CTS-step emulation primitive for `smith-step-emulation`. -/
theorem System5_nSteps_decrement_then_pop (cfg : System5Config) (k : Nat)
    (h_bag : cfg.bag ≠ []) (h_rules : cfg.rules ≠ [])
    (h_no_small : ∀ j : Nat, 1 ≤ j → j ≤ k → (↑j : Int) ∉ cfg.bag)
    (h_kplus1 : ((k + 1 : Nat) : Int) ∈ cfg.bag) :
    ∃ (nextRule : List Int) (restRules : List (List Int)),
      cfg.rules.map (fun r => r.map (· + ((k + 1 : Nat) : Int)))
        = nextRule :: restRules ∧
      System5.nSteps cfg (k + 1)
        = some { bag := xorMerge ((cfg.bag.map (· - ((k + 1 : Nat) : Int))).erase 0)
                                  nextRule
                 rules := restRules } := by
  obtain ⟨cfg_k, h_nsteps_k, h_bag_k, h_rules_k⟩ :=
    System5_nSteps_k_pure_decrement cfg k h_bag h_rules h_no_small
  have h_bag_k_ne : cfg_k.bag ≠ [] := by
    rw [h_bag_k]; intro h; rw [List.map_eq_nil_iff] at h; exact h_bag h
  have h_rules_k_ne : cfg_k.rules ≠ [] := by
    rw [h_rules_k]; intro h; rw [List.map_eq_nil_iff] at h; exact h_rules h
  have h_zero_k : 0 ∈ cfg_k.bag.map (· - 1) := by
    rw [h_bag_k, ← List_Int_map_sub_succ]
    rw [List.mem_map]
    refine ⟨((k + 1 : Nat) : Int), h_kplus1, ?_⟩
    show (((k + 1 : Nat) : Int) - ((k + 1 : Nat) : Int)) = 0
    omega
  obtain ⟨nextRule, restRules, h_split, h_nsteps_one⟩ :=
    System5_nSteps_one_pop_rule cfg_k h_bag_k_ne h_rules_k_ne h_zero_k
  have h_rules_split :
      cfg.rules.map (fun r => r.map (· + ((k + 1 : Nat) : Int)))
        = nextRule :: restRules := by
    have h_eq : (fun r : List Int => r.map (· + ((k + 1 : Nat) : Int)))
              = (fun r => r.map (· + 1)) ∘ (fun r => r.map (· + (k : Int))) := by
      funext r
      simp only [Function.comp]
      rw [← List_Int_map_add_succ]
    rw [h_eq, ← List.map_map, ← h_rules_k]
    exact h_split
  refine ⟨nextRule, restRules, h_rules_split, ?_⟩
  rw [System5.nSteps_add, h_nsteps_k]
  show System5.nSteps cfg_k 1 = _
  rw [h_nsteps_one]
  congr 1
  show ({ bag := xorMerge ((cfg_k.bag.map (· - 1)).erase 0) nextRule
          rules := restRules } : System5Config) = _
  congr 1
  rw [h_bag_k, ← List_Int_map_sub_succ]

/-- **System 5 `nSteps`-none succ propagation** (analogue of iter
    326).  Direct via `System5.nSteps_add`. -/
theorem System5_nSteps_none_succ
    (cfg : System5Config) (n : Nat)
    (h : System5.nSteps cfg n = none) :
    System5.nSteps cfg (n + 1) = none := by
  rw [System5.nSteps_add, h]
  rfl

/-- **System 5 `nSteps`-none monotone propagation**: once `nSteps cfg
    n = none`, also `= none` for all `m ≥ n`. -/
theorem System5_nSteps_none_propagate
    (cfg : System5Config) (n m : Nat)
    (h_le : n ≤ m) (h_n : System5.nSteps cfg n = none) :
    System5.nSteps cfg m = none := by
  obtain ⟨k, h_k⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  rw [h_k]
  clear h_k h_le m
  induction k with
  | zero => exact h_n
  | succ j ih =>
    rw [show n + (j + 1) = (n + j) + 1 from by omega]
    exact System5_nSteps_none_succ cfg (n + j) ih

/-- **System 5 `nSteps`-some monotonicity** (analogue of iter 362). -/
theorem System5_nSteps_some_le
    (cfg : System5Config) (k n : Nat) (h_le : k ≤ n)
    (result : System5Config) (h : System5.nSteps cfg n = some result) :
    ∃ intermediate, System5.nSteps cfg k = some intermediate := by
  cases h_k : System5.nSteps cfg k with
  | none =>
    have h_n := System5_nSteps_none_propagate cfg k n h_le h_k
    rw [h_n] at h
    cases h
  | some intermediate => exact ⟨intermediate, rfl⟩

/-- **`System5_nSteps_some_decompose` (iter 714)**: sharpens iter 713's
    `_nSteps_some_le` — when `nSteps cfg n = some result` and `k ≤ n`,
    not only does the intermediate at step `k` exist, but `nSteps
    intermediate (n - k) = some result` follows.  Lets downstream code
    split a successful System 5 trajectory at any intermediate step.
    Proof: `_nSteps_some_le` gives the intermediate; `nSteps_add` then
    derives the suffix trajectory. -/
theorem System5_nSteps_some_decompose
    (cfg : System5Config) (k n : Nat) (h_le : k ≤ n)
    (result : System5Config) (h : System5.nSteps cfg n = some result) :
    ∃ intermediate,
      System5.nSteps cfg k = some intermediate
      ∧ System5.nSteps intermediate (n - k) = some result := by
  obtain ⟨intermediate, h_k⟩ := System5_nSteps_some_le cfg k n h_le result h
  refine ⟨intermediate, h_k, ?_⟩
  have h_eq : k + (n - k) = n := by omega
  rw [show n = k + (n - k) from h_eq.symm] at h
  rw [System5.nSteps_add, h_k] at h
  show System5.nSteps intermediate (n - k) = some result
  rw [Option.bind_some] at h
  exact h

/-- **`System5_Halts_imp_nSteps_eventually_none` (iter 551)**:
    System5 analog of iter 549/550.  `System5.Halts cfg` (defined
    as `∃ n, nSteps cfg n = none`) lifts to the eventually-none
    form `∃ N, ∀ k > N, nSteps cfg k = none`.  Proof: decompose the
    `nSteps = none` witness via iter 437's
    `System5_nSteps_none_decompose` to get an intermediate halted
    cfg, then apply iter 443's `System5_nSteps_past_step_none_eq_none`
    to extend to all later step counts. -/
theorem System5_Halts_imp_nSteps_eventually_none (cfg : System5Config)
    (h : System5.Halts cfg) :
    ∃ N, ∀ k, k > N → System5.nSteps cfg k = none := by
  obtain ⟨n, h_n⟩ := h
  obtain ⟨k, _, cfg', h_step, h_halt⟩ :=
    System5_nSteps_none_decompose cfg n h_n
  refine ⟨k, ?_⟩
  intro m h_m
  have h_step_eq : System5.step cfg' = none :=
    (System5_step_none_iff cfg').mpr h_halt
  have h_split : m = k + (m - k) := by omega
  rw [h_split]
  exact System5_nSteps_past_step_none_eq_none cfg k cfg' h_step h_step_eq
    (m - k) (by omega)


/-- **`System5_Halts_exact_step_form` (iter 554)**: System5 analog
    of iter 553.  For any halting System5 cfg, there's an exact
    step `N` reaching a halted cfg (`bag = [] ∨ rules = []`), and
    beyond `N` all nSteps return `none`.  Combines
    `System5_nSteps_halts_iff_reaches_halted` (existence) with
    `System5_halted_nSteps_eq_none` (post-halt-is-none) via
    `System5.nSteps_add`. -/
theorem System5_Halts_exact_step_form (cfg : System5Config)
    (h : System5.Halts cfg) :
    ∃ N result, System5.nSteps cfg N = some result ∧
                (result.bag = [] ∨ result.rules = []) ∧
                ∀ k, k > N → System5.nSteps cfg k = none := by
  obtain ⟨N, result, h_n, h_halt⟩ :=
    (System5_nSteps_halts_iff_reaches_halted cfg).mp h
  refine ⟨N, result, h_n, h_halt, ?_⟩
  intro k h_k
  have h_split : k = N + (k - N) := by omega
  rw [h_split, System5.nSteps_add, h_n]
  show System5.nSteps result (k - N) = none
  exact System5_halted_nSteps_eq_none result (k - N) h_halt (by omega)

/-- **`System5_Halts_iff_exact_step_witness` (iter 561)**: System5
    analog of iter 558/559/560.  `System5.Halts cfg ↔ ∃ exact halt-step
    witness with eventually-none beyond`.  Forward direction is iter
    554; reverse uses `System5_nSteps_none_of_reaches_halted` to
    derive `nSteps cfg (N+1) = none`, witnessing the existential
    halt-shape `System5.Halts`. -/
theorem System5_Halts_iff_exact_step_witness (cfg : System5Config) :
    System5.Halts cfg ↔
    ∃ N result, System5.nSteps cfg N = some result ∧
                (result.bag = [] ∨ result.rules = []) ∧
                ∀ k, k > N → System5.nSteps cfg k = none := by
  constructor
  · exact System5_Halts_exact_step_form cfg
  · rintro ⟨N, result, h_n, h_halt, _⟩
    exact ⟨N + 1, System5_nSteps_none_of_reaches_halted cfg result N h_n h_halt⟩

/-- **`System5_Halts_succ_boundary` (iter 716)**: from `System5.Halts
    cfg`, extracts the exact halt boundary — there exists `n` with
    `nSteps cfg n = some result ∧ nSteps cfg (n+1) = none`.  Direct
    corollary of `_Halts_exact_step_form`: at the exact halt step `N`,
    the state is `some result` (with `bag = []` or `rules = []`), and
    the next step is in the `eventually-none` zone (since `N + 1 > N`).
    Canonical "halt boundary" witness for downstream code. -/
theorem System5_Halts_succ_boundary (cfg : System5Config)
    (h : System5.Halts cfg) :
    ∃ n result, System5.nSteps cfg n = some result
              ∧ System5.nSteps cfg (n + 1) = none := by
  obtain ⟨N, result, h_n, _h_halt, h_eventual⟩ :=
    System5_Halts_exact_step_form cfg h
  exact ⟨N, result, h_n, h_eventual (N + 1) (by omega)⟩

/-- **`System5_Halts_exact_step_form_unique` (iter 565)**: System5
    uniqueness analog of iter 556/557.  The exact halt step witness
    is unique. -/
theorem System5_Halts_exact_step_form_unique (cfg : System5Config)
    (N₁ N₂ : Nat) (result₁ result₂ : System5Config)
    (h₁_n : System5.nSteps cfg N₁ = some result₁)
    (h₁_eventual : ∀ k, k > N₁ → System5.nSteps cfg k = none)
    (h₂_n : System5.nSteps cfg N₂ = some result₂)
    (h₂_eventual : ∀ k, k > N₂ → System5.nSteps cfg k = none) :
    N₁ = N₂ := by
  rcases Nat.lt_or_ge N₁ N₂ with h_lt | h_ge
  · have h_none := h₁_eventual N₂ h_lt
    rw [h_none] at h₂_n; cases h₂_n
  · rcases Nat.lt_or_ge N₂ N₁ with h_lt' | h_ge'
    · have h_none := h₂_eventual N₁ h_lt'
      rw [h_none] at h₁_n; cases h₁_n
    · omega
/-- **`System5_Halts_iff_step_or_halted` (iter 572)**: System5 analog
    of iter 570/571.  `System5.Halts cfg ↔ (cfg.bag = [] ∨ cfg.rules
    = []) ∨ (∃ cfg', System5.step cfg = some cfg' ∧ System5.Halts
    cfg')`.  Forward direction is `System5_Halts_step_decompose`;
    reverse uses `System5.Halts_of_empty_bag/_rules` and
    `System5_Halts_step_pred`. -/
theorem System5_Halts_iff_step_or_halted (cfg : System5Config) :
    System5.Halts cfg ↔ (cfg.bag = [] ∨ cfg.rules = []) ∨
                       ∃ cfg', System5.step cfg = some cfg' ∧
                               System5.Halts cfg' := by
  constructor
  · exact System5_Halts_step_decompose cfg
  · rintro ((h_bag | h_rules) | ⟨cfg', h_step, h_halts⟩)
    · exact System5.Halts_of_empty_bag cfg h_bag
    · exact System5.Halts_of_empty_rules cfg h_rules
    · exact System5_Halts_step_pred cfg cfg' h_step h_halts
/-- **`System5_Halts_first_none` (iter 574)**: System5 analog of
    iter 416 (`CTS_Halts_first_none` / `BiTM_Halts_first_none`).
    From `System5.Halts cfg`, extracts the smallest `n` with
    `System5.nSteps cfg n = none`.  Proof uses
    `find_min_or_none` (now in `TagSystem.HaltsEmpty`) on the
    decidable predicate `nSteps cfg n = none`, with the existing
    halts witness as the bound. -/
theorem System5_Halts_first_none (cfg : System5Config)
    (h : System5.Halts cfg) :
    ∃ n, System5.nSteps cfg n = none ∧ ∀ m < n, System5.nSteps cfg m ≠ none := by
  obtain ⟨N, hN⟩ := h
  rcases find_min_or_none (fun n => System5.nSteps cfg n = none) N with
    ⟨k, _h_le, h_pk, h_min⟩ | h_none
  · exact ⟨k, h_pk, h_min⟩
  · exact absurd hN (h_none N (Nat.le_refl _))
/-- **`System5_Halts_no_period` (iter 575)**: System5 analog of
    `BiTM_Halts_no_period` / `CTS_Halts_no_period`.  A halting
    System5 cfg cannot be periodic.  Direct contrapositive of
    existing `System5_periodic_not_halts`. -/
theorem System5_Halts_no_period
    (cfg : System5Config) (h : System5.Halts cfg)
    (p : Nat) (h_pos : p ≥ 1) :
    System5.nSteps cfg p ≠ some cfg :=
  fun h_period => System5_periodic_not_halts cfg p h_pos h_period h
/-- **`System5_not_Halts_iff_nSteps_always_some` (iter 576)**: System5
    analog of `BiTM_not_Halts_iff_nSteps_always_some` (now in
    `BiTM.HaltInduction`).  Since `System5.Halts cfg` is defined as
    `∃ n, nSteps cfg n = none`, the negation is "no n with nSteps =
    none", which by the Option dichotomy is "∀ n, nSteps = some _". -/
theorem System5_not_Halts_iff_nSteps_always_some (cfg : System5Config) :
    ¬ System5.Halts cfg ↔ ∀ n, ∃ result, System5.nSteps cfg n = some result := by
  constructor
  · intro h_not_halts n
    cases h_n : System5.nSteps cfg n with
    | none => exact absurd ⟨n, h_n⟩ h_not_halts
    | some r => exact ⟨r, rfl⟩
  · intro h_all ⟨n, h_n⟩
    obtain ⟨r, h_r⟩ := h_all n
    rw [h_r] at h_n; cases h_n
/-- **`System5_nSteps_halt_unique` (iter 582)**: System5 analog of
    `BiTM_nSteps_halt_unique` / `CTS_nSteps_halt_unique`.  Two
    valid halt counts agree.  Halt criterion: `step r = none`. -/
theorem System5_nSteps_halt_unique (cfg : System5Config)
    (n₁ n₂ : Nat) (r₁ r₂ : System5Config)
    (h₁ : System5.nSteps cfg n₁ = some r₁) (h_step₁ : System5.step r₁ = none)
    (h₂ : System5.nSteps cfg n₂ = some r₂) (h_step₂ : System5.step r₂ = none) :
    n₁ = n₂ := by
  rcases Nat.lt_or_ge n₁ n₂ with h_lt | h_ge
  · obtain ⟨k, hk_pos, rfl⟩ : ∃ k, k ≥ 1 ∧ n₂ = n₁ + k :=
      ⟨n₂ - n₁, by omega, by omega⟩
    rw [System5_nSteps_past_step_none_eq_none cfg n₁ r₁ h₁ h_step₁ k hk_pos] at h₂
    cases h₂
  · rcases Nat.lt_or_eq_of_le h_ge with h_lt | h_eq
    · obtain ⟨k, hk_pos, rfl⟩ : ∃ k, k ≥ 1 ∧ n₁ = n₂ + k :=
        ⟨n₁ - n₂, by omega, by omega⟩
      rw [System5_nSteps_past_step_none_eq_none cfg n₂ r₂ h₂ h_step₂ k hk_pos] at h₁
      cases h₁
    · exact h_eq.symm

/-- **`System5_step_none_imp_nSteps_pos_none` (iter 720)**: if `step
    cfg = none`, then `nSteps cfg n = none` for all `n ≥ 1`.  Direct
    via `System5.nSteps_one` (gives `nSteps cfg 1 = none`) and
    `System5_nSteps_none_propagate`.  Useful canonical form: a
    halted-at-cfg state stays halted for all subsequent step counts. -/
theorem System5_step_none_imp_nSteps_pos_none
    (cfg : System5Config) (h : System5.step cfg = none)
    (n : Nat) (h_n : 1 ≤ n) :
    System5.nSteps cfg n = none := by
  have h_one : System5.nSteps cfg 1 = none := by
    rw [System5.nSteps_one]; exact h
  exact System5_nSteps_none_propagate cfg 1 n h_n h_one

end BiTM
