/-
  BiTM.System5

  Smith's "System 5" simulator (PDF `TM23Proof.pdf` p. 30, `system5.pl`):
  a parity-multiset bag plus a queue of integer-list rules.  One step
  decrements every bag element, increments every rule element, and
  either pops a rule (XOR-merging it into the bag) when a `0`
  surfaces, or proceeds without popping otherwise.

  Contents:
    * `System5Config` structure
    * `System5.step` definition
    * `System5_step_pure_decrement`: no-pop case characterisation
    * `System5_step_none_iff`: halting iff bag or rules empty
    * `System5_step_some_iff`: dual: success iff both nonempty
-/

import BiTM.XorMerge
import BiTM.HaltInduction
import TagSystem.TagToCTS

namespace BiTM

open TM
open TagSystem

/-- A System 5 configuration: a bag (parity multiset) + a queue of rules. -/
structure System5Config where
  /-- The current bag (parity-mod-2 multiset). -/
  bag : List Int
  /-- The remaining rules; rules are popped (consumed) as `0` in bag triggers. -/
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
    the rules - no rule pop, no XOR-merge. -/
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
  rw [ite_eq_right h_first_false] at h_step
  rw [ite_eq_right h_zero] at h_step
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
    rw [ite_eq_right h_first_false] at h
    by_cases h_zero : 0 ∈ cfg.bag.map (· - 1)
    · rw [ite_eq_left h_zero] at h
      cases h_cfg_rules : cfg.rules with
      | nil => exact h_rules h_cfg_rules
      | cons r rs =>
        rw [h_cfg_rules] at h; cases h
    · rw [ite_eq_right h_zero] at h
      cases h
  · intro h
    rcases h with h | h
    · have : (cfg.bag.map (· - 1)).isEmpty = true := by
        rw [h]; rfl
      rw [ite_eq_left (Or.inl this)]
    · have : (cfg.rules.map (fun r => r.map (· + 1))).isEmpty = true := by
        rw [h]; rfl
      rw [ite_eq_left (Or.inr this)]

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

/-- **Explicit P-step characterization**.  When the rules
    head is known (cfg.rules = r1 :: rest) and `0 in cfg.bag.map(fun x => x - 1)`,
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
  rw [ite_eq_right h_first_false, ite_eq_left h_zero]
  rw [h_rules]
  rfl

/-- **Bridge between `1 in bag` and `0 in bag.map(fun x => x - 1)`**.
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

/-- 1-step iteration is `System5.step`. -/
theorem System5.nSteps_one (cfg : System5Config) :
    System5.nSteps cfg 1 = System5.step cfg := by
  show (match System5.step cfg with
        | none => none
        | some cfg' => System5.nSteps cfg' 0) = System5.step cfg
  cases System5.step cfg <;> rfl

/-- Additive composition:
    `nSteps cfg (n + m) = nSteps cfg n >>= (fun c => nSteps c m)`. -/
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

/-- Direct-recursion form: `nSteps cfg (n+1) = step cfg >>= (fun c => nSteps c n)`.
    Definitional, but stated explicitly for ergonomic use. -/
theorem System5.nSteps_succ (cfg : System5Config) (n : Nat) :
    System5.nSteps cfg (n + 1)
      = (System5.step cfg).bind (fun c => System5.nSteps c n) := by
  rw [Nat.add_comm, System5.nSteps_add, System5.nSteps_one]

/-- Shift composition: two `(fun x => x + _)` maps compose to a single map of
    the sum.  `(l.map (fun x => x + a)).map (fun x => x + b)` equals
    `l.map (fun x => x + (a + b))`. -/
theorem List_Int_map_add_compose (l : List Int) (a b : Int) :
    (l.map (· + a)).map (· + b) = l.map (· + (a + b)) := by
  rw [List.map_map]
  congr 1
  funext x
  show (x + a) + b = x + (a + b)
  omega

/-- Dual: two `(fun x => x - _)` maps compose to a single map of the sum.
    `(l.map (fun x => x - a)).map (fun x => x - b) = l.map (fun x => x - (a + b))`. -/
theorem List_Int_map_sub_compose (l : List Int) (a b : Int) :
    (l.map (· - a)).map (· - b) = l.map (· - (a + b)) := by
  rw [List.map_map]
  congr 1
  funext x
  show (x - a) - b = x - (a + b)
  omega

/-- Helper: iterated subtraction commutes - `l.map (fun x => x - (k+1))`
    equals `l.map (fun x => x - k)` then `fun x => x - 1`. -/
theorem List_Int_map_sub_succ (l : List Int) (k : Nat) :
    l.map (· - ((k + 1 : Nat) : Int)) = (l.map (· - (k : Int))).map (· - 1) := by
  rw [List.map_map]
  congr 1
  funext x
  show x - ((k + 1 : Nat) : Int) = (x - (k : Int)) - 1
  omega

/-- Helper: iterated addition commutes - `l.map (fun x => x + (k+1))`
    equals `l.map (fun x => x + k)` then `fun x => x + 1`. -/
theorem List_Int_map_add_succ (l : List Int) (k : Nat) :
    l.map (· + ((k + 1 : Nat) : Int)) = (l.map (· + (k : Int))).map (· + 1) := by
  rw [List.map_map]
  congr 1
  funext x
  show x + ((k + 1 : Nat) : Int) = (x + (k : Int)) + 1
  omega

/-- `nSteps` form of pure decrement.  Combines `System5.nSteps_one`,
    `_step_some_iff`, and `_step_pure_decrement`. -/
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

/-- Multi-step pure decrement.  If no value in `{1, ..., k}` appears in
    `cfg.bag`, then `k` consecutive System 5 steps are pure decrements.
    Workhorse for `cy2s5.pl`-style System 5 trajectories between successive
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


/-! ## The Nodup invariant -/

end BiTM
