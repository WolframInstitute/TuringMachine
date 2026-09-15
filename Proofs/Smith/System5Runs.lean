/-
  Smith.System5Runs

  Infrastructure for the per-step lemma of PLAN.md target T1 (milestone M2):
  the shape of a System 5 run between two rule pops, the permutation-level
  effect of a pop on the bag, the arithmetic of a uniform shift, and a
  decoder from a System 5 bag back to the working string of the cyclic tag
  system it represents.

  Contents:
    * `xorMerge` at the level of `List.Perm`: `xorMerge_perm_append` (a rule
      disjoint from the bag is appended) and `xorMerge_perm_cancel` (a rule
      that duplicates a block of the bag deletes it).
    * `System5_run_pure_decrement`: `j` steps with every bag element above
      `j` are `j` pure decrements.  `System5_step_pop`, the composite
      `System5_run_then_pop` (decrements down to the next pop and the pop
      itself, in one shift), and the two permutation corollaries
      `System5_step_pop_perm_append` and `System5_step_pop_perm_cancel`.
    * Arithmetic: `map_sub_erase` (erasing the 0 of a decremented list is
      erasing the element that equals the shift), `pairsOf_map_sub`,
      `pairsAsc_map_sub`, `appendantsFrom_congr`, `appendantsFrom_mod` and
      `Represents_phase_mod` (a CTS step reduces the phase modulo the number
      of appendants; `appendantsFrom` does not care).
    * `decodeBag`: sort the bag, read it two integers at a time, a gap of 1
      for a `0` and of 2 for a `1`.  `decodeBag_pairsOf`, `decodeBag_of_perm`,
      `Represents_decode` and `Represents_data_unique`, with positive and
      negative `decide` examples.
-/

import Smith.Represents
import Mathlib.Data.List.Sort

namespace Smith

open TagSystem
open BiTM

/-! ## `xorMerge` at the level of permutations

`xorMerge` is the parity merge of `system5.pl`.  The two situations the
per-step lemma meets are the extreme ones: the popped rule is disjoint from
the bag (it is appended) or it repeats a block of the bag exactly (the block
disappears).  Both are stated as permutations, which is the level at which
`Represents` reads the bag. -/

/-- A rule disjoint from the bag is appended to it. -/
theorem xorMerge_perm_append (xs ys : List Int)
    (h_ys : ys.Nodup) (h_disj : ∀ y ∈ ys, y ∉ xs) :
    (xorMerge xs ys).Perm (xs ++ ys) := by
  rw [xorMerge_disjoint_eq_reverse_append xs ys h_disj h_ys]
  exact List.perm_append_comm.trans ((List.reverse_perm ys).append_left xs)

/-- A rule that repeats a block of the bag deletes that block: if the bag is
    a permutation of `l ++ q` with `q` disjoint from `l` and the merged list
    is a permutation of `q`, what is left is a permutation of `l`. -/
theorem xorMerge_perm_cancel (xs ys l q : List Int)
    (h_xs : xs.Nodup) (h_q : q.Nodup)
    (h_perm : xs.Perm (l ++ q)) (h_disj : ∀ y ∈ q, y ∉ l)
    (h_ys : ys.Perm q) :
    (xorMerge xs ys).Perm l := by
  have h_ys_nodup : ys.Nodup := h_ys.symm.nodup h_q
  have h_lq : (l ++ q).Nodup := h_perm.nodup h_xs
  have h_l : l.Nodup := (List.nodup_append.mp h_lq).1
  refine (List.perm_ext_iff_of_nodup (xorMerge_nodup xs ys h_xs) h_l).mpr ?_
  intro x
  rw [xorMerge_mem_iff xs ys h_xs h_ys_nodup]
  have hq : x ∈ ys ↔ x ∈ q := h_ys.mem_iff
  have hx : x ∈ xs ↔ x ∈ l ∨ x ∈ q := by
    rw [h_perm.mem_iff]; exact List.mem_append
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rcases hx.mp h1 with h | h
      · exact h
      · exact absurd (hq.mpr h) h2
    · exact absurd (hx.mpr (Or.inr (hq.mp h2))) h1
  · intro hl
    exact Or.inl ⟨hx.mpr (Or.inl hl), fun hys => h_disj x (hq.mp hys) hl⟩

/-! ## Runs of System 5 -/

/-- A run of pure decrements: while every bag element is strictly above the
    number of steps taken, no element ever reaches 0, so no rule is popped
    and the run is a uniform shift of bag and rules. -/
theorem System5_run_pure_decrement (cfg : System5Config) (j : Nat)
    (h_bag : cfg.bag ≠ []) (h_rules : cfg.rules ≠ [])
    (h_gt : ∀ x ∈ cfg.bag, (j : Int) < x) :
    System5.nSteps cfg j
      = some { bag := cfg.bag.map (· - (j : Int)),
               rules := cfg.rules.map (fun r => r.map (· + (j : Int))) } := by
  have h_no_small : ∀ i : Nat, 1 ≤ i → i ≤ j → (↑i : Int) ∉ cfg.bag := by
    intro i _ hij hmem
    have := h_gt _ hmem
    omega
  obtain ⟨cfg', hrun, hb, hr⟩ :=
    System5_nSteps_k_pure_decrement cfg j h_bag h_rules h_no_small
  rw [hrun]
  obtain ⟨b, r⟩ := cfg'
  simp only at hb hr
  rw [hb, hr]

/-- The pop step in the form the per-step lemma uses: the bag holds a 1 and
    the rule list is known, so the step pops the head rule incremented by 1
    and merges it into the decremented bag with the 0 erased. -/
theorem System5_step_pop (cfg : System5Config) (r : List Int)
    (rest : List (List Int)) (h_rules : cfg.rules = r :: rest)
    (h_one : (1 : Int) ∈ cfg.bag) :
    System5.step cfg
      = some { bag := xorMerge ((cfg.bag.map (· - 1)).erase 0) (r.map (· + 1)),
               rules := rest.map (fun r => r.map (· + 1)) } := by
  have h_zero : (0 : Int) ∈ cfg.bag.map (· - 1) :=
    (System5_one_mem_iff_zero_in_decremented cfg.bag).mp h_one
  have h_bag : cfg.bag ≠ [] := by
    intro h; rw [h] at h_one; exact absurd h_one (by simp)
  exact System5_step_explicit_pop cfg r rest h_rules h_bag h_zero

/-- The workhorse of the per-step lemma: `j` pure decrements followed by the
    pop they set up.  The bag element that equals `j + 1` reaches 0 at step
    `j + 1`, so the head rule is popped shifted by the whole elapsed time and
    the surviving rules carry the same shift. -/
theorem System5_run_then_pop (cfg : System5Config) (j : Nat) (r : List Int)
    (rest : List (List Int)) (h_rules : cfg.rules = r :: rest)
    (h_gt : ∀ x ∈ cfg.bag, (j : Int) < x)
    (h_mem : ((j : Nat) : Int) + 1 ∈ cfg.bag) :
    System5.nSteps cfg (j + 1)
      = some { bag := xorMerge ((cfg.bag.map (· - ((j + 1 : Nat) : Int))).erase 0)
                               (r.map (· + ((j + 1 : Nat) : Int))),
               rules := rest.map (fun s => s.map (· + ((j + 1 : Nat) : Int))) } := by
  have h_bag : cfg.bag ≠ [] := by
    intro h; rw [h] at h_mem; exact absurd h_mem (by simp)
  have h_rules_ne : cfg.rules ≠ [] := by rw [h_rules]; simp
  rw [System5.nSteps_add, System5_run_pure_decrement cfg j h_bag h_rules_ne h_gt,
      Option.bind_some, System5.nSteps_one]
  have h_one : (1 : Int) ∈ cfg.bag.map (· - (j : Int)) := by
    rw [List.mem_map]
    exact ⟨((j : Nat) : Int) + 1, h_mem, by omega⟩
  have h_head : cfg.rules.map (fun s => s.map (· + (j : Int)))
      = r.map (· + (j : Int)) :: rest.map (fun s => s.map (· + (j : Int))) := by
    rw [h_rules, List.map_cons]
  rw [System5_step_pop
        { bag := cfg.bag.map (· - (j : Int)),
          rules := cfg.rules.map (fun s => s.map (· + (j : Int))) }
        (r.map (· + (j : Int))) (rest.map (fun s => s.map (· + (j : Int)))) h_head h_one]
  have hb : (cfg.bag.map (· - (j : Int))).map (· - 1)
      = cfg.bag.map (· - ((j + 1 : Nat) : Int)) := (List_Int_map_sub_succ cfg.bag j).symm
  have hr2 : (r.map (· + (j : Int))).map (· + 1)
      = r.map (· + ((j + 1 : Nat) : Int)) := (List_Int_map_add_succ r j).symm
  have hrest : ∀ l : List (List Int),
      (l.map (fun s => s.map (· + (j : Int)))).map (fun s => s.map (· + 1))
        = l.map (fun s => s.map (· + ((j + 1 : Nat) : Int))) := by
    intro l
    induction l with
    | nil => rfl
    | cons s t ih =>
      rw [List.map_cons, List.map_cons, List.map_cons, ih, ← List_Int_map_add_succ]
  simp only [hb, hr2, hrest]

/-- Permutation form of a pop whose rule is disjoint from the bag: the new
    bag is the decremented bag with the 0 erased, followed by the rule. -/
theorem System5_step_pop_perm_append (cfg : System5Config) (r : List Int)
    (rest : List (List Int)) (h_rules : cfg.rules = r :: rest)
    (h_one : (1 : Int) ∈ cfg.bag) (h_r : (r.map (· + 1)).Nodup)
    (h_disj : ∀ y ∈ r.map (· + 1), y ∉ (cfg.bag.map (· - 1)).erase 0) :
    ∃ cfg', System5.step cfg = some cfg' ∧
      cfg'.bag.Perm ((cfg.bag.map (· - 1)).erase 0 ++ r.map (· + 1)) ∧
      cfg'.rules = rest.map (fun r => r.map (· + 1)) :=
  ⟨_, System5_step_pop cfg r rest h_rules h_one,
    xorMerge_perm_append _ _ h_r h_disj, rfl⟩

/-- Permutation form of a pop whose rule repeats a block of the bag: the
    block is cancelled and the new bag is a permutation of the rest. -/
theorem System5_step_pop_perm_cancel (cfg : System5Config) (r : List Int)
    (rest : List (List Int)) (l q : List Int) (h_rules : cfg.rules = r :: rest)
    (h_one : (1 : Int) ∈ cfg.bag) (h_nodup : cfg.bag.Nodup) (h_q : q.Nodup)
    (h_perm : ((cfg.bag.map (· - 1)).erase 0).Perm (l ++ q))
    (h_disj : ∀ y ∈ q, y ∉ l) (h_r : (r.map (· + 1)).Perm q) :
    ∃ cfg', System5.step cfg = some cfg' ∧ cfg'.bag.Perm l ∧
      cfg'.rules = rest.map (fun r => r.map (· + 1)) :=
  ⟨_, System5_step_pop cfg r rest h_rules h_one,
    xorMerge_perm_cancel _ _ l q
      (List.Nodup.erase _ (nodup_map_sub_one h_nodup)) h_q h_perm h_disj h_r, rfl⟩

/-! ## Arithmetic of a uniform shift

`List_Int_map_sub_compose`, `List_Int_map_sub_succ` and
`List_Int_map_add_succ` of `BiTM.System5` already compose the shifts; what is
missing is the interaction of a shift with `List.erase` and with the bag and
start lists of `Smith.Represents`. -/

/-- Erasing the 0 of a uniformly decremented list erases the single element
    that equals the shift. -/
theorem map_sub_erase (l : List Int) (c : Int) :
    (l.map (· - c)).erase 0 = (l.erase c).map (· - c) := by
  have hinj : Function.Injective (fun x : Int => x - c) := by
    intro x y h
    simp only at h
    omega
  have h := List.map_erase (f := fun x : Int => x - c) hinj (a := c) l
  simpa using h.symm

/-- Shifting the starts down shifts the bag down. -/
theorem pairsOf_map_sub (w : List Bool) (a : List Int) (m : Int) :
    pairsOf w (a.map (· - m)) = (pairsOf w a).map (· - m) := by
  induction w generalizing a with
  | nil => rfl
  | cons b w ih =>
    cases a with
    | nil => rfl
    | cons x a =>
      show (x - m) :: (x - m + gap b) :: pairsOf w (a.map (· - m))
         = (x - m) :: (x + gap b - m) :: (pairsOf w a).map (· - m)
      rw [ih a, show x - m + gap b = x + gap b - m from by omega]

/-- Shifting the starts down preserves the ascending condition. -/
theorem pairsAsc_map_sub (lo : Int) (w : List Bool) (a : List Int) (m : Int)
    (h : pairsAsc lo w a = true) : pairsAsc (lo - m) w (a.map (· - m)) = true := by
  induction w generalizing lo a with
  | nil =>
    cases a with
    | nil => rfl
    | cons x a => simp at h
  | cons b w ih =>
    cases a with
    | nil => simp at h
    | cons x a =>
      rw [pairsAsc_cons_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      show (decide (lo - m < x - m) && pairsAsc (x - m + gap b) w (a.map (· - m))) = true
      rw [show x - m + gap b = x + gap b - m from by omega, ih (x + gap b) a h.2]
      simp only [Bool.and_true, decide_eq_true_eq]
      omega

/-- Two phase streams that read the same appendant at every offset give the
    same list of appendants. -/
theorem appendantsFrom_congr (C : CTS) (p q n : Nat)
    (h : ∀ k, C.currentAppendant (p + k) = C.currentAppendant (q + k)) :
    appendantsFrom C p n = appendantsFrom C q n := by
  induction n generalizing p q with
  | zero => rfl
  | succ n ih =>
    have h0 : C.currentAppendant p = C.currentAppendant q := by simpa using h 0
    have hstep : ∀ k, C.currentAppendant (p + 1 + k) = C.currentAppendant (q + 1 + k) := by
      intro k
      have hk := h (k + 1)
      rw [show p + (k + 1) = p + 1 + k by omega,
          show q + (k + 1) = q + 1 + k by omega] at hk
      exact hk
    rw [appendantsFrom_succ, appendantsFrom_succ, h0, ih (p + 1) (q + 1) hstep]

/-- `appendantsFrom` does not see the phase reduction a CTS step performs. -/
theorem appendantsFrom_mod (C : CTS) (p n : Nat) :
    appendantsFrom C (p % C.appendants.length) n = appendantsFrom C p n := by
  refine appendantsFrom_congr C _ p n ?_
  intro k
  have h1 := currentAppendant_mod C (p % C.appendants.length + k)
  have h2 := currentAppendant_mod C (p + k)
  rw [Nat.mod_add_mod] at h1
  exact h1.symm.trans h2

/-- `Represents` does not see the phase reduction a CTS step performs. -/
theorem Represents_phase_mod (s : System5Config) (C : CTS) (c : CTSConfig) (b : Nat) :
    Represents s C { data := c.data, phase := c.phase % C.appendants.length } b
      ↔ Represents s C c b := by
  simp only [Represents, appendantsFrom_mod]

/-! ## Decoding a bag

The bag of a represented configuration is a permutation of the pairs of an
ascending list of starts, so sorting it and reading it two integers at a time
recovers the working string.  `decodeFrom` mirrors `pairsAsc` clause by
clause: the next pair must start strictly above the end of the previous one,
a gap of 1 is a `0` and a gap of 2 is a `1`.  Starting at `lo = 0` forces the
smallest bag element to be at least 1. -/

/-- The bag in ascending order. -/
def sortBag (bag : List Int) : List Int := List.insertionSort (· ≤ ·) bag

/-- Read an ascending list of integers two at a time from the bound `lo`:
    the pair must start strictly above `lo`, a gap of 1 decodes to `false`
    and a gap of 2 to `true`, and everything else fails. -/
def decodeFrom : Int → List Int → Option (List Bool)
  | _, [] => some []
  | _, [_] => none
  | lo, x :: y :: rest =>
      if lo < x then
        if y = x + 1 then (decodeFrom (x + 1) rest).map (fun w => false :: w)
        else if y = x + 2 then (decodeFrom (x + 2) rest).map (fun w => true :: w)
        else none
      else none

/-- The empty bag decodes to the empty working string. -/
@[simp] theorem decodeFrom_nil (lo : Int) : decodeFrom lo [] = some [] := rfl

/-- An odd-length bag does not decode. -/
@[simp] theorem decodeFrom_singleton (lo x : Int) : decodeFrom lo [x] = none := rfl

/-- One pair peeled off the front. -/
theorem decodeFrom_cons_cons (lo x y : Int) (rest : List Int) :
    decodeFrom lo (x :: y :: rest)
      = if lo < x then
          if y = x + 1 then (decodeFrom (x + 1) rest).map (fun w => false :: w)
          else if y = x + 2 then (decodeFrom (x + 2) rest).map (fun w => true :: w)
          else none
        else none := rfl

/-- The decoder of a System 5 bag: sort, then read pairs from the bound 0. -/
def decodeBag (bag : List Int) : Option (List Bool) := decodeFrom 0 (sortBag bag)

/-- Sorting permutes. -/
theorem sortBag_perm (l : List Int) : (sortBag l).Perm l :=
  List.perm_insertionSort _ l

/-- Sorting sorts. -/
theorem sortBag_pairwise (l : List Int) : (sortBag l).Pairwise (· ≤ ·) :=
  List.pairwise_insertionSort _ l

/-- Sorting a permutation of an ascending list returns that list. -/
theorem sortBag_eq_of_perm (bag l : List Int)
    (hperm : bag.Perm l) (hl : l.Pairwise (· ≤ ·)) : sortBag bag = l :=
  List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun x y _ _ h1 h2 => by omega)
    (sortBag_pairwise bag) hl ((sortBag_perm bag).trans hperm)

/-- The decoder inverts `pairsOf` on an ascending family of starts. -/
theorem decodeFrom_pairsOf (lo : Int) (w : List Bool) (a : List Int)
    (h : pairsAsc lo w a = true) : decodeFrom lo (pairsOf w a) = some w := by
  induction w generalizing lo a with
  | nil =>
    cases a with
    | nil => rfl
    | cons x a => simp at h
  | cons b w ih =>
    cases a with
    | nil => simp at h
    | cons x a =>
      rw [pairsAsc_cons_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [pairsOf_cons, decodeFrom_cons_cons, if_pos h.1]
      cases b with
      | false =>
        have hg : x + gap false = x + 1 := rfl
        rw [hg, if_pos rfl, ih (x + 1) a (by rw [← hg]; exact h.2)]
        rfl
      | true =>
        have hg : x + gap true = x + 2 := rfl
        rw [hg, if_neg (by omega), if_pos rfl, ih (x + 2) a (by rw [← hg]; exact h.2)]
        rfl

/-- Any permutation of a valid family of pairs decodes to its working
    string. -/
theorem decodeBag_of_perm (bag : List Int) (w : List Bool) (a : List Int)
    (hasc : pairsAsc 0 w a = true) (hperm : bag.Perm (pairsOf w a)) :
    decodeBag bag = some w := by
  have hpw : (pairsOf w a).Pairwise (· ≤ ·) :=
    (pairsOf_pairwise 0 w a hasc).imp (fun h => Int.le_of_lt h)
  rw [decodeBag, sortBag_eq_of_perm bag (pairsOf w a) hperm hpw]
  exact decodeFrom_pairsOf 0 w a hasc

/-- The decoder inverts the bag clause of `Represents`. -/
theorem decodeBag_pairsOf (w : List Bool) (a : List Int)
    (hasc : pairsAsc 0 w a = true) : decodeBag (pairsOf w a) = some w :=
  decodeBag_of_perm _ w a hasc (List.Perm.refl _)

/-- A represented bag decodes to the working string it represents. -/
theorem Represents_decode (s : System5Config) (C : CTS) (c : CTSConfig) (b : Nat)
    (h : Represents s C c b) : decodeBag s.bag = some c.data := by
  obtain ⟨⟨a, hasc, hperm⟩, -⟩ := h
  exact decodeBag_of_perm s.bag c.data a hasc hperm

/-- One System 5 bag represents at most one working string, whatever the
    cyclic tag system, the phase and the budget. -/
theorem Represents_data_unique (s : System5Config) (C C' : CTS) (c c' : CTSConfig)
    (b b' : Nat) (h : Represents s C c b) (h' : Represents s C' c' b') :
    c.data = c'.data := by
  have h1 := Represents_decode s C c b h
  have h2 := Represents_decode s C' c' b' h'
  rw [h1] at h2
  exact Option.some.inj h2

/-! ## Examples

Positive and negative `decide` checks for the decoder, as required by the
vacuity discipline of PLAN.md section 6. -/

/-- Worked example of `System5_run_pure_decrement`: two steps below the
    minimum of the bag shift bag and rules. -/
theorem ex_run_pure_decrement :
    System5.nSteps { bag := [3, 5], rules := [[10], [12]] } 2
      = some { bag := [1, 3], rules := [[12], [14]] } := by decide

/-- Worked example of `System5_step_pop`: the 1 in the bag pops the head
    rule, incremented, into the decremented bag with the 0 erased. -/
theorem ex_step_pop :
    System5.step { bag := [1, 3], rules := [[12], [14]] }
      = some { bag := [13, 2], rules := [[15]] } := by decide

/-- Worked example of `System5_run_then_pop`: two decrements and the pop
    they set up, in one step count. -/
theorem ex_run_then_pop :
    System5.nSteps { bag := [3, 5], rules := [[10], [12]] } 3
      = some { bag := [13, 2], rules := [[15]] } := by decide

/-- The bag of the TM23Proof.pdf p. 29 example decodes to the doubled
    working string `0011`. -/
theorem decodeBag_pdf29 :
    decodeBag [1, 2, 3, 4, 5, 7, 8, 10] = some [false, false, true, true] := by decide

/-- Two `1` pairs. -/
theorem decodeBag_two_ones : decodeBag [1, 3, 4, 6] = some [true, true] := by decide

/-- The decoder sorts: an unsorted bag decodes like its sorted form. -/
theorem decodeBag_unsorted : decodeBag [2, 4, 3, 1] = some [false, false] := by decide

/-- An odd-length bag does not decode. -/
theorem decodeBag_odd : decodeBag [1, 2, 3] = none := by decide

/-- A gap of 3 does not decode. -/
theorem decodeBag_bad_gap : decodeBag [1, 2, 3, 6] = none := by decide

/-- A bag reaching below 1 does not decode. -/
theorem decodeBag_below_one : decodeBag [0, 1] = none := by decide

/-- Overlapping pairs do not decode: the second pair must start strictly
    above the end of the first. -/
theorem decodeBag_overlap : decodeBag [1, 2, 2, 3] = none := by decide

end Smith
