/-
  Smith.Represents

  The representation relation of PLAN.md section 2 (target theorem T1),
  stated between a System 5 configuration and a configuration of a DOUBLED
  two-colour cyclic tag system (TM23Proof.pdf p. 19, "Initial condition").

  A System 5 configuration represents a cyclic tag configuration when

    * its bag is a permutation of the pairs of a strictly increasing list of
      starting integers, one pair per bit of the working string, with a gap
      of 1 for a `0` and of 2 for a `1` (`pairsOf`, `pairsAsc`);
    * its rule list begins with the rule pairs of the appendants the doubled
      system reads from the current phase onward, at least `budget` of them,
      encoded from some counter `i` that sits at least 3 above every element
      of the bag (`ruleBlocks`, `appendantsFrom`).

  Both clauses are relations, not equalities with the canonical encoder
  output: the rule list may be any uniform increment of the encoding and may
  carry an arbitrary unconstrained tail, which is what makes the relation
  survive a System 5 step (obstruction (b) of PLAN.md section 1).

  Fidelity note on the rules clause.  Smith's p. 19 condition asks only that
  the lower integer of each pair of a second rule sit at least 3 above every
  integer of the initial bag, of every previous rule other than the first
  rule of a pair, and of the earlier bits of the same appendant; any spacing
  meeting those bounds is acceptable.  The clause below pins the canonical
  `cy2s5.pl` layout instead: `encodePaired` advances the counter by exactly
  4 per doubled `0` and 6 per doubled `1` and `ruleBlocks` lays consecutive
  rule pairs down contiguously, so the only freedom left is the base counter
  `i` and the unconstrained tail.  The Lean relation is therefore a strict
  sub-relation of Smith's.  It is contained in Smith's: in the canonical
  layout each of those bounds is met with equality (a doubled `0` pair
  occupies `x, x + 1` and the next pair starts at `x + 4`; a doubled `1`
  pair occupies `x, x + 3` and the next pair starts at `x + 6`).  The
  containment is strict: a hand-built program with extra slack, such as the
  one Smith prints on p. 19, lies in the relation only as far as its prefix
  agrees with the canonical layout, see `pdf19`, `pdf19_represents_budget2`
  and `pdf19_not_represents_budget3`.  The restriction is adequate for T1,
  because the canonical layout is what the encoder emits and what one
  System 5 step re-establishes, with the threshold met exactly; proving that
  is the M2 per-step lemma.  Relaxing the clause to Smith's "at least 3"
  condition is a possible later generalisation and is not needed downstream.

  Doubling is a precondition, not a side condition: `encodePaired` reads an
  appendant two bits at a time and drops a trailing odd bit, so the rules
  clause is meaningful only for `C = double C0`.  Every statement about
  `Represents` here and in M2 is stated over a doubled system.

  Contents:
    * `gap`, `pairsOf`, `pairsAsc` and their structural lemmas.
    * `encodePaired`, `ruleBlocks`, `appendantsFrom`: the rule side.
    * `Represents`, its structural consequences, and `Represents_shift`.
    * `ctsToSystem5_represents`: the canonical encoder satisfies it.
    * Non-degeneracy: the PDF p. 29 example holds by `decide`; a bag paired
      with the wrong word and the empty bag with a nonempty word do not,
      and neither does a rule list whose counter is too low or whose rule
      pair is in the wrong order.
    * `pdf19`: the hand-built p. 19 program, in the relation at budget 2 and
      out of it at budget 3, which pins the canonical-spacing restriction.
-/

import Smith.Doubling
import BiTM.CTSToSystem5
import Mathlib.Data.Multiset.Basic

namespace Smith

universe u

open TagSystem
open BiTM

/-! ## The System 5 step system -/

/-- System 5 as a `StepSys`. -/
def system5Sys : StepSys System5Config := ⟨System5.step⟩

/-- The step function of `system5Sys`. -/
@[simp] theorem system5Sys_step (s : System5Config) :
    system5Sys.step s = System5.step s := rfl

/-- The generic `nSteps` of `system5Sys` is the hand-rolled `System5.nSteps`. -/
theorem system5Sys_nSteps (s : System5Config) (n : Nat) :
    system5Sys.nSteps s n = System5.nSteps s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [StepSys.nSteps_succ_left, system5Sys_step]
    cases h : System5.step s with
    | none => simp [System5.nSteps, h]
    | some s' => simp [System5.nSteps, h, ih]

/-! ## The bag side: pairs of integers -/

/-- The gap between the two bag integers of one bit of the working string:
    1 for a `0`, 2 for a `1` (TM23Proof.pdf p. 19). -/
def gap (b : Bool) : Int := if b then 2 else 1

/-- The gap is positive. -/
theorem gap_pos (b : Bool) : 0 < gap b := by cases b <;> decide

/-- The bag of a working string, given the lower integer of each bit.
    The `i`-th bit contributes `a i` and `a i + gap (w i)`. -/
def pairsOf : List Bool → List Int → List Int
  | [], _ => []
  | b :: w, x :: a => x :: (x + gap b) :: pairsOf w a
  | _ :: _, [] => []

/-- `pairsOf` on the empty word. -/
@[simp] theorem pairsOf_nil (a : List Int) : pairsOf [] a = [] := rfl

/-- `pairsOf` on a nonempty word and a nonempty start list. -/
@[simp] theorem pairsOf_cons (b : Bool) (w : List Bool) (x : Int) (a : List Int) :
    pairsOf (b :: w) (x :: a) = x :: (x + gap b) :: pairsOf w a := rfl

/-- `pairsOf` runs out when there are fewer starts than bits. -/
@[simp] theorem pairsOf_cons_nil (b : Bool) (w : List Bool) :
    pairsOf (b :: w) [] = [] := rfl

/-- The starts are strictly increasing and leave room for the gaps: `lo` is
    below the first start, and the pair of one bit ends strictly below the
    start of the next.  Bool-valued, hence decidable. -/
def pairsAsc : Int → List Bool → List Int → Bool
  | _, [], [] => true
  | lo, b :: w, x :: a => decide (lo < x) && pairsAsc (x + gap b) w a
  | _, [], _ :: _ => false
  | _, _ :: _, [] => false

/-- `pairsAsc` on the empty word and the empty start list. -/
@[simp] theorem pairsAsc_nil_nil (lo : Int) : pairsAsc lo [] [] = true := rfl

/-- `pairsAsc` on a nonempty word and a nonempty start list. -/
@[simp] theorem pairsAsc_cons_cons (lo : Int) (b : Bool) (w : List Bool)
    (x : Int) (a : List Int) :
    pairsAsc lo (b :: w) (x :: a) = (decide (lo < x) && pairsAsc (x + gap b) w a) := rfl

/-- `pairsAsc` fails when the start list is longer than the word. -/
@[simp] theorem pairsAsc_nil_cons (lo x : Int) (a : List Int) :
    pairsAsc lo [] (x :: a) = false := rfl

/-- `pairsAsc` fails when the start list is shorter than the word. -/
@[simp] theorem pairsAsc_cons_nil (lo : Int) (b : Bool) (w : List Bool) :
    pairsAsc lo (b :: w) [] = false := rfl

/-- One start per bit. -/
theorem pairsAsc_length (lo : Int) (w : List Bool) (a : List Int)
    (h : pairsAsc lo w a = true) : a.length = w.length := by
  induction w generalizing lo a with
  | nil => cases a with
    | nil => rfl
    | cons x a => simp at h
  | cons b w ih =>
    cases a with
    | nil => simp at h
    | cons x a =>
      rw [pairsAsc_cons_cons, Bool.and_eq_true] at h
      simp [ih (x + gap b) a h.2]

/-- Two bag entries per bit. -/
theorem pairsOf_length (lo : Int) (w : List Bool) (a : List Int)
    (h : pairsAsc lo w a = true) : (pairsOf w a).length = 2 * w.length := by
  induction w generalizing lo a with
  | nil => rfl
  | cons b w ih =>
    cases a with
    | nil => simp at h
    | cons x a =>
      rw [pairsAsc_cons_cons, Bool.and_eq_true] at h
      rw [pairsOf_cons]
      simp only [List.length_cons, ih (x + gap b) a h.2]
      omega

/-- Every bag entry lies strictly above the lower bound. -/
theorem pairsOf_gt (lo : Int) (w : List Bool) (a : List Int)
    (h : pairsAsc lo w a = true) : ∀ y ∈ pairsOf w a, lo < y := by
  induction w generalizing lo a with
  | nil => intro y hy; cases hy
  | cons b w ih =>
    cases a with
    | nil => simp at h
    | cons x a =>
      rw [pairsAsc_cons_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      intro y hy
      rw [pairsOf_cons] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h.1
      rcases List.mem_cons.mp hy with rfl | hy
      · have := gap_pos b; omega
      · have := ih (x + gap b) a h.2 y hy
        have := gap_pos b
        omega

/-- The bag of a valid family of pairs is strictly increasing. -/
theorem pairsOf_pairwise (lo : Int) (w : List Bool) (a : List Int)
    (h : pairsAsc lo w a = true) : (pairsOf w a).Pairwise (· < ·) := by
  induction w generalizing lo a with
  | nil => exact List.Pairwise.nil
  | cons b w ih =>
    cases a with
    | nil => simp at h
    | cons x a =>
      rw [pairsAsc_cons_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [pairsOf_cons]
      have htail := ih (x + gap b) a h.2
      have hgt := pairsOf_gt (x + gap b) w a h.2
      have hg := gap_pos b
      refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, htail⟩⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · have := hgt y hy; omega
      · intro y hy
        exact hgt y hy

/-- The bag of a valid family of pairs has no duplicates. -/
theorem pairsOf_nodup (lo : Int) (w : List Bool) (a : List Int)
    (h : pairsAsc lo w a = true) : (pairsOf w a).Nodup := by
  have hp := pairsOf_pairwise lo w a h
  refine List.Pairwise.imp ?_ hp
  intro x y hxy
  omega

/-- Lowering the bound preserves `pairsAsc`. -/
theorem pairsAsc_mono (lo lo' : Int) (w : List Bool) (a : List Int)
    (hle : lo' ≤ lo) (h : pairsAsc lo w a = true) : pairsAsc lo' w a = true := by
  cases w with
  | nil => cases a with
    | nil => rfl
    | cons x a => simp at h
  | cons b w =>
    cases a with
    | nil => simp at h
    | cons x a =>
      rw [pairsAsc_cons_cons, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨by omega, h.2⟩

/-- A strictly increasing bag that is a permutation of a family of pairs is
    that family of pairs.  This is what lets a `decide`-checked negative
    example refute the existential over the starts. -/
theorem eq_pairsOf_of_perm (lo : Int) (w : List Bool) (a : List Int) (bag : List Int)
    (hasc : pairsAsc lo w a = true) (hperm : bag.Perm (pairsOf w a))
    (hsorted : bag.Pairwise (· < ·)) : bag = pairsOf w a :=
  List.Perm.eq_of_pairwise (le := (· < ·))
    (fun x y _ _ h1 h2 => by omega) hsorted (pairsOf_pairwise lo w a hasc) hperm

/-! ## The rule side: rule pairs of doubled appendants -/

/-- The System 5 rule pair of one appendant of a DOUBLED cyclic tag system
    (TM23Proof.pdf p. 19).  The appendant is read two bits at a time, since
    doubling makes every bit occur twice: a pair of `0`s contributes
    `i, i+1` to the second rule and advances the counter by 4, a pair of
    `1`s contributes `i, i+3` and advances it by 6.  The first rule is the
    second with 2 added to each integer. -/
def encodePaired : List Bool → Int → List Int × List Int × Int
  | true :: _ :: rest, i =>
      let (r1, r2, i') := encodePaired rest (i + 6)
      ((i + 2) :: (i + 5) :: r1, i :: (i + 3) :: r2, i')
  | false :: _ :: rest, i =>
      let (r1, r2, i') := encodePaired rest (i + 4)
      ((i + 2) :: (i + 3) :: r1, i :: (i + 1) :: r2, i')
  | _, i => ([], [], i)

/-- A blank appendant encodes to a blank rule pair. -/
@[simp] theorem encodePaired_nil (i : Int) : encodePaired [] i = ([], [], i) := rfl

/-- On a doubled appendant, `encodePaired` is the `cy2s5.pl` appendant
    encoder of the undoubled appendant. -/
theorem encodePaired_dbl (a : List Bool) (i : Int) :
    encodePaired (dbl a) i = encodeAppendant a i := by
  induction a generalizing i with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | true =>
      show (let (r1, r2, i') := encodePaired (dbl rest) (i + 6)
            ((i + 2) :: (i + 5) :: r1, i :: (i + 3) :: r2, i')) = _
      rw [ih (i + 6)]
      rfl
    | false =>
      show (let (r1, r2, i') := encodePaired (dbl rest) (i + 4)
            ((i + 2) :: (i + 3) :: r1, i :: (i + 1) :: r2, i')) = _
      rw [ih (i + 4)]
      rfl

/-- The first rule of a pair is the second with 2 added to each integer. -/
theorem encodePaired_fst_eq_snd_add_two (w : List Bool) (i : Int) :
    (encodePaired w i).1 = (encodePaired w i).2.1.map (· + 2) := by
  induction w, i using encodePaired.induct with
  | case1 b rest i r1 r2 i' heq ih =>
    show (i + 2) :: (i + 5) :: (encodePaired rest (i + 6)).1
       = ((i : Int) :: (i + 3) :: (encodePaired rest (i + 6)).2.1).map (· + 2)
    rw [show (((i : Int) :: (i + 3) :: (encodePaired rest (i + 6)).2.1).map (· + 2))
          = (i + 2) :: (i + 3 + 2) :: ((encodePaired rest (i + 6)).2.1.map (· + 2)) from rfl,
        ← ih, show (i : Int) + 3 + 2 = i + 5 from by omega]
  | case2 b rest i r1 r2 i' heq ih =>
    show (i + 2) :: (i + 3) :: (encodePaired rest (i + 4)).1
       = ((i : Int) :: (i + 1) :: (encodePaired rest (i + 4)).2.1).map (· + 2)
    rw [show (((i : Int) :: (i + 1) :: (encodePaired rest (i + 4)).2.1).map (· + 2))
          = (i + 2) :: (i + 1 + 2) :: ((encodePaired rest (i + 4)).2.1.map (· + 2)) from rfl,
        ← ih, show (i : Int) + 1 + 2 = i + 3 from by omega]
  | case3 t i h1 h2 =>
    cases t with
    | nil => rfl
    | cons b t' =>
      cases t' with
      | nil => cases b <;> rfl
      | cons b2 rest =>
        cases b with
        | true => exact (h1 b2 rest rfl).elim
        | false => exact (h2 b2 rest rfl).elim

/-- The rule pairs of a list of (doubled) appendants, threading the rule
    counter: two System 5 rules per appendant. -/
def ruleBlocks : List (List Bool) → Int → List (List Int) × Int
  | [], i => ([], i)
  | w :: ws, i =>
      let (r1, r2, i') := encodePaired w i
      let (rs, i'') := ruleBlocks ws i'
      (r1 :: r2 :: rs, i'')

/-- No appendants, no rules. -/
@[simp] theorem ruleBlocks_nil (i : Int) : ruleBlocks [] i = ([], i) := rfl

/-- One appendant contributes its two rules. -/
theorem ruleBlocks_cons (w : List Bool) (ws : List (List Bool)) (i : Int) :
    ruleBlocks (w :: ws) i
      = ((encodePaired w i).1 :: (encodePaired w i).2.1 ::
           (ruleBlocks ws (encodePaired w i).2.2).1,
         (ruleBlocks ws (encodePaired w i).2.2).2) := rfl

/-- Rule blocks of a concatenation. -/
theorem ruleBlocks_append (l1 l2 : List (List Bool)) (i : Int) :
    ruleBlocks (l1 ++ l2) i
      = ((ruleBlocks l1 i).1 ++ (ruleBlocks l2 (ruleBlocks l1 i).2).1,
         (ruleBlocks l2 (ruleBlocks l1 i).2).2) := by
  induction l1 generalizing i with
  | nil => rfl
  | cons w ws ih =>
    rw [List.cons_append, ruleBlocks_cons, ruleBlocks_cons, ih]
    rfl

/-- Two rules per appendant. -/
theorem ruleBlocks_length (l : List (List Bool)) (i : Int) :
    (ruleBlocks l i).1.length = 2 * l.length := by
  induction l generalizing i with
  | nil => rfl
  | cons w ws ih =>
    rw [ruleBlocks_cons]
    simp only [List.length_cons, ih]
    omega

/-- The appendants a cyclic tag system reads at the `n` consecutive phases
    starting at `phase`. -/
def appendantsFrom (C : CTS) (phase : Nat) : Nat → List (List Bool)
  | 0 => []
  | n + 1 => C.currentAppendant phase :: appendantsFrom C (phase + 1) n

/-- No phases, no appendants. -/
@[simp] theorem appendantsFrom_zero (C : CTS) (p : Nat) : appendantsFrom C p 0 = [] := rfl

/-- One phase peeled off the front. -/
theorem appendantsFrom_succ (C : CTS) (p n : Nat) :
    appendantsFrom C p (n + 1) = C.currentAppendant p :: appendantsFrom C (p + 1) n := rfl

/-- One appendant per phase. -/
@[simp] theorem appendantsFrom_length (C : CTS) (p n : Nat) :
    (appendantsFrom C p n).length = n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [appendantsFrom_succ, ih]

/-- Phases add. -/
theorem appendantsFrom_add (C : CTS) (p m n : Nat) :
    appendantsFrom C p (m + n) = appendantsFrom C p m ++ appendantsFrom C (p + m) n := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, appendantsFrom_succ, appendantsFrom_succ,
        ih (p + 1), show p + 1 + m = p + (m + 1) by omega]
    rfl

/-- Lookup in `appendantsFrom`. -/
theorem appendantsFrom_getElem? (C : CTS) (p n j : Nat) (hj : j < n) :
    (appendantsFrom C p n)[j]? = some (C.currentAppendant (p + j)) := by
  induction n generalizing p j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [appendantsFrom_succ]
    | succ j =>
      rw [appendantsFrom_succ, List.getElem?_cons_succ, ih (p + 1) j (by omega),
          show p + 1 + j = p + (j + 1) by omega]

/-- A full turn of the phase changes nothing. -/
theorem currentAppendant_add_length (C : CTS) (p : Nat) :
    C.currentAppendant (p + C.appendants.length) = C.currentAppendant p := by
  have h1 := currentAppendant_getElem? C (p + C.appendants.length)
  rw [Nat.add_mod_right] at h1
  exact Option.some.inj (h1.symm.trans (currentAppendant_getElem? C p))

/-- `appendantsFrom` is periodic in the phase. -/
theorem appendantsFrom_period (C : CTS) (p n : Nat) :
    appendantsFrom C (p + C.appendants.length) n = appendantsFrom C p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [appendantsFrom_succ, appendantsFrom_succ, currentAppendant_add_length,
        show p + C.appendants.length + 1 = (p + 1) + C.appendants.length by omega, ih]

/-- Lookup in a rotated list. -/
theorem rotateLeft_getElem? {alpha : Type u} (l : List alpha) (r j : Nat)
    (hr : r < l.length) (hj : j < l.length) :
    (l.rotateLeft r)[j]? = l[(r + j) % l.length]? := by
  by_cases h1 : l.length ≤ 1
  · have hr0 : r = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hr0
    subst hj0
    have hrot : l.rotateLeft 0 = l := by
      show (if l.length ≤ 1 then l else
            List.drop (0 % l.length) l ++ List.take (0 % l.length) l) = l
      rw [if_pos h1]
    rw [hrot, Nat.zero_add, Nat.mod_eq_of_lt hj]
  · have hrot : l.rotateLeft r = List.drop r l ++ List.take r l := by
      show (if l.length ≤ 1 then l else
            List.drop (r % l.length) l ++ List.take (r % l.length) l) = _
      rw [if_neg h1, Nat.mod_eq_of_lt hr]
    rw [hrot]
    by_cases hj2 : j < l.length - r
    · rw [List.getElem?_append_left (by simp; omega)]
      simp only [List.getElem?_drop]
      congr 1
      exact (Nat.mod_eq_of_lt (by omega)).symm
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_drop]
      rw [List.getElem?_take_of_lt (by omega)]
      congr 1
      have hmod : (r + j) % l.length = r + j - l.length := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      omega

/-- The appendants read over one full turn are the appendant list rotated to
    start at the current phase: this identifies `appendantsFrom` with the
    `appendantsFromPhase` of the `cy2s5.pl` encoder. -/
theorem appendantsFrom_full (C : CTS) (p : Nat) :
    appendantsFrom C p C.appendants.length
      = C.appendants.rotateLeft (p % C.appendants.length) := by
  have hk : 0 < C.appendants.length := C.nonempty
  have hlen : (C.appendants.rotateLeft (p % C.appendants.length)).length
      = C.appendants.length := BiTM.length_rotateLeft _ _
  apply List.ext_getElem?
  intro j
  by_cases hj : j < C.appendants.length
  · rw [appendantsFrom_getElem? C p _ j hj,
        rotateLeft_getElem? C.appendants (p % C.appendants.length) j
          (Nat.mod_lt _ hk) hj]
    rw [Nat.mod_add_mod, currentAppendant_getElem? C (p + j)]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by rw [hlen]; omega)]

/-! ## The doubled system and the `cy2s5.pl` encoder -/

/-- Over a doubled system, `appendantsFrom` at an even phase interleaves the
    doubled appendants of the original system with blanks. -/
theorem appendantsFrom_double (C : CTS) (p m : Nat) :
    appendantsFrom (double C) (2 * p) (2 * m)
      = (appendantsFrom C p m).flatMap (fun a => [dbl a, []]) := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, appendantsFrom_succ,
        appendantsFrom_succ, double_currentAppendant_even,
        double_currentAppendant_odd,
        show 2 * p + 1 + 1 = 2 * (p + 1) by omega, ih (p + 1),
        appendantsFrom_succ]
    simp

/-- Rule blocks of an interleaved doubled appendant list are exactly the
    four rules per appendant of `cy2s5.pl` (`processCycle`). -/
theorem ruleBlocks_flatMap (L : List (List Bool)) (i : Int) :
    ruleBlocks (L.flatMap (fun a => [dbl a, []])) i = processCycle L i := by
  induction L generalizing i with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatMap_cons]
    show ruleBlocks (dbl a :: [] :: rest.flatMap (fun a => [dbl a, []])) i = _
    rw [ruleBlocks_cons, ruleBlocks_cons, encodePaired_dbl, encodePaired_nil,
        ih (encodeAppendant a i).2.2, processCycle_cons]

/-- Rule blocks over a doubled system, from an even phase, are the rules
    `cy2s5.pl` emits for the original system from the matching phase. -/
theorem ruleBlocks_appendantsFrom_double (C : CTS) (p m : Nat) (i : Int) :
    ruleBlocks (appendantsFrom (double C) (2 * p) (2 * m)) i
      = processCycle (appendantsFrom C p m) i := by
  rw [appendantsFrom_double, ruleBlocks_flatMap]

/-- `processCycle` over a concatenation. -/
theorem processCycle_append (l1 l2 : List (List Bool)) (i : Int) :
    processCycle (l1 ++ l2) i
      = ((processCycle l1 i).1 ++ (processCycle l2 (processCycle l1 i).2).1,
         (processCycle l2 (processCycle l1 i).2).2) := by
  induction l1 generalizing i with
  | nil => rfl
  | cons a rest ih =>
    rw [List.cons_append, processCycle_cons, processCycle_cons, ih]
    rfl

/-- One full turn of `processCycle` over the appendants read from phase `p`
    is one `cy2s5.pl` cycle over the rotated appendant list. -/
theorem processCycle_appendantsFrom_cycles (C : CTS) (p N : Nat) (i : Int) :
    (processCycle (appendantsFrom C p (C.appendants.length * N)) i).1
      = nCycles (C.appendants.rotateLeft (p % C.appendants.length)) N i := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
    have harith : C.appendants.length * (N + 1)
        = C.appendants.length + C.appendants.length * N := by
      rw [Nat.mul_succ]; omega
    rw [harith, appendantsFrom_add, appendantsFrom_period, processCycle_append,
        nCycles_succ, appendantsFrom_full]
    dsimp only
    congr 1
    exact ih _

/-! ## Bounds on rule blocks -/

/-- Encoding an appendant never lowers the rule counter. -/
theorem encodePaired_counter_ge (w : List Bool) (i : Int) : i ≤ (encodePaired w i).2.2 := by
  induction w, i using encodePaired.induct with
  | case1 b rest i r1 r2 i' heq ih =>
    show i ≤ (encodePaired rest (i + 6)).2.2
    omega
  | case2 b rest i r1 r2 i' heq ih =>
    show i ≤ (encodePaired rest (i + 4)).2.2
    omega
  | case3 t i h1 h2 =>
    cases t with
    | nil => exact Int.le_refl i
    | cons b t' =>
      cases t' with
      | nil => cases b <;> exact Int.le_refl i
      | cons b2 rest =>
        cases b with
        | true => exact (h1 b2 rest rfl).elim
        | false => exact (h2 b2 rest rfl).elim

/-- Every integer of the first rule of a pair is at least the rule counter. -/
theorem encodePaired_fst_ge (w : List Bool) (i : Int) :
    ∀ x ∈ (encodePaired w i).1, i ≤ x := by
  induction w, i using encodePaired.induct with
  | case1 b rest i r1 r2 i' heq ih =>
    show ∀ x ∈ (i + 2) :: (i + 5) :: (encodePaired rest (i + 6)).1, i ≤ x
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih x hx; omega
  | case2 b rest i r1 r2 i' heq ih =>
    show ∀ x ∈ (i + 2) :: (i + 3) :: (encodePaired rest (i + 4)).1, i ≤ x
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih x hx; omega
  | case3 t i h1 h2 =>
    cases t with
    | nil => intro x hx; cases hx
    | cons b t' =>
      cases t' with
      | nil => cases b <;> (intro x hx; cases hx)
      | cons b2 rest =>
        cases b with
        | true => exact (h1 b2 rest rfl).elim
        | false => exact (h2 b2 rest rfl).elim

/-- Every integer of the second rule of a pair is at least the rule counter. -/
theorem encodePaired_snd_ge (w : List Bool) (i : Int) :
    ∀ x ∈ (encodePaired w i).2.1, i ≤ x := by
  induction w, i using encodePaired.induct with
  | case1 b rest i r1 r2 i' heq ih =>
    show ∀ x ∈ i :: (i + 3) :: (encodePaired rest (i + 6)).2.1, i ≤ x
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih x hx; omega
  | case2 b rest i r1 r2 i' heq ih =>
    show ∀ x ∈ i :: (i + 1) :: (encodePaired rest (i + 4)).2.1, i ≤ x
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih x hx; omega
  | case3 t i h1 h2 =>
    cases t with
    | nil => intro x hx; cases hx
    | cons b t' =>
      cases t' with
      | nil => cases b <;> (intro x hx; cases hx)
      | cons b2 rest =>
        cases b with
        | true => exact (h1 b2 rest rfl).elim
        | false => exact (h2 b2 rest rfl).elim

/-- A block of rules never lowers the rule counter. -/
theorem ruleBlocks_counter_ge (L : List (List Bool)) (i : Int) : i ≤ (ruleBlocks L i).2 := by
  induction L generalizing i with
  | nil => exact Int.le_refl i
  | cons w ws ih =>
    rw [ruleBlocks_cons]
    have h1 := encodePaired_counter_ge w i
    have h2 := ih (encodePaired w i).2.2
    omega

/-- Every integer of every rule of a block is at least the starting rule
    counter.  With the `Represents` clause `x + 3 <= i` for every bag
    element this is Smith's condition that the second rule of each pair sits
    at least 3 above everything in the bag (TM23Proof.pdf p. 19). -/
theorem ruleBlocks_ge (L : List (List Bool)) (i : Int) :
    ∀ r ∈ (ruleBlocks L i).1, ∀ x ∈ r, i ≤ x := by
  induction L generalizing i with
  | nil => intro r hr; cases hr
  | cons w ws ih =>
    rw [ruleBlocks_cons]
    intro r hr x hx
    rcases List.mem_cons.mp hr with rfl | hr
    · exact encodePaired_fst_ge w i x hx
    rcases List.mem_cons.mp hr with rfl | hr
    · exact encodePaired_snd_ge w i x hx
    · have h1 := ih (encodePaired w i).2.2 r hr x hx
      have h2 := encodePaired_counter_ge w i
      omega

/-! ## The canonical encoder as a family of pairs -/

/-- The lower integers of the pairs of a doubled working string, as
    `cy2s5.pl` lays them out from counter `i`: a `0` bit of the original
    string contributes starts `i` and `i + 2`, a `1` bit `i` and `i + 3`. -/
def startsOf : List Bool → Int → List Int
  | [], _ => []
  | true :: rest, i => i :: (i + 3) :: startsOf rest (i + 6)
  | false :: rest, i => i :: (i + 2) :: startsOf rest (i + 4)

/-- The `cy2s5.pl` bag is exactly the family of pairs of `startsOf` over the
    doubled working string. -/
theorem pairsOf_dbl_startsOf (data : List Bool) (i : Int) :
    pairsOf (dbl data) (startsOf data i) = ctsConfigToSystem5BagAux data i := by
  induction data generalizing i with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | true =>
      show (i : Int) :: (i + gap true) :: (i + 3) :: (i + 3 + gap true) ::
           pairsOf (dbl rest) (startsOf rest (i + 6))
         = (i : Int) :: (i + 2) :: (i + 3) :: (i + 5) ::
           ctsConfigToSystem5BagAux rest (i + 6)
      rw [ih (i + 6), show gap true = 2 from rfl,
          show (i : Int) + 3 + 2 = i + 5 from by omega]
    | false =>
      show (i : Int) :: (i + gap false) :: (i + 2) :: (i + 2 + gap false) ::
           pairsOf (dbl rest) (startsOf rest (i + 4))
         = (i : Int) :: (i + 1) :: (i + 2) :: (i + 3) ::
           ctsConfigToSystem5BagAux rest (i + 4)
      rw [ih (i + 4), show gap false = 1 from rfl,
          show (i : Int) + 2 + 1 = i + 3 from by omega]

/-- The `cy2s5.pl` starts satisfy the ascending condition. -/
theorem pairsAsc_dbl_startsOf (data : List Bool) (lo i : Int) (h : lo < i) :
    pairsAsc lo (dbl data) (startsOf data i) = true := by
  induction data generalizing lo i with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | true =>
      show (decide (lo < i) && (decide (i + gap true < i + 3) &&
            pairsAsc (i + 3 + gap true) (dbl rest) (startsOf rest (i + 6)))) = true
      rw [show gap true = 2 from rfl, show (i : Int) + 3 + 2 = i + 5 from by omega,
          ih (i + 5) (i + 6) (by omega)]
      simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
      omega
    | false =>
      show (decide (lo < i) && (decide (i + gap false < i + 2) &&
            pairsAsc (i + 2 + gap false) (dbl rest) (startsOf rest (i + 4)))) = true
      rw [show gap false = 1 from rfl, show (i : Int) + 2 + 1 = i + 3 from by omega,
          ih (i + 3) (i + 4) (by omega)]
      simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
      omega

/-- The `cy2s5.pl` counter never decreases. -/
theorem foldl_counter_ge (data : List Bool) (i : Int) :
    i ≤ data.foldl (fun acc b => acc + if b then (6 : Int) else 4) i := by
  induction data generalizing i with
  | nil => exact Int.le_refl i
  | cons b rest ih =>
    show i ≤ rest.foldl (fun acc b => acc + if b then (6 : Int) else 4)
      (i + if b then (6 : Int) else 4)
    have := ih (i + if b then (6 : Int) else 4)
    cases b <;> simp at this ⊢ <;> omega

/-- Every bag entry lies strictly below the counter the working-string loop
    ends at; this is what makes the rule counter sit 3 above the bag. -/
theorem bagAux_lt_counter (data : List Bool) (i : Int) :
    ∀ x ∈ ctsConfigToSystem5BagAux data i,
      x + 1 ≤ data.foldl (fun acc b => acc + if b then (6 : Int) else 4) i := by
  induction data generalizing i with
  | nil => intro x hx; cases hx
  | cons b rest ih =>
    cases b with
    | true =>
      intro x hx
      have hfold : (true :: rest).foldl (fun acc b => acc + if b then (6 : Int) else 4) i
          = rest.foldl (fun acc b => acc + if b then (6 : Int) else 4) (i + 6) := by
        simp
      have hge := foldl_counter_ge rest (i + 6)
      rw [hfold]
      have hx' : x ∈ (i : Int) :: (i + 2) :: (i + 3) :: (i + 5) ::
        ctsConfigToSystem5BagAux rest (i + 6) := hx
      rcases List.mem_cons.mp hx' with rfl | hx
      · omega
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact ih (i + 6) x hx
    | false =>
      intro x hx
      have hfold : (false :: rest).foldl (fun acc b => acc + if b then (6 : Int) else 4) i
          = rest.foldl (fun acc b => acc + if b then (6 : Int) else 4) (i + 4) := by
        simp
      have hge := foldl_counter_ge rest (i + 4)
      rw [hfold]
      have hx' : x ∈ (i : Int) :: (i + 1) :: (i + 2) :: (i + 3) ::
        ctsConfigToSystem5BagAux rest (i + 4) := hx
      rcases List.mem_cons.mp hx' with rfl | hx
      · omega
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact ih (i + 4) x hx

/-! ## The representation relation -/

/-- `Represents s C c budget`: the System 5 configuration `s` is a
    canonically spaced acceptable initial condition (TM23Proof.pdf p. 19)
    for the DOUBLED cyclic tag system `C` in configuration `c`, good for at
    least `budget` further appendants.

    Clause one: the bag is a permutation of the pairs of some strictly
    increasing list of starts, one pair per bit of the working string, with
    a gap of 1 for a `0` and of 2 for a `1`, all above 0.

    Clause two: the rule list starts with the rule pairs of the `budget`
    appendants the system reads from the current phase onward, encoded from
    some counter `i` that sits at least 3 above every bag element, followed
    by an arbitrary unconstrained tail.  Existential in `i` and in the tail,
    so the clause survives a uniform increment of the rules and the dropping
    of consumed rule groups.

    Clause two pins the canonical `cy2s5.pl` spacing and is therefore a
    strict sub-relation of Smith's p. 19 condition, which allows any spacing
    of at least 3; see the fidelity note in the file header.  `C` must be a
    doubled system for the clause to be meaningful. -/
def Represents (s : System5Config) (C : CTS) (c : CTSConfig) (budget : Nat) : Prop :=
  (∃ a : List Int, pairsAsc 0 c.data a = true ∧ s.bag.Perm (pairsOf c.data a)) ∧
  (∃ (i : Int) (rest : List (List Int)),
      (∀ x ∈ s.bag, x + 3 ≤ i) ∧
      s.rules = (ruleBlocks (appendantsFrom C c.phase budget) i).1 ++ rest)

/-- The bag clause as an equality of multisets. -/
theorem Represents_bag_multiset (s : System5Config) (C : CTS) (c : CTSConfig) (b : Nat)
    (h : Represents s C c b) :
    ∃ a : List Int, pairsAsc 0 c.data a = true ∧
      (s.bag : Multiset Int) = (pairsOf c.data a : Multiset Int) := by
  obtain ⟨⟨a, hasc, hperm⟩, -⟩ := h
  exact ⟨a, hasc, Quot.sound hperm⟩

/-- A represented bag has no duplicates, the invariant under which
    `System5.step` is faithful to `system5.pl`. -/
theorem Represents_bag_nodup (s : System5Config) (C : CTS) (c : CTSConfig) (b : Nat)
    (h : Represents s C c b) : s.bag.Nodup := by
  obtain ⟨⟨a, hasc, hperm⟩, -⟩ := h
  exact hperm.symm.nodup (pairsOf_nodup 0 c.data a hasc)

/-- A represented bag contains no 0, as Conjecture 5 requires. -/
theorem Represents_bag_ge_one (s : System5Config) (C : CTS) (c : CTSConfig) (b : Nat)
    (h : Represents s C c b) : ∀ x ∈ s.bag, 1 ≤ x := by
  obtain ⟨⟨a, hasc, hperm⟩, -⟩ := h
  intro x hx
  have := pairsOf_gt 0 c.data a hasc x (hperm.subset hx)
  omega

/-- Two bag entries per bit of the working string. -/
theorem Represents_bag_length (s : System5Config) (C : CTS) (c : CTSConfig) (b : Nat)
    (h : Represents s C c b) : s.bag.length = 2 * c.data.length := by
  obtain ⟨⟨a, hasc, hperm⟩, -⟩ := h
  rw [hperm.length_eq, pairsOf_length 0 c.data a hasc]

/-- Non-degeneracy: a nonempty working string forces a nonempty bag.  This is
    the "no degenerate witness" theorem of PLAN.md section 6 for link B. -/
theorem Represents_bag_ne_nil_of_data_ne_nil (s : System5Config) (C : CTS)
    (c : CTSConfig) (b : Nat) (h : Represents s C c b) (hd : c.data ≠ []) :
    s.bag ≠ [] := by
  intro hbag
  have hlen := Represents_bag_length s C c b h
  rw [hbag, List.length_nil] at hlen
  have : c.data.length ≠ 0 := by
    intro hc
    exact hd (List.eq_nil_of_length_eq_zero hc)
  omega

/-- Non-degeneracy, converse form: a nonempty bag forces a nonempty working
    string. -/
theorem Represents_data_ne_nil_of_bag_ne_nil (s : System5Config) (C : CTS)
    (c : CTSConfig) (b : Nat) (h : Represents s C c b) (hb : s.bag ≠ []) :
    c.data ≠ [] := by
  intro hdata
  have hlen := Represents_bag_length s C c b h
  rw [hdata, List.length_nil] at hlen
  exact hb (List.eq_nil_of_length_eq_zero (by omega))

/-- Structural fact: the first rule of the leading pair is the second with 2
    added to each integer, which is what makes the second cancel the first
    when it surfaces. -/
theorem Represents_rules_pair (s : System5Config) (C : CTS) (c : CTSConfig) (b : Nat)
    (h : Represents s C c b) (hb : 1 ≤ b) :
    ∃ r1 r2 tl, s.rules = r1 :: r2 :: tl ∧ r1 = r2.map (· + 2) := by
  obtain ⟨-, i, rest, -, hrules⟩ := h
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [appendantsFrom_succ, ruleBlocks_cons] at hrules
  refine ⟨_, _, _, hrules, ?_⟩
  exact encodePaired_fst_eq_snd_add_two (C.currentAppendant c.phase) i

/-- Structural fact: every integer of every rule of the leading blocks sits
    at least 3 above every element of the bag. -/
theorem Represents_rules_ge (s : System5Config) (C : CTS) (c : CTSConfig) (b : Nat)
    (h : Represents s C c b) :
    ∃ i, (∀ x ∈ s.bag, x + 3 ≤ i) ∧
      (∀ r ∈ (ruleBlocks (appendantsFrom C c.phase b) i).1, ∀ x ∈ r,
        ∀ y ∈ s.bag, y + 3 ≤ x) := by
  obtain ⟨-, i, rest, hbound, hrules⟩ := h
  refine ⟨i, hbound, ?_⟩
  intro r hr x hx y hy
  have h1 := ruleBlocks_ge (appendantsFrom C c.phase b) i r hr x hx
  have h2 := hbound y hy
  omega

/-- Structural fact: in a doubled system an odd phase reads the blank
    appendant, so its rule pair is a pair of blank rules. -/
theorem ruleBlocks_odd_phase_blank (C : CTS) (p m : Nat) (i : Int) :
    (ruleBlocks (appendantsFrom (double C) (2 * p + 1) (m + 1)) i).1
      = [] :: [] :: (ruleBlocks (appendantsFrom (double C) (2 * p + 2) m) i).1 := by
  rw [appendantsFrom_succ, ruleBlocks_cons, double_currentAppendant_odd,
      encodePaired_nil, show 2 * p + 1 + 1 = 2 * p + 2 from rfl]

/-- Structural fact, at the level of the relation: a System 5 configuration
    representing a doubled system at an odd phase has two blank rules in
    front. -/
theorem Represents_blank_rules (s : System5Config) (C : CTS) (c : CTSConfig)
    (p b : Nat) (h : Represents s (double C) c b) (hphase : c.phase = 2 * p + 1)
    (hb : 1 ≤ b) : ∃ tl, s.rules = [] :: [] :: tl := by
  obtain ⟨-, i, rest, -, hrules⟩ := h
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [hphase, ruleBlocks_odd_phase_blank] at hrules
  exact ⟨_, hrules⟩

/-! ## The base case: the `cy2s5.pl` encoder represents -/

/-- The canonical `cy2s5.pl` encoder output represents the doubled system.
    The budget is `2 * |appendants| * N`, the number of appendants of the
    doubled system times the number of full cycles the encoder emitted.

    Stronger than the form quoted in PLAN.md section 2: neither `1 <= N` nor
    `cfg.data <> []` is needed.  With those two hypotheses the relation is
    additionally non-degenerate, see `ctsToSystem5_represents_nontrivial`. -/
theorem ctsToSystem5_represents (C : CTS) (cfg : CTSConfig) (N : Nat) :
    Represents (ctsToSystem5 C cfg N) (double C) (dblCfg cfg)
      (2 * (C.appendants.length * N)) := by
  constructor
  · refine ⟨startsOf cfg.data 1, pairsAsc_dbl_startsOf cfg.data 0 1 (by omega), ?_⟩
    show (ctsConfigToSystem5Bag cfg).Perm (pairsOf (dbl cfg.data) (startsOf cfg.data 1))
    rw [pairsOf_dbl_startsOf]
    exact List.Perm.refl _
  · refine ⟨counterAfterWorkingString cfg.data + 2, [], ?_, ?_⟩
    · intro x hx
      have hb : x ∈ ctsConfigToSystem5BagAux cfg.data 1 := hx
      have := bagAux_lt_counter cfg.data 1 x hb
      have hc : counterAfterWorkingString cfg.data
          = cfg.data.foldl (fun acc b => acc + if b then (6 : Int) else 4) 1 := rfl
      omega
    · show ctsRulesToSystem5Rules C cfg N
        = (ruleBlocks (appendantsFrom (double C) (2 * cfg.phase)
            (2 * (C.appendants.length * N))) (counterAfterWorkingString cfg.data + 2)).1 ++ []
      rw [List.append_nil, ruleBlocks_appendantsFrom_double,
          processCycle_appendantsFrom_cycles]
      rfl

/-- Non-degeneracy of the base case: with at least one cycle and a nonempty
    working string the represented configuration has a nonempty bag and a
    nonempty rule list, so the relation is not the trivial one. -/
theorem ctsToSystem5_represents_nontrivial (C : CTS) (cfg : CTSConfig) (N : Nat)
    (hN : 1 ≤ N) (hdata : cfg.data ≠ []) :
    (ctsToSystem5 C cfg N).bag ≠ [] ∧ (ctsToSystem5 C cfg N).rules ≠ [] ∧
      1 ≤ 2 * (C.appendants.length * N) := by
  refine ⟨?_, ctsRulesToSystem5Rules_ne_nil C cfg N hN, ?_⟩
  · exact Represents_bag_ne_nil_of_data_ne_nil _ _ _ _
      (ctsToSystem5_represents C cfg N) (by simpa using hdata)
  · have := C.nonempty
    have : 1 ≤ C.appendants.length * N := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    omega

/-! ## Non-degeneracy examples

The `cy2s5.pl 3 01 1 10` example of TM23Proof.pdf p. 29: working string
`01`, appendants `1` and `10`, bag `1,2,3,4,5,7,8,10` and rules
`15,18 / 13,16 / "" / "" / 21,24,27,28 / 19,22,25,26 / "" / ""`.

At budget 0 the rules clause is vacuous (no appendant is constrained, the
whole rule list is the unconstrained tail) and `Represents` reduces to the
bag clause, as `ex_represents_budget_zero` records.  The two negative
examples that follow the positive one fail on the bag clause alone; the two
after them, `ex_not_represents_low_counter` and
`ex_not_represents_swapped_rules`, fail on the rules clause alone, at
budget 1.  The p. 19 pair at the end of the section pins the
canonical-spacing restriction described in the file header. -/

/-- The cyclic tag system `01 1 10` of TM23Proof.pdf p. 29. -/
def exCTS : CTS where
  appendants := [[true], [true, false]]
  nonempty := by decide

/-- Its initial configuration, working string `01`. -/
def exCfg : CTSConfig := { data := [false, true], phase := 0 }

/-- The `cy2s5.pl` output of TM23Proof.pdf p. 29. -/
theorem ex_encoder :
    ctsToSystem5 exCTS exCfg 1
      = { bag := [1, 2, 3, 4, 5, 7, 8, 10],
          rules := [[15, 18], [13, 16], [], [], [21, 24, 27, 28], [19, 22, 25, 26], [], []] } := by
  decide

/-- Positive example: the p. 29 configuration represents the doubled system,
    with starts `1, 3, 5, 8` for the doubled working string `0011` and rule
    counter 13. -/
theorem ex_represents :
    Represents (ctsToSystem5 exCTS exCfg 1) (double exCTS) (dblCfg exCfg) 4 :=
  ⟨⟨[1, 3, 5, 8], by decide, by decide⟩, ⟨13, [], by decide, by decide⟩⟩

/-- The same fact from the general base-case theorem. -/
theorem ex_represents_general :
    Represents (ctsToSystem5 exCTS exCfg 1) (double exCTS) (dblCfg exCfg) 4 :=
  ctsToSystem5_represents exCTS exCfg 1

/-- Negative example: the bag `1,2,3,5,6,8,15,18` is not an acceptable
    initial condition for the doubled working string `0011`; its second pair
    has gap 2 where the word asks for 1. -/
theorem ex_not_represents_wrong_bag (rules : List (List Int)) (b : Nat) :
    ¬ Represents { bag := [1, 2, 3, 5, 6, 8, 15, 18], rules := rules }
        (double exCTS) (dblCfg exCfg) b := by
  rintro ⟨⟨a, hasc, hperm⟩, -⟩
  have hdata : (dblCfg exCfg).data = [false, false, true, true] := by decide
  rw [hdata] at hasc hperm
  have hsorted : ([1, 2, 3, 5, 6, 8, 15, 18] : List Int).Pairwise (· < ·) := by decide
  have heq := eq_pairsOf_of_perm 0 [false, false, true, true] a
    [1, 2, 3, 5, 6, 8, 15, 18] hasc hperm hsorted
  rcases a with _ | ⟨a0, a⟩
  · simp at heq
  rcases a with _ | ⟨a1, a⟩
  · simp [gap] at heq
  rcases a with _ | ⟨a2, a⟩
  · simp [gap] at heq
  rcases a with _ | ⟨a3, a⟩
  · simp [gap] at heq
  · simp [gap] at heq
    omega

/-- Negative example: the empty bag never represents a nonempty working
    string. -/
theorem ex_not_represents_empty_bag (rules : List (List Int)) (b : Nat) :
    ¬ Represents { bag := [], rules := rules } (double exCTS) (dblCfg exCfg) b := by
  intro h
  have hlen := Represents_bag_length _ _ _ _ h
  have hdata : (dblCfg exCfg).data = [false, false, true, true] := by decide
  rw [hdata] at hlen
  simp at hlen

/-- Positive example for `pairsAsc` itself: the starts `1, 3, 5, 8` fit the
    word `0011`. -/
theorem ex_pairsAsc_pos : pairsAsc 0 [false, false, true, true] [1, 3, 5, 8] = true := by
  decide

/-- Negative example for `pairsAsc`: the same starts do not fit the word
    `1111`, whose gaps of 2 leave no room between the second and third
    pair. -/
theorem ex_pairsAsc_neg : pairsAsc 0 [true, true, true, true] [1, 3, 5, 8] = false := by
  decide

/-- At budget 0 the rules clause constrains nothing: any rule list at all
    goes with a bag that satisfies the bag clause. -/
theorem ex_represents_budget_zero :
    Represents { bag := [1, 2, 3, 4, 5, 7, 8, 10], rules := [[999]] }
      (double exCTS) (dblCfg exCfg) 0 :=
  ⟨⟨[1, 3, 5, 8], by decide, by decide⟩, ⟨13, [[999]], by decide, by decide⟩⟩

/-- Negative example on the rules clause alone: the p. 29 bag with the rule
    pair of the first doubled appendant encoded from counter 3.  The bag is
    acceptable, the rule pair has the right shape, but the counter is forced
    to 3 and the bag element 10 then breaks the threshold `x + 3 <= i`. -/
theorem ex_not_represents_low_counter :
    ¬ Represents { bag := [1, 2, 3, 4, 5, 7, 8, 10], rules := [[5, 8], [3, 6]] }
        (double exCTS) (dblCfg exCfg) 1 := by
  rintro ⟨-, i, rest, hbound, hrules⟩
  have happ : appendantsFrom (double exCTS) (dblCfg exCfg).phase 1 = [[true, true]] := by decide
  rw [happ] at hrules
  simp [ruleBlocks, encodePaired] at hrules
  have := hbound 10 (by simp)
  omega

/-- Negative example on the rules clause alone: the same two rules with the
    pair in the wrong order.  The clause forces the first rule to be the
    second with 2 added to each integer, so no counter fits. -/
theorem ex_not_represents_swapped_rules :
    ¬ Represents { bag := [1, 2, 3, 4, 5, 7, 8, 10], rules := [[13, 16], [15, 18]] }
        (double exCTS) (dblCfg exCfg) 1 := by
  rintro ⟨-, i, rest, -, hrules⟩
  have happ : appendantsFrom (double exCTS) (dblCfg exCfg).phase 1 = [[true, true]] := by decide
  rw [happ] at hrules
  simp [ruleBlocks, encodePaired] at hrules
  omega

/-! ### The hand-built program of TM23Proof.pdf p. 19

Smith's own System 5 initial condition for the doubled cyclic tag system
`111100 1111 "" 00 "" 0011 "" "" ""` (the doubling of `110 11 0 01 ""`,
`pdfCTS` and `pdfCfg` of `Smith.Doubling`), quoted on p. 19 as good for 8
steps.  Its bag and its first rule pair agree with the canonical encoder,
but from the third rule pair on it uses the slack Smith's "at least 3"
condition allows, so it is in `Represents` at budget 2 and out of it at
budget 3.  This is the worked witness that the rules clause is a strict
sub-relation of Smith's condition. -/

/-- The System 5 initial condition printed on TM23Proof.pdf p. 19. -/
def pdf19 : System5Config :=
  { bag := [1, 3, 4, 6, 7, 9, 10, 12, 13, 14, 15, 16],
    rules := [[21, 24, 27, 30], [19, 22, 25, 28], [], [], [35, 36], [33, 34], [], [],
              [41, 42, 45, 48], [39, 40, 43, 46], [], [], [], [], [], []] }

/-- The p. 19 program is not the canonical encoder output: the encoder
    continues from counter 31 where Smith continues from 33. -/
theorem pdf19_ne_encoder : ctsToSystem5 pdfCTS pdfCfg 1 ≠ pdf19 := by decide

/-- Positive example: the p. 19 program represents the doubled p. 18 system
    for two appendants, with starts `1, 4, 7, 10, 13, 15` for the doubled
    working string `111100` and rule counter 19. -/
theorem pdf19_represents_budget2 :
    Represents pdf19 (double pdfCTS) (dblCfg pdfCfg) 2 :=
  ⟨⟨[1, 4, 7, 10, 13, 15], by decide, by decide⟩,
   ⟨19, [[35, 36], [33, 34], [], [], [41, 42, 45, 48], [39, 40, 43, 46], [], [],
         [], [], [], []], by decide, by decide⟩⟩

/-- Negative example: at budget 3 the third rule pair is constrained, and
    Smith's `35,36 / 33,34` is not the canonical `33,34 / 31,32`, so the
    p. 19 program leaves the relation.  This is the strictness of the
    sub-relation, not a defect of the program. -/
theorem pdf19_not_represents_budget3 :
    ¬ Represents pdf19 (double pdfCTS) (dblCfg pdfCfg) 3 := by
  rintro ⟨-, i, rest, -, hrules⟩
  have happ : appendantsFrom (double pdfCTS) (dblCfg pdfCfg).phase 3
      = [[true, true, true, true], [], [false, false]] := by decide
  rw [happ] at hrules
  simp [ruleBlocks, encodePaired, pdf19] at hrules
  omega

/-! ## Uniform increments -/

/-- Shifting the rule counter shifts the whole rule pair. -/
theorem encodePaired_shift (w : List Bool) (i m : Int) :
    encodePaired w (i + m)
      = ((encodePaired w i).1.map (· + m), (encodePaired w i).2.1.map (· + m),
         (encodePaired w i).2.2 + m) := by
  induction w, i using encodePaired.induct with
  | case1 b rest i r1 r2 i' heq ih =>
    show (let (r1, r2, i') := encodePaired rest (i + m + 6)
          ((i + m + 2) :: (i + m + 5) :: r1, (i + m) :: (i + m + 3) :: r2, i'))
       = ((((i + 2) :: (i + 5) :: (encodePaired rest (i + 6)).1).map (· + m)),
          (((i : Int) :: (i + 3) :: (encodePaired rest (i + 6)).2.1).map (· + m)),
          (encodePaired rest (i + 6)).2.2 + m)
    rw [show i + m + 6 = i + 6 + m from by omega, ih]
    simp only [List.map_cons, Prod.mk.injEq]
    refine ⟨?_, ?_, trivial⟩ <;> simp <;> omega
  | case2 b rest i r1 r2 i' heq ih =>
    show (let (r1, r2, i') := encodePaired rest (i + m + 4)
          ((i + m + 2) :: (i + m + 3) :: r1, (i + m) :: (i + m + 1) :: r2, i'))
       = ((((i + 2) :: (i + 3) :: (encodePaired rest (i + 4)).1).map (· + m)),
          (((i : Int) :: (i + 1) :: (encodePaired rest (i + 4)).2.1).map (· + m)),
          (encodePaired rest (i + 4)).2.2 + m)
    rw [show i + m + 4 = i + 4 + m from by omega, ih]
    simp only [List.map_cons, Prod.mk.injEq]
    refine ⟨?_, ?_, trivial⟩ <;> simp <;> omega
  | case3 t i h1 h2 =>
    cases t with
    | nil => rfl
    | cons b t' =>
      cases t' with
      | nil => cases b <;> rfl
      | cons b2 rest =>
        cases b with
        | true => exact (h1 b2 rest rfl).elim
        | false => exact (h2 b2 rest rfl).elim

/-- Shifting the rule counter shifts every rule of a block. -/
theorem ruleBlocks_shift (L : List (List Bool)) (i m : Int) :
    ruleBlocks L (i + m)
      = ((ruleBlocks L i).1.map (List.map (· + m)), (ruleBlocks L i).2 + m) := by
  induction L generalizing i with
  | nil => rfl
  | cons w ws ih =>
    rw [ruleBlocks_cons, ruleBlocks_cons, encodePaired_shift w i m]
    simp only []
    rw [ih ((encodePaired w i).2.2)]
    simp

/-- Shifting the starts shifts the bag. -/
theorem pairsOf_map_add (w : List Bool) (a : List Int) (m : Int) :
    pairsOf w (a.map (· + m)) = (pairsOf w a).map (· + m) := by
  induction w generalizing a with
  | nil => rfl
  | cons b w ih =>
    cases a with
    | nil => rfl
    | cons x a =>
      show (x + m) :: (x + m + gap b) :: pairsOf w (a.map (· + m))
         = (x + m) :: (x + gap b + m) :: (pairsOf w a).map (· + m)
      rw [ih a, show x + m + gap b = x + gap b + m from by omega]

/-- Shifting the starts preserves the ascending condition. -/
theorem pairsAsc_map_add (lo : Int) (w : List Bool) (a : List Int) (m : Int)
    (h : pairsAsc lo w a = true) : pairsAsc (lo + m) w (a.map (· + m)) = true := by
  induction w generalizing lo a with
  | nil => cases a with
    | nil => rfl
    | cons x a => simp at h
  | cons b w ih =>
    cases a with
    | nil => simp at h
    | cons x a =>
      rw [pairsAsc_cons_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      show (decide (lo + m < x + m) && pairsAsc (x + m + gap b) w (a.map (· + m))) = true
      rw [show x + m + gap b = x + gap b + m from by omega, ih (x + gap b) a h.2]
      simp only [Bool.and_true, decide_eq_true_eq]
      omega

/-- The relation survives a uniform increment of bag and rules by any
    `m >= 0`.  Together with the unconstrained tail of the rules clause this
    is what lets `Represents` be re-established after a System 5 step. -/
theorem Represents_shift (s : System5Config) (C : CTS) (c : CTSConfig) (b : Nat) (m : Int)
    (hm : 0 ≤ m) (h : Represents s C c b) :
    Represents { bag := s.bag.map (· + m), rules := s.rules.map (List.map (· + m)) }
      C c b := by
  obtain ⟨⟨a, hasc, hperm⟩, i, rest, hbound, hrules⟩ := h
  constructor
  · refine ⟨a.map (· + m), ?_, ?_⟩
    · exact pairsAsc_mono (0 + m) 0 c.data (a.map (· + m)) (by omega)
        (pairsAsc_map_add 0 c.data a m hasc)
    · show (s.bag.map (· + m)).Perm (pairsOf c.data (a.map (· + m)))
      rw [pairsOf_map_add]
      exact hperm.map _
  · refine ⟨i + m, rest.map (List.map (· + m)), ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := hbound y hy
      omega
    · show s.rules.map (List.map (· + m)) = _
      rw [hrules, List.map_append, ruleBlocks_shift]

end Smith
