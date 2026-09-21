/-
  Smith.System3Runs

  The runs of System 3 (`sys3` of `Smith.Lookahead`) that the emulation of
  System 4 is made of (TM23Proof.pdf p. 12-15), on the zipper
  configurations, with the blocks of 1s and 2s read as bits
  (`Smith.ParityBlocks`, `2` is `true`):

    * `walkLeft`: in state A the head walks left over 1s and 2s without
      changing them, onto the first cell that is not one (Lemma 0.1).
    * `turnA`: at a 0 in state A the 0 becomes a 2 and the head moves right
      in state B (rules 2 and 5 of System 4 and the turn at the left end).
    * `scanBlock`: in state B or C the head crosses a block of 1s and 2s,
      replacing it by its prefix-XOR from the entering state and leaving in
      the state given by the block's parity (Lemma 0.2-0.8); at a 0 after
      the block, an exit in state B lands on the 0 in state B (System 4's
      star active in state B), and an exit that would be in state C turns
      the last cell of the block, a 2, into a 0 and lands on the 0 in state
      A (the two 0s of System 4's star active in state C, p. 11 and 13).
    * `starB`: a 0 active in state B becomes a 2 and the head moves left in
      state A (rule 4).

  Contents: `toCell`, `ofBits`, `toBits`, `stB`, and the run lemmas.
-/

import Smith.Lookahead
import Smith.ParityBlocks
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

namespace Smith

open TM
open LState

/-- A bit as a tape cell: `true` is `2`, `false` is `1`. -/
def toCell (b : Bool) : Fin 3 := if b then 2 else 1

/-- A block of bits as tape cells. -/
def ofBits (x : Bits) : List (Fin 3) := x.map toCell

/-- Tape cells as bits: `2` is `true`, everything else `false`. -/
def toBits (l : List (Fin 3)) : Bits := l.map (· = 2)

/-- The scanning states: `false` is B, `true` is C. -/
def stB (s : Bool) : LState := if s then C else B

@[simp] theorem stB_false : stB false = B := rfl
@[simp] theorem stB_true : stB true = C := rfl
@[simp] theorem toCell_true : toCell true = 2 := rfl
@[simp] theorem toCell_false : toCell false = 1 := rfl
@[simp] theorem ofBits_nil : ofBits [] = [] := rfl
@[simp] theorem ofBits_cons (b : Bool) (x : Bits) : ofBits (b :: x) = toCell b :: ofBits x := rfl
@[simp] theorem length_ofBits (x : Bits) : (ofBits x).length = x.length := by simp [ofBits]
theorem toCell_ne_zero (b : Bool) : toCell b ≠ 0 := by cases b <;> decide
theorem toBits_ofBits (x : Bits) : toBits (ofBits x) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [toBits, ofBits, toCell] at ih ⊢ <;> exact ih

/-! ## The walk to the left in state A -/

/-- In state A the head walks left over 1s and 2s, unchanged (`A1 -> A1<`,
    `A2 -> A2<`), onto the cell `z` beyond them. -/
theorem walkLeft (P : List (Fin 3)) (hP : ∀ c ∈ P, c ≠ 0) (z : Fin 3) (L : List (Fin 3))
    (a : Fin 3) (ha : a ≠ 0) (R : List (Fin 3)) :
    lnSteps sys3 ⟨P ++ z :: L, a, R, A⟩ (P.length + 1) = some ⟨L, z, P.reverse ++ a :: R, A⟩ := by
  induction P generalizing a R with
  | nil =>
    rw [List.length_nil, Nat.zero_add, lnSteps_one]
    fin_cases a <;> simp at ha ⊢ <;> cases R <;> simp [lstep, sys3]
  | cons c P ih =>
    rw [List.length_cons, lnSteps_succ]
    have hc : c ≠ 0 := hP c List.mem_cons_self
    have hstep : lstep sys3 ⟨(c :: P) ++ z :: L, a, R, A⟩ = some ⟨P ++ z :: L, c, a :: R, A⟩ := by
      fin_cases a <;> simp at ha <;> cases R <;> simp [lstep, sys3]
    rw [hstep, Option.bind_some, ih (fun d hd => hP d (List.mem_cons_of_mem _ hd)) c hc (a :: R)]
    simp

/-- At a 0 in state A: the 0 becomes a 2, the head moves right in state B. -/
theorem turnA (L : List (Fin 3)) (b : Fin 3) (R : List (Fin 3)) :
    lstep sys3 ⟨L, 0, b :: R, A⟩ = some ⟨2 :: L, b, R, B⟩ := by
  simp [lstep, sys3]

/-- A 0 active in state B: the 0 becomes a 2, the head moves left in state A. -/
theorem starB (c : Fin 3) (L : List (Fin 3)) (R : List (Fin 3)) :
    lstep sys3 ⟨c :: L, 0, R, B⟩ = some ⟨L, c, 2 :: R, A⟩ := by
  cases R <;> simp [lstep, sys3]

/-! ## The scan -/

/-- One scanning step inside a block: the cell `a` followed by a cell `b`
    that is not a 0 is replaced by `s ^^ a` and the state becomes `s ^^ a`. -/
theorem scanStep (L : List (Fin 3)) (s a : Bool) (b : Fin 3) (hb : b ≠ 0) (R : List (Fin 3)) :
    lstep sys3 ⟨L, toCell a, b :: R, stB s⟩ = some ⟨toCell (s ^^ a) :: L, b, R, stB (s ^^ a)⟩ := by
  cases s <;> cases a <;> fin_cases b <;> simp at hb <;> simp [lstep, sys3, toCell, stB]

/-- The last cell of a block followed by a 0, when the scan leaves in state
    B: the head lands on the 0 in state B. -/
theorem scanLastB (L : List (Fin 3)) (s a : Bool) (h : (s ^^ a) = false) (R : List (Fin 3)) :
    lstep sys3 ⟨L, toCell a, 0 :: R, stB s⟩ = some ⟨toCell (s ^^ a) :: L, 0, R, B⟩ := by
  cases s <;> cases a <;> simp at h <;> cases R <;> simp [lstep, sys3, toCell, stB]

/-- The last cell of a block followed by a 0, when the scan would leave in
    state C: the cell, which would become a 2, becomes a 0 and the head
    lands on the 0 in state A (`B20 -> A00>`, `C10 -> A00>`). -/
theorem scanLastC (L : List (Fin 3)) (s a : Bool) (h : (s ^^ a) = true) (R : List (Fin 3)) :
    lstep sys3 ⟨L, toCell a, 0 :: R, stB s⟩ = some ⟨0 :: L, 0, R, A⟩ := by
  cases s <;> cases a <;> simp at h <;> cases R <;> simp [lstep, sys3, toCell, stB]

/-- The scan of a block that is followed by a cell `c` that is not a 0
    (an adjacent block): the block becomes its prefix-XOR from the entering
    state, the head lands on `c` in the exit state. -/
theorem scanBlock (L : List (Fin 3)) (s : Bool) (a : Bool) (x : Bits) (c : Fin 3) (hc : c ≠ 0)
    (R : List (Fin 3)) :
    lnSteps sys3 ⟨L, toCell a, ofBits x ++ c :: R, stB s⟩ (x.length + 1)
      = some ⟨(ofBits (scanFrom s (a :: x))).reverse ++ L, c, R, stB (s ^^ parity (a :: x))⟩ := by
  induction x generalizing L s a with
  | nil =>
    rw [List.length_nil, Nat.zero_add, lnSteps_one, ofBits_nil, List.nil_append,
      scanStep L s a c hc R]
    simp [scanFrom, parity_cons]
  | cons b x ih =>
    rw [List.length_cons, lnSteps_succ, ofBits_cons, List.cons_append,
      scanStep L s a (toCell b) (toCell_ne_zero b) _, Option.bind_some, ih]
    simp only [scanFrom, parity_cons, ofBits_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, Bool.xor_assoc]
    rfl

/-- The scan of a block followed by a 0, exit in state B. -/
theorem scanBlock0B (L : List (Fin 3)) (s : Bool) (a : Bool) (x : Bits) (R : List (Fin 3))
    (h : (s ^^ parity (a :: x)) = false) :
    lnSteps sys3 ⟨L, toCell a, ofBits x ++ 0 :: R, stB s⟩ (x.length + 1)
      = some ⟨(ofBits (scanFrom s (a :: x))).reverse ++ L, 0, R, B⟩ := by
  induction x generalizing L s a with
  | nil =>
    rw [parity_cons, parity_nil, Bool.xor_false] at h
    rw [List.length_nil, Nat.zero_add, lnSteps_one, ofBits_nil, List.nil_append, scanLastB L s a h R]
    simp [scanFrom]
  | cons b x ih =>
    have h' : ((s ^^ a) ^^ parity (b :: x)) = false := by
      rw [Bool.xor_assoc, ← parity_cons]; exact h
    rw [List.length_cons, lnSteps_succ, ofBits_cons, List.cons_append,
      scanStep L s a (toCell b) (toCell_ne_zero b) _, Option.bind_some, ih _ _ _ h']
    simp [scanFrom]

/-- The scan of a block followed by a 0, exit that would be in state C: the
    last cell becomes a 0 and the head lands on the 0 in state A. -/
theorem scanBlock0C (L : List (Fin 3)) (s : Bool) (a : Bool) (x : Bits) (R : List (Fin 3))
    (h : (s ^^ parity (a :: x)) = true) :
    lnSteps sys3 ⟨L, toCell a, ofBits x ++ 0 :: R, stB s⟩ (x.length + 1)
      = some ⟨0 :: (ofBits (scanFrom s (a :: x))).dropLast.reverse ++ L, 0, R, A⟩ := by
  induction x generalizing L s a with
  | nil =>
    rw [parity_cons, parity_nil, Bool.xor_false] at h
    rw [List.length_nil, Nat.zero_add, lnSteps_one, ofBits_nil, List.nil_append, scanLastC L s a h R]
    simp [scanFrom]
  | cons b x ih =>
    have h' : ((s ^^ a) ^^ parity (b :: x)) = true := by
      rw [Bool.xor_assoc, ← parity_cons]; exact h
    rw [List.length_cons, lnSteps_succ, ofBits_cons, List.cons_append,
      scanStep L s a (toCell b) (toCell_ne_zero b) _, Option.bind_some, ih _ _ _ h']
    simp only [scanFrom, ofBits_cons]
    rw [List.dropLast_cons_of_ne_nil
      (l := toCell ((s ^^ a) ^^ b) :: ofBits (scanFrom ((s ^^ a) ^^ b) x)) (by simp)]
    simp

end Smith
