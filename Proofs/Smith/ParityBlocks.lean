/-
  Smith.ParityBlocks

  The algebra behind Smith's Lemmas 0 and 1 and Corollaries 0 and 1
  (TM23Proof.pdf p. 5-9): a block of 1s and 2s in System 3, read as a
  bit string (`2` is `true`), is transformed by a scan in state B into its
  prefix-XOR (`T`), and by a scan in state C into the prefix-XOR of the
  block with its first bit toggled.  The parity of the block at the `k`-th
  scan, `parAt x k = parity (T^[k] x)`, is linear in `x`, and Smith's
  strings for the one-element sets, the rows of the rule-60 cellular
  automaton `row n i` (p. 8), satisfy `parAt (row n i) k = (k = i)` for
  `i, k < n = 2^w`: `T` sends `row (i + 1)` to `row i` and `row 0` to
  `row (n - 1)`, a cycle of length `2^w`, which is the period of Lemma 1
  and follows from the Frobenius identity
  `stepR^[2^w] x = shiftR^[2^w] x xor x`.

  Contents:
    * `xorB`, `shiftR`, `scanFrom`, `T`, `parity`, `stepR`, `row`.
    * Linearity and commutation: `scanFrom_xor`, `T_xor`, `shiftR_xor`,
      `stepR_xor`, `T_shiftR`, `T_stepR`, `stepR_shiftR`.
    * `scanC_eq`: a C-scan is a B-scan of the block with its first bit
      toggled (the "state parity" of Lemma 1).
    * `T_row_succ`, `stepR_iterate_two_pow` (Frobenius), `row_two_pow`,
      `T_row_zero`, `row_last_ones`, `parity_row`.
    * `parAt`, `parAt_xor`, `parAt_T`, `parAt_row`.
-/

import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Basic

namespace Smith

/-- A block of 1s and 2s as bits, `2` being `true`. -/
abbrev Bits := List Bool

/-- Pointwise XOR of two blocks of the same length. -/
def xorB (x y : Bits) : Bits := List.zipWith xor x y

/-- Shift right by one, a `false` coming in at the left, the last bit dropped. -/
def shiftR (x : Bits) : Bits := (false :: x).dropLast

/-- The prefix-XOR of a block from an initial state `s`: the transducer of
    a System 3 scan (state B is `false`, state C is `true`). -/
def scanFrom : Bool → Bits → Bits
  | _, [] => []
  | s, b :: xs => (s ^^ b) :: scanFrom (s ^^ b) xs

/-- The scan in state B. -/
def T (x : Bits) : Bits := scanFrom false x

/-- The parity of a block: the number of `2`s mod 2. -/
def parity (x : Bits) : Bool := x.foldl (· ^^ ·) false

def zeros (n : Nat) : Bits := List.replicate n false
def ones (n : Nat) : Bits := List.replicate n true

/-- The block `2 1 1 ... 1` of length `n`, Smith's string for the set `{0}`. -/
def unit (n : Nat) : Bits := true :: zeros (n - 1)

/-- One row of the rule-60 cellular automaton: `x` XOR `x` shifted right. -/
def stepR (x : Bits) : Bits := xorB (shiftR x) x

/-- Smith's strings for the one-element sets, p. 8: `row n i` is the
    string for `{i}` at width `n`. -/
def row (n : Nat) : Nat → Bits
  | 0 => unit n
  | i + 1 => stepR (row n i)

/-! ## Lengths -/

@[simp] theorem length_xorB (x y : Bits) (h : x.length = y.length) : (xorB x y).length = x.length := by
  simp [xorB, h]

@[simp] theorem length_shiftR (x : Bits) : (shiftR x).length = x.length := by
  simp [shiftR]

@[simp] theorem length_scanFrom (s : Bool) (x : Bits) : (scanFrom s x).length = x.length := by
  induction x generalizing s with
  | nil => rfl
  | cons b xs ih => simp [scanFrom, ih]

@[simp] theorem length_T (x : Bits) : (T x).length = x.length := length_scanFrom _ _

@[simp] theorem length_zeros (n : Nat) : (zeros n).length = n := by simp [zeros]
@[simp] theorem length_ones (n : Nat) : (ones n).length = n := by simp [ones]

theorem length_unit (n : Nat) (hn : 1 ≤ n) : (unit n).length = n := by
  simp [unit]; omega

@[simp] theorem length_stepR (x : Bits) : (stepR x).length = x.length := by
  simp [stepR]

theorem length_row (n i : Nat) (hn : 1 ≤ n) : (row n i).length = n := by
  induction i with
  | zero => simp [row, length_unit n hn]
  | succ i ih => simp [row, ih]

/-! ## XOR -/

theorem xorB_cons (a b : Bool) (x y : Bits) : xorB (a :: x) (b :: y) = (a ^^ b) :: xorB x y := rfl

@[simp] theorem xorB_nil_left (y : Bits) : xorB [] y = [] := rfl
@[simp] theorem xorB_nil_right (x : Bits) : xorB x [] = [] := by cases x <;> rfl

theorem xorB_comm (x y : Bits) : xorB x y = xorB y x := by
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a x ih => cases y with
    | nil => rfl
    | cons b y => rw [xorB_cons, xorB_cons, ih, Bool.xor_comm]

theorem xorB_assoc (x y z : Bits) : xorB (xorB x y) z = xorB x (xorB y z) := by
  induction x generalizing y z with
  | nil => rfl
  | cons a x ih => cases y with
    | nil => rfl
    | cons b y => cases z with
      | nil => rfl
      | cons c z => rw [xorB_cons, xorB_cons, xorB_cons, xorB_cons, ih, Bool.xor_assoc]

theorem xorB_self (x : Bits) : xorB x x = zeros x.length := by
  induction x with
  | nil => rfl
  | cons a x ih => rw [xorB_cons, ih, Bool.xor_self]; rfl

theorem xorB_zeros_right (x : Bits) : xorB x (zeros x.length) = x := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    rw [List.length_cons]
    show xorB (a :: x) (false :: zeros x.length) = a :: x
    rw [xorB_cons, ih, Bool.xor_false]

theorem xorB_zeros_left (x : Bits) : xorB (zeros x.length) x = x := by
  rw [xorB_comm, xorB_zeros_right]

theorem xorB_dropLast (x y : Bits) (h : x.length = y.length) :
    (xorB x y).dropLast = xorB x.dropLast y.dropLast := by
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a x ih => cases y with
    | nil => simp at h
    | cons b y =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      cases x with
      | nil => cases y with
        | nil => rfl
        | cons _ _ => simp at h
      | cons a' x' => cases y with
        | nil => simp at h
        | cons b' y' =>
          have e1 : (xorB (a :: a' :: x') (b :: b' :: y')).dropLast
              = (a ^^ b) :: (xorB (a' :: x') (b' :: y')).dropLast := by
            rw [xorB_cons]
            exact List.dropLast_cons_of_ne_nil (by simp [xorB])
          have e2 : (a :: a' :: x').dropLast = a :: (a' :: x').dropLast :=
            List.dropLast_cons_of_ne_nil (by simp)
          have e3 : (b :: b' :: y').dropLast = b :: (b' :: y').dropLast :=
            List.dropLast_cons_of_ne_nil (by simp)
          rw [e1, e2, e3, xorB_cons a b, ih (b' :: y') h]

/-! ## Linearity of the scan -/

theorem scanFrom_xor (s t : Bool) (x y : Bits) (h : x.length = y.length) :
    scanFrom (s ^^ t) (xorB x y) = xorB (scanFrom s x) (scanFrom t y) := by
  induction x generalizing s t y with
  | nil => cases y with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a x ih => cases y with
    | nil => simp at h
    | cons b y =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [xorB_cons, scanFrom, scanFrom, scanFrom, xorB_cons]
      have e : ((s ^^ t) ^^ (a ^^ b)) = ((s ^^ a) ^^ (t ^^ b)) := by
        cases s <;> cases t <;> cases a <;> cases b <;> rfl
      rw [e, ← ih (s ^^ a) (t ^^ b) y h]

theorem T_xor (x y : Bits) (h : x.length = y.length) : T (xorB x y) = xorB (T x) (T y) := by
  unfold T
  rw [← scanFrom_xor false false x y h]
  rfl

theorem scanFrom_zeros (s : Bool) (n : Nat) : scanFrom s (zeros n) = List.replicate n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [zeros] at ih ⊢
    rw [List.replicate_succ, scanFrom, Bool.xor_false, ih, List.replicate_succ]

theorem T_zeros (n : Nat) : T (zeros n) = zeros n := scanFrom_zeros false n

theorem scanFrom_true_zeros (n : Nat) : scanFrom true (zeros n) = ones n := scanFrom_zeros true n

/-- A scan in state C is a scan in state B of the block with its first bit
    toggled: Smith's state parity (p. 6-7). -/
theorem scanC_eq (x : Bits) : scanFrom true x = xorB (T x) (ones x.length) := by
  have h := scanFrom_xor false true x (zeros x.length) (by simp)
  rw [Bool.false_xor, xorB_zeros_right, scanFrom_true_zeros] at h
  exact h

theorem scanC_eq_T_toggle (a : Bool) (x : Bits) :
    scanFrom true (a :: x) = T ((!a) :: x) := by
  simp [T, scanFrom]

/-! ## Commutation with the shift -/

theorem scanFrom_dropLast (s : Bool) (x : Bits) : scanFrom s x.dropLast = (scanFrom s x).dropLast := by
  induction x generalizing s with
  | nil => rfl
  | cons a x ih =>
    cases x with
    | nil => rfl
    | cons b y =>
      rw [List.dropLast_cons_of_ne_nil (by simp), scanFrom, scanFrom, ih,
        List.dropLast_cons_of_ne_nil (by simp [scanFrom])]

theorem T_shiftR (x : Bits) : T (shiftR x) = shiftR (T x) := by
  unfold T shiftR
  rw [scanFrom_dropLast, scanFrom, Bool.xor_false]

theorem shiftR_xor (x y : Bits) (h : x.length = y.length) :
    shiftR (xorB x y) = xorB (shiftR x) (shiftR y) := by
  unfold shiftR
  rw [← xorB_dropLast (false :: x) (false :: y) (by simp [h]), xorB_cons, Bool.xor_false]

theorem stepR_xor (x y : Bits) (h : x.length = y.length) :
    stepR (xorB x y) = xorB (stepR x) (stepR y) := by
  unfold stepR
  rw [shiftR_xor x y h, xorB_assoc, xorB_assoc]
  congr 1
  rw [← xorB_assoc, xorB_comm (shiftR y) x, xorB_assoc]

theorem stepR_shiftR (x : Bits) : stepR (shiftR x) = shiftR (stepR x) := by
  unfold stepR
  rw [shiftR_xor (shiftR x) x (by simp)]

theorem T_stepR (x : Bits) : T (stepR x) = stepR (T x) := by
  unfold stepR
  rw [T_xor _ _ (by simp), T_shiftR]

/-! ## The rows -/

theorem row_eq_iterate (n i : Nat) : row n i = stepR^[i] (unit n) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [row, ih, Function.iterate_succ_apply']

theorem T_unit (n : Nat) (hn : 1 ≤ n) : T (unit n) = ones n := by
  unfold unit T
  rw [scanFrom, Bool.false_xor, scanFrom_zeros]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [ones, List.replicate_succ]

theorem shiftR_ones (n : Nat) (hn : 1 ≤ n) : shiftR (ones n) = false :: ones (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [shiftR, ones, List.replicate_succ]

theorem stepR_ones (n : Nat) (hn : 1 ≤ n) : stepR (ones n) = unit n := by
  unfold stepR
  rw [shiftR_ones n hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [ones, unit, List.replicate_succ, Nat.add_sub_cancel, zeros]
  rw [xorB_cons, Bool.false_xor]
  congr 1
  have := xorB_self (List.replicate m true)
  simpa [zeros] using this

/-- `T` steps the rows down. -/
theorem T_row_succ (n i : Nat) (hn : 1 ≤ n) : T (row n (i + 1)) = row n i := by
  induction i with
  | zero =>
    show T (stepR (unit n)) = unit n
    rw [T_stepR, T_unit n hn, stepR_ones n hn]
  | succ i ih =>
    show T (stepR (row n (i + 1))) = stepR (row n i)
    rw [T_stepR, ih]

theorem T_iterate_row (n i k : Nat) (hn : 1 ≤ n) (hk : k ≤ i) : T^[k] (row n i) = row n (i - k) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [Function.iterate_succ_apply, T_row_succ n j hn, ih j (by omega)]
    congr 1
    omega

/-! ## The period `2^w` -/

theorem length_stepR_iterate (m : Nat) (x : Bits) : (stepR^[m] x).length = x.length := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih, length_stepR]

theorem length_shiftR_iterate (m : Nat) (x : Bits) : (shiftR^[m] x).length = x.length := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih, length_shiftR]

theorem stepR_iterate_xor (m : Nat) (x y : Bits) (h : x.length = y.length) :
    stepR^[m] (xorB x y) = xorB (stepR^[m] x) (stepR^[m] y) := by
  induction m generalizing x y with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      stepR_xor x y h, ih _ _ (by simp [h])]

theorem shiftR_iterate_xor (m : Nat) (x y : Bits) (h : x.length = y.length) :
    shiftR^[m] (xorB x y) = xorB (shiftR^[m] x) (shiftR^[m] y) := by
  induction m generalizing x y with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      shiftR_xor x y h, ih _ _ (by simp [h])]

theorem stepR_shiftR_iterate (k : Nat) (x : Bits) : stepR (shiftR^[k] x) = shiftR^[k] (stepR x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, stepR_shiftR]

theorem stepR_iterate_shiftR_iterate (m k : Nat) (x : Bits) :
    stepR^[m] (shiftR^[k] x) = shiftR^[k] (stepR^[m] x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepR_shiftR_iterate, ih]

/-- The Frobenius identity of the rule-60 automaton over GF(2). -/
theorem stepR_iterate_two_pow (w : Nat) (x : Bits) :
    stepR^[2 ^ w] x = xorB (shiftR^[2 ^ w] x) x := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih =>
    have hl1 : (shiftR^[2 ^ w] x).length = x.length := length_shiftR_iterate _ _
    have hl2 : (shiftR^[2 ^ w] (shiftR^[2 ^ w] x)).length = (shiftR^[2 ^ w] x).length :=
      length_shiftR_iterate _ _
    rw [Nat.pow_succ, Nat.mul_two, Function.iterate_add_apply, ih x, stepR_iterate_xor _ _ _ hl1,
      stepR_iterate_shiftR_iterate, ih, shiftR_iterate_xor _ _ _ hl1,
      ← Function.iterate_add_apply, xorB_assoc, ← xorB_assoc (shiftR^[2 ^ w] x),
      xorB_self, hl1, xorB_zeros_left]

theorem shiftR_iterate_eq_take (m : Nat) (x : Bits) :
    shiftR^[m] x = (List.replicate m false ++ x).take x.length := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold shiftR
    rw [List.dropLast_eq_take, List.length_cons, List.length_take, List.length_append,
      List.length_replicate, Nat.min_eq_left (by omega), Nat.add_sub_cancel,
      List.replicate_succ, List.cons_append]
    cases x with
    | nil => rfl
    | cons a xs =>
      rw [List.length_cons, List.take_succ_cons, List.take_succ_cons, List.take_take,
        Nat.min_eq_left (Nat.le_succ _)]

theorem shiftR_iterate_zeros (x : Bits) (m : Nat) (hm : x.length ≤ m) :
    shiftR^[m] x = zeros x.length := by
  rw [shiftR_iterate_eq_take, List.take_append_of_le_length (by simp; omega), List.take_replicate,
    Nat.min_eq_left hm]
  rfl

theorem row_two_pow (w : Nat) : row (2 ^ w) (2 ^ w) = row (2 ^ w) 0 := by
  rw [row_eq_iterate, stepR_iterate_two_pow,
    shiftR_iterate_zeros _ _ (by rw [length_unit _ Nat.one_le_two_pow]; exact Nat.le_refl _),
    xorB_zeros_left]
  rfl

/-- `T` closes the cycle: `row 0` goes to the last row. -/
theorem T_row_zero (w : Nat) : T (row (2 ^ w) 0) = row (2 ^ w) (2 ^ w - 1) := by
  have h := T_row_succ (2 ^ w) (2 ^ w - 1) Nat.one_le_two_pow
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, row_two_pow] at h
  exact h

theorem row_last_ones (w : Nat) : row (2 ^ w) (2 ^ w - 1) = ones (2 ^ w) := by
  rw [← T_row_zero]
  show T (unit (2 ^ w)) = _
  rw [T_unit _ Nat.one_le_two_pow]

/-! ## Parities -/

@[simp] theorem parity_nil : parity [] = false := rfl

theorem parity_cons (a : Bool) (x : Bits) : parity (a :: x) = (a ^^ parity x) := by
  unfold parity
  simp only [List.foldl_cons, Bool.false_xor]
  induction x generalizing a with
  | nil => simp
  | cons b y ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih (a ^^ b), ih b, Bool.xor_assoc]

theorem parity_xor (x y : Bits) (h : x.length = y.length) : parity (xorB x y) = (parity x ^^ parity y) := by
  induction x generalizing y with
  | nil => cases y with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a x ih => cases y with
    | nil => simp at h
    | cons b y =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [xorB_cons, parity_cons, parity_cons, parity_cons, ih y h]
      cases a <;> cases b <;> cases parity x <;> cases parity y <;> rfl

theorem parity_zeros (n : Nat) : parity (zeros n) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zeros, List.replicate_succ] at ih ⊢; rw [parity_cons, ih]; rfl

theorem parity_unit (n : Nat) : parity (unit n) = true := by
  unfold unit
  rw [parity_cons, parity_zeros]
  rfl

theorem scanFrom_getLast? (s : Bool) (x : Bits) (hx : x ≠ []) :
    (scanFrom s x).getLast? = some (s ^^ parity x) := by
  induction x generalizing s with
  | nil => exact absurd rfl hx
  | cons a y ih =>
    cases y with
    | nil => simp [scanFrom, parity_cons]
    | cons b z =>
      rw [scanFrom, scanFrom, List.getLast?_cons_cons, ← scanFrom, ih (s ^^ a) (by simp)]
      simp only [parity_cons, Bool.xor_assoc]

theorem T_getLast? (x : Bits) (hx : x ≠ []) : (T x).getLast? = some (parity x) := by
  unfold T
  rw [scanFrom_getLast? false x hx, Bool.false_xor]

/-- The rows have support in `[0, i]`. -/
theorem row_getElem_false (n i j : Nat) (hn : 1 ≤ n) (hij : i < j) (hj : j < n) :
    (row n i)[j]'(by rw [length_row n i hn]; exact hj) = false := by
  induction i generalizing j with
  | zero =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp [row, unit, zeros]
  | succ i ih =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hlen : (row n (i + 1)) = xorB (shiftR (row n i)) (row n i) := rfl
    simp only [hlen, xorB, List.getElem_zipWith]
    have h1 : (shiftR (row n i))[j' + 1]'(by rw [length_shiftR, length_row n i hn]; exact hj) = false := by
      unfold shiftR
      rw [List.getElem_dropLast, List.getElem_cons_succ]
      exact ih j' (by omega) (by omega)
    have h2 : (row n i)[j' + 1]'(by rw [length_row n i hn]; exact hj) = false := ih (j' + 1) (by omega) hj
    rw [h1, h2]
    rfl

theorem row_getLast? (n i : Nat) (hn : 1 ≤ n) (hi : i + 1 < n) : (row n i).getLast? = some false := by
  have hne : row n i ≠ [] := by
    intro h
    have := length_row n i hn
    rw [h] at this
    simp at this
    omega
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by rw [length_row n i hn]; omega)]
  congr 1
  have := row_getElem_false n i ((row n i).length - 1) hn (by rw [length_row n i hn]; omega)
    (by rw [length_row n i hn]; omega)
  exact this

theorem parity_row (n i : Nat) (hn : 1 ≤ n) (hi : i < n) : parity (row n i) = decide (i = 0) := by
  cases i with
  | zero => rw [row, parity_unit]; rfl
  | succ i =>
    have hne : row n (i + 1) ≠ [] := by
      intro h
      have := length_row n (i + 1) hn
      rw [h] at this
      simp at this
      omega
    have h := T_getLast? (row n (i + 1)) hne
    rw [T_row_succ n i hn, row_getLast? n i hn hi] at h
    have hd : decide (i + 1 = 0) = false := by simp
    rw [hd]
    exact (Option.some.inj h).symm

/-! ## The parity set -/

/-- The parity of the block at its `k`-th scan (in state B). -/
def parAt (x : Bits) (k : Nat) : Bool := parity (T^[k] x)

theorem length_T_iterate (k : Nat) (x : Bits) : (T^[k] x).length = x.length := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, length_T]

theorem T_iterate_xor (k : Nat) (x y : Bits) (h : x.length = y.length) :
    T^[k] (xorB x y) = xorB (T^[k] x) (T^[k] y) := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      T_xor x y h, ih _ _ (by simp [h])]

/-- The parity set is linear in the block. -/
theorem parAt_xor (x y : Bits) (h : x.length = y.length) (k : Nat) :
    parAt (xorB x y) k = (parAt x k ^^ parAt y k) := by
  unfold parAt
  rw [T_iterate_xor k x y h, parity_xor _ _ (by rw [length_T_iterate, length_T_iterate, h])]

/-- A scan shifts the parity set down by one. -/
theorem parAt_T (x : Bits) (k : Nat) : parAt (T x) k = parAt x (k + 1) := by
  unfold parAt
  rw [Function.iterate_succ_apply]

/-- Smith's strings for one-element sets have odd parity exactly at the
    scan of their element (within the first `2^w` scans). -/
theorem parAt_row (w i k : Nat) (hi : i < 2 ^ w) (hk : k < 2 ^ w) :
    parAt (row (2 ^ w) i) k = decide (k = i) := by
  unfold parAt
  have hn : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  rcases Nat.lt_or_ge i k with hik | hki
  · obtain ⟨d, rfl⟩ : ∃ d, k = (d + 1) + i := ⟨k - i - 1, by omega⟩
    rw [Function.iterate_add_apply, T_iterate_row _ _ _ hn (Nat.le_refl i), Nat.sub_self,
      Function.iterate_succ_apply, T_row_zero, T_iterate_row _ _ _ hn (by omega),
      parity_row _ _ hn (by omega)]
    simp only [decide_eq_decide]
    omega
  · rw [T_iterate_row _ _ _ hn hki, parity_row _ _ hn (by omega)]
    simp only [decide_eq_decide]
    omega

/-! ## Checks against the PDF -/

/-- The rows of width 16, p. 8. -/
example : row 16 0 = [true, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false] := by decide
example : row 16 3 = [true, true, true, true, false, false, false, false, false, false, false,
    false, false, false, false, false] := by decide
example : row 16 5 = [true, true, false, false, true, true, false, false, false, false, false,
    false, false, false, false, false] := by decide
example : row 16 15 = ones 16 := by decide

/-- The parity set of `row 4 i` within the first four scans is `{i}`. -/
example : ∀ i k : Fin 4, parAt (row 4 i) k = decide ((k : Nat) = i) := by decide

/-- The period: the fifth scan of `row 4 1` is odd again (Lemma 1). -/
example : parAt (row 4 1) 5 = true := by decide

/-- A scan in state C differs from a scan in state B by the toggle of the
    first bit, p. 7 (`21` under C is `T` of `11`). -/
example : scanFrom true [true, false, true, true] = T [false, false, true, true] := by decide

end Smith
