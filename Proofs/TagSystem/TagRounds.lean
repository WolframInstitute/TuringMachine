/-
  TagSystem.TagRounds

  A 2-tag system over an arbitrary alphabet, and its runs described by
  rounds. A round processes the whole current word: the tag reads every
  other symbol, starting with the first, and appends the productions of the
  symbols read (`passOut`). A word of even length is replaced by `passOut`
  of it in half as many steps (`nStepsP_even`); a word of odd length reads
  its last symbol together with the first symbol of what was appended, so
  the result is `passOut` of it without its first symbol (`nStepsP_odd`),
  which shifts the frame of the next round by one. The Cocke-Minsky
  simulation of a Turing machine (`TagSystem.CockeMinsky`) is built from
  these two facts and the computation of `passOut` on words made of pairs
  and of runs.

  Contents: `stepP`, `nStepsP`, `passOut`, `pairs2`, the `passOut`
  computation lemmas, `nStepsP_even`, `nStepsP_odd`.
-/

import TagSystem.Basic
import Mathlib.Tactic.Ring

namespace TagSystem

universe u

variable {σ : Type u}

/-- The 2-tag step with productions `P`: read the first symbol, delete the
    first two, append the production of the symbol read. -/
def stepP (P : σ → List σ) : List σ → Option (List σ)
  | [] => none
  | [_] => none
  | a :: _ :: rest => some (rest ++ P a)

/-- `n` steps. -/
def nStepsP (P : σ → List σ) (w : List σ) : Nat → Option (List σ)
  | 0 => some w
  | n + 1 => (stepP P w).bind fun w' => nStepsP P w' n

@[simp] theorem nStepsP_zero (P : σ → List σ) (w : List σ) : nStepsP P w 0 = some w := rfl

theorem nStepsP_succ (P : σ → List σ) (w : List σ) (n : Nat) :
    nStepsP P w (n + 1) = (stepP P w).bind fun w' => nStepsP P w' n := rfl

theorem nStepsP_add (P : σ → List σ) (w : List σ) (n m : Nat) :
    nStepsP P w (n + m) = (nStepsP P w n).bind fun w' => nStepsP P w' m := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_right_comm, nStepsP_succ, nStepsP_succ]
    cases stepP P w with
    | none => rfl
    | some w' => simp only [Option.bind_some]; exact ih w'

theorem stepP_cons_cons (P : σ → List σ) (a b : σ) (rest : List σ) :
    stepP P (a :: b :: rest) = some (rest ++ P a) := rfl

/-- The productions of every other symbol, starting with the first. -/
def passOut (P : σ → List σ) : List σ → List σ
  | [] => []
  | [a] => P a
  | a :: _ :: rest => P a ++ passOut P rest

@[simp] theorem passOut_nil (P : σ → List σ) : passOut P [] = [] := rfl
@[simp] theorem passOut_singleton (P : σ → List σ) (a : σ) : passOut P [a] = P a := rfl
@[simp] theorem passOut_cons_cons (P : σ → List σ) (a b : σ) (rest : List σ) :
    passOut P (a :: b :: rest) = P a ++ passOut P rest := rfl

/-- `m` copies of the pair `a b`. -/
def pairs2 (a b : σ) : Nat → List σ
  | 0 => []
  | m + 1 => a :: b :: pairs2 a b m

@[simp] theorem pairs2_zero (a b : σ) : pairs2 a b 0 = [] := rfl
@[simp] theorem pairs2_succ (a b : σ) (m : Nat) : pairs2 a b (m + 1) = a :: b :: pairs2 a b m := rfl
@[simp] theorem length_pairs2 (a b : σ) (m : Nat) : (pairs2 a b m).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [pairs2, ih]; omega

theorem pairs2_add (a b : σ) (m n : Nat) : pairs2 a b (m + n) = pairs2 a b m ++ pairs2 a b n := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add, pairs2_succ, pairs2_succ, ih]; rfl

/-- `m` copies of a word. -/
def reps (w : List σ) : Nat → List σ
  | 0 => []
  | m + 1 => w ++ reps w m

@[simp] theorem reps_zero (w : List σ) : reps w 0 = [] := rfl
@[simp] theorem reps_succ (w : List σ) (m : Nat) : reps w (m + 1) = w ++ reps w m := rfl
@[simp] theorem length_reps (w : List σ) (m : Nat) : (reps w m).length = m * w.length := by
  induction m with
  | zero => simp
  | succ m ih => simp [reps, ih]; ring

theorem reps_add (w : List σ) (m n : Nat) : reps w (m + n) = reps w m ++ reps w n := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add, reps_succ, reps_succ, ih, List.append_assoc]

theorem reps_pair (a b : σ) (m : Nat) : reps [a, b] m = pairs2 a b m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [reps, pairs2, ih]

theorem reps_mul (w : List σ) (m n : Nat) : reps (reps w m) n = reps w (m * n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [reps_succ, ih, ← reps_add, Nat.mul_succ, Nat.add_comm]

/-! ## `passOut` on pairs and runs -/

/-- Aligned pairs: the first of each pair is read. -/
theorem passOut_pairs2 (P : σ → List σ) (a b : σ) (m : Nat) (l : List σ) :
    passOut P (pairs2 a b m ++ l) = reps (P a) m ++ passOut P l := by
  induction m with
  | zero => simp
  | succ m ih => simp [pairs2, reps, ih]

/-- Shifted pairs: after one leading `b`, the second of each pair is read,
    and the frame stays shifted. -/
theorem passOut_shift (P : σ → List σ) (a b : σ) (m : Nat) (l : List σ) :
    passOut P (b :: (pairs2 a b m ++ l)) = reps (P b) m ++ passOut P (b :: l) := by
  induction m with
  | zero => simp
  | succ m ih => simp [pairs2, reps, ih]

/-- A run of even length. -/
theorem passOut_replicate_even (P : σ → List σ) (r : σ) (j : Nat) (l : List σ) :
    passOut P (List.replicate (2 * j) r ++ l) = reps (P r) j ++ passOut P l := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 from by omega, List.replicate_succ, List.replicate_succ,
      List.cons_append, List.cons_append, passOut_cons_cons, ih, reps_succ, List.append_assoc]

/-- A run of odd length: the frame shifts after it. -/
theorem passOut_replicate_odd (P : σ → List σ) (r : σ) (j : Nat) (l : List σ) :
    passOut P (List.replicate (2 * j + 1) r ++ l) = reps (P r) j ++ passOut P (r :: l) := by
  rw [List.replicate_succ', List.append_assoc, List.singleton_append, passOut_replicate_even]

/-- `passOut` splits after an even prefix. -/
theorem passOut_append_even (P : σ → List σ) (n : Nat) :
    ∀ (u l : List σ), u.length = 2 * n → passOut P (u ++ l) = passOut P u ++ passOut P l := by
  induction n with
  | zero =>
    intro u l hu
    obtain rfl := List.eq_nil_of_length_eq_zero (by omega)
    simp
  | succ n ih =>
    intro u l hu
    obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, u = a :: b :: rest := by
      cases u with
      | nil => simp at hu
      | cons a u' =>
        cases u' with
        | nil => simp at hu; omega
        | cons b rest => exact ⟨a, b, rest, rfl⟩
    rw [List.cons_append, List.cons_append, passOut_cons_cons, passOut_cons_cons,
      ih rest l (by simp at hu; omega), List.append_assoc]

/-! ## Rounds -/

/-- A round over a word of even length `2n`: `n` steps replace it by
    `passOut` of it, after whatever was pending. -/
theorem nStepsP_even (P : σ → List σ) (n : Nat) :
    ∀ (u t : List σ), u.length = 2 * n → nStepsP P (u ++ t) n = some (t ++ passOut P u) := by
  induction n with
  | zero =>
    intro u t hu
    obtain rfl := List.eq_nil_of_length_eq_zero (by omega)
    simp
  | succ n ih =>
    intro u t hu
    obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, u = a :: b :: rest := by
      cases u with
      | nil => simp at hu
      | cons a u' =>
        cases u' with
        | nil => simp at hu; omega
        | cons b rest => exact ⟨a, b, rest, rfl⟩
    rw [nStepsP_succ, List.cons_append, List.cons_append, stepP_cons_cons, Option.bind_some,
      List.append_assoc, ih rest (t ++ P a) (by simp at hu; omega), passOut_cons_cons,
      List.append_assoc]

/-- A round over a word of odd length `2n + 1` whose first productions are
    not all empty: `n + 1` steps replace it by `passOut` of it without its
    first symbol (the last symbol read takes the first appended symbol as
    its deleted partner). -/
theorem nStepsP_odd (P : σ → List σ) (n : Nat) (u : List σ) (z : σ) (hu : u.length = 2 * n)
    (hne : passOut P u ≠ []) :
    nStepsP P (u ++ [z]) (n + 1) = some ((passOut P (u ++ [z])).tail) := by
  rw [nStepsP_add, nStepsP_even P n u [z] hu, Option.bind_some, nStepsP_succ]
  obtain ⟨c, rest, hc⟩ := List.exists_cons_of_ne_nil hne
  rw [List.singleton_append, hc, stepP_cons_cons, Option.bind_some, nStepsP_zero,
    passOut_append_even P n u [z] hu, passOut_singleton, hc, List.cons_append, List.tail_cons]

/-- Reading a symbol skips the next one. -/
theorem passOut_cons_tail (P : σ → List σ) (c : σ) (l : List σ) :
    passOut P (c :: l) = P c ++ passOut P l.tail := by
  cases l with
  | nil => simp
  | cons b rest => rfl

theorem reps_succ' (w : List σ) (m : Nat) : reps w (m + 1) = reps w m ++ w := by
  rw [reps_add, reps_succ, reps_zero, List.append_nil]

/-- After a leading symbol, the second of each pair is read, and the frame
    stays shifted. -/
theorem passOut_cons_pairs2 (P : σ → List σ) (c a b : σ) (m : Nat) (l : List σ) :
    passOut P (c :: (pairs2 a b m ++ l)) = P c ++ reps (P b) m ++ passOut P l.tail := by
  cases m with
  | zero => rw [pairs2_zero, List.nil_append, passOut_cons_tail, reps_zero, List.append_nil]
  | succ m =>
    rw [pairs2_succ, List.cons_append, List.cons_append, passOut_cons_cons, passOut_shift,
      passOut_cons_tail, reps_succ', List.append_assoc, List.append_assoc]

/-- A run read from its second symbol on: half of it, rounded up. -/
theorem passOut_replicate (P : σ → List σ) (r : σ) (k : Nat) :
    passOut P (List.replicate k r) = reps (P r) ((k + 1) / 2) := by
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
  · subst hj
    have := passOut_replicate_even P r j []
    rw [List.append_nil, passOut_nil, List.append_nil] at this
    rw [this, show (2 * j + 1) / 2 = j from by omega]
  · subst hj
    have := passOut_replicate_odd P r j []
    rw [List.append_nil, passOut_singleton, ← reps_succ'] at this
    rw [this, show (2 * j + 1 + 1) / 2 = j + 1 from by omega]

/-- A symbol before a run: the symbol, then half of the run. -/
theorem passOut_cons_replicate (P : σ → List σ) (c r : σ) (n : Nat) :
    passOut P (c :: List.replicate n r) = P c ++ reps (P r) (n / 2) := by
  rw [passOut_cons_tail]
  cases n with
  | zero => simp
  | succ n =>
    rw [List.replicate_succ, List.tail_cons, passOut_replicate, show (n + 1) / 2 = (n + 1) / 2 from rfl]

/-- A symbol, a run, and a rest: the rest is read from its first symbol
    when the run has odd length, from its second when even. -/
theorem passOut_cons_replicate_append (P : σ → List σ) (c r : σ) (n : Nat) (l : List σ) :
    passOut P (c :: (List.replicate n r ++ l))
      = P c ++ reps (P r) (n / 2) ++ (if n % 2 = 0 then passOut P l.tail else passOut P l) := by
  rw [passOut_cons_tail]
  cases n with
  | zero => simp
  | succ n =>
    rw [List.replicate_succ, List.cons_append, List.tail_cons]
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' n
    · subst hj
      rw [passOut_replicate_even, show (2 * j + 1) / 2 = j from by omega,
        ite_eq_right (by omega), List.append_assoc]
    · subst hj
      rw [passOut_replicate_odd, passOut_cons_tail, show (2 * j + 1 + 1) / 2 = j + 1 from by omega,
        ite_eq_left (by omega), reps_succ', List.append_assoc, List.append_assoc]

/-- The odd round on the whole word: a word `a :: l` of odd length at least
    3 whose first production is nonempty. -/
theorem nStepsP_odd' (P : σ → List σ) (n : Nat) (a : σ) (l : List σ) (hl : l.length = 2 * n)
    (hn : 1 ≤ n) (hPa : P a ≠ []) :
    nStepsP P (a :: l) (n + 1) = some ((passOut P (a :: l)).tail) := by
  obtain ⟨l', z, hz⟩ : ∃ l' z, l = l' ++ [z] := by
    cases hl' : l.reverse with
    | nil => rw [List.reverse_eq_nil_iff] at hl'; rw [hl'] at hl; simp at hl; omega
    | cons z l' =>
      refine ⟨l'.reverse, z, ?_⟩
      rw [← List.reverse_reverse l, hl', List.reverse_cons]
  subst hz
  have hl'' : (a :: l').length = 2 * n := by simp at hl ⊢; omega
  rw [← List.cons_append]
  refine nStepsP_odd P n (a :: l') z hl'' ?_
  rw [passOut_cons_tail]
  intro h
  exact hPa (List.append_eq_nil_iff.mp h).1

end TagSystem
