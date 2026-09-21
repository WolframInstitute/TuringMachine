/-
  TagSystem.CockeMinsky

  PLAN.md target T7, first half (milestone M4b): a 2-tag system simulates a
  binary Turing machine, after Cocke and Minsky (1964; Minsky 1967, section
  14.6), in the phase design below.

  A configuration of the machine in state `q`, with left tape read as the
  number `m` (nearest cell least significant), scanned cell `h` and right
  tape read as `n`, is the word

      A_q x (al_q x)^m B_q x (be_q x)^N,   N = h + 2 n,

  the scanned cell being the lowest bit of the right number. One machine
  step is three or five rounds of the tag system (`TagSystem.TagRounds`):

    * round 1 (`A -> P1 P0`, `al -> p p`, `B -> Q`, `be -> r`) leaves
      `P1 P0 (p p)^m Q r^N`, whose length has the parity of `N + 1`;
    * round 2 reads `P1`, `m` of the `p`, `Q`, and `N / 2` of the `r`
      (the run starts after an odd prefix), producing pairs `E1 E0`,
      `(e1 e0)^m`, `F1 F0`, `(f1 f0)^(N/2)`; when `N` is even the round has
      odd length, its last read takes `E1` as deleted partner, and round 3
      reads the second of every pair: every symbol read in round 3 knows
      `h = N mod 2`, and `N` has lost its lowest bit;
    * round 3 executes the transition `(q, h) -> (q', w, d)`. For a move to
      the right the word `A_q' x (al x)^(w + 2m) B x (be x)^(N/2)` is written
      directly (a leading pad `x` when the frame is shifted restores it).
      For a move to the left, round 3 writes `G g^m H H k^(4 (N/2))`, round 4
      reads `m / 2` of the `g` and half of the `k`, producing pairs whose
      frame in round 5 selects `b = m mod 2`, and round 5 writes
      `A_q' x (al x)^(m/2) B x (be x)^(2w + b + 4 (N/2))`.

  Contents: `Kind`, `Sym`, the productions `prod`, `cword`, the rounds
  `round1` to `round5`, `val`, `word`, `ValidCfg`, `tm_step_tag`.
-/

import TagSystem.TagRounds
import BiTM.Basic

namespace TagSystem

open TM
open BiTM

/-- The kinds of symbols. -/
inductive Kind
  | A | al | B | be
  | P1 | P0 | p | Q | r
  | E | e | F | f
  | G | g | H | k
  | I | i | J | j
  deriving DecidableEq, Repr

/-- A symbol: the pad `x` (`none`), or a kind with a state and two bits (the
    scanned bit and the parity of the left number, where the kind uses them). -/
abbrev Sym := Option (Kind × Nat × Bool × Bool)

/-- The pad. -/
abbrev X : Sym := none

def sy (kd : Kind) (q : Nat) (h b : Bool) : Sym := some (kd, q, h, b)

def cA (q : Nat) : Sym := sy Kind.A q false false
def cAl (q : Nat) : Sym := sy Kind.al q false false
def cB (q : Nat) : Sym := sy Kind.B q false false
def cBe (q : Nat) : Sym := sy Kind.be q false false
def cP1 (q : Nat) : Sym := sy Kind.P1 q false false
def cP0 (q : Nat) : Sym := sy Kind.P0 q false false
def cp (q : Nat) : Sym := sy Kind.p q false false
def cQ (q : Nat) : Sym := sy Kind.Q q false false
def cr (q : Nat) : Sym := sy Kind.r q false false
def cE (q : Nat) (h : Bool) : Sym := sy Kind.E q h false
def ce (q : Nat) (h : Bool) : Sym := sy Kind.e q h false
def cF (q : Nat) (h : Bool) : Sym := sy Kind.F q h false
def cf (q : Nat) (h : Bool) : Sym := sy Kind.f q h false
def cG (q : Nat) (h : Bool) : Sym := sy Kind.G q h false
def cg (q : Nat) (h : Bool) : Sym := sy Kind.g q h false
def cH (q : Nat) (h : Bool) : Sym := sy Kind.H q h false
def ck (q : Nat) (h : Bool) : Sym := sy Kind.k q h false
def cI (q : Nat) (h b : Bool) : Sym := sy Kind.I q h b
def ci (q : Nat) (h b : Bool) : Sym := sy Kind.i q h b
def cJ (q : Nat) (h b : Bool) : Sym := sy Kind.J q h b
def cj (q : Nat) (h b : Bool) : Sym := sy Kind.j q h b

/-- A bit as a symbol of the machine. -/
def bit (h : Bool) : Nat := if h then 1 else 0

/-- The pad written when the frame is shifted. -/
def pad (h : Bool) : List Sym := if h then [] else [X]

@[simp] theorem pad_true : pad true = [] := rfl
@[simp] theorem pad_false : pad false = [X] := rfl

variable (tm : Machine)

/-- The next state, the written bit and the direction of the transition at
    `(q, h)`. -/
def nxt (q : Nat) (h : Bool) : Nat := (tm.transition q (bit h)).nextState
def wr (q : Nat) (h : Bool) : Nat := (tm.transition q (bit h)).write % 2
def dr (q : Nat) (h : Bool) : Dir := (tm.transition q (bit h)).dir

/-- The productions. -/
def prod : Sym → List Sym
  | none => []
  | some (Kind.A, q, _, _) => [cP1 q, cP0 q]
  | some (Kind.al, q, _, _) => [cp q, cp q]
  | some (Kind.B, q, _, _) => [cQ q]
  | some (Kind.be, q, _, _) => [cr q]
  | some (Kind.P1, q, _, _) => [cE q true, cE q false]
  | some (Kind.P0, _, _, _) => []
  | some (Kind.p, q, _, _) => [ce q true, ce q false]
  | some (Kind.Q, q, _, _) => [cF q true, cF q false]
  | some (Kind.r, q, _, _) => [cf q true, cf q false]
  | some (Kind.E, q, h, _) =>
      match dr tm q h with
      | Dir.R => pad h ++ cA (nxt tm q h) :: X :: pairs2 (cAl (nxt tm q h)) X (wr tm q h)
      | Dir.L => pad h ++ [cG q h]
  | some (Kind.e, q, h, _) =>
      match dr tm q h with
      | Dir.R => [cAl (nxt tm q h), X, cAl (nxt tm q h), X]
      | Dir.L => [cg q h]
  | some (Kind.F, q, h, _) =>
      match dr tm q h with
      | Dir.R => [cB (nxt tm q h), X]
      | Dir.L => [cH q h, cH q h]
  | some (Kind.f, q, h, _) =>
      match dr tm q h with
      | Dir.R => [cBe (nxt tm q h), X]
      | Dir.L => [ck q h, ck q h, ck q h, ck q h]
  | some (Kind.G, q, h, _) => [cI q h true, cI q h false]
  | some (Kind.g, q, h, _) => [ci q h true, ci q h false]
  | some (Kind.H, q, h, _) => [cJ q h true, cJ q h false]
  | some (Kind.k, q, h, _) => [cj q h true, cj q h false]
  | some (Kind.I, q, h, b) => pad b ++ [cA (nxt tm q h), X]
  | some (Kind.i, q, h, _) => [cAl (nxt tm q h), X]
  | some (Kind.J, q, h, b) =>
      cB (nxt tm q h) :: X :: pairs2 (cBe (nxt tm q h)) X (2 * wr tm q h + bit b)
  | some (Kind.j, q, h, _) => [cBe (nxt tm q h), X, cBe (nxt tm q h), X]

@[simp] theorem prod_X : prod tm X = [] := rfl
@[simp] theorem prod_A (q : Nat) : prod tm (cA q) = [cP1 q, cP0 q] := rfl
@[simp] theorem prod_al (q : Nat) : prod tm (cAl q) = [cp q, cp q] := rfl
@[simp] theorem prod_B (q : Nat) : prod tm (cB q) = [cQ q] := rfl
@[simp] theorem prod_be (q : Nat) : prod tm (cBe q) = [cr q] := rfl
@[simp] theorem prod_P1 (q : Nat) : prod tm (cP1 q) = [cE q true, cE q false] := rfl
@[simp] theorem prod_p (q : Nat) : prod tm (cp q) = [ce q true, ce q false] := rfl
@[simp] theorem prod_Q (q : Nat) : prod tm (cQ q) = [cF q true, cF q false] := rfl
@[simp] theorem prod_r (q : Nat) : prod tm (cr q) = [cf q true, cf q false] := rfl
theorem prod_E_R (q : Nat) (h : Bool) (hd : dr tm q h = Dir.R) :
    prod tm (cE q h) = pad h ++ cA (nxt tm q h) :: X :: pairs2 (cAl (nxt tm q h)) X (wr tm q h) := by
  simp [prod, cE, sy, hd]
theorem prod_E_L (q : Nat) (h : Bool) (hd : dr tm q h = Dir.L) :
    prod tm (cE q h) = pad h ++ [cG q h] := by
  simp [prod, cE, sy, hd]
theorem prod_e_R (q : Nat) (h : Bool) (hd : dr tm q h = Dir.R) :
    prod tm (ce q h) = pairs2 (cAl (nxt tm q h)) X 2 := by
  simp [prod, ce, sy, hd, pairs2]
theorem prod_e_L (q : Nat) (h : Bool) (hd : dr tm q h = Dir.L) :
    prod tm (ce q h) = [cg q h] := by
  simp [prod, ce, sy, hd]
theorem prod_F_R (q : Nat) (h : Bool) (hd : dr tm q h = Dir.R) :
    prod tm (cF q h) = [cB (nxt tm q h), X] := by
  simp [prod, cF, sy, hd]
theorem prod_F_L (q : Nat) (h : Bool) (hd : dr tm q h = Dir.L) :
    prod tm (cF q h) = [cH q h, cH q h] := by
  simp [prod, cF, sy, hd]
theorem prod_f_R (q : Nat) (h : Bool) (hd : dr tm q h = Dir.R) :
    prod tm (cf q h) = [cBe (nxt tm q h), X] := by
  simp [prod, cf, sy, hd]
theorem prod_f_L (q : Nat) (h : Bool) (hd : dr tm q h = Dir.L) :
    prod tm (cf q h) = List.replicate 4 (ck q h) := by
  simp [prod, cf, sy, hd, List.replicate]
@[simp] theorem prod_G (q : Nat) (h : Bool) : prod tm (cG q h) = [cI q h true, cI q h false] := rfl
@[simp] theorem prod_g (q : Nat) (h : Bool) : prod tm (cg q h) = [ci q h true, ci q h false] := rfl
@[simp] theorem prod_H (q : Nat) (h : Bool) : prod tm (cH q h) = [cJ q h true, cJ q h false] := rfl
@[simp] theorem prod_k (q : Nat) (h : Bool) : prod tm (ck q h) = [cj q h true, cj q h false] := rfl
@[simp] theorem prod_I (q : Nat) (h b : Bool) : prod tm (cI q h b) = pad b ++ [cA (nxt tm q h), X] := rfl
@[simp] theorem prod_i (q : Nat) (h b : Bool) : prod tm (ci q h b) = [cAl (nxt tm q h), X] := rfl
@[simp] theorem prod_J (q : Nat) (h b : Bool) :
    prod tm (cJ q h b) = cB (nxt tm q h) :: X :: pairs2 (cBe (nxt tm q h)) X (2 * wr tm q h + bit b) := rfl
@[simp] theorem prod_j (q : Nat) (h b : Bool) : prod tm (cj q h b) = pairs2 (cBe (nxt tm q h)) X 2 := rfl

/-! ## The words of the rounds -/

/-- The configuration word. -/
def cword (q m N : Nat) : List Sym :=
  cA q :: X :: (pairs2 (cAl q) X m ++ cB q :: X :: pairs2 (cBe q) X N)

/-- After round 1. -/
def W1 (q m N : Nat) : List Sym :=
  cP1 q :: cP0 q :: (pairs2 (cp q) (cp q) m ++ cQ q :: List.replicate N (cr q))

/-- After round 2: `h` is the scanned bit, `n2` the right number without it. -/
def W2 (q : Nat) (h : Bool) (m n2 : Nat) : List Sym :=
  (if h then [cE q true] else []) ++
    cE q false :: (pairs2 (ce q true) (ce q false) m ++
      cF q true :: cF q false :: pairs2 (cf q true) (cf q false) n2)

/-- After round 3 of a move to the left. -/
def W3 (q : Nat) (h : Bool) (m n2 : Nat) : List Sym :=
  cG q h :: (List.replicate m (cg q h) ++ cH q h :: cH q h :: List.replicate (4 * n2) (ck q h))

/-- After round 4 of a move to the left: `b` is the parity of the left
    number, `i` its half. -/
def W4 (q : Nat) (h b : Bool) (i n2 : Nat) : List Sym :=
  (if b then [cI q h true] else []) ++
    cI q h false :: (pairs2 (ci q h true) (ci q h false) i ++
      cJ q h true :: cJ q h false :: pairs2 (cj q h true) (cj q h false) (2 * n2))

theorem reps_singleton (a : Sym) (n : Nat) : reps [a] n = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [reps, List.replicate_succ, ih]

theorem reps_replicate (a : Sym) (k n : Nat) :
    reps (List.replicate k a) n = List.replicate (k * n) a := by
  induction n with
  | zero => simp
  | succ n ih => rw [reps_succ, ih, Nat.mul_succ, Nat.add_comm, List.replicate_append_replicate]

theorem reps_pairs2_two (a b : Sym) (m : Nat) : reps (pairs2 a b 2) m = pairs2 a b (2 * m) := by
  rw [← reps_pair, reps_mul, reps_pair]

theorem pairs2_eq_append_nil (a b : Sym) (m : Nat) : pairs2 a b m = pairs2 a b m ++ [] :=
  (List.append_nil _).symm

/-! ## Round 1 -/

theorem length_cword (q m N : Nat) : (cword q m N).length = 2 * (m + N + 2) := by
  simp [cword]; omega

theorem round1 (q m N : Nat) :
    nStepsP (prod tm) (cword q m N) (m + N + 2) = some (W1 q m N) := by
  have h := nStepsP_even (prod tm) (m + N + 2) (cword q m N) [] (length_cword q m N)
  rw [List.append_nil, List.nil_append] at h
  rw [h]
  congr 1
  simp only [cword, passOut_cons_cons, passOut_pairs2, prod_A, prod_al, prod_B, reps_pair, W1]
  rw [pairs2_eq_append_nil (cBe q) X N, passOut_pairs2, passOut_nil, List.append_nil, prod_be,
    reps_singleton]
  simp

/-! ## Round 2 -/

theorem length_W1 (q m N : Nat) : (W1 q m N).length = 2 * m + N + 3 := by
  simp [W1]; omega

theorem passOut_W1 (q m N : Nat) :
    passOut (prod tm) (W1 q m N)
      = cE q true :: cE q false :: (pairs2 (ce q true) (ce q false) m ++
          cF q true :: cF q false :: pairs2 (cf q true) (cf q false) (N / 2)) := by
  simp only [W1, passOut_cons_cons, passOut_pairs2, prod_P1, prod_p, passOut_cons_replicate, prod_Q,
    prod_r, reps_pair, List.cons_append, List.nil_append]

theorem round2 (q m N : Nat) :
    nStepsP (prod tm) (W1 q m N) (m + N / 2 + 2) = some (W2 q (N % 2 = 1) m (N / 2)) := by
  obtain ⟨n2, hN | hN⟩ := Nat.even_or_odd' N
  · subst hN
    have hl : (cP0 q :: (pairs2 (cp q) (cp q) m ++ cQ q :: List.replicate (2 * n2) (cr q))).length
        = 2 * (m + n2 + 1) := by simp; omega
    have h := nStepsP_odd' (prod tm) (m + n2 + 1) (cP1 q) _ hl (by omega) (by simp)
    rw [show m + (2 * n2) / 2 + 2 = m + n2 + 1 + 1 from by omega]
    unfold W1
    rw [h]
    congr 1
    rw [← W1, passOut_W1, List.tail_cons, W2, ite_eq_right (by simp only [decide_eq_true_eq]; omega),
      List.nil_append, show 2 * n2 / 2 = n2 from by omega]
  · subst hN
    have hl : (W1 q m (2 * n2 + 1)).length = 2 * (m + n2 + 2) := by rw [length_W1]; omega
    have h := nStepsP_even (prod tm) (m + n2 + 2) (W1 q m (2 * n2 + 1)) [] hl
    rw [List.append_nil, List.nil_append] at h
    rw [show m + (2 * n2 + 1) / 2 + 2 = m + n2 + 2 from by omega, h, passOut_W1, W2,
      ite_eq_left (by simp only [decide_eq_true_eq]; omega), show (2 * n2 + 1) / 2 = n2 from by omega]
    rfl

/-! ## Round 3 -/

theorem passOut_W2 (q : Nat) (h : Bool) (m n2 : Nat) :
    passOut (prod tm) (W2 q h m n2)
      = prod tm (cE q h) ++ reps (prod tm (ce q h)) m ++ prod tm (cF q h) ++
          reps (prod tm (cf q h)) n2 := by
  cases h with
  | true =>
    simp only [W2, ite_true, List.singleton_append, passOut_cons_cons, passOut_pairs2]
    rw [pairs2_eq_append_nil (cf q true) (cf q false) n2, passOut_pairs2, passOut_nil,
      List.append_nil, List.append_assoc, List.append_assoc]
  | false =>
    simp only [W2, Bool.false_eq_true, ite_false, List.nil_append]
    rw [pairs2_eq_append_nil (cf q true) (cf q false) n2, passOut_cons_pairs2, List.tail_cons,
      passOut_cons_pairs2, List.tail_nil, passOut_nil, List.append_nil]
    simp only [List.append_assoc]

theorem prod_E_ne_nil (q : Nat) (h : Bool) : prod tm (cE q h) ≠ [] := by
  cases hd : dr tm q h
  · rw [prod_E_L tm q h hd]; cases h <;> simp [pad]
  · rw [prod_E_R tm q h hd]; cases h <;> simp [pad]

/-- Round 3 of a move to the right. -/
theorem round3R (q : Nat) (h : Bool) (m n2 : Nat) (hd : dr tm q h = Dir.R) :
    nStepsP (prod tm) (W2 q h m n2) (m + n2 + 2)
      = some (cword (nxt tm q h) (wr tm q h + 2 * m) n2) := by
  have hpo : passOut (prod tm) (W2 q h m n2)
      = pad h ++ cword (nxt tm q h) (wr tm q h + 2 * m) n2 := by
    rw [passOut_W2, prod_E_R tm q h hd, prod_e_R tm q h hd, prod_F_R tm q h hd, prod_f_R tm q h hd,
      reps_pairs2_two, reps_pair, cword, pairs2_add]
    simp
  cases h with
  | true =>
    have hl : (W2 q true m n2).length = 2 * (m + n2 + 2) := by simp [W2]; omega
    have h := nStepsP_even (prod tm) (m + n2 + 2) (W2 q true m n2) [] hl
    rw [List.append_nil, List.nil_append] at h
    rw [h, hpo, pad_true, List.nil_append]
  | false =>
    have hl : (pairs2 (ce q true) (ce q false) m ++
        cF q true :: cF q false :: pairs2 (cf q true) (cf q false) n2).length
        = 2 * (m + n2 + 1) := by simp; omega
    have h := nStepsP_odd' (prod tm) (m + n2 + 1) (cE q false) _ hl (by omega)
      (prod_E_ne_nil tm q false)
    rw [show m + n2 + 2 = m + n2 + 1 + 1 from rfl]
    have hW : W2 q false m n2 = cE q false :: (pairs2 (ce q true) (ce q false) m ++
        cF q true :: cF q false :: pairs2 (cf q true) (cf q false) n2) := by
      simp [W2]
    rw [hW, h, ← hW, hpo, pad_false, List.singleton_append, List.tail_cons]

/-- Round 3 of a move to the left. -/
theorem round3L (q : Nat) (h : Bool) (m n2 : Nat) (hd : dr tm q h = Dir.L) :
    nStepsP (prod tm) (W2 q h m n2) (m + n2 + 2) = some (W3 q h m n2) := by
  have hpo : passOut (prod tm) (W2 q h m n2) = pad h ++ W3 q h m n2 := by
    rw [passOut_W2, prod_E_L tm q h hd, prod_e_L tm q h hd, prod_F_L tm q h hd, prod_f_L tm q h hd,
      reps_singleton, reps_replicate, W3]
    simp
  cases h with
  | true =>
    have hl : (W2 q true m n2).length = 2 * (m + n2 + 2) := by simp [W2]; omega
    have h := nStepsP_even (prod tm) (m + n2 + 2) (W2 q true m n2) [] hl
    rw [List.append_nil, List.nil_append] at h
    rw [h, hpo, pad_true, List.nil_append]
  | false =>
    have hl : (pairs2 (ce q true) (ce q false) m ++
        cF q true :: cF q false :: pairs2 (cf q true) (cf q false) n2).length
        = 2 * (m + n2 + 1) := by simp; omega
    have h := nStepsP_odd' (prod tm) (m + n2 + 1) (cE q false) _ hl (by omega)
      (prod_E_ne_nil tm q false)
    rw [show m + n2 + 2 = m + n2 + 1 + 1 from rfl]
    have hW : W2 q false m n2 = cE q false :: (pairs2 (ce q true) (ce q false) m ++
        cF q true :: cF q false :: pairs2 (cf q true) (cf q false) n2) := by
      simp [W2]
    rw [hW, h, ← hW, hpo, pad_false, List.singleton_append, List.tail_cons]

/-! ## Round 4 -/

theorem passOut_W3 (q : Nat) (h : Bool) (m n2 : Nat) :
    passOut (prod tm) (W3 q h m n2)
      = cI q h true :: cI q h false :: (pairs2 (ci q h true) (ci q h false) (m / 2) ++
          cJ q h true :: cJ q h false :: pairs2 (cj q h true) (cj q h false) (2 * n2)) := by
  rw [W3, passOut_cons_replicate_append, prod_G, prod_g, reps_pair]
  have hH : passOut (prod tm) (cH q h :: cH q h :: List.replicate (4 * n2) (ck q h))
      = cJ q h true :: cJ q h false :: pairs2 (cj q h true) (cj q h false) (2 * n2) := by
    rw [passOut_cons_cons, passOut_replicate, prod_H, prod_k, reps_pair,
      show (4 * n2 + 1) / 2 = 2 * n2 from by omega]
    rfl
  have hH' : passOut (prod tm) ((cH q h :: cH q h :: List.replicate (4 * n2) (ck q h)).tail)
      = cJ q h true :: cJ q h false :: pairs2 (cj q h true) (cj q h false) (2 * n2) := by
    rw [List.tail_cons, passOut_cons_replicate, prod_H, prod_k, reps_pair,
      show 4 * n2 / 2 = 2 * n2 from by omega]
    rfl
  rw [hH, hH']
  simp

theorem round4 (q : Nat) (h : Bool) (m n2 : Nat) :
    nStepsP (prod tm) (W3 q h m n2) (m / 2 + 2 * n2 + 2) = some (W4 q h (m % 2 = 1) (m / 2) n2) := by
  obtain ⟨i, hm | hm⟩ := Nat.even_or_odd' m
  · subst hm
    have hl : (List.replicate (2 * i) (cg q h) ++ cH q h :: cH q h :: List.replicate (4 * n2) (ck q h)).length
        = 2 * (i + 2 * n2 + 1) := by simp; omega
    have hs := nStepsP_odd' (prod tm) (i + 2 * n2 + 1) (cG q h) _ hl (by omega) (by simp)
    rw [show 2 * i / 2 + 2 * n2 + 2 = i + 2 * n2 + 1 + 1 from by omega]
    unfold W3
    rw [hs]
    congr 1
    rw [← W3, passOut_W3, List.tail_cons, W4, ite_eq_right (by simp only [decide_eq_true_eq]; omega),
      List.nil_append, show 2 * i / 2 = i from by omega]
  · subst hm
    have hl : (W3 q h (2 * i + 1) n2).length = 2 * (i + 2 * n2 + 2) := by simp [W3]; omega
    have hs := nStepsP_even (prod tm) (i + 2 * n2 + 2) (W3 q h (2 * i + 1) n2) [] hl
    rw [List.append_nil, List.nil_append] at hs
    rw [show (2 * i + 1) / 2 + 2 * n2 + 2 = i + 2 * n2 + 2 from by omega, hs, passOut_W3, W4,
      ite_eq_left (by simp only [decide_eq_true_eq]; omega), show (2 * i + 1) / 2 = i from by omega]
    rfl

/-! ## Round 5 -/

theorem passOut_W4 (q : Nat) (h b : Bool) (i n2 : Nat) :
    passOut (prod tm) (W4 q h b i n2)
      = prod tm (cI q h b) ++ reps (prod tm (ci q h b)) i ++ prod tm (cJ q h b) ++
          reps (prod tm (cj q h b)) (2 * n2) := by
  cases b with
  | true =>
    simp only [W4, ite_true, List.singleton_append, passOut_cons_cons, passOut_pairs2]
    rw [pairs2_eq_append_nil (cj q h true) (cj q h false) (2 * n2), passOut_pairs2, passOut_nil,
      List.append_nil, List.append_assoc, List.append_assoc]
  | false =>
    simp only [W4, Bool.false_eq_true, ite_false, List.nil_append]
    rw [pairs2_eq_append_nil (cj q h true) (cj q h false) (2 * n2), passOut_cons_pairs2,
      List.tail_cons, passOut_cons_pairs2, List.tail_nil, passOut_nil, List.append_nil]
    simp only [List.append_assoc]

theorem round5 (q : Nat) (h b : Bool) (i n2 : Nat) :
    nStepsP (prod tm) (W4 q h b i n2) (i + 2 * n2 + 2)
      = some (cword (nxt tm q h) i (2 * wr tm q h + bit b + 4 * n2)) := by
  have hpo : passOut (prod tm) (W4 q h b i n2)
      = pad b ++ cword (nxt tm q h) i (2 * wr tm q h + bit b + 4 * n2) := by
    rw [passOut_W4, prod_I, prod_i, prod_J, prod_j, reps_pair, reps_pairs2_two,
      show 4 * n2 = 2 * (2 * n2) from by omega]
    simp [cword, pairs2_add]
  cases b with
  | true =>
    have hl : (W4 q h true i n2).length = 2 * (i + 2 * n2 + 2) := by simp [W4]; omega
    have hs := nStepsP_even (prod tm) (i + 2 * n2 + 2) (W4 q h true i n2) [] hl
    rw [List.append_nil, List.nil_append] at hs
    rw [hs, hpo, pad_true, List.nil_append]
  | false =>
    have hl : (pairs2 (ci q h true) (ci q h false) i ++
        cJ q h true :: cJ q h false :: pairs2 (cj q h true) (cj q h false) (2 * n2)).length
        = 2 * (i + 2 * n2 + 1) := by simp; omega
    have hs := nStepsP_odd' (prod tm) (i + 2 * n2 + 1) (cI q h false) _ hl (by omega) (by simp)
    rw [show i + 2 * n2 + 2 = i + 2 * n2 + 1 + 1 from rfl]
    have hW : W4 q h false i n2 = cI q h false :: (pairs2 (ci q h true) (ci q h false) i ++
        cJ q h true :: cJ q h false :: pairs2 (cj q h true) (cj q h false) (2 * n2)) := by
      simp [W4]
    rw [hW, hs, ← hW, hpo, pad_false, List.singleton_append, List.tail_cons]

/-! ## The machine step -/

/-- A tape half as a number, nearest cell least significant. -/
def val : List Nat → Nat
  | [] => 0
  | a :: l => a + 2 * val l

@[simp] theorem val_nil : val [] = 0 := rfl
@[simp] theorem val_cons (a : Nat) (l : List Nat) : val (a :: l) = a + 2 * val l := rfl

/-- The word of a configuration. -/
def word (c : Config) : List Sym := cword c.state (val c.left) (c.head + 2 * val c.right)

/-- The tape holds bits. -/
def ValidCfg (c : Config) : Prop := c.head < 2 ∧ (∀ a ∈ c.left, a < 2) ∧ (∀ a ∈ c.right, a < 2)

theorem val_readHead (l : List Nat) : (readHead l).1 + 2 * val (readHead l).2 = val l := by
  cases l <;> rfl

theorem readHead_fst (l : List Nat) (hl : ∀ a ∈ l, a < 2) : (readHead l).1 = val l % 2 := by
  cases l with
  | nil => rfl
  | cons a l =>
    have := hl a List.mem_cons_self
    show a = (a + 2 * val l) % 2
    omega

theorem val_readHead_snd (l : List Nat) (hl : ∀ a ∈ l, a < 2) : val (readHead l).2 = val l / 2 := by
  cases l with
  | nil => rfl
  | cons a l =>
    have := hl a List.mem_cons_self
    show val l = (a + 2 * val l) / 2
    omega

theorem step_R (q : Nat) (left : List Nat) (head : Nat) (right : List Nat) (hq : q ≠ 0)
    (hd : (tm.transition q head).dir = Dir.R) :
    BiTM.step tm ⟨q, left, head, right⟩
      = some ⟨(tm.transition q head).nextState, (tm.transition q head).write :: left,
              (readHead right).1, (readHead right).2⟩ := by
  unfold BiTM.step
  simp only [beq_iff_eq, hq, ite_false, hd]

theorem step_L (q : Nat) (left : List Nat) (head : Nat) (right : List Nat) (hq : q ≠ 0)
    (hd : (tm.transition q head).dir = Dir.L) :
    BiTM.step tm ⟨q, left, head, right⟩
      = some ⟨(tm.transition q head).nextState, (readHead left).2, (readHead left).1,
              (tm.transition q head).write :: right⟩ := by
  unfold BiTM.step
  simp only [beq_iff_eq, hq, ite_false, hd]

theorem bit_decide_head (head : Nat) (hh : head < 2) : bit (decide (head = 1)) = head := by
  rcases Nat.lt_succ_iff.mp hh |> Nat.le_one_iff_eq_zero_or_eq_one.mp with rfl | rfl <;> rfl

theorem bit_decide_mod (m : Nat) : bit (decide (m % 2 = 1)) = m % 2 := by
  rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
  · simp [bit, h0]
  · simp [bit, h1]

/-- One step of the machine is three or five rounds of the tag system. -/
theorem tm_step_tag (c c' : Config) (hv : ValidCfg c)
    (hb : (tm.transition c.state c.head).write < 2) (hs : BiTM.step tm c = some c') :
    ∃ k, 1 ≤ k ∧ nStepsP (prod tm) (word c) k = some (word c') := by
  obtain ⟨q, left, head, right⟩ := c
  obtain ⟨hh, hl, hr⟩ := hv
  simp only at hh hl hr hb
  have hq : q ≠ 0 := by
    intro hq
    subst hq
    simp [BiTM.step] at hs
  have hbit : bit (decide (head = 1)) = head := bit_decide_head head hh
  have hnxt : nxt tm q (decide (head = 1)) = (tm.transition q head).nextState := by
    simp [nxt, hbit]
  have hwr : wr tm q (decide (head = 1)) = (tm.transition q head).write := by
    simp only [wr, hbit]
    exact Nat.mod_eq_of_lt hb
  have hdr : dr tm q (decide (head = 1)) = (tm.transition q head).dir := by
    simp [dr, hbit]
  have hpar : decide ((head + 2 * val right) % 2 = 1) = decide (head = 1) := by
    rw [decide_eq_decide]; omega
  have hhalf : (head + 2 * val right) / 2 = val right := by omega
  cases hd : (tm.transition q head).dir with
  | R =>
    rw [step_R tm q left head right hq hd] at hs
    obtain rfl := Option.some.inj hs
    refine ⟨(val left + (head + 2 * val right) + 2) + (val left + (head + 2 * val right) / 2 + 2) +
      (val left + (head + 2 * val right) / 2 + 2), by omega, ?_⟩
    simp only [word, val_cons, val_readHead]
    rw [nStepsP_add, nStepsP_add, round1, Option.bind_some, round2, Option.bind_some, hpar,
      hhalf, round3R tm q _ _ _ (by rw [hdr, hd]), hnxt, hwr]
  | L =>
    rw [step_L tm q left head right hq hd] at hs
    obtain rfl := Option.some.inj hs
    refine ⟨(val left + (head + 2 * val right) + 2) + (val left + (head + 2 * val right) / 2 + 2) +
      (val left + (head + 2 * val right) / 2 + 2) + (val left / 2 + 2 * ((head + 2 * val right) / 2) + 2) +
      (val left / 2 + 2 * ((head + 2 * val right) / 2) + 2), by omega, ?_⟩
    simp only [word, val_cons, readHead_fst left hl, val_readHead_snd left hl]
    rw [nStepsP_add, nStepsP_add, nStepsP_add, nStepsP_add, round1, Option.bind_some,
      round2, Option.bind_some, hpar, hhalf, round3L tm q _ _ _ (by rw [hdr, hd]), Option.bind_some,
      round4, Option.bind_some, round5, hnxt, hwr, bit_decide_mod]
    have e : 2 * (tm.transition q head).write + val left % 2 + 4 * val right
        = val left % 2 + 2 * ((tm.transition q head).write + 2 * val right) := by omega
    rw [e]

end TagSystem
