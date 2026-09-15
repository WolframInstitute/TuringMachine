/-
  Smith.Doubling

  Link A of the Smith chain (PLAN.md section 3): the doubling trick of
  TM23Proof.pdf p. 18.  Every two-colour cyclic tag system is emulated by
  one in which the elements of the strings to be added always occur in
  pairs: double every bit of the working string and of every appendant, and
  insert a blank appendant after each original appendant.

  On the PDF's own example the cyclic tag system

      110 11 0 01 ""

  becomes

      111100 1111 "" 00 "" 0011 "" "" ""

  Contents:
    * `ctsSys`: a cyclic tag system as a `Smith.StepSys`.
    * `dbl`, `dblAppendants`, `double`, `dblCfg`.
    * `dbl_length`, `dbl_append`, and the appendant lookups
      `double_currentAppendant_even` / `double_currentAppendant_odd`.
    * `double_nSteps_two`: two steps of the doubled system are one step of
      the original, the halting case included.
    * `double_nSteps`: the `2 * n` step corollary.
    * `double_forwardSim`: the same statement as a `ForwardSim`, with two
      target steps per source step.
    * `decide`-checked vectors for the PDF example and the negative
      examples that make the relation non-degenerate.
-/

import Smith.Simulation
import TagSystem.Basic

namespace Smith

open TagSystem

/-! ## The step system of a cyclic tag system -/

/-- A cyclic tag system as a `StepSys`. -/
def ctsSys (C : CTS) : StepSys CTSConfig := ⟨C.step⟩

/-- The step function of `ctsSys`. -/
@[simp] theorem ctsSys_step (C : CTS) (c : CTSConfig) :
    (ctsSys C).step c = C.step c := rfl

/-- The generic `nSteps` of `ctsSys` is the hand-rolled `CTS.nSteps`. -/
theorem ctsSys_nSteps (C : CTS) (c : CTSConfig) (n : Nat) :
    (ctsSys C).nSteps c n = C.nSteps c n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [StepSys.nSteps_succ_left, ctsSys_step]
    cases h : C.step c with
    | none => simp [CTS.nSteps, h]
    | some c' => simp [CTS.nSteps, h, ih]

/-- One step peeled off the front of `CTS.nSteps`. -/
theorem CTS_nSteps_succ_left (C : CTS) (c : CTSConfig) (n : Nat) :
    C.nSteps c (n + 1) = (C.step c).bind (fun c' => C.nSteps c' n) := by
  rw [← ctsSys_nSteps, StepSys.nSteps_succ_left, ctsSys_step]
  cases h : C.step c with
  | none => simp
  | some c' => simp [ctsSys_nSteps]

/-- The step of a cyclic tag system on a nonempty working string. -/
theorem CTS_step_cons (C : CTS) (b : Bool) (rest : List Bool) (p : Nat) :
    C.step { data := b :: rest, phase := p }
      = some { data := if b then rest ++ C.currentAppendant p else rest,
               phase := (p + 1) % C.appendants.length } := rfl

/-- A cyclic tag system with an empty working string is stuck. -/
theorem CTS_step_nil (C : CTS) (p : Nat) :
    C.step { data := [], phase := p } = none := rfl

/-! ## Doubling -/

/-- Each bit of a binary word twice. -/
def dbl : List Bool → List Bool
  | [] => []
  | b :: rest => b :: b :: dbl rest

/-- Doubling the empty word. -/
@[simp] theorem dbl_nil : dbl [] = [] := rfl

/-- Doubling a nonempty word. -/
@[simp] theorem dbl_cons (b : Bool) (w : List Bool) :
    dbl (b :: w) = b :: b :: dbl w := rfl

/-- Doubling doubles the length. -/
@[simp] theorem dbl_length (w : List Bool) : (dbl w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b rest ih => simp only [dbl_cons, List.length_cons, ih]; omega

/-- Doubling is a monoid map for concatenation. -/
@[simp] theorem dbl_append (u v : List Bool) : dbl (u ++ v) = dbl u ++ dbl v := by
  induction u with
  | nil => rfl
  | cons b rest ih => simp [ih]

/-- Only the empty word doubles to the empty word. -/
@[simp] theorem dbl_eq_nil_iff (w : List Bool) : dbl w = [] ↔ w = [] := by
  cases w <;> simp

/-- The doubled appendant list: each appendant doubled, each followed by a
    blank appendant. -/
def dblAppendants : List (List Bool) → List (List Bool)
  | [] => []
  | a :: rest => dbl a :: [] :: dblAppendants rest

/-- The doubled appendant list is twice as long. -/
@[simp] theorem dblAppendants_length (l : List (List Bool)) :
    (dblAppendants l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp only [dblAppendants, List.length_cons, ih]; omega

/-- Even positions of the doubled appendant list hold the doubled
    appendants. -/
theorem dblAppendants_getElem?_even (l : List (List Bool)) (i : Nat) :
    (dblAppendants l)[2 * i]? = (l[i]?).map dbl := by
  induction l generalizing i with
  | nil => cases i <;> simp [dblAppendants]
  | cons a rest ih =>
    cases i with
    | zero => simp [dblAppendants]
    | succ j =>
      have h : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      rw [h]
      simp only [dblAppendants, List.getElem?_cons_succ]
      exact ih j

/-- Odd positions of the doubled appendant list hold the blank appendant. -/
theorem dblAppendants_getElem?_odd (l : List (List Bool)) (i : Nat) :
    (dblAppendants l)[2 * i + 1]? = (l[i]?).map (fun _ => []) := by
  induction l generalizing i with
  | nil => cases i <;> simp [dblAppendants]
  | cons a rest ih =>
    cases i with
    | zero => simp [dblAppendants]
    | succ j =>
      have h : 2 * (j + 1) + 1 = (2 * j + 1 + 1) + 1 := by omega
      rw [h]
      simp only [dblAppendants, List.getElem?_cons_succ]
      exact ih j

/-- The doubled cyclic tag system. -/
def double (C : CTS) : CTS where
  appendants := dblAppendants C.appendants
  nonempty := by
    rw [dblAppendants_length]
    have := C.nonempty
    omega

/-- The appendant list of the doubled system. -/
@[simp] theorem double_appendants (C : CTS) :
    (double C).appendants = dblAppendants C.appendants := rfl

/-- The doubled system has twice as many appendants. -/
theorem double_appendants_length (C : CTS) :
    (double C).appendants.length = 2 * C.appendants.length := by
  simp

/-- The doubled configuration: doubled working string, doubled phase. -/
def dblCfg (c : CTSConfig) : CTSConfig :=
  { data := dbl c.data, phase := 2 * c.phase }

/-- Working string of a doubled configuration. -/
@[simp] theorem dblCfg_data (c : CTSConfig) : (dblCfg c).data = dbl c.data := rfl

/-- Phase of a doubled configuration. -/
@[simp] theorem dblCfg_phase (c : CTSConfig) : (dblCfg c).phase = 2 * c.phase := rfl

/-! ## Appendant lookups -/

/-- `CTS.currentAppendant` as an `Option` lookup. -/
theorem currentAppendant_getElem? (C : CTS) (p : Nat) :
    C.appendants[p % C.appendants.length]? = some (C.currentAppendant p) := by
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ C.nonempty)]
  rfl

/-- Reducing a phase modulo the number of appendants changes nothing. -/
theorem currentAppendant_mod (C : CTS) (p : Nat) :
    C.currentAppendant (p % C.appendants.length) = C.currentAppendant p := by
  have hmm : p % C.appendants.length % C.appendants.length = p % C.appendants.length :=
    Nat.mod_eq_of_lt (Nat.mod_lt _ C.nonempty)
  have h1 := currentAppendant_getElem? C (p % C.appendants.length)
  rw [hmm] at h1
  exact Option.some.inj (h1.symm.trans (currentAppendant_getElem? C p))

/-- An even phase of the doubled system reads the doubled appendant the
    original system reads at half that phase. -/
theorem double_currentAppendant_even (C : CTS) (p : Nat) :
    (double C).currentAppendant (2 * p) = dbl (C.currentAppendant p) := by
  have hmod : 2 * p % (double C).appendants.length = 2 * (p % C.appendants.length) := by
    rw [double_appendants_length, Nat.mul_mod_mul_left]
  have h1 := currentAppendant_getElem? (double C) (2 * p)
  rw [hmod, double_appendants, dblAppendants_getElem?_even,
      currentAppendant_getElem? C p] at h1
  simp only [Option.map_some] at h1
  exact (Option.some.inj h1).symm

/-- An odd phase of the doubled system reads the blank appendant. -/
theorem double_currentAppendant_odd (C : CTS) (p : Nat) :
    (double C).currentAppendant (2 * p + 1) = [] := by
  have hk : 0 < C.appendants.length := C.nonempty
  have hlt : p % C.appendants.length < C.appendants.length := Nat.mod_lt _ hk
  have hmod : (2 * p + 1) % (double C).appendants.length
      = 2 * (p % C.appendants.length) + 1 := by
    rw [double_appendants_length]
    have hsplit : (2 * p + 1) % (2 * C.appendants.length)
        = (2 * p % (2 * C.appendants.length) + 1 % (2 * C.appendants.length))
          % (2 * C.appendants.length) := Nat.add_mod _ _ _
    rw [hsplit, Nat.mul_mod_mul_left,
        Nat.mod_eq_of_lt (show 1 < 2 * C.appendants.length by omega),
        Nat.mod_eq_of_lt (show 2 * (p % C.appendants.length) + 1
          < 2 * C.appendants.length by omega)]
  have h1 := currentAppendant_getElem? (double C) (2 * p + 1)
  rw [hmod, double_appendants, dblAppendants_getElem?_odd,
      currentAppendant_getElem? C p] at h1
  simp only [Option.map_some] at h1
  exact (Option.some.inj h1).symm

/-! ## The two-step lemma -/

/-- Two steps of the doubled system are exactly one step of the original,
    the halting case included: the doubled working string is empty exactly
    when the original one is, and a one-bit working string still affords the
    doubled system its two steps. -/
theorem double_nSteps_two (C : CTS) (c : CTSConfig) :
    (double C).nSteps (dblCfg c) 2 = Option.map dblCfg (C.step c) := by
  have hk : 0 < C.appendants.length := C.nonempty
  obtain ⟨data, p⟩ := c
  cases data with
  | nil => rfl
  | cons b rest =>
    have hodd : (double C).currentAppendant
        ((2 * p + 1) % (double C).appendants.length) = [] := by
      rw [currentAppendant_mod]
      exact double_currentAppendant_odd C p
    have hph : ((2 * p + 1) % (double C).appendants.length + 1)
        % (double C).appendants.length = 2 * ((p + 1) % C.appendants.length) := by
      rw [Nat.mod_add_mod, double_appendants_length,
          show 2 * p + 1 + 1 = 2 * (p + 1) by omega, Nat.mul_mod_mul_left]
    have h2 : ∀ w : List Bool,
        (double C).step { data := b :: w,
                          phase := (2 * p + 1) % (double C).appendants.length }
          = some { data := w, phase := 2 * ((p + 1) % C.appendants.length) } := by
      intro w
      rw [CTS_step_cons, hodd, hph]
      cases b <;> simp
    rw [← ctsSys_nSteps, show (2 : Nat) = 1 + 1 from rfl, StepSys.nSteps_add,
        StepSys.nSteps_one, ctsSys_step]
    cases b with
    | false =>
      have h1 : (double C).step (dblCfg { data := false :: rest, phase := p })
          = some { data := false :: dbl rest,
                   phase := (2 * p + 1) % (double C).appendants.length } := by
        show (double C).step { data := false :: false :: dbl rest, phase := 2 * p } = _
        rw [CTS_step_cons]
        simp
      rw [h1, Option.bind_some, StepSys.nSteps_one, ctsSys_step, h2 (dbl rest),
          CTS_step_cons]
      simp [dblCfg]
    | true =>
      have h1 : (double C).step (dblCfg { data := true :: rest, phase := p })
          = some { data := true :: (dbl rest ++ dbl (C.currentAppendant p)),
                   phase := (2 * p + 1) % (double C).appendants.length } := by
        show (double C).step { data := true :: true :: dbl rest, phase := 2 * p } = _
        rw [CTS_step_cons, double_currentAppendant_even]
        simp
      rw [h1, Option.bind_some, StepSys.nSteps_one, ctsSys_step,
          h2 (dbl rest ++ dbl (C.currentAppendant p)), CTS_step_cons]
      simp [dblCfg]

/-- `2 * n` steps of the doubled system are `n` steps of the original. -/
theorem double_nSteps (C : CTS) (c : CTSConfig) (n : Nat) :
    (double C).nSteps (dblCfg c) (2 * n) = Option.map dblCfg (C.nSteps c n) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, ← ctsSys_nSteps, StepSys.nSteps_add,
        ctsSys_nSteps, double_nSteps_two, CTS_nSteps_succ_left]
    cases hstep : C.step c with
    | none => simp
    | some c' =>
      simp only [Option.map_some, Option.bind_some]
      rw [ctsSys_nSteps, ih c']

/-- Link A as a forward simulation: two steps of the doubled system per step
    of the original, so the target genuinely moves. -/
theorem double_forwardSim (C : CTS) :
    ForwardSim (ctsSys C) (ctsSys (double C)) (fun c d => d = dblCfg c) := by
  refine ForwardSim_of_fun (ctsSys C) (ctsSys (double C)) dblCfg ?_
  intro c c' hstep
  refine ⟨2, by omega, ?_⟩
  rw [ctsSys_nSteps, double_nSteps_two, ctsSys_step] at *
  rw [hstep]
  rfl

/-! ## The PDF example and non-degeneracy

The cyclic tag system of TM23Proof.pdf p. 18, `110 11 0 01 ""`, and its
double `111100 1111 "" 00 "" 0011 "" "" ""`. -/

/-- The cyclic tag system `110 11 0 01 ""` of TM23Proof.pdf p. 18. -/
def pdfCTS : CTS where
  appendants := [[true, true], [false], [false, true], []]
  nonempty := by decide

/-- Its initial configuration, working string `110`. -/
def pdfCfg : CTSConfig := { data := [true, true, false], phase := 0 }

/-- The doubled appendant list printed on TM23Proof.pdf p. 18. -/
theorem pdf_double_appendants :
    (double pdfCTS).appendants
      = [[true, true, true, true], [], [false, false], [],
         [false, false, true, true], [], [], []] := by
  decide

/-- The doubled working string printed on TM23Proof.pdf p. 18. -/
theorem pdf_double_data :
    (dblCfg pdfCfg).data = [true, true, true, true, false, false] := by
  decide

/-- Even steps agree on the PDF example: the first four steps of the
    original against the first eight steps of its double. -/
theorem pdf_double_steps_agree :
    ((double pdfCTS).nSteps (dblCfg pdfCfg) 0
        = Option.map dblCfg (pdfCTS.nSteps pdfCfg 0)) ∧
    ((double pdfCTS).nSteps (dblCfg pdfCfg) 2
        = Option.map dblCfg (pdfCTS.nSteps pdfCfg 1)) ∧
    ((double pdfCTS).nSteps (dblCfg pdfCfg) 4
        = Option.map dblCfg (pdfCTS.nSteps pdfCfg 2)) ∧
    ((double pdfCTS).nSteps (dblCfg pdfCfg) 6
        = Option.map dblCfg (pdfCTS.nSteps pdfCfg 3)) ∧
    ((double pdfCTS).nSteps (dblCfg pdfCfg) 8
        = Option.map dblCfg (pdfCTS.nSteps pdfCfg 4)) := by
  decide

/-- Non-degeneracy, negative: the correspondence really needs two doubled
    steps per original step; after a single doubled step the two sides
    differ. -/
theorem pdf_double_odd_step_differs :
    (double pdfCTS).nSteps (dblCfg pdfCfg) 1
      ≠ Option.map dblCfg (pdfCTS.nSteps pdfCfg 1) := by
  decide

/-- Non-degeneracy, negative: not every word is a doubled word, so `dblCfg`
    is not surjective and the relation of `double_forwardSim` is proper. -/
theorem dbl_ne_true_false (w : List Bool) : dbl w ≠ [true, false] := by
  cases w with
  | nil => simp
  | cons b rest =>
    intro h
    rw [dbl_cons] at h
    injection h with h1 h2
    injection h2 with h3 _
    rw [h1] at h3
    exact absurd h3 (by simp)

end Smith
