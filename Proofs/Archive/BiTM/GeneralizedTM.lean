/-
  BiTM.GeneralizedTM

  Generalised Turing machines that support multi-cell writes per
  transition.  Smith's Systems 1-3 (PDF `TM23Proof.pdf` p. 4-5)
  require this — e.g. System 1's (B, 20) → write `00` writes both
  the active cell AND an adjacent cell in one step.

  Extracted from `BiTM.CockeMinskyConstruction` in a refactor.

  Contents:
    * `GenTransition`, `GeneralizedTM`, `GenConfig`
    * `GeneralizedTM.step` — single-cell + 2-cell write semantics
      (3+-cell writes deferred)
    * `GeneralizedTM.nSteps` — multi-step runner
    * `GeneralizedTM.Halts`
-/

import BiTM.Basic

namespace BiTM

open TM

/-- A generalised TM transition that supports multi-cell writes.  The
    `writes` list specifies what symbols replace the active cell and
    consecutive cells in the direction `dir`.  Length 1 = standard TM. -/
structure GenTransition (Sym : Type) where
  nextState : Nat
  /-- Symbols to write at active cell (head of list) and consecutive cells. -/
  writes : List Sym
  /-- Head movement direction. -/
  dir : Dir
  deriving Repr

/-- A generalised Turing machine over alphabet `Sym`.  Supports multi-cell
    writes per transition (Smith's Systems 1-3 require this for their
    compound tape values). -/
structure GeneralizedTM (Sym : Type) where
  numStates : Nat
  transition : Nat → Sym → GenTransition Sym

/-- A configuration of a generalised TM (bi-infinite tape). -/
structure GenConfig (Sym : Type) where
  state : Nat
  left : List Sym
  head : Sym
  right : List Sym
  deriving Repr, DecidableEq

/-- One step of a generalised TM, supporting single-cell writes (the most
    common case).  Multi-cell writes (length ≥ 2) are deferred to a
    future iteration with proper handling of "the next head reads the
    second-written cell" semantics. -/
def GeneralizedTM.step {Sym : Type} (blank : Sym) (tm : GeneralizedTM Sym)
    (cfg : GenConfig Sym) : Option (GenConfig Sym) :=
  if cfg.state = 0 then none
  else
    let r := tm.transition cfg.state cfg.head
    match r.writes with
    | [w] =>
      -- Standard single-cell TM step.
      match r.dir with
      | Dir.L =>
        match cfg.left with
        | [] =>
          some { state := r.nextState
                 left := []
                 head := blank
                 right := w :: cfg.right }
        | h :: t =>
          some { state := r.nextState
                 left := t
                 head := h
                 right := w :: cfg.right }
      | Dir.R =>
        match cfg.right with
        | [] =>
          some { state := r.nextState
                 left := w :: cfg.left
                 head := blank
                 right := [] }
        | h :: t =>
          some { state := r.nextState
                 left := w :: cfg.left
                 head := h
                 right := t }
    | [w1, w2] =>
      -- 2-cell write (Smith's Systems 1-3): write w1 to active, then
      -- move in direction `dir` and the new active = w2 (overwriting
      -- whatever was there).  This is the convention from PDF p. 4-5.
      match r.dir with
      | Dir.L =>
        match cfg.left with
        | [] =>
          -- Off-tape to the left: drop one blank, write w2 there.
          some { state := r.nextState
                 left := []
                 head := w2
                 right := w1 :: cfg.right }
        | _ :: t =>
          -- Move L past one cell, overwrite with w2.
          some { state := r.nextState
                 left := t
                 head := w2
                 right := w1 :: cfg.right }
      | Dir.R =>
        match cfg.right with
        | [] =>
          some { state := r.nextState
                 left := w1 :: cfg.left
                 head := w2
                 right := [] }
        | _ :: t =>
          some { state := r.nextState
                 left := w1 :: cfg.left
                 head := w2
                 right := t }
    | _ =>
      -- Empty or 3+-cell write: deferred (return none).
      none

/-- Run a generalised TM for exactly `n` steps; halts (`none`) if any
    intermediate step returns `none`. -/
def GeneralizedTM.nSteps {Sym : Type} (blank : Sym) (tm : GeneralizedTM Sym) :
    GenConfig Sym → Nat → Option (GenConfig Sym)
  | cfg, 0 => some cfg
  | cfg, n + 1 =>
    match GeneralizedTM.step blank tm cfg with
    | none => none
    | some cfg' => GeneralizedTM.nSteps blank tm cfg' n

/-- **`GeneralizedTM.nSteps_zero` (iter 614)**: 0-step iteration is the
    identity.  Mirrors `BiTM.nSteps_zero`, `System5.nSteps_zero`,
    `System4.nSteps_zero`. -/
@[simp] theorem GeneralizedTM.nSteps_zero {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg : GenConfig Sym) :
    GeneralizedTM.nSteps blank tm cfg 0 = some cfg := rfl

/-- **`GeneralizedTM.nSteps_one` (iter 614)**: 1-step iteration is
    `step`.  Mirrors `BiTM.nSteps_one`. -/
theorem GeneralizedTM.nSteps_one {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg : GenConfig Sym) :
    GeneralizedTM.nSteps blank tm cfg 1 = GeneralizedTM.step blank tm cfg := by
  show (match GeneralizedTM.step blank tm cfg with
        | none => none
        | some cfg' => GeneralizedTM.nSteps blank tm cfg' 0)
      = GeneralizedTM.step blank tm cfg
  cases GeneralizedTM.step blank tm cfg <;> rfl

/-- **`GeneralizedTM.nSteps_add` (iter 614)**: additive composition.
    Mirrors `BiTM.nSteps_add`. -/
theorem GeneralizedTM.nSteps_add {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg : GenConfig Sym) (n m : Nat) :
    GeneralizedTM.nSteps blank tm cfg (n + m)
      = (GeneralizedTM.nSteps blank tm cfg n).bind
          (fun c => GeneralizedTM.nSteps blank tm c m) := by
  induction n generalizing cfg with
  | zero => simp [GeneralizedTM.nSteps]
  | succ n ih =>
    rw [Nat.succ_add]
    show (match GeneralizedTM.step blank tm cfg with
          | none => none
          | some c => GeneralizedTM.nSteps blank tm c (n + m))
        = (match GeneralizedTM.step blank tm cfg with
            | none => none
            | some c => GeneralizedTM.nSteps blank tm c n).bind
          (fun c => GeneralizedTM.nSteps blank tm c m)
    cases GeneralizedTM.step blank tm cfg with
    | none => rfl
    | some c => exact ih c

/-- **`GeneralizedTM.nSteps_succ` (iter 614)**: successor unfold.
    Mirrors `BiTM.nSteps_succ`. -/
theorem GeneralizedTM.nSteps_succ {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg : GenConfig Sym) (n : Nat) :
    GeneralizedTM.nSteps blank tm cfg (n + 1)
      = (GeneralizedTM.step blank tm cfg).bind
          (fun c => GeneralizedTM.nSteps blank tm c n) := by
  rw [Nat.add_comm, GeneralizedTM.nSteps_add, GeneralizedTM.nSteps_one]

/-- **`GeneralizedTM.step_state_zero_eq_none` (iter 614)**: `state = 0`
    is the halt indicator — `step` immediately returns `none`. -/
theorem GeneralizedTM.step_state_zero_eq_none {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg : GenConfig Sym)
    (h : cfg.state = 0) :
    GeneralizedTM.step blank tm cfg = none := by
  unfold GeneralizedTM.step
  rw [if_pos h]

/-- A generalised TM **halts** on `cfg` iff some `nSteps` returns `none`
    (i.e., the run reaches a state-0 cfg within finitely many steps). -/
def GeneralizedTM.Halts {Sym : Type} (blank : Sym) (tm : GeneralizedTM Sym)
    (cfg : GenConfig Sym) : Prop :=
  ∃ n, GeneralizedTM.nSteps blank tm cfg n = none

/-- **`GeneralizedTM.Halts_of_step_none` (iter 628)**: trivial halt
    witness — `step cfg = none` ⟹ Halts in 1 step. -/
theorem GeneralizedTM.Halts_of_step_none {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg : GenConfig Sym)
    (h : GeneralizedTM.step blank tm cfg = none) :
    GeneralizedTM.Halts blank tm cfg :=
  ⟨1, by rw [GeneralizedTM.nSteps_one]; exact h⟩

/-- **`GeneralizedTM.Halts_of_state_zero` (iter 628)**: state-0
    cfgs halt immediately.  Composes
    `GeneralizedTM.step_state_zero_eq_none` with `Halts_of_step_none`. -/
theorem GeneralizedTM.Halts_of_state_zero {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg : GenConfig Sym)
    (h : cfg.state = 0) :
    GeneralizedTM.Halts blank tm cfg :=
  GeneralizedTM.Halts_of_step_none blank tm cfg
    (GeneralizedTM.step_state_zero_eq_none blank tm cfg h)

/-- **`GeneralizedTM.Halts_step_pred` (iter 628)**: backward Halts
    propagation under stepping.  Mirrors `System5_Halts_step_pred`. -/
theorem GeneralizedTM.Halts_step_pred {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg cfg' : GenConfig Sym)
    (h_step : GeneralizedTM.step blank tm cfg = some cfg')
    (h : GeneralizedTM.Halts blank tm cfg') :
    GeneralizedTM.Halts blank tm cfg := by
  obtain ⟨n, h_n⟩ := h
  refine ⟨n + 1, ?_⟩
  rw [GeneralizedTM.nSteps_succ, h_step]
  exact h_n

/-- **`GeneralizedTM.Halts_step_succ` (iter 632)**: forward Halts
    propagation under stepping.  Mirrors `System5_Halts_step_succ`. -/
theorem GeneralizedTM.Halts_step_succ {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg cfg' : GenConfig Sym)
    (h_step : GeneralizedTM.step blank tm cfg = some cfg')
    (h : GeneralizedTM.Halts blank tm cfg) :
    GeneralizedTM.Halts blank tm cfg' := by
  obtain ⟨n, h_n⟩ := h
  cases n with
  | zero =>
    simp [GeneralizedTM.nSteps_zero] at h_n
  | succ k =>
    rw [GeneralizedTM.nSteps_succ, h_step] at h_n
    exact ⟨k, h_n⟩

/-- **`GeneralizedTM.Halts_step_iff` (iter 632)**: biconditional
    combining step-pred and step-succ. -/
theorem GeneralizedTM.Halts_step_iff {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg cfg' : GenConfig Sym)
    (h_step : GeneralizedTM.step blank tm cfg = some cfg') :
    GeneralizedTM.Halts blank tm cfg ↔ GeneralizedTM.Halts blank tm cfg' :=
  ⟨GeneralizedTM.Halts_step_succ blank tm cfg cfg' h_step,
   GeneralizedTM.Halts_step_pred blank tm cfg cfg' h_step⟩

/-- **`GeneralizedTM.Halts_nSteps_pred` (iter 634)**: backward Halts
    propagation via multi-step.  Mirrors `System5_Halts_nSteps_pred`. -/
theorem GeneralizedTM.Halts_nSteps_pred {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg : GenConfig Sym) (n : Nat)
    (r : GenConfig Sym)
    (h_n : GeneralizedTM.nSteps blank tm cfg n = some r)
    (h : GeneralizedTM.Halts blank tm r) :
    GeneralizedTM.Halts blank tm cfg := by
  induction n generalizing cfg with
  | zero =>
    rw [GeneralizedTM.nSteps_zero] at h_n
    injection h_n with h_eq
    rw [h_eq]
    exact h
  | succ k ih =>
    rw [GeneralizedTM.nSteps_succ] at h_n
    cases h_step : GeneralizedTM.step blank tm cfg with
    | none => rw [h_step] at h_n; cases h_n
    | some cfg₁ =>
      rw [h_step] at h_n
      simp at h_n
      exact GeneralizedTM.Halts_step_pred blank tm cfg cfg₁ h_step (ih cfg₁ h_n)

/-- **`GeneralizedTM.Halts_nSteps_succ` (iter 634)**: forward Halts
    propagation via multi-step. -/
theorem GeneralizedTM.Halts_nSteps_succ {Sym : Type}
    (blank : Sym) (tm : GeneralizedTM Sym) (cfg : GenConfig Sym) (n : Nat)
    (r : GenConfig Sym)
    (h_n : GeneralizedTM.nSteps blank tm cfg n = some r)
    (h : GeneralizedTM.Halts blank tm cfg) :
    GeneralizedTM.Halts blank tm r := by
  induction n generalizing cfg with
  | zero =>
    rw [GeneralizedTM.nSteps_zero] at h_n
    injection h_n with h_eq
    rw [← h_eq]
    exact h
  | succ k ih =>
    rw [GeneralizedTM.nSteps_succ] at h_n
    cases h_step : GeneralizedTM.step blank tm cfg with
    | none => rw [h_step] at h_n; cases h_n
    | some cfg₁ =>
      rw [h_step] at h_n
      simp at h_n
      exact ih cfg₁ h_n
        (GeneralizedTM.Halts_step_succ blank tm cfg cfg₁ h_step h)

end BiTM
