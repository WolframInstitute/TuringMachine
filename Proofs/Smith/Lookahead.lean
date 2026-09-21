/-
  Smith.Lookahead

  The machine type of Smith's Systems 0 to 3 (TM23Proof.pdf p. 3-5 and the
  interpreter `sys0-3.pl`, p. 45): a Turing-machine-like system whose
  rules read the active cell and, for some (state, symbol) pairs, its right
  neighbour as well, rewrite the cells they read, and move the head by one.
  System 0 is Wolfram's (2,3) machine; Systems 1, 2, 3 are its relabelings
  with the lookahead rules `B20`, `B21`, `B22` (and a third state C).

  A configuration is a finite zipper, like `BiTM.Config`: the cells to the
  left of the head nearest first, the head cell, the cells to the right
  nearest first, and the state.  The tape is finite and is never extended:
  a move off either end is `none`, and so is a two-cell rule with no right
  neighbour.  In the chain the exit of System 3 ("the first cell to become
  active after the emulation has finished is the cell to the right of the
  initial condition") is observed as the two-cell rule `C 1` at the right
  end of the tape, where `lstep` returns `none` (`rep3_exit` in
  `Smith/Conjecture0.lean`); relabeled to System 0 it is the one-cell rule
  `B 2` at the last cell, which `wolfram23` executes onto the blank right of
  the tape (`toBi_exit` in `Smith/Wolfram23Bridge.lean`,
  `wolfram23_exit_step` in `Smith/Conjecture0.lean`).  `exitRight` records
  the state in which a one-cell rule leaves the tape to the right; it is
  used only by the p. 47 check below.

  Contents:
    * `LState`, `LRule`, `LMachine`, `LConfig`, `lstep`, `lnSteps`,
      `exitRight`, `toList`.
    * `sys0`, `sys1`, `sys2`, `sys3`: the rule tables of p. 45.
    * `decide` checks: one-cell rules ignore the neighbour, and the
      `sys0-3.pl 0 N 00A00000` trace of p. 47 with its exit.
-/

import Smith.Simulation
import TM.Defs
import Mathlib.Tactic.DeriveFintype

namespace Smith

open TM

/-- The states A, B, C of Systems 0 to 3. -/
inductive LState : Type
  | A : LState
  | B : LState
  | C : LState
  deriving DecidableEq, Repr, Fintype

/-- A rule: rewrite the active cell (`one`) or the active cell and its
    right neighbour (`two`), change state, move by one. -/
inductive LRule : Type
  | one (st : LState) (a : Fin 3) (d : Dir) : LRule
  | two (st : LState) (a b : Fin 3) (d : Dir) : LRule
  deriving DecidableEq, Repr

/-- A lookahead machine: the rule for a state, the active symbol and the
    right neighbour (`0` when there is none). -/
structure LMachine where
  trans : LState → Fin 3 → Fin 3 → LRule

/-- A configuration: cells left of the head nearest first, the head cell,
    cells right of the head nearest first, and the state. -/
structure LConfig where
  left : List (Fin 3)
  head : Fin 3
  right : List (Fin 3)
  state : LState
  deriving DecidableEq, Repr

/-- The tape as a list, left to right. -/
def LConfig.toList (c : LConfig) : List (Fin 3) := c.left.reverse ++ c.head :: c.right

/-- The index of the head on `toList`. -/
def LConfig.pos (c : LConfig) : Nat := c.left.length

/-- One step. -/
def lstep (M : LMachine) (c : LConfig) : Option LConfig :=
  match c.right with
  | [] =>
    match M.trans c.state c.head 0 with
    | LRule.one _ _ Dir.R => none
    | LRule.one st' a' Dir.L =>
        match c.left with
        | [] => none
        | x :: L' => some ⟨L', x, [a'], st'⟩
    | LRule.two _ _ _ _ => none
  | b :: R' =>
    match M.trans c.state c.head b with
    | LRule.one st' a' Dir.R => some ⟨a' :: c.left, b, R', st'⟩
    | LRule.one st' a' Dir.L =>
        match c.left with
        | [] => none
        | x :: L' => some ⟨L', x, a' :: b :: R', st'⟩
    | LRule.two st' a' b' Dir.R => some ⟨a' :: c.left, b', R', st'⟩
    | LRule.two st' a' b' Dir.L =>
        match c.left with
        | [] => none
        | x :: L' => some ⟨L', x, a' :: b' :: R', st'⟩

/-- The exit to the right: from `c`, a one-cell rule moving right at the
    last cell leaves the tape in state `st'` after writing `a'`; the result
    is that state and the final tape.  `none` when `c` does not exit. -/
def exitRight (M : LMachine) (c : LConfig) : Option (LState × List (Fin 3)) :=
  match c.right with
  | [] =>
    match M.trans c.state c.head 0 with
    | LRule.one st' a' Dir.R => some (st', (a' :: c.left).reverse)
    | _ => none
  | _ :: _ => none

/-- A lookahead machine as a `StepSys`. -/
def lsys (M : LMachine) : StepSys LConfig := ⟨lstep M⟩

@[simp] theorem lsys_step (M : LMachine) (c : LConfig) : (lsys M).step c = lstep M c := rfl

/-- `n` steps. -/
def lnSteps (M : LMachine) (c : LConfig) (n : Nat) : Option LConfig := (lsys M).nSteps c n

@[simp] theorem lnSteps_zero (M : LMachine) (c : LConfig) : lnSteps M c 0 = some c := rfl

theorem lnSteps_succ (M : LMachine) (c : LConfig) (n : Nat) :
    lnSteps M c (n + 1) = (lstep M c).bind fun c' => lnSteps M c' n := by
  unfold lnSteps
  rw [StepSys.nSteps_succ_left, lsys_step]

@[simp] theorem lnSteps_one (M : LMachine) (c : LConfig) : lnSteps M c 1 = lstep M c := by
  unfold lnSteps
  rw [StepSys.nSteps_one, lsys_step]

theorem lnSteps_add (M : LMachine) (c : LConfig) (n m : Nat) :
    lnSteps M c (n + m) = (lnSteps M c n).bind fun c' => lnSteps M c' m := by
  unfold lnSteps
  exact StepSys.nSteps_add _ _ _ _

/-- A run that is over stays over. -/
theorem lnSteps_none_add (M : LMachine) (c : LConfig) (n m : Nat) (h : lnSteps M c n = none) :
    lnSteps M c (n + m) = none := by
  rw [lnSteps_add, h]
  rfl

/-- A step never changes the length of the tape. -/
theorem lstep_length (M : LMachine) (c c' : LConfig) (h : lstep M c = some c') :
    c'.toList.length = c.toList.length := by
  obtain ⟨L, a, R, st⟩ := c
  simp only [LConfig.toList, List.length_append, List.length_reverse, List.length_cons]
  cases R with
  | nil =>
    cases hr : M.trans st a 0 with
    | one st' a' d =>
      cases d <;> cases L <;> simp [lstep, hr] at h
      all_goals (subst h; simp)
    | two _ _ _ _ => simp [lstep, hr] at h
  | cons b R' =>
    cases hr : M.trans st a b with
    | one st' a' d =>
      cases d <;> cases L <;> simp [lstep, hr] at h
      all_goals (subst h; simp; omega)
    | two st' a' b' d =>
      cases d <;> cases L <;> simp [lstep, hr] at h
      all_goals (subst h; simp; omega)

/-! ## The rule tables of p. 45 -/

open LState LRule Dir in
/-- System 0, Wolfram's (2,3) machine:
    `A0 -> B1>, B0 -> A2<, A1 -> A2<, B1 -> B2>, A2 -> A1<, B2 -> A0>`. -/
def sys0 : LMachine where
  trans
    | A, 0, _ => one B 1 R
    | A, 1, _ => one A 2 L
    | A, 2, _ => one A 1 L
    | B, 0, _ => one A 2 L
    | B, 1, _ => one B 2 R
    | B, 2, _ => one A 0 R
    | C, _, _ => one C 0 R

open LState LRule Dir in
/-- System 1: System 0 with `B2` replaced by the lookahead rules
    `B20 -> A00>, B21 -> B12>, B22 -> B11>`. -/
def sys1 : LMachine where
  trans
    | A, 0, _ => one B 1 R
    | A, 1, _ => one A 2 L
    | A, 2, _ => one A 1 L
    | B, 0, _ => one A 2 L
    | B, 1, _ => one B 2 R
    | B, 2, 0 => two A 0 0 R
    | B, 2, 1 => two B 1 2 R
    | B, 2, 2 => two B 1 1 R
    | C, _, _ => one C 0 R

open LState LRule Dir in
/-- System 2. -/
def sys2 : LMachine where
  trans
    | A, 0, _ => one B 1 R
    | A, 1, _ => one A 2 L
    | A, 2, _ => one A 1 L
    | B, 0, _ => one A 2 L
    | B, 1, _ => one B 2 R
    | B, 2, 0 => two A 0 0 R
    | B, 2, 1 => two C 1 1 R
    | B, 2, 2 => two C 1 2 R
    | C, 0, _ => one A 2 L
    | C, 1, 0 => two A 0 0 R
    | C, 1, 1 => two C 1 1 R
    | C, 1, 2 => two C 1 2 R
    | C, 2, _ => one B 2 R

open LState LRule Dir in
/-- System 3. -/
def sys3 : LMachine where
  trans
    | A, 0, _ => one B 2 R
    | A, 1, _ => one A 1 L
    | A, 2, _ => one A 2 L
    | B, 0, _ => one A 2 L
    | B, 1, _ => one B 1 R
    | B, 2, 0 => two A 0 0 R
    | B, 2, 1 => two C 2 1 R
    | B, 2, 2 => two C 2 2 R
    | C, 0, _ => one A 2 L
    | C, 1, 0 => two A 0 0 R
    | C, 1, 1 => two C 2 1 R
    | C, 1, 2 => two C 2 2 R
    | C, 2, _ => one B 1 R

/-- `true` on a one-cell rule. -/
def LRule.isOne : LRule → Bool
  | LRule.one _ _ _ => true
  | LRule.two _ _ _ _ => false

/-- A `one` rule does not read the neighbour. -/
def LMachine.OneIgnoresNeighbour (M : LMachine) : Prop :=
  ∀ st a b b', (M.trans st a b).isOne = true → M.trans st a b' = M.trans st a b

theorem sys0_one : sys0.OneIgnoresNeighbour := by
  unfold LMachine.OneIgnoresNeighbour; decide

theorem sys1_one : sys1.OneIgnoresNeighbour := by
  unfold LMachine.OneIgnoresNeighbour; decide

theorem sys2_one : sys2.OneIgnoresNeighbour := by
  unfold LMachine.OneIgnoresNeighbour; decide

theorem sys3_one : sys3.OneIgnoresNeighbour := by
  unfold LMachine.OneIgnoresNeighbour; decide

/-! ## Checks against the PDF -/

/-- System 0 is Wolfram's table (p. 3, `Tests.SmithVectors` D6): the same
    six rules as `BiTM.wolfram23`, state `A = 1`, `B = 2`. -/
example : sys0.trans LState.A 0 0 = LRule.one LState.B 1 Dir.R := by decide
example : sys0.trans LState.B 2 0 = LRule.one LState.A 0 Dir.R := by decide

/-- The tapes of the `sys0-3.pl 0 N 00A00000` trace, p. 47. -/
def traceP47 : List (List (Fin 3)) :=
  [[0,0,0,0,0,0,0], [0,0,1,0,0,0,0], [0,0,1,2,0,0,0], [0,0,2,2,0,0,0], [0,1,2,2,0,0,0],
   [0,1,0,2,0,0,0], [0,1,0,1,0,0,0], [0,1,1,1,0,0,0], [0,1,1,2,0,0,0], [0,1,1,2,2,0,0],
   [0,1,1,1,2,0,0], [0,1,2,1,2,0,0], [0,2,2,1,2,0,0], [1,2,2,1,2,0,0], [1,0,2,1,2,0,0],
   [1,0,1,1,2,0,0], [1,1,1,1,2,0,0], [1,1,2,1,2,0,0], [1,1,2,2,2,0,0], [1,1,2,2,0,0,0],
   [1,1,2,2,0,1,0], [1,1,2,2,0,1,2], [1,1,2,2,0,2,2], [1,1,2,2,1,2,2], [1,1,2,2,1,0,2],
   [1,1,2,2,1,0,1], [1,1,2,2,1,1,1], [1,1,2,2,1,1,2]]

/-- The tapes of the first `n + 1` configurations of a run. -/
def tapes (M : LMachine) (c : LConfig) : Nat → List (List (Fin 3))
  | 0 => [c.toList]
  | n + 1 =>
    match lstep M c with
    | none => [c.toList]
    | some c' => c.toList :: tapes M c' n

/-- The initial configuration of the p. 47 run, `00A00000`. -/
def cfgP47 : LConfig := ⟨[0, 0], 0, [0, 0, 0, 0], LState.A⟩

/-- The 27 tapes with the head on the tape, then the exit: the 28th line of
    the trace is the tape after the last write, with the head past its end
    in state B. -/
example : tapes sys0 cfgP47 27 = traceP47.take 27 := by decide

example : (lnSteps sys0 cfgP47 26).bind (exitRight sys0)
    = some (LState.B, [1, 1, 2, 2, 1, 1, 2]) := by decide

example : traceP47[27]? = some [1, 1, 2, 2, 1, 1, 2] := by decide

/-- The leftmost visit of the p. 47 run: cell 0 in state A after 12 steps
    (the `0221200 / A` line). -/
example : lnSteps sys0 cfgP47 12 = some ⟨[], 0, [2, 2, 1, 2, 0, 0], LState.A⟩ := by decide

/-- After 26 steps the head is on the last cell in state B (`1122111 / B`),
    and the next step leaves the tape. -/
example : lnSteps sys0 cfgP47 26 = some ⟨[1, 1, 2, 2, 1, 1], 1, [], LState.B⟩ := by decide

example : lnSteps sys0 cfgP47 27 = none := by decide

end Smith
