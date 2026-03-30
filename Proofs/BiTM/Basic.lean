/-
  BiTM.Basic

  Formalization of bi-infinite tape Turing machines.
  Uses shared definitions from TM.Defs.

  Key differences from OneSidedTM:
  - Tape is bi-infinite: represented as (left, head, right) where
    left and right are infinite in both directions
  - No boundary-based halting: halts when state = 0
  - Suitable for standard TMs like Wolfram's (2,3) UTM
-/

import TM.Defs

namespace BiTM

open TM

-- ============================================================================
-- Bi-infinite Tape TM
-- ============================================================================

/-- Configuration of a bi-infinite tape TM.
    left:  cells to the left of head (closest first), implicitly 0 beyond
    head:  current cell symbol
    right: cells to the right of head (closest first), implicitly 0 beyond
    State 0 = halted. -/
structure Config where
  state : Nat
  left  : List Nat
  head  : Nat
  right : List Nat
  deriving DecidableEq, BEq, Repr

/-- A TM has halted when it reaches state 0 -/
def halted (cfg : Config) : Bool :=
  cfg.state == 0

/-- Read from a list, returning 0 (blank) if beyond bounds -/
def readHead (l : List Nat) : Nat × List Nat :=
  match l with
  | [] => (0, [])
  | x :: xs => (x, xs)

/-- Single step of a bi-infinite tape TM.
    Returns none if already halted. -/
def step (tm : Machine) (cfg : Config) : Option Config :=
  if cfg.state == 0 then none
  else
    let r := tm.transition cfg.state cfg.head
    match r.dir with
    | Dir.L =>
      let (newHead, newLeft) := readHead cfg.left
      some { state := r.nextState,
             left  := newLeft,
             head  := newHead,
             right := r.write :: cfg.right }
    | Dir.R =>
      let (newHead, newRight) := readHead cfg.right
      some { state := r.nextState,
             left  := r.write :: cfg.left,
             head  := newHead,
             right := newRight }

/-- Run with fuel. Returns some if halted, none if fuel exhausted. -/
def eval (tm : Machine) (cfg : Config) : Nat → Option Config
  | 0 => if halted cfg then some cfg else none
  | fuel + 1 =>
    if halted cfg then some cfg
    else match step tm cfg with
    | none => some cfg
    | some cfg' => eval tm cfg' fuel

/-- Predicate: TM halts on given configuration -/
def Halts (tm : Machine) (cfg : Config) : Prop :=
  ∃ fuel result, eval tm cfg fuel = some result

/-- Run for exactly n steps without checking halting. Returns none if
    the machine halts before n steps. -/
def nSteps (tm : Machine) (cfg : Config) : Nat → Option Config
  | 0 => some cfg
  | n + 1 =>
    match step tm cfg with
    | none => none
    | some cfg' => nSteps tm cfg' n

/-- Extract tape contents as a list centered on the head position.
    Returns (left_reversed, head, right). -/
def tapeContents (cfg : Config) : List Nat × Nat × List Nat :=
  (cfg.left.reverse, cfg.head, cfg.right)

-- ============================================================================
-- Wolfram's (2,3) Universal Turing Machine
-- ============================================================================

/-- Wolfram's 2-state 3-symbol Turing machine (machine 596440).
    The smallest known candidate universal TM.
    Proven universal by Alex Smith (2007).

    States: 1 = A, 2 = B (0 = halt, never reached by this machine)
    Symbols: 0, 1, 2

    Transition table:
    ┌────────┬─────────┬─────────┬─────────┐
    │        │  sym 0  │  sym 1  │  sym 2  │
    ├────────┼─────────┼─────────┼─────────┤
    │ A (1)  │ 1,R,B   │ 2,L,A   │ 1,L,A   │
    │ B (2)  │ 2,L,A   │ 2,R,B   │ 0,R,A   │
    └────────┴─────────┴─────────┴─────────┘ -/
def wolfram23 : Machine where
  numStates := 3   -- 0=halt, 1=A, 2=B
  numSymbols := 3  -- 0, 1, 2
  transition := fun state sym =>
    match state, sym with
    | 1, 0 => { nextState := 2, write := 1, dir := Dir.R }  -- A,0 → 1,R,B
    | 1, 1 => { nextState := 1, write := 2, dir := Dir.L }  -- A,1 → 2,L,A
    | 1, 2 => { nextState := 1, write := 1, dir := Dir.L }  -- A,2 → 1,L,A
    | 2, 0 => { nextState := 1, write := 2, dir := Dir.L }  -- B,0 → 2,L,A
    | 2, 1 => { nextState := 2, write := 2, dir := Dir.R }  -- B,1 → 2,R,B
    | 2, 2 => { nextState := 1, write := 0, dir := Dir.R }  -- B,2 → 0,R,A
    | _, _ => { nextState := 0, write := 0, dir := Dir.R }  -- unused/halt

/-- Initial configuration: state A, blank tape -/
def wolfram23_init : Config :=
  { state := 1, left := [], head := 0, right := [] }

-- ============================================================================
-- Evolution verification
-- ============================================================================

-- Step 1: A reads 0 → write 1, move R, go to B
theorem wolfram23_step1 :
    step wolfram23 wolfram23_init =
    some { state := 2, left := [1], head := 0, right := [] } := by
  native_decide

-- Step 2: B reads 0 → write 2, move L, go to A
theorem wolfram23_step2 :
    nSteps wolfram23 wolfram23_init 2 =
    some { state := 1, left := [], head := 1, right := [2] } := by
  native_decide

-- After 10 steps: verify the machine is still running (never halts)
theorem wolfram23_runs_10 :
    eval wolfram23 wolfram23_init 10 = none := by
  native_decide

-- After 20 steps: still running
theorem wolfram23_runs_20 :
    eval wolfram23 wolfram23_init 20 = none := by
  native_decide

end BiTM
