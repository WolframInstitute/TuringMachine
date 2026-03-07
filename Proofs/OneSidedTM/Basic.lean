/-
  OneSidedTM.Basic

  Formalization of one-sided (semi-infinite tape) deterministic Turing machines,
  matching the semantics of the TuringMachineSearch Wolfram/Rust paclet.

  Conventions (matching models.rs):
  - Tape: List of Nat digits, LSB at index 0, implicitly 0-padded beyond the list
  - Head starts at position 0 (the LSB end of the input)
  - States are 1-indexed: {1, ..., s}. State 0 is unused.
  - Direction: Left = toward MSB (position + 1), Right = toward LSB (position - 1)
  - Halting: machine halts when head at position 0 tries to move Right
  - Output: tape contents read as a base-k integer after halting
-/

namespace OneSidedTM

/-- Direction of head movement -/
inductive Dir where
  | L  -- Left: toward MSB (position + 1)
  | R  -- Right: toward LSB (position - 1)
  deriving Repr, DecidableEq, BEq

/-- A transition rule: (nextState, writeSymbol, direction) -/
structure Rule where
  nextState : Nat
  write     : Nat
  dir       : Dir
  deriving Repr, DecidableEq, BEq

/-- A deterministic TM.
    The transition function maps (state, readSymbol) → Rule.
    States are 1..s, symbols are 0..k-1. -/
structure TM where
  numStates  : Nat
  numSymbols : Nat
  transition : Nat → Nat → Rule

/-- Configuration of a running TM -/
structure Config where
  state : Nat        -- current state (1-indexed)
  head  : Nat        -- head position on tape (0 = LSB)
  tape  : List Nat   -- tape contents, LSB first
  deriving Repr, DecidableEq, BEq

/-- Read the symbol at a given position on the tape (0 beyond bounds) -/
def readTape (tape : List Nat) (pos : Nat) : Nat :=
  tape.getD pos 0

/-- Write a symbol at a given position, extending tape with 0s if needed -/
def writeTape (tape : List Nat) (pos : Nat) (val : Nat) : List Nat :=
  if pos < tape.length then
    tape.set pos val
  else
    -- Extend tape with zeros up to pos, then write val
    tape ++ List.replicate (pos - tape.length) 0 ++ [val]

/-- Result of a single step: either a new Config or Halted with final Config -/
inductive StepResult where
  | continue : Config → StepResult
  | halted   : Config → StepResult
  deriving Repr

/-- Execute one step of the TM.
    Halting: when the head is at position 0 and the rule says move Right,
    the machine halts (would move to position -1, which is off the tape). -/
def step (tm : TM) (cfg : Config) : StepResult :=
  let sym := readTape cfg.tape cfg.head
  let rule := tm.transition cfg.state sym
  let newTape := writeTape cfg.tape cfg.head rule.write
  let newState := rule.nextState
  match rule.dir with
  | Dir.R =>
    -- Moving right (toward LSB). If head is at 0, halt.
    if cfg.head == 0 then
      StepResult.halted { state := newState, head := 0, tape := newTape }
    else
      StepResult.continue { state := newState, head := cfg.head - 1, tape := newTape }
  | Dir.L =>
    -- Moving left (toward MSB). Head position increases.
    StepResult.continue { state := newState, head := cfg.head + 1, tape := newTape }

/-- Run the TM for up to `fuel` steps. Returns `some cfg` if halted, `none` if fuel exhausted. -/
def eval (tm : TM) (cfg : Config) : Nat → Option Config
  | 0 => none
  | fuel + 1 =>
    match step tm cfg with
    | StepResult.halted cfg' => some cfg'
    | StepResult.continue cfg' => eval tm cfg' fuel

/-- Convert a natural number to its binary digit list (LSB first).
    0 → [0], 1 → [1], 2 → [0, 1], 3 → [1, 1], 4 → [0, 0, 1], etc. -/
def toBinary : Nat → List Nat
  | 0 => [0]
  | n + 1 => toBinaryPos (n + 1)
where
  toBinaryPos : Nat → List Nat
    | 0 => []
    | n + 1 =>
      let m := n + 1
      (m % 2) :: toBinaryPos (m / 2)
  termination_by n => n

/-- Convert a binary digit list (LSB first) to a natural number -/
def fromBinary : List Nat → Nat
  | [] => 0
  | d :: rest => d + 2 * fromBinary rest

/-- Trim trailing zeros from a digit list (normalize representation).
    We keep at least one digit. -/
def trimTrailingZeros : List Nat → List Nat
  | [] => [0]
  | l =>
    let r := l.reverse.dropWhile (· == 0)
    if r.isEmpty then [0] else r.reverse

/-- Create the initial configuration for running a TM on input n.
    Head starts at position 0 (LSB), state 1. -/
def initConfig (n : Nat) : Config :=
  let tape := toBinary n
  { state := 1, head := 0, tape := tape }

/-- Extract the output value from a halted configuration -/
def outputValue (cfg : Config) : Nat :=
  fromBinary (trimTrailingZeros cfg.tape)

/-- Run a TM on input n for up to `fuel` steps and return the output value -/
def run (tm : TM) (n : Nat) (fuel : Nat) : Option Nat :=
  (eval tm (initConfig n) fuel).map outputValue

/-- A TM computes the successor function: for every n ≥ 1,
    there exists sufficient fuel such that running the TM on n yields n + 1 -/
def ComputesSucc (tm : TM) : Prop :=
  ∀ n : Nat, n ≥ 1 → ∃ fuel : Nat, run tm n fuel = some (n + 1)

-- ============================================================================
-- Basic lemmas about fromBinary / toBinary
-- ============================================================================

@[simp] theorem fromBinary_nil : fromBinary [] = 0 := rfl
@[simp] theorem fromBinary_cons (d : Nat) (rest : List Nat) :
    fromBinary (d :: rest) = d + 2 * fromBinary rest := rfl

theorem fromBinary_toBinaryPos (n : Nat) (hn : n > 0) :
    fromBinary (toBinary.toBinaryPos n) = n := by
  match n with
  | 0 => omega
  | n + 1 =>
    unfold toBinary.toBinaryPos
    simp [fromBinary]
    have h_div : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by omega)
    by_cases h0 : (n + 1) / 2 = 0
    · simp [h0, toBinary.toBinaryPos, fromBinary]
      omega
    · have := fromBinary_toBinaryPos ((n + 1) / 2) (by omega)
      rw [this]
      omega

theorem fromBinary_toBinary (n : Nat) : fromBinary (toBinary n) = n := by
  unfold toBinary
  split
  · simp [fromBinary]
  · exact fromBinary_toBinaryPos _ (by omega)

-- ============================================================================
-- Decidable evaluation (for computational verification)
-- ============================================================================

/-- Decidable check: does TM produce output v on input n within fuel steps? -/
def checkRun (tm : TM) (n : Nat) (fuel : Nat) (expected : Nat) : Bool :=
  match run tm n fuel with
  | some v => v == expected
  | none => false

end OneSidedTM
