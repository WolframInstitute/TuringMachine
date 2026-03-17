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

  Shared definitions (Dir, Rule, Machine) are imported from TM.Defs.
-/

import TM.Defs

namespace OneSidedTM

-- Open TM namespace to use shared Dir, Rule, Machine types directly
open TM

/-- A deterministic TM (alias for TM.Machine for backward compatibility) -/
abbrev TM := Machine

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
  let tr := tm.transition cfg.state sym
  let newTape := writeTape cfg.tape cfg.head tr.write
  let newState := tr.nextState
  match tr.dir with
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
-- Tape manipulation lemmas
-- ============================================================================

@[simp] theorem readTape_nil (pos : Nat) : readTape [] pos = 0 := rfl

@[simp] theorem readTape_cons_zero (d : Nat) (rest : List Nat) :
    readTape (d :: rest) 0 = d := rfl

@[simp] theorem readTape_cons_succ (d : Nat) (rest : List Nat) (i : Nat) :
    readTape (d :: rest) (i + 1) = readTape rest i := rfl

@[simp] theorem writeTape_cons_zero (d : Nat) (rest : List Nat) (v : Nat) :
    writeTape (d :: rest) 0 v = v :: rest := by
  simp [writeTape, List.set]

@[simp] theorem writeTape_cons_succ (d : Nat) (rest : List Nat) (i : Nat) (v : Nat) :
    writeTape (d :: rest) (i + 1) v = d :: writeTape rest i v := by
  unfold writeTape
  simp only [List.length_cons, Nat.add_lt_add_iff_right]
  split <;> simp [List.set] <;> (try (congr; omega))

theorem rt_beyond (tape : List Nat) (pos : Nat) (h : pos ≥ tape.length) :
    readTape tape pos = 0 := by
  induction tape generalizing pos with
  | nil => simp [readTape, List.getD]
  | cons d rest ih =>
    cases pos with
    | zero => simp at h
    | succ p => simp [readTape_cons_succ]; exact ih p (by simp at h; omega)

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
-- Eval determinism: the halted configuration is unique
-- ============================================================================

/-- Decode a {2,2} TM rule number into its transition function. -/
def fromRuleNumber (ruleNum : Nat) : TM :=
  let d0 := (ruleNum / 512) % 8  -- (state 1, sym 1)
  let d1 := (ruleNum / 64) % 8   -- (state 1, sym 0)
  let d2 := (ruleNum / 8) % 8    -- (state 2, sym 1)
  let d3 := ruleNum % 8           -- (state 2, sym 0)
  let decode (d : Nat) : Rule :=
    { nextState := d / 4 % 2 + 1
    , write := (d / 2) % 2
    , dir := if d % 2 == 1 then Dir.R else Dir.L }
  { numStates := 2
  , numSymbols := 2
  , transition := fun state sym =>
      match state, sym with
      | 1, 0 => decode d1
      | 1, 1 => decode d0
      | 2, 0 => decode d3
      | 2, 1 => decode d2
      | _, _ => { nextState := 1, write := 0, dir := Dir.R }
  }

/-- Decode a {3,2} TM rule number into its transition function. -/
def fromRuleNumber32 (ruleNum : Nat) : TM :=
  let d0 := (ruleNum / 248832) % 12 -- (state 1, sym 1)
  let d1 := (ruleNum / 20736) % 12  -- (state 1, sym 0)
  let d2 := (ruleNum / 1728) % 12   -- (state 2, sym 1)
  let d3 := (ruleNum / 144) % 12    -- (state 2, sym 0)
  let d4 := (ruleNum / 12) % 12     -- (state 3, sym 1)
  let d5 := ruleNum % 12            -- (state 3, sym 0)
  let decode (d : Nat) : Rule :=
    { nextState := d / 4 + 1
    , write := (d / 2) % 2
    , dir := if d % 2 == 1 then Dir.R else Dir.L }
  { numStates := 3
  , numSymbols := 2
  , transition := fun state sym =>
      match state, sym with
      | 1, 1 => decode d0
      | 1, 0 => decode d1
      | 2, 1 => decode d2
      | 2, 0 => decode d3
      | 3, 1 => decode d4
      | 3, 0 => decode d5
      | _, _ => { nextState := 1, write := 0, dir := Dir.L }
  }

theorem rep_snoc (n : Nat) (v : Nat) :
    List.replicate n v ++ [v] = List.replicate (n + 1) v := by
  induction n with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, List.cons_append, ih]

theorem wt_split (n : Nat) (d : Nat) (suf : List Nat) (v : Nat) :
    writeTape (List.replicate n 0 ++ d :: suf) n v = List.replicate n 0 ++ v :: suf := by
  induction n with
  | zero => simp [writeTape, List.set]
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [show (0 :: List.replicate m 0) ++ d :: suf =
      0 :: (List.replicate m 0 ++ d :: suf) from by simp, writeTape_cons_succ]
    rw [ih]; simp [List.replicate_succ]

theorem rt_split (n : Nat) (d : Nat) (suf : List Nat) :
    readTape (List.replicate n 0 ++ d :: suf) n = d := by
  induction n with
  | zero => simp [readTape, List.getD]
  | succ m ih =>
    rw [List.replicate_succ]
    simp only [show (0 :: List.replicate m 0) ++ d :: suf =
      0 :: (List.replicate m 0 ++ d :: suf) from by simp, readTape_cons_succ]
    exact ih

theorem wt_rep_extend (n : Nat) (v : Nat) :
    writeTape (List.replicate n 0) n v = List.replicate n 0 ++ [v] := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ]
    rw [writeTape_cons_succ, ih]
    rfl

theorem rt_zeros (n : Nat) (suf : List Nat) (i : Nat) (hi : i < n) :
    readTape (List.replicate n 0 ++ suf) i = 0 := by
  induction n generalizing i with
  | zero => contradiction
  | succ m ih =>
    cases i with
    | zero => rfl
    | succ j =>
      rw [List.replicate_succ]
      simp only [show (0 :: List.replicate m 0) ++ suf = 0 :: (List.replicate m 0 ++ suf) by rfl, readTape_cons_succ]
      apply ih j; omega

-- ============================================================================
-- Tape identities and utility lemmas
-- ============================================================================

theorem read_write_self (tape : List Nat) (i v : Nat) :
    readTape (writeTape tape i v) i = v := by
  induction tape generalizing i with
  | nil =>
    unfold writeTape; simp; induction i with
    | zero => simp [readTape, List.getD]
    | succ j ih => simp [List.replicate_succ, readTape_cons_succ, ih]
  | cons d rest ih =>
    cases i with
    | zero => simp [writeTape_cons_zero, readTape_cons_zero]
    | succ i' => simp [writeTape_cons_succ, readTape_cons_succ, ih]

theorem read_write_other (tape : List Nat) (i j v : Nat) (h : i ≠ j) :
    readTape (writeTape tape i v) j = readTape tape j := by
  induction tape generalizing i j with
  | nil =>
    unfold writeTape; simp
    induction i generalizing j with
    | zero => 
      cases j with
      | zero => contradiction
      | succ j' => simp [readTape, List.getD]
    | succ i' ih =>
      cases j with
      | zero => simp [List.replicate_succ, readTape_cons_zero, readTape_nil]
      | succ j' => 
        simp [List.replicate_succ, readTape_cons_succ]
        by_cases he : i' = j'
        · subst he; exact absurd rfl h
        · exact ih j' he
  | cons d rest ih =>
    cases i with
    | zero =>
      cases j with
      | zero => contradiction
      | succ j' => simp [writeTape_cons_zero, readTape_cons_succ]
    | succ i' =>
      cases j with
      | zero => simp [writeTape_cons_succ, readTape_cons_zero]
      | succ j' => 
        simp [writeTape_cons_succ, readTape_cons_succ]
        exact ih i' j' (by omega)

theorem write_write_eq (tape : List Nat) (i v1 v2 : Nat) :
    writeTape (writeTape tape i v1) i v2 = writeTape tape i v2 := by
  induction tape generalizing i with
  | nil =>
    simp [writeTape, List.set]
    repeat (split <;> try simp [List.set])
  | cons d rest ih =>
    cases i with
    | zero => simp [writeTape_cons_zero]
    | succ i' => simp [writeTape_cons_succ, ih]

theorem writeTape_length (tape : List Nat) (i v : Nat) :
    (writeTape tape i v).length = max tape.length (i + 1) := by
  unfold writeTape; split
  · simp; omega
  · simp; omega

theorem writeTape_read_id (tape : List Nat) (pos : Nat) (h : pos < tape.length) :
    writeTape tape pos (readTape tape pos) = tape := by
  induction tape generalizing pos with
  | nil => simp at h
  | cons d rest ih =>
    cases pos with
    | zero => simp [writeTape_cons_zero, readTape_cons_zero, List.set]
    | succ p => 
      simp [writeTape_cons_succ, readTape_cons_succ]
      congr 1; exact ih p (by simp at h; omega)

theorem writeTape_val_eq_id (tape : List Nat) (pos v : Nat)
    (hlen : pos < tape.length) (hval : readTape tape pos = v) :
    writeTape tape pos v = tape := by
  rw [← hval]; exact writeTape_read_id tape pos hlen

/-- If eval halts with fuel, it halts with the same result with more fuel -/
theorem eval_mono (tm : TM) (cfg : Config) (fuel k : Nat) (cfg' : Config) :
    eval tm cfg fuel = some cfg' → eval tm cfg (fuel + k) = some cfg' := by
  induction fuel generalizing cfg with
  | zero => simp [eval]
  | succ n ih =>
    intro h
    cases hstep : step tm cfg with
    | halted c =>
      simp [eval, hstep] at h
      subst h
      show eval tm cfg (n + 1 + k) = some c
      rw [show n + 1 + k = (n + k) + 1 from by omega]
      simp [eval, hstep]
    | «continue» c =>
      simp [eval, hstep] at h
      show eval tm cfg (n + 1 + k) = some cfg'
      rw [show n + 1 + k = (n + k) + 1 from by omega]
      simp [eval, hstep]
      exact ih c h

/-- Eval is deterministic: if it halts at two different fuel values,
    the result is the same -/
theorem eval_det (tm : TM) (cfg : Config) (fuel1 fuel2 : Nat) (cfg1 cfg2 : Config) :
    eval tm cfg fuel1 = some cfg1 → eval tm cfg fuel2 = some cfg2 → cfg1 = cfg2 := by
  intro h1 h2
  have hm1 := eval_mono tm cfg fuel1 fuel2 cfg1 h1
  have hm2 := eval_mono tm cfg fuel2 fuel1 cfg2 h2
  rw [Nat.add_comm] at hm2
  simp [hm1] at hm2
  exact hm2
-- ============================================================================
-- Decidable evaluation (for computational verification)
-- ============================================================================

/-- Decidable check: does TM produce output v on input n within fuel steps? -/
def checkRun (tm : TM) (n : Nat) (fuel : Nat) (expected : Nat) : Bool :=
  match run tm n fuel with
  | some v => v == expected
  | none => false

end OneSidedTM
