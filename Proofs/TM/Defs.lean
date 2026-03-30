/-
  TM.Defs

  Shared definitions for Turing machine formalizations.
  Used by both OneSidedTM (semi-infinite tape) and BiTM (bi-infinite tape).

  Conventions:
  - States are Nat: 0 = halt state, 1..s = active states
  - Symbols are Nat: 0 = blank
  - Direction: L = left, R = right
-/

namespace TM

/-- Direction of head movement -/
inductive Dir where
  | L  -- left
  | R  -- right
  deriving Repr, DecidableEq, BEq

/-- A transition rule: (nextState, writeSymbol, direction) -/
structure Rule where
  nextState : Nat
  write     : Nat
  dir       : Dir
  deriving Repr, DecidableEq, BEq

/-- A deterministic Turing machine.
    The transition function maps (state, readSymbol) → Rule.
    States are 0..numStates-1, symbols are 0..numSymbols-1.
    State 0 is the halt state. -/
structure Machine where
  numStates  : Nat
  numSymbols : Nat
  transition : Nat → Nat → Rule

/-- Decode a Wolfram-style TM rule number into a transition function.
    Rule number encodes all transitions as a base-(2·s·k) number. -/
def decodeRule (s k : Nat) (ruleNum : Nat) : Machine where
  numStates := s
  numSymbols := k
  transition := fun state sym =>
    let idx := state * k + sym
    let totalActions := 2 * s * k
    if totalActions == 0 then { nextState := 0, write := 0, dir := Dir.R }
    else
      let action := (ruleNum / (totalActions ^ idx)) % totalActions
      let d := if action % 2 == 0 then Dir.R else Dir.L
      let rest := action / 2
      { nextState := rest / k, write := rest % k, dir := d }

end TM
