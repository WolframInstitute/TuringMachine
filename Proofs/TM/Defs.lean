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
    The transition function maps (state, readSymbol) -> Rule.
    States are 0..numStates-1, symbols are 0..numSymbols-1.
    State 0 is the halt state. -/
structure Machine where
  numStates  : Nat
  numSymbols : Nat
  transition : Nat → Nat → Rule

end TM
