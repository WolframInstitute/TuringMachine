import OneSidedTM.Decide
import OneSidedTM.Basic
open OneSidedTM
open TM

def fromRuleNumber32 (ruleNum : Nat) : TM :=
  let d0 := (ruleNum / 248832) % 12
  let d1 := (ruleNum / 20736) % 12
  let d2 := (ruleNum / 1728) % 12
  let d3 := (ruleNum / 144) % 12
  let d4 := (ruleNum / 12) % 12
  let d5 := ruleNum % 12
  let decode (d : Nat) : Rule :=
    { nextState := d / 4 % 3 + 1, write := (d / 2) % 2, dir := if d % 2 == 1 then Dir.R else Dir.L }
  { numStates := 3, numSymbols := 2, transition := fun state sym =>
      match state, sym with
      | 1, 0 => decode d1 | 1, 1 => decode d0
      | 2, 0 => decode d3 | 2, 1 => decode d2
      | 3, 0 => decode d5 | 3, 1 => decode d4
      | _, _ => { nextState := 1, write := 0, dir := Dir.R } }

def trace (tm : TM) (n : Nat) : IO Unit := do
  let mut cfg : Config := initConfig n
  for i in [0:20] do
    IO.println s!"Step {i}: State {cfg.state}, Head {cfg.head}, Tape {cfg.tape}"
    match step tm cfg with
    | StepResult.continue next => cfg := next
    | StepResult.halted next =>
      IO.println s!"Halted: State {next.state}, Head {next.head}, Tape {next.tape}"
      break

def main : IO Unit := do
  trace (fromRuleNumber32 248514) 3
