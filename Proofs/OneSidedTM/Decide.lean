/-
  OneSidedTM.Decide

  Computational exploration: decode TM rules from Wolfram rule numbers,
  batch verify candidate +1 rules, find counterexamples, analyze structure.
-/

import OneSidedTM.Basic

namespace OneSidedTM
open TM

-- ============================================================================
-- Encoding TM rules from Wolfram {2,2} rule numbers
-- ============================================================================

/-- Decode a {2,2} TM rule number into its transition function.

    Wolfram convention (from models.rs):
    - 4 transitions encoded as a 4-digit base-8 number
    - digit_index = i*k + (k-1-j) for state i+1, symbol j
    - For {2,2}: digit_index mapping:
        0 → (state 1, sym 1)
        1 → (state 1, sym 0)
        2 → (state 2, sym 1)
        3 → (state 2, sym 0)
    - Each digit d encodes: nextState = d/4 % 2 + 1, write = d/2 % 2, dir = d % 2
      where dir 1 = Right (toward LSB), dir 0 = Left (toward MSB) -/
def fromRuleNumber22 (ruleNum : Nat) : TM :=
  let d0 := (ruleNum / 512) % 8  -- (state 1, sym 1)
  let d1 := (ruleNum / 64) % 8   -- (state 1, sym 0)
  let d2 := (ruleNum / 8) % 8    -- (state 2, sym 1)
  let d3 := ruleNum % 8           -- (state 2, sym 0)
  let decode (d : Nat) : Rule :=
    { nextState := d / 4 % 2 + 1
    , write := d / 2 % 2
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

-- Verify our decoder matches the known rule 445 transitions
-- Rule 445 in base 8: 445 = 6*64 + 7*8 + 5 → digits [0, 6, 7, 5]
-- d0=0 → (1,1): ns=1, w=0, L ↔ {1,1}→{1,0,-1} ✓
-- d1=6 → (1,0): ns=2, w=1, L ↔ {1,0}→{2,1,-1} ✓
-- d2=7 → (2,1): ns=2, w=1, R ↔ {2,1}→{2,1,1}  ✓
-- d3=5 → (2,0): ns=2, w=0, R ↔ {2,0}→{2,0,1}  ✓
#eval checkRun (fromRuleNumber22 445) 3 20 (4)  -- should be true
#eval checkRun (fromRuleNumber22 445) 7 30 (8)  -- should be true

-- ============================================================================
-- Batch verification
-- ============================================================================

/-- Find the first input n ∈ [1..maxN] where a TM fails to compute +1 -/
def findFirstFailure (tm : TM) (maxN : Nat) (maxFuel : Nat) : Option Nat :=
  let rec go (n : Nat) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      if n > maxN then none
      else if !checkRun tm n maxFuel (n + 1) then some n
      else go (n + 1) fuel'
  go 1 maxN

-- ============================================================================
-- The 17 candidate +1 rules (found by OneSidedTuringMachineFind for inputs 1..20)
-- ============================================================================

def candidateRules : List Nat :=
  [445, 453, 461, 469, 477, 485, 493, 501, 509,
   1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]

-- Check all candidates for failures up to input 200
#eval! candidateRules.map fun r =>
  (r, findFirstFailure (fromRuleNumber22 r) 200 1000)

-- ============================================================================
-- Structural analysis: which rules share the "active" transitions?
-- ============================================================================

/-- Describe a rule's transitions compactly -/
def describeRule (ruleNum : Nat) : String :=
  let tm := fromRuleNumber22 ruleNum
  let show_one (s sy : Nat) :=
    let r := tm.transition s sy
    s!"({r.nextState},{r.write},{match r.dir with | Dir.L => "L" | Dir.R => "R"})"
  s!"{ruleNum}: (1,0)→{show_one 1 0} (1,1)→{show_one 1 1} (2,0)→{show_one 2 0} (2,1)→{show_one 2 1}"

#eval candidateRules.map describeRule

-- ============================================================================
-- Formal counterexample infrastructure
-- ============================================================================

/-- Proof that a specific rule does NOT compute n ↦ n+1 for a given input -/
def notSuccAt (ruleNum n fuel : Nat) : Prop :=
  run (fromRuleNumber22 ruleNum) n fuel ≠ some (n + 1)

-- Once we find failures in the #eval above, we can formalize them:
-- theorem rule_XXX_fails_at_N : notSuccAt XXX N 1000 := by native_decide

end OneSidedTM
