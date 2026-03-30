import Lean
import Std.Data.HashMap
import OneSidedTM.Basic

open OneSidedTM
open TM

def formatRule (r : Rule) : String :=
  let ds := match r.dir with | Dir.L => "L" | Dir.R => "R"
  s!"({r.nextState},{r.write},{ds})"

def fromRuleNumber32 (ruleNum : Nat) : TM :=
  let d0 := (ruleNum / 248832) % 12 -- (state 1, sym 1)
  let d1 := (ruleNum / 20736) % 12  -- (state 1, sym 0)
  let d2 := (ruleNum / 1728) % 12   -- (state 2, sym 1)
  let d3 := (ruleNum / 144) % 12    -- (state 2, sym 0)
  let d4 := (ruleNum / 12) % 12     -- (state 3, sym 1)
  let d5 := ruleNum % 12            -- (state 3, sym 0)
  let decode (d : Nat) : Rule :=
    { nextState := d / 4 % 3 + 1
    , write := (d / 2) % 2
    , dir := if d % 2 == 1 then Dir.R else Dir.L }
  { numStates := 3
  , numSymbols := 2
  , transition := fun state sym =>
      match state, sym with
      | 1, 0 => decode d1
      | 1, 1 => decode d0
      | 2, 0 => decode d3
      | 2, 1 => decode d2
      | 3, 0 => decode d5
      | 3, 1 => decode d4
      | _, _ => { nextState := 1, write := 0, dir := Dir.R }
  }

-- Classify by deep structural properties
def classify (tm : TM) : String :=
  let t11 := tm.transition 1 1
  let t10 := tm.transition 1 0
  -- Phase 1: Carry/Scan type
  let phase1 :=
    if t11.nextState == 1 && t11.dir == Dir.L && t11.write == 0 then "Carry"
    else if t11.nextState == 1 && t11.dir == Dir.L && t11.write == 1 then "Scan"
    else if t11.dir == Dir.L then
      s!"MultiState({t11.nextState},{t11.write})"
    else "NonStandard"

  -- Phase 2: Absorb direction
  let absDir := if t10.dir == Dir.R then "R" else "L"
  let absWrite := t10.write

  -- Phase 3: Determine walkback structure
  let as_ := t10.nextState
  let bs_ := if as_ == 2 then 3 else 2

  -- Check if walkback uses 1 or 2 states
  let tas0 := tm.transition as_ 0
  let tas1 := tm.transition as_ 1
  let tbs0 := tm.transition bs_ 0
  let tbs1 := tm.transition bs_ 1

  -- For Carry+AbsorbR: walkback reads 0s, clears
  -- For Scan+AbsorbR: walkback reads 1s, clears
  let walkType :=
    -- Simple self-loop walkback (1 state)
    if phase1 == "Carry" && absDir == "R" then
      if tas0.nextState == as_ && tas0.dir == Dir.R && tas0.write == 0 then "Self"
      else if tas0.nextState == bs_ && tas0.dir == Dir.R && tbs0.nextState == as_ && tbs0.dir == Dir.R then "Toggle"
      else if tas0.nextState == bs_ && tas0.dir == Dir.R && tbs0.nextState == bs_ && tbs0.dir == Dir.R then "Drop"
      -- Bouncing walkback (L then R pattern)
      else if tas0.dir == Dir.L && tas0.nextState == bs_ then
        if tbs0.dir == Dir.R && tbs0.nextState == as_ &&
           tbs1.dir == Dir.R && tbs1.nextState == as_ then "BounceSimple"
        else s!"BounceComplex(bs0={formatRule tbs0},bs1={formatRule tbs1})"
      else s!"Other(as0={formatRule tas0})"
    else if phase1 == "Scan" && absDir == "R" then
      if tas1.nextState == as_ && tas1.dir == Dir.R && tas1.write == 0 then "Self"
      else if tas1.nextState == bs_ && tas1.dir == Dir.R && tbs1.nextState == as_ && tbs1.dir == Dir.R then "Toggle"
      else if tas1.nextState == bs_ && tas1.dir == Dir.R && tbs1.nextState == bs_ && tbs1.dir == Dir.R then "Drop"
      -- Bouncing clear
      else if tas1.dir == Dir.L && tas1.nextState == bs_ then
        if tbs0.dir == Dir.R && tbs0.nextState == as_ &&
           tbs1.dir == Dir.R && tbs1.nextState == as_ then "BounceSimple"
        else s!"BounceComplex(bs0={formatRule tbs0},bs1={formatRule tbs1})"
      else s!"Other(as1={formatRule tas1})"
    else if absDir == "L" then
      -- Absorb-L patterns
      if tas0.dir == Dir.R && tas1.dir == Dir.R then
        if tas0.nextState == as_ && tas1.nextState == as_ then "WalkbackSelf"
        else if tas0.nextState == bs_ || tas0.nextState == as_ then s!"WalkbackMixed"
        else s!"WalkbackOther"
      else s!"NonStdWalk"
    else "Unknown"

  s!"{phase1}+Abs{absDir}(w={absWrite},st={as_})+{walkType}"

def main : IO Unit := do
  let lines ← IO.FS.lines "/tmp/rules32.txt"
  let mut groups : Std.HashMap String (List Nat) := Std.HashMap.empty

  for line in lines do
    if line.isEmpty then continue
    let rNum := line.toNat!
    let tm := fromRuleNumber32 rNum
    let cls := classify tm
    let cur := groups.getD cls []
    groups := groups.insert cls (rNum :: cur)

  let mut sortedGroups : Array (String × List Nat) := #[]
  for x in groups.toList do sortedGroups := sortedGroups.push x
  let sorted := sortedGroups.qsort (fun a b => a.2.length > b.2.length)

  let mut total := 0
  for x in sorted do
    let (k,v) := x
    total := total + v.length
    IO.println s!"{k}: {v.length} rules"

  IO.println s!"\nTotal: {total}"
