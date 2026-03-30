import Lean
import Std.Data.HashMap
import OneSidedTM.Basic
import OneSidedTM.Decide

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

-- ClassS: Scan + self-loop clear. Dead transition: (bs,*) all dead since only as is used.
def isClassS (tm : TM) : Bool :=
  let t11 := tm.transition 1 1
  let t10 := tm.transition 1 0
  if t11 == { nextState := 1, write := 1, dir := Dir.L } &&
     t10.write == 1 && t10.dir == Dir.R then
    let as_ := t10.nextState
    if as_ == 2 || as_ == 3 then
      let tas1 := tm.transition as_ 1
      -- Only check as1 = self-loop clear. (as,0) is halt. (bs,*) are dead.
      tas1 == { nextState := as_, write := 0, dir := Dir.R }
    else false
  else false

-- ClassSX_Toggle: Scan + toggle clear. Dead: (bs,0) in some variants.
def isClassSX_Toggle (tm : TM) : Bool :=
  let t11 := tm.transition 1 1
  let t10 := tm.transition 1 0
  if t11 == { nextState := 1, write := 1, dir := Dir.L } &&
     t10.write == 1 && t10.dir == Dir.R then
    let as_ := t10.nextState
    let bs_ := if as_ == 2 then 3 else 2
    let tas1 := tm.transition as_ 1
    let tbs1 := tm.transition bs_ 1
    -- Toggle: as->bs->as. (bs,0) is dead (bs only sees 1s after scan).
    tas1 == { nextState := bs_, write := 0, dir := Dir.R } &&
    tbs1 == { nextState := as_, write := 0, dir := Dir.R }
  else false

-- ClassSX_Drop: Scan + drop clear. Dead: (bs,0).
def isClassSX_Drop (tm : TM) : Bool :=
  let t11 := tm.transition 1 1
  let t10 := tm.transition 1 0
  if t11 == { nextState := 1, write := 1, dir := Dir.L } &&
     t10.write == 1 && t10.dir == Dir.R then
    let as_ := t10.nextState
    let bs_ := if as_ == 2 then 3 else 2
    let tas1 := tm.transition as_ 1
    let tbs1 := tm.transition bs_ 1
    -- Drop: as->bs->bs. (bs,0) is dead.
    tas1 == { nextState := bs_, write := 0, dir := Dir.R } &&
    tbs1 == { nextState := bs_, write := 0, dir := Dir.R }
  else false

-- ClassW: Carry + walkback Self/Toggle/Drop. Dead: (bs,1) for self (bs never used).
def isClassW (tm : TM) : Bool :=
  let t11 := tm.transition 1 1
  let t10 := tm.transition 1 0
  if t11 == { nextState := 1, write := 0, dir := Dir.L } &&
     t10.write == 1 && t10.dir == Dir.R then
    let as_ := t10.nextState
    if as_ == 2 || as_ == 3 then
      let bs_ := if as_ == 2 then 3 else 2
      let tas0 := tm.transition as_ 0
      let tbs0 := tm.transition bs_ 0
      -- Self: as reads 0, writes 0, goes R, stays in as. (bs,*) all dead.
      if tas0 == { nextState := as_, write := 0, dir := Dir.R } then true
      -- Toggle: as->bs->as. (bs,1) dead (carry cleared all 1s).
      else if tas0 == { nextState := bs_, write := 0, dir := Dir.R } && tbs0 == { nextState := as_, write := 0, dir := Dir.R } then true
      -- Drop: as->bs->bs. (bs,1) dead.
      else if tas0 == { nextState := bs_, write := 0, dir := Dir.R } && tbs0 == { nextState := bs_, write := 0, dir := Dir.R } then true
      else false
    else false
  else false

-- ClassWL: Carry + absorb-L + walkback. Dead: (bs,*) all dead (only as walks back).
-- Now also accept toggle/drop walkback variants.
def isClassWL (tm : TM) : Bool :=
  let t11 := tm.transition 1 1
  let t10 := tm.transition 1 0
  if t11 == { nextState := 1, write := 0, dir := Dir.L } &&
     t10.write == 1 && t10.dir == Dir.L then
    let as_ := t10.nextState
    if as_ == 2 || as_ == 3 then
      let bs_ := if as_ == 2 then 3 else 2
      let tas0 := tm.transition as_ 0
      let tas1 := tm.transition as_ 1
      let tbs0 := tm.transition bs_ 0
      let tbs1 := tm.transition bs_ 1
      -- Self walkback: (as,0)->as,0,R; (as,1)->as,1,R. (bs,*) dead.
      if tas0 == { nextState := as_, write := 0, dir := Dir.R } &&
         tas1 == { nextState := as_, write := 1, dir := Dir.R } then true
      -- Toggle walkback: (as,0)->bs,0,R; (bs,0)->as,0,R; (as,1)->bs,1,R; (bs,1)->as,1,R
      else if tas0.dir == Dir.R && tas0.write == 0 && tas0.nextState == bs_ &&
              tbs0.dir == Dir.R && tbs0.write == 0 && tbs0.nextState == as_ &&
              tas1.dir == Dir.R && tas1.write == 1 && tas1.nextState == bs_ &&
              tbs1.dir == Dir.R && tbs1.write == 1 && tbs1.nextState == as_ then true
      else false
    else false
  else false

-- ClassB: Carry + any Bouncing Walkback variant
-- Core: (1,1)->1,0,L  (1,0)->as,1,R  then 2-state bounce cycle using as+bs
-- The bounce cycle: as reads bit, goes L to bs; bs reads bit, goes R to as; as reads/clears
-- Many write-value variants exist. We check:
--  (as,0).dir = L, (as,0).nextState = bs  [walk_L]
--  (bs,0).dir = R, (bs,0).nextState = as  [walk_R_0]
--  (bs,1).dir = R, (bs,1).nextState = as  [walk_R_1]
--  (as,1).dir = R  [walk_clr]
--  (as,1).nextState = as OR bs  [self or toggle walk_clr]
def isClassB (tm : TM) : Bool :=
  let t11 := tm.transition 1 1
  let t10 := tm.transition 1 0
  if t11 == { nextState := 1, write := 0, dir := Dir.L } &&
     t10.write == 1 && t10.dir == Dir.R then
    let as_ := t10.nextState
    if as_ == 2 || as_ == 3 then
      let bs_ := if as_ == 2 then 3 else 2
      let tas0 := tm.transition as_ 0
      let tbs0 := tm.transition bs_ 0
      let tbs1 := tm.transition bs_ 1
      let tas1 := tm.transition as_ 1
      -- Core structural checks: directions and state transitions
      tas0.dir == Dir.L && tas0.nextState == bs_ &&  -- as reads 0, goes L to bs
      tbs0.dir == Dir.R && tbs0.nextState == as_ &&  -- bs reads 0, goes R to as
      tbs1.dir == Dir.R && tbs1.nextState == as_ &&  -- bs reads 1, goes R to as
      tas1.dir == Dir.R &&                           -- as reads 1, goes R (clear)
      (tas1.nextState == as_ || tas1.nextState == bs_) -- self or toggle
    else false
  else false

-- ClassSB: Scan + any Bouncing Clear variant
-- Core: (1,1)->1,1,L  (1,0)->as,1,R  then 2-state bounce on clear phase
def isClassSB (tm : TM) : Bool :=
  let t11 := tm.transition 1 1
  let t10 := tm.transition 1 0
  if t11 == { nextState := 1, write := 1, dir := Dir.L } &&
     t10.write == 1 && t10.dir == Dir.R then
    let as_ := t10.nextState
    if as_ == 2 || as_ == 3 then
      let bs_ := if as_ == 2 then 3 else 2
      let tas1 := tm.transition as_ 1
      let tbs0 := tm.transition bs_ 0
      let tbs1 := tm.transition bs_ 1
      let tas0 := tm.transition as_ 0
      -- Bouncing clear: as reads 1, bounces L to bs; bs goes R back
      tas1.dir == Dir.L && tas1.nextState == bs_ &&  -- as reads 1, goes L to bs
      tbs0.dir == Dir.R && tbs0.nextState == as_ &&  -- bs reads 0, goes R to as
      tbs1.dir == Dir.R && tbs1.nextState == as_ &&  -- bs reads 1, goes R to as
      tas0.dir == Dir.R &&                           -- as reads 0, goes R (walk)
      (tas0.nextState == as_ || tas0.nextState == bs_) -- self or toggle
    else false
  else false

-- ClassRC: Reverse Carry (Groups 19-20)
-- (1,1)->α,0,L  (α,1)->α,0,L  (α,0)->β,1,R  (β,0)->β,0,R
def isClassRC (tm : TM) : Bool :=
  let t11 := tm.transition 1 1
  if t11.write == 0 && t11.dir == Dir.L then
    let as_ := t11.nextState
    if as_ == 2 || as_ == 3 then
      let bs_ := if as_ == 2 then 3 else 2
      let tas1 := tm.transition as_ 1
      let tas0 := tm.transition as_ 0
      let tbs0 := tm.transition bs_ 0
      tas1 == { nextState := as_, write := 0, dir := Dir.L } &&
      tas0 == { nextState := bs_, write := 1, dir := Dir.R } &&
      tbs0 == { nextState := bs_, write := 0, dir := Dir.R }
    else false
  else false

-- ClassRS: Reverse Scan (Groups 21-22)
-- (1,1)->1,1,L  (1,0)->α,0,L  (α,0)->β,0,R  (β,0)->β,1,R  (β,1)->β,0,R
def isClassRS (tm : TM) : Bool :=
  let t11 := tm.transition 1 1
  let t10 := tm.transition 1 0
  if t11 == { nextState := 1, write := 1, dir := Dir.L } &&
     t10.write == 0 && t10.dir == Dir.L then
    let as_ := t10.nextState
    if as_ == 2 || as_ == 3 then
      let bs_ := if as_ == 2 then 3 else 2
      let tas0 := tm.transition as_ 0
      let tbs0 := tm.transition bs_ 0
      let tbs1 := tm.transition bs_ 1
      tas0 == { nextState := bs_, write := 0, dir := Dir.R } &&
      tbs0 == { nextState := bs_, write := 1, dir := Dir.R } &&
      tbs1 == { nextState := bs_, write := 0, dir := Dir.R }
    else false
  else false

def main : IO Unit := do
  let lines ← IO.FS.lines "/tmp/rules32.txt"
  let mut sCount := 0
  let mut sxCount := 0
  let mut wCount := 0
  let mut wlCount := 0
  let mut bCount := 0
  let mut sbCount := 0
  let mut rcCount := 0
  let mut rsCount := 0
  let mut unknown : Array Nat := #[]

  for line in lines do
    if line.isEmpty then continue
    let rNum := line.toNat!
    let tm := fromRuleNumber32 rNum

    if isClassS tm then sCount := sCount + 1
    else if isClassSX_Toggle tm || isClassSX_Drop tm then sxCount := sxCount + 1
    else if isClassW tm then wCount := wCount + 1
    else if isClassWL tm then wlCount := wlCount + 1
    else if isClassB tm then bCount := bCount + 1
    else if isClassSB tm then sbCount := sbCount + 1
    else if isClassRC tm then rcCount := rcCount + 1
    else if isClassRS tm then rsCount := rsCount + 1
    else
      unknown := unknown.push rNum

  IO.println s!"S: {sCount}, SX: {sxCount}, W: {wCount}, WL: {wlCount}, B: {bCount}, SB: {sbCount}, RC: {rcCount}, RS: {rsCount}"
  IO.println s!"Total Proven: {sCount + sxCount + wCount + wlCount + bCount + sbCount + rcCount + rsCount}"
  IO.println s!"Unknown Rules: {unknown.size}"

  let mut uGroups : Std.HashMap String (List Nat) := Std.HashMap.empty
  for rNum in unknown do
    let tm := fromRuleNumber32 rNum
    let t10 := tm.transition 1 0
    let t11 := tm.transition 1 1
    let key := s!"(1,0)→{formatRule t10} (1,1)→{formatRule t11}"
    let cur := uGroups.getD key []
    uGroups := uGroups.insert key (rNum :: cur)
    
  let mut sortedUGroups : Array (String × List Nat) := #[]
  for x in uGroups.toList do sortedUGroups := sortedUGroups.push x
  let sorted := sortedUGroups.qsort (fun a b => a.2.length > b.2.length)
  
  let mut i := 1
  for x in sorted do
    let (k,v) := x
    let exRule := v.head!
    let tm := fromRuleNumber32 exRule
    IO.println s!"\nUnknown Group {i}: {k}  => {v.length} rules (example: {exRule})"
    for s in [1, 2, 3] do
      for c in [0, 1] do
        IO.println s!"  ({s},{c}) -> {formatRule (tm.transition s c)}"
    i := i + 1
