import Lean
import Std.Data.HashMap
import OneSidedTM.Basic
import OneSidedTM.Decide

open OneSidedTM
open TM

def formatRule (r : Rule) : String :=
  let ds := match r.dir with | Dir.L => "L" | Dir.R => "R"
  s!"({r.nextState},{r.write},{ds})"

def main : IO Unit := do
  let lines ← IO.FS.lines "/tmp/rules32.txt"
  let mut groups : Std.HashMap String (List Nat) := Std.HashMap.empty
  for line in lines do
    if line.isEmpty then continue
    let rNum := line.toNat!
    let tm := fromRuleNumber rNum
    let t10 := tm.transition 1 0
    let t11 := tm.transition 1 1
    let key := s!"(1,0)→{formatRule t10} (1,1)→{formatRule t11}"
    let cur := groups.getD key []
    groups := groups.insert key (rNum :: cur)

  let mut sortedGroups : Array (String × List Nat) := #[]
  for x in groups.toList do
    sortedGroups := sortedGroups.push x
  
  -- Sort by descending length
  let sorted := sortedGroups.qsort (fun a b => a.2.length > b.2.length)
  
  let mut i := 1
  for x in sorted do
    let (k,v) := x
    IO.println s!"Group {i}: {k}  => {v.length} rules (example: {v.head!})"
    i := i + 1
