/-
  Tests.SmithVectors

  Regression tests of the Smith-chain definitions against the printed traces
  of Alex Smith's own Perl interpreters (`docs/TM23Proof.pdf`).  Each test
  cites the page it comes from.

  This is the only module of the Smith chain (TM, TagSystem, BiTM, Tests) that
  may use `native_decide`, and `native_decide` is used only for the System 4
  runs of D5, where the kernel cannot finish the computation in reasonable
  time: those runs are about 10^4 steps over a 545-element tape.  Everything
  else, the structural checks of the D4 tape included, closes by `decide`.
  Nothing outside this file depends on anything established here, so the
  `native_decide` axiom does not reach the development: every claim below is
  an `example`, and every `def` in the file is used only by `example`s.

  Vectors:
    * D1  `cy2s5.pl 3 01 1 10`                       (p. 29)
    * D2  `cy2s5.pl 50 F test1.cy`                    (p. 28-29)
    * D3  `system5.pl` default and C traces of D1     (p. 31)
    * D4  `s52s4.pl 16 2 1,4 1,6 "" ""`               (p. 33)
    * D5  `system4.pl C` on the D4 tape               (p. 41)
    * D6  the System 0 transition table               (p. 3)
    * D7  the scheduled times of the D5 run under `RepS4` (M3)
-/

import BiTM.CTSToSystem5
import BiTM.System5ToSystem4
import BiTM.System4
import BiTM.Wolfram23Valid
import Smith.Conjecture4
import Smith.Conjecture3
import Smith.Conjecture0

namespace Tests

open TM
open TagSystem
open BiTM

/-! ## Helpers -/

/-- Insertion sort on integers.  The Perl interpreters print the keys of a
    hash with `sort {$a <=> $b}`, so every printed bag or set is compared
    against its sorted form. -/
def sortInts : List Int -> List Int
  | [] => []
  | x :: xs => insertInt x (sortInts xs)
where
  insertInt (x : Int) : List Int -> List Int
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insertInt x ys

/-- The bag as `system5.pl` prints it at the start of an iteration: every
    entry decremented, duplicates already gone, sorted. -/
def s5PrintedBag (cfg : System5Config) : List Int :=
  sortInts (cfg.bag.map (· - 1))

/-- The rules as `system5.pl` prints them at the start of an iteration: every
    entry incremented. -/
def s5PrintedRules (cfg : System5Config) : List (List Int) :=
  cfg.rules.map (fun r => r.map (· + 1))

/-- The configuration of a System 5 run after `k` steps, or the empty
    configuration if the run has already stopped. -/
def s5At (cfg : System5Config) (k : Nat) : System5Config :=
  (System5.nSteps cfg k).getD { bag := [], rules := [] }

/-- The C output format of `system5.pl` (PDF p. 30-31).  In C mode `$cpr`
    starts at 1, is reset to 1 at the top of every iteration, and is set to 2
    exactly when a `0` is found in the decremented bag and a rule is popped;
    `00` is printed when it is 2 and `11` when it is 1.  A `0` survives the
    decrement iff `1` was in the bag before the step.  When the loop ends the
    program prints the literal `111...`. -/
def c5Format (cfg : System5Config) : Nat -> String
  | 0 => ""
  | fuel + 1 =>
      match System5.step cfg with
      | none => "111..."
      | some cfg' =>
          (if (0 : Int) ∈ cfg.bag.map (· - 1) then "00" else "11")
            ++ c5Format cfg' fuel

/-- The sorted set at tape position `i`, or `[]` if that position holds a
    star or does not exist. -/
def s4SetAt (cfg : System4Config) (i : Nat) : List Int :=
  match cfg.elems[i]? with
  | some (System4Elem.set s) => sortInts s
  | _ => []

/-- `true` when tape position `i` holds a star. -/
def s4IsStarAt (cfg : System4Config) (i : Nat) : Bool :=
  match cfg.elems[i]? with
  | some System4Elem.star => true
  | _ => false

/-- The C output format of `system4.pl` (PDF p. 34-37).  `$cpr` starts at 1.
    Rule 1 firing at the leftmost element (`$active` is 0, so the head turns
    round into state B) sets `$cpr` to 2.  The next star reached in state B
    (rule 4) prints `1` and the next star reached in state C (rule 5) prints
    `0`, each resetting `$cpr` to 1.  The run stops when the active element
    falls off the right end of the tape.

    The Perl would also print for a star reached in state B at position 0,
    where `System4.step` stops instead; that case does not arise on the tapes
    `s52s4.pl` emits, whose leftmost element is a set. -/
def c4Format : System4Config -> Nat -> String -> Nat -> String
  | _, _, acc, 0 => acc
  | cfg, cpr, acc, fuel + 1 =>
      if h : cfg.active < cfg.elems.length then
        let cur := cfg.elems.get ⟨cfg.active, h⟩
        let cpr1 :=
          match cur, cfg.state with
          | System4Elem.set _, System4State.A =>
              if cfg.active = 0 && cpr == 1 then 2 else cpr
          | _, _ => cpr
        match System4.step cfg with
        | none => acc
        | some cfg' =>
            match cur, cfg.state with
            | System4Elem.star, System4State.B =>
                if cpr1 == 2 then c4Format cfg' 1 (acc ++ "1") fuel
                else c4Format cfg' cpr1 acc fuel
            | System4Elem.star, System4State.C =>
                if cpr1 == 2 then c4Format cfg' 1 (acc ++ "0") fuel
                else c4Format cfg' cpr1 acc fuel
            | _, _ => c4Format cfg' cpr1 acc fuel
      else acc

/-! ## D1: `cy2s5.pl 3 01 1 10` (PDF p. 29) -/

/-- The two-appendant cyclic tag system `1 10` of PDF p. 29. -/
def ctsD1 : CTS where
  appendants := [[true], [true, false]]
  nonempty := by decide

/-- Its working string `01` at phase 0. -/
def cfgD1 : CTSConfig := { data := [false, true], phase := 0 }

example : (ctsToSystem5 ctsD1 cfgD1 1).bag = [1, 2, 3, 4, 5, 7, 8, 10] := by decide

example : (ctsToSystem5 ctsD1 cfgD1 1).rules
    = [[15, 18], [13, 16], [], [],
       [21, 24, 27, 28], [19, 22, 25, 26], [], []] := by decide

/-- The 12 rules `cy2s5.pl 3 01 1 10` prints.  The Perl's `n` counts
    appendant emissions (4 rules each), the Lean `n` counts full cycles over
    the appendant list (here 8 rules each), so 12 rules is one and a half
    Lean cycles: it is a prefix of the Lean `n = 2` stream, not equal to it. -/
def rulesD1Pdf : List (List Int) :=
  [[15, 18], [13, 16], [], [],
   [21, 24, 27, 28], [19, 22, 25, 26], [], [],
   [31, 34], [29, 32], [], []]

example : (ctsToSystem5 ctsD1 cfgD1 2).rules.take 12 = rulesD1Pdf := by decide

example : (ctsToSystem5 ctsD1 cfgD1 2).rules.length = 16 := by decide

/-- The rotation by the phase: at phase 1 the rule stream starts with the
    appendant `CTS.currentAppendant` reads at phase 1, which is `10`, and the
    counter still starts at `counterAfterWorkingString + 2 = 13`. -/
example : (ctsToSystem5 ctsD1 { data := [false, true], phase := 1 } 1).rules
    = [[15, 18, 21, 22], [13, 16, 19, 20], [], [], [25, 28], [23, 26], [], []] := by
  decide

/-! ## D2: `cy2s5.pl 50 F test1.cy` (PDF p. 28-29) -/

-- The 200-rule stream of `n = 10` needs more than the default unfolding depth.
set_option maxRecDepth 8000

/-- `test1.cy`: working string `11011`, appendants `101 01 0 "" 010`. -/
def ctsD2 : CTS where
  appendants := [[true, false, true], [false, true], [false], [],
                 [false, true, false]]
  nonempty := by decide

/-- Its working string `11011` at phase 0. -/
def cfgD2 : CTSConfig := { data := [true, true, false, true, true], phase := 0 }

example : (ctsToSystem5 ctsD2 cfgD2 10).bag
    = [1, 3, 4, 6, 7, 9, 10, 12, 13, 14, 15, 16, 17, 19, 20, 22, 23, 25, 26, 28] := by
  decide

/-- The Lean `n = 10` is the Perl `n = 50`: five appendants per cycle. -/
example : (ctsToSystem5 ctsD2 cfgD2 10).rules.length = 200 := by decide

example : (ctsToSystem5 ctsD2 cfgD2 10).rules.take 22
    = [[33, 36, 39, 40, 43, 46], [31, 34, 37, 38, 41, 44], [], [],
       [49, 50, 53, 56], [47, 48, 51, 54], [], [],
       [59, 60], [57, 58], [], [],
       [], [], [], [],
       [63, 64, 67, 70, 73, 74], [61, 62, 65, 68, 71, 72], [], [],
       [77, 80, 83, 84, 87, 90], [75, 78, 81, 82, 85, 88]] := by decide

/-! ## D3: the `system5.pl` trace of D1 (PDF p. 31) -/

/-- The System 5 program `system5.pl` is run on in the PDF trace: the D1 bag
    with the 12 rules `cy2s5.pl 3 01 1 10` prints. -/
def s5D3 : System5Config := { bag := [1, 2, 3, 4, 5, 7, 8, 10], rules := rulesD1Pdf }

/-- The run stops after exactly 36 steps, when the rules run out. -/
example : (System5.nSteps s5D3 36).isSome = true := by decide

example : System5.nSteps s5D3 37 = none := by decide

/-- The first three printed bags (PDF p. 31, lines 1 to 3). -/
example : s5PrintedBag (s5At s5D3 0) = [0, 1, 2, 3, 4, 6, 7, 9] := by decide

example : s5PrintedBag (s5At s5D3 1) = [0, 1, 2, 3, 5, 6, 8, 15, 18] := by decide

example : s5PrintedBag (s5At s5D3 2) = [0, 1, 2, 4, 5, 7] := by decide

/-- The rules printed on the first line of the PDF trace. -/
example : s5PrintedRules (s5At s5D3 0)
    = [[16, 19], [14, 17], [], [],
       [22, 25, 28, 29], [20, 23, 26, 27], [], [],
       [32, 35], [30, 33], [], []] := by decide

/-- The C-format line of PDF p. 31.  Two characters per step for 36 steps,
    then the literal `111...` the Perl prints when the loop ends. -/
example : c5Format s5D3 200
    = "000000000011000011001111111111111111111111111111111111111111001100001100111..." := by
  decide

/-- The Lean encoder at `n = 1` (8 rules) runs out of rules after 10 steps;
    at `n = 2` (16 rules) after 40.  Neither equals the PDF's 36, because the
    PDF program has 12 rules. -/
example : (System5.nSteps (ctsToSystem5 ctsD1 cfgD1 1) 10).isSome = true := by decide

example : System5.nSteps (ctsToSystem5 ctsD1 cfgD1 1) 11 = none := by decide

/-! ## D4: `s52s4.pl 16 2 1,4 1,6 "" ""` (PDF p. 33) -/

/-- The System 5 program of PDF p. 33: bag `2`, rules `1,4 1,6 "" ""`. -/
def s5D4 : System5Config := { bag := [2], rules := [[1, 4], [1, 6], [], []] }

/-- Its System 4 encoding at `f = 16`. -/
def s4D4 : System4Config := system5ToSystem4 s5D4 16

/-- One bag set, 16 star/empty pairs, and `8 * 16 = 128` elements for each of
    the four rules. -/
example : s4D4.elems.length = 545 := by decide

/-- 16 stars in the padding and 64 in each rule block. -/
example : (s4D4.elems.filter (fun e => e.isStar)).length = 272 := by decide

example : s4D4.state = System4State.A := by decide

example : s4D4.active = 0 := by decide

/-- The leftmost element is the encoded bag: `2 * 2 - 2 = 2`. -/
example : s4D4.elems.head? = some (System4Elem.set [2]) := by decide

/-- Then 16 star/empty-set pairs. -/
example : s4IsStarAt s4D4 1 = true := by decide

example : s4SetAt s4D4 2 = [] := by decide

example : s4IsStarAt s4D4 31 = true := by decide

example : s4SetAt s4D4 32 = [] := by decide

/-- The first rule block: a star, then all of `0..48` with `1 * 2 + 19 = 21`
    and `4 * 2 + 19 = 27` toggled out. -/
example : s4IsStarAt s4D4 33 = true := by decide

example : s4SetAt s4D4 34 = ((allInts 49).erase 21).erase 27 := by decide

/-- Then 32 star/empty pairs, a star, and the set of all of `0..48`. -/
example : s4IsStarAt s4D4 99 = true := by decide

example : s4SetAt s4D4 100 = allInts 49 := by decide

/-- Then 30 star/empty pairs, and the second rule block starts: `1,6` toggles
    out `21` and `6 * 2 + 19 = 31`. -/
example : s4IsStarAt s4D4 161 = true := by decide

example : s4SetAt s4D4 162 = ((allInts 49).erase 21).erase 31 := by decide

/-- The encoded tape is well formed: leftmost element a set, no two adjacent
    stars, every set duplicate-free. -/
example : s4D4.WellFormed := by decide

/-! ## D5: `system4.pl C` on the D4 tape (PDF p. 41) -/

/-- The run falls off the right end of the tape after exactly 9906 steps. -/
example : (System4.nSteps s4D4 9906).isSome = true := by native_decide

example : System4.nSteps s4D4 9907 = none := by native_decide

/-- The C-format output of PDF p. 41.  With the two stars per rule block
    restored this is exactly Smith's line; the encoder without them printed
    `11001111100111100`. -/
example : c4Format s4D4 1 "" 20000 = "110011110011110010" := by native_decide

/-! ## D6: the System 0 transition table (PDF p. 3) -/

example : wolfram23.transition 1 0 = { nextState := 2, write := 1, dir := Dir.R } := by
  decide

example : wolfram23.transition 1 1 = { nextState := 1, write := 2, dir := Dir.L } := by
  decide

example : wolfram23.transition 1 2 = { nextState := 1, write := 1, dir := Dir.L } := by
  decide

example : wolfram23.transition 2 0 = { nextState := 1, write := 2, dir := Dir.L } := by
  decide

example : wolfram23.transition 2 1 = { nextState := 2, write := 2, dir := Dir.R } := by
  decide

example : wolfram23.transition 2 2 = { nextState := 1, write := 0, dir := Dir.R } := by
  decide

/-! ## D7: the D5 run at the times `conjecture4_finite` schedules (M3)

The System 5 program of D4 is `2 1,4 1,6 "" ""`; its bags are `2`, `1`,
`3,6`, `2,5`, `1,4`, ... (one D-step, one P-step, two D-steps).  The bounds
of `conjecture4_finite` at `f = 16` hold for a budget of 4 steps (the rule
entry 6 needs `6 + 2h < 16`).  The head is back at the left end in state A
after 8, 1336, 1616 and 1904 System 4 steps, and there `decodeS4` below the
band `2f - 2j - 2` reads the System 5 bag.  The times in between at which
the head is also at the left end in state A (570, the end of the first pop
phase, and 1475, the middle of a D-step) decode to `none`, because the
parity set then holds odd integers.  These runs are 10^3 steps long, so they
close by `native_decide` like D5. -/

example : (System4.nSteps s4D4 8).bind (fun c => Smith.decodeS4 c 28) = some [1] := by
  native_decide

example : (System4.nSteps s4D4 1336).bind (fun c => Smith.decodeS4 c 26) = some [3, 6] := by
  native_decide

example : (System4.nSteps s4D4 1616).bind (fun c => Smith.decodeS4 c 24) = some [2, 5] := by
  native_decide

example : (System4.nSteps s4D4 1904).bind (fun c => Smith.decodeS4 c 22) = some [1, 4] := by
  native_decide

example : (System4.nSteps s4D4 1904).map (fun c => (c.active, c.state)) = some (0, System4State.A) := by
  native_decide

example : (System4.nSteps s4D4 570).bind (fun c => Smith.decodeS4 c 26) = none := by
  native_decide

example : (System4.nSteps s4D4 1475).bind (fun c => Smith.decodeS4 c 24) = none := by
  native_decide

/-- The D-step of `Smith.System4Runs` on the D4 tape, by `decide`: the bag
    set `{2}` is decremented twice and two empty sets are merged. -/
example : System4.nSteps s4D4 8
    = some ⟨Smith.sets [[0], [], []] ++ starredEmptyPairs 14
              ++ Smith.encBlocks [[1, 4], [1, 6], [], []] 16 0,
            0, System4State.A⟩ := by
  decide

/-! ## D8: the System 3 emulation of a System 4 run (M5)

The System 4 tape `[{1,2}, *, {3}]` in state A at its left end takes six
steps: the turn (rule 1), a scan of `{1,2}` to `{0,1}` in state B (rule 3),
the deletion of the star (rule 4), the turn, a scan of `{0,1}` to `{0}` that
toggles the state to C, and a scan of `{3}` to `{2}` after which the head is
off the tape.  With blocks of width 16 (`w = 4`, budget 6) `initAC` gives the
System 3 tape `0^6 2 2 1 | 2112 2^12 | 0 | 121 121 ... | 1`, and the System 3
run visits, at the times `conjecture3_finite` schedules (the turn `p + 2t + 6`
with `p = 0, t = 1`, then `p = 15, t = 2`; the scans 16; rule 4 one step), a
head in state B on the first cell of the active block, on the star's 0 in
state B, in state A on the last cell of the first block, in state C on the
first cell of the last block, and finally on the closing 1 in state C with
nothing to its right; the run is stuck there.  The blocks decode to their
sets on the six scans of the window. -/

def s4D8 : System4Config :=
  ⟨[System4Elem.set [1, 2], System4Elem.star, System4Elem.set [3]], 0, System4State.A⟩

def s3D8 : Smith.LConfig := (Smith.initAC 4 6 [1, 2] [System4Elem.star, System4Elem.set [3]]).toL

example : s4D8.WellFormed := by decide

example : s3D8.toList
    = [0, 0, 0, 0, 0, 0, 2, 2, 1] ++ [2, 1, 1, 2] ++ List.replicate 12 2 ++ [0]
      ++ [1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2] ++ [1] := by decide

example : Smith.Decodes (Smith.encSet 16 [1, 2]) [1, 2] 6 := by decide
example : Smith.Decodes (Smith.encSet 16 [3]) [3] 6 := by decide
example : Smith.Decodes (Smith.encSet 16 []) [] 6 := by decide
example : Smith.firstTrue (Smith.encSet 16 [1, 2]) ∧ Smith.firstTrue (Smith.encSet 16 [3]) := by decide

example : (System4.nSteps s4D8 6).map (fun c => (c.elems, c.active, c.state))
    = some ([System4Elem.set [0], System4Elem.set [2]], 2, System4State.C) := by decide

example : (Smith.lnSteps Smith.sys3 s3D8 8).map (fun c => (c.head, c.state))
    = some (2, Smith.LState.B) := by decide
example : (Smith.lnSteps Smith.sys3 s3D8 24).map (fun c => (c.head, c.state))
    = some (0, Smith.LState.B) := by decide
example : (Smith.lnSteps Smith.sys3 s3D8 25).map (fun c => (c.head, c.right.length, c.state))
    = some (1, 17, Smith.LState.A) := by decide
example : (Smith.lnSteps Smith.sys3 s3D8 50).map (fun c => (c.head, c.state))
    = some (2, Smith.LState.B) := by decide
example : (Smith.lnSteps Smith.sys3 s3D8 66).map (fun c => (c.head, c.state))
    = some (2, Smith.LState.C) := by decide
example : (Smith.lnSteps Smith.sys3 s3D8 82).map (fun c => (c.head, c.right, c.state))
    = some (1, [], Smith.LState.C) := by decide
example : Smith.lnSteps Smith.sys3 s3D8 83 = none := by decide

/-- The block of `{0}` left behind after the second scan of the first block
    still decodes to `{0}` on the four scans of the remaining budget. -/
example : (Smith.lnSteps Smith.sys3 s3D8 66).map
      (fun c => decide (Smith.Decodes (Smith.toBits (c.left.take 16).reverse) [0] 4)) = some true := by
  decide

/-! ## D9: the wolfram23 decoder (M6)

`decodeW23 N b` reads the blocks from the head cell up to the first 0, XORs
them, takes the parity set below the band `b`, reads it as the bag by
`x / 2 + 1` and the bag as the working string by `decodeBag`.  On the tape of
`initAC 3 3 [0, 2] [*, {}]` (one block of width 8 for the set `{0, 2}`, whose
bag is `{1, 2}`, the pairs of the word `0`) it decodes to `[false]` once the
head has turned (8 System 3 steps: state B on the first cell), and on the tape
of `initAC 3 3 [0, 2] [{2, 4}, *, {}]` (conglomerate `{0, 2} xor {2, 4} =
{0, 4}`, bag `{1, 3}`, word `1`) to `[true]`.  Negative instances: at time 0
the head is in state A, where `phi3` swaps the head cell, and the block no
longer decodes; the set `{1}` puts the parity at an odd position, which is
not a bag; a tape whose cells do not make whole blocks. -/

def s3D9 : Smith.LConfig := (Smith.initAC 3 3 [0, 2] [System4Elem.star, System4Elem.set []]).toL

def s3D9b : Smith.LConfig :=
  (Smith.initAC 3 3 [0, 2] [System4Elem.set [2, 4], System4Elem.star, System4Elem.set []]).toL

def s3D9c : Smith.LConfig := (Smith.initAC 3 3 [1] [System4Elem.star, System4Elem.set []]).toL

example : (Smith.lnSteps Smith.sys3 s3D9 8).map
    (fun c => Smith.decodeW23 8 4 (Smith.toBi (Smith.phi2 (Smith.phi3 c)))) = some (some [false]) := by
  decide

example : (Smith.lnSteps Smith.sys3 s3D9b 8).map
    (fun c => Smith.decodeW23 8 6 (Smith.toBi (Smith.phi2 (Smith.phi3 c)))) = some (some [true]) := by
  decide

example : Smith.decodeW23 8 4 (Smith.toBi (Smith.phi2 (Smith.phi3 s3D9))) = none := by decide

example : (Smith.lnSteps Smith.sys3 s3D9c 8).map
    (fun c => Smith.decodeW23 8 4 (Smith.toBi (Smith.phi2 (Smith.phi3 c)))) = some none := by
  decide

example : Smith.decodeW23 8 4 ⟨1, [], 2, [1, 1, 0]⟩ = none := by decide

/-- The exit of System 3 from the `off` configuration is a two-cell rule
    reading the implicit 0, and wolfram23 makes the step `B2 -> 0, R, A`
    after the relabelings. -/
example : Smith.lstep Smith.sys3 ⟨[2, 1, 1, 2, 2, 0], 1, [], Smith.LState.C⟩ = none := by decide
example : BiTM.step wolfram23 (Smith.toBi (Smith.phi2 (Smith.phi3 ⟨[2, 1, 1, 2, 2, 0], 1, [], Smith.LState.C⟩)))
    = some ⟨1, [0, 1, 2, 2, 1, 1, 0], 0, []⟩ := by decide

end Tests
