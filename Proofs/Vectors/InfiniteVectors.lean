/-
  Vectors.InfiniteVectors

  Regression tests of the block construction of `Smith.Infinite` (T6, M7) on
  two small programs. E1 to E5: the program of D9 (`Vectors.SmithVectors`),
  `{0, 2} * {}`, whose System 4 run lasts 4 steps, exits in state C and never
  turns at its left end; the block around it has the guard parameter `n = 7`
  and `r = 5` guards, as `block_exists` would choose (`n = T4 + 3`,
  `r = T4 + 1`), the width `2^5` and the band 4. E6: the program
  `{0} {0, 1} * {2}`, whose run of 9 steps turns once at its left end, so
  that a guard is consumed (`pad_turn`, `merged`). E7: two blocks of
  different widths chained. E8: the side conditions of `BlockSpec` and the
  halting reading of the block index.

  Everything closes by `decide +kernel` (kernel reduction, no extra axiom)
  or `decide`; nothing outside this file depends on it.

  Vectors:
    * E1  the System 4 run of the block: entry, exit, stuck alone
    * E2  the System 3 run of the block from `entry3`: decode, exit
    * E3  two blocks chained: `start3`, the decodes and the exit of each
    * E4  wolfram23 on `startFin`: the decodes, the size invariant, the exit
    * E5  the infinite tape: `tape`, `istart`, `truncI` decodes as `startFin`
    * E6  a block whose program turns: the guard consumed, the exit
    * E7  two blocks of different widths: `segCells`, `tape`, the decodes
    * E8  `BlockSpec`'s side conditions, the decode at `dt 0`, a halting machine
-/

import Smith.Infinite
import Vectors.TMToCTSVectors

namespace Tests

open TM
open BiTM
open Smith

/-! ## Helpers: a predicate along a run, in one pass -/

/-- `P` at every configuration of the first `k` steps of the System 3 run
    from `c`; a run that ends early fails. -/
def allSteps3 (P : LConfig → Bool) : LConfig → Nat → Bool
  | c, 0 => P c
  | c, k + 1 => P c && match lstep sys3 c with
    | none => false
    | some c' => allSteps3 P c' k

/-- The same along a wolfram23 run. -/
def allStepsW (P : BiTM.Config → Bool) : BiTM.Config → Nat → Bool
  | c, 0 => P c
  | c, k + 1 => P c && match BiTM.step wolfram23 c with
    | none => false
    | some c' => allStepsW P c' k

/-- The same along a run on the infinite tape. -/
def allStepsI (P : IConfig → Bool) : IConfig → Nat → Bool
  | d, 0 => P d
  | d, k + 1 => P d && match istep wolfram23 d with
    | none => false
    | some d' => allStepsI P d' k

/-! ## The block -/

/-- The block of D9's program: `n = 7`, `r = 5`, width `2^5`, band 4, the
    truncated System 4 run of 13 steps, one decode time (the entry). -/
def bdE : BlockData := ⟨7, 5, 5, 4, [0, 2], [System4Elem.star, System4Elem.set []], 13, fun _ => 10⟩

/-- The constant sequence of blocks. -/
def bdsE : Nat → BlockData := fun _ => bdE

example : bdE.tape = [System4Elem.star, System4Elem.set [1, 7], System4Elem.star,
    System4Elem.set [1, 7], System4Elem.star, System4Elem.set [1, 7], System4Elem.star,
    System4Elem.set [1, 7], System4Elem.star, System4Elem.set [0, 1, 6],
    System4Elem.set [0, 2], System4Elem.star, System4Elem.set []] := by decide +kernel

example : bdE.cells.length = 224 := by decide +kernel

/-! ## E1: the System 4 run of the block -/

/-- The program alone: 4 steps to the exit in state C. -/
example : System4.nSteps ⟨bdE.orig, 0, System4State.A⟩ 4
    = some ⟨[System4Elem.set [1], System4Elem.star, System4Elem.set [0]], 3, System4State.C⟩ := by
  decide +kernel

/-- The entry: `2 r = 10` steps through the guards to the program's first
    set in state B, the guards now `{6}` and the innermost `{5}`. -/
example : System4.nSteps ⟨bdE.tape, 0, System4State.C⟩ 10
    = some (padCfg 7 5 0 [System4Elem.star] [] ⟨bdE.orig, 0, System4State.B⟩) := by decide +kernel

example : (System4.nSteps ⟨bdE.tape, 0, System4State.C⟩ 10).map (fun c => (c.elems, c.active, c.state))
    = some ([System4Elem.star, System4Elem.set [6], System4Elem.star, System4Elem.set [6],
        System4Elem.star, System4Elem.set [6], System4Elem.star, System4Elem.set [6],
        System4Elem.star, System4Elem.set [5], System4Elem.set [0, 2], System4Elem.star,
        System4Elem.set []], 10, System4State.B) := by decide +kernel

/-- The exit at `H = 13`: the program's exit configuration padded, the head
    past the last element in state C. -/
example : System4.nSteps ⟨bdE.tape, 0, System4State.C⟩ 13
    = some (padCfg 7 5 0 [System4Elem.star] []
        ⟨[System4Elem.set [1], System4Elem.star, System4Elem.set [0]], 3, System4State.C⟩) := by
  decide +kernel

example : (System4.nSteps ⟨bdE.tape, 0, System4State.C⟩ 13).map
    (fun c => (c.active == c.elems.length, c.state)) = some (true, System4State.C) := by decide +kernel

/-- Alone, the block is stuck at its exit; in the chain, the next block's
    leading star is where the head lands. -/
example : System4.nSteps ⟨bdE.tape, 0, System4State.C⟩ 14 = none := by decide +kernel

/-- The head is on the leading star only at time 0 (`SafeC`). -/
example : (List.range 14).all (fun j => (System4.nSteps ⟨bdE.tape, 0, System4State.C⟩ j).all
    (fun c => c.active != 0 || c.state == System4State.C)) = true := by decide +kernel

/-! ## E2: the System 3 run of the block -/

/-- The entry configuration: a 0 left of the head, the block's cells and
    nothing after them. -/
example : entry3 [] bdE [] = ⟨[0], 0, bdE.cells, LState.A⟩ := by decide +kernel

/-- After 160 steps (32 per System 4 step of the entry through the five
    guards) the head has turned on the program's first set: the tape decodes
    to the word `0` (D9). -/
example : (lnSteps sys3 (entry3 [] bdE []) 160).map
    (fun c => (c.head, c.state, decodeW23 32 4 (toBi (phi2 (phi3 c)))))
    = some (2, LState.B, some [false]) := by decide +kernel

/-- The exit at 224 steps: the head on the closing 0 in state A with a 0 to
    its left, nothing to its right (`rep3_exit_zero`). -/
example : (lnSteps sys3 (entry3 [] bdE []) 224).map
    (fun c => (c.head, c.state, c.right, c.left.head?, c.left.length))
    = some (0, LState.A, [], some 0, 225) := by decide +kernel

example : lnSteps sys3 (entry3 [] bdE []) 225 = none := by decide +kernel

/-! ## E3: two blocks chained -/

example : segCells bdsE 0 2 = bdE.cells ++ bdE.cells := by decide +kernel

example : start3 bdsE 1 = ⟨[], 2, 0 :: (bdE.cells ++ bdE.cells), LState.B⟩ := by decide +kernel

/-- The first step enters block 0. -/
example : lnSteps sys3 (start3 bdsE 1) 1 = some (entry3 [] bdE bdE.cells) := by decide +kernel

/-- Block 0 decodes at `1 + 160`, exits at `1 + 224` onto block 1's entry;
    block 1 decodes at `1 + 224 + 160` and exits at `1 + 448`. -/
example : (lnSteps sys3 (start3 bdsE 1) 161).map
    (fun c => (c.head, c.state, decodeW23 32 4 (toBi (phi2 (phi3 c)))))
    = some (2, LState.B, some [false]) := by decide +kernel

example : (lnSteps sys3 (start3 bdsE 1) 225).map
    (fun c => (c.head, c.state, c.right.length, c.left.head?, c.left.length))
    = some (0, LState.A, 224, some 0, 225) := by decide +kernel

example : (lnSteps sys3 (start3 bdsE 1) 385).map
    (fun c => (c.head, c.state, decodeW23 32 4 (toBi (phi2 (phi3 c)))))
    = some (2, LState.B, some [false]) := by decide +kernel

example : (lnSteps sys3 (start3 bdsE 1) 449).map
    (fun c => (c.head, c.state, c.right, c.left.head?, c.left.length))
    = some (0, LState.A, [], some 0, 449) := by decide +kernel

/-! ## E4: wolfram23 on the finite tape of the two blocks -/

example : startFin bdsE 1 = ⟨2, [], 2, 0 :: (bdE.cells ++ bdE.cells).map Fin.val⟩ := by decide +kernel

example : biSize (startFin bdsE 1) = 450 := by decide +kernel

/-- The decodes of blocks 0 and 1, at the System 0 times of the System 3
    times 161 and 385. -/
example : (BiTM.nSteps wolfram23 (startFin bdsE 1) 335).map
    (fun c => (c.state, c.left.length, decodeW23 32 4 c)) = some (2, 161, some [false]) := by decide +kernel

example : (BiTM.nSteps wolfram23 (startFin bdsE 1) 793).map
    (fun c => (c.state, c.left.length, decodeW23 32 4 c)) = some (2, 385, some [false]) := by decide +kernel

/-- The exit of block 1 at time 917: the head on the last cell, a 0, in
    state A; the run stays on the explicit tape until then and leaves it at
    the next step. -/
example : (BiTM.nSteps wolfram23 (startFin bdsE 1) 917).map
    (fun c => (c.state, c.head, c.right, c.left.length)) = some (1, 0, [], 449) := by decide +kernel

example : (List.range 918).all (fun τ => (BiTM.nSteps wolfram23 (startFin bdsE 1) τ).all
    (fun c => biSize c == 450)) = true := by decide +kernel

example : (BiTM.nSteps wolfram23 (startFin bdsE 1) 918).map biSize = some 451 := by decide +kernel

/-- No step before the exit moves left from an empty left tape; in fact the
    head is on the first cell only at time 0. -/
example : (List.range 917).all (fun τ => (BiTM.nSteps wolfram23 (startFin bdsE 1) τ).all
    (fun c => c.left != [] || (wolfram23.transition c.state c.head).dir == Dir.R)) = true := by
  decide +kernel

example : (BiTM.step wolfram23 (startFin bdsE 1)).map
    (fun c1 => allStepsW (fun c => c.left != []) c1 916) = some true := by decide +kernel

/-! ## E5: the infinite tape -/

/-- The cells: the 0 of the entry, then block 0 (first cell 2, closing 0 at
    224), then block 1 (first cell 2 at 225, closing 0 at 448), and so on. -/
example : (List.range 8).map (tape bdsE) = [0, 2, 1, 1, 1, 1, 1, 1] := by decide +kernel

example : (tape bdsE 224, tape bdsE 225, tape bdsE 448, tape bdsE 449) = (0, 2, 0, 2) := by decide +kernel

example : (List.range 450).all (fun i => tape bdsE i < 3) = true := by decide +kernel

/-- The finite start of two blocks is the first 449 cells of the infinite
    tape. -/
example : truncI 449 (istart (tape bdsE)) = startFin bdsE 1 := by decide +kernel

/-- The infinite run decodes as the finite one does, on a window of 64
    cells, which reaches the first 0 right of the head. -/
example : (inSteps wolfram23 (istart (tape bdsE)) 335).map
    (fun d => (d.state, d.left.length, decodeW23 32 4 (truncI 64 d))) = some (2, 161, some [false]) := by
  decide +kernel

example : (inSteps wolfram23 (istart (tape bdsE)) 793).map
    (fun d => (d.state, d.left.length, decodeW23 32 4 (truncI 64 d))) = some (2, 385, some [false]) := by
  decide +kernel

/-- The decodes on the theorem's own window, `W = biSize (startFin bd k) = 450`. -/
example : (inSteps wolfram23 (istart (tape bdsE)) 793).map
    (fun d => decodeW23 32 4 (truncI 450 d)) = some (some [false]) := by decide +kernel

/-- Window stability, the point of the theorem's "every larger window"
    clause: at 335 the first 0 right of the head is cell 31; the window of
    30 cells does not decode, and every window from 31 on decodes alike
    (a window ending inside the conglomerate acts as a terminator, which is
    why the clause quantifies over all larger windows). -/
example : (inSteps wolfram23 (istart (tape bdsE)) 335).map
    (fun d => (d.right 31, [30, 31, 32, 64].map fun W => decodeW23 32 4 (truncI W d)))
    = some (0, [none, some [false], some [false], some [false]]) := by decide +kernel

/-- The left-end clause has bite: on the all-zero tape wolfram23 is back on
    the first cell in state A at time 12 and moves left from it. -/
example : (inSteps wolfram23 (istart (fun _ => 0)) 12).map
    (fun d => (d.state, d.left, d.head, (wolfram23.transition d.state d.head).dir))
    = some (1, [], 1, Dir.L) := by decide

/-- Past the exit of block 1 the infinite run enters block 2 instead of
    leaving the tape: at time 918 the head is on block 2's first cell, a 2;
    the head is on the first cell only at time 0. -/
example : (inSteps wolfram23 (istart (tape bdsE)) 918).map
    (fun d => (d.state, d.left.length, d.head)) = some (2, 450, 2) := by decide +kernel

example : (istep wolfram23 (istart (tape bdsE))).map
    (fun d1 => allStepsI (fun d => d.left != []) d1 917) = some true := by decide +kernel

/-! ## E6: a block whose program turns at its left end -/

/-- The program `{0} {0, 1} * {2}` runs 9 steps, turns once (at its time 5,
    state A on its first element) and exits in state C. The block:
    `n = 12`, `r = 10`, width `2^6`, band 4. -/
def bdT : BlockData :=
  ⟨12, 10, 6, 4, [0], [System4Elem.set [0, 1], System4Elem.star, System4Elem.set [2]], 31, fun _ => 20⟩

example : System4.nSteps ⟨bdT.orig, 0, System4State.A⟩ 5
    = some ⟨[System4Elem.set [], System4Elem.set [0], System4Elem.set [2]], 0, System4State.A⟩ := by
  decide +kernel

example : System4.nSteps ⟨bdT.orig, 0, System4State.A⟩ 6
    = some ⟨[System4Elem.set [], System4Elem.set [0], System4Elem.set [2]], 0, System4State.B⟩ := by
  decide +kernel

example : System4.nSteps ⟨bdT.orig, 0, System4State.A⟩ 9
    = some ⟨[System4Elem.set [], System4Elem.set [], System4Elem.set [1]], 3, System4State.C⟩ := by
  decide +kernel

/-- The entry in `2 r = 20` steps. -/
example : System4.nSteps ⟨bdT.tape, 0, System4State.C⟩ 20
    = some (padCfg 12 10 0 [System4Elem.star] [] ⟨bdT.orig, 0, System4State.B⟩) := by decide +kernel

/-- The turn: the program's configuration at its time 5 padded with no turn
    at block time 24, and at its time 6 padded with one turn `2 * 0 + 4`
    steps later (`pad_turn`): the innermost guard `{10}` has lost its star
    and become `{9}` (`merged 12 1 = [{11}, {9}]`). -/
example : System4.nSteps ⟨bdT.tape, 0, System4State.C⟩ 24
    = some (padCfg 12 10 0 [System4Elem.star] []
        ⟨[System4Elem.set [], System4Elem.set [0], System4Elem.set [2]], 0, System4State.A⟩) := by
  decide +kernel

example : System4.nSteps ⟨bdT.tape, 0, System4State.C⟩ 28
    = some (padCfg 12 10 1 [System4Elem.star] []
        ⟨[System4Elem.set [], System4Elem.set [0], System4Elem.set [2]], 0, System4State.B⟩) := by
  decide +kernel

example : (System4.nSteps ⟨bdT.tape, 0, System4State.C⟩ 28).map (fun c => (c.elems.drop 17, c.active))
    = some ([System4Elem.set [11], System4Elem.set [9], System4Elem.set [], System4Elem.set [0],
        System4Elem.set [2]], 19) := by decide +kernel

/-- The exit at `H = 31` with one turn, stuck alone at 32, `SafeC`. -/
example : System4.nSteps ⟨bdT.tape, 0, System4State.C⟩ 31
    = some (padCfg 12 10 1 [System4Elem.star] []
        ⟨[System4Elem.set [], System4Elem.set [], System4Elem.set [1]], 3, System4State.C⟩) := by
  decide +kernel

example : System4.nSteps ⟨bdT.tape, 0, System4State.C⟩ 32 = none := by decide +kernel

example : (List.range 32).all (fun j => (System4.nSteps ⟨bdT.tape, 0, System4State.C⟩ j).all
    (fun c => c.active != 0 || c.state == System4State.C)) = true := by decide +kernel

/-- The System 3 run of the block: 832 cells, the exit after 1218 steps in
    the shape of `rep3_exit_zero`, the head on the leftmost cell only at
    time 0. -/
example : bdT.cells.length = 832 := by decide +kernel

example : (lnSteps sys3 (entry3 [] bdT []) 1218).map
    (fun c => (c.head, c.state, c.right, c.left.head?, c.left.length))
    = some (0, LState.A, [], some 0, 833) := by decide +kernel

example : lnSteps sys3 (entry3 [] bdT []) 1219 = none := by decide +kernel

example : (lstep sys3 (entry3 [] bdT [])).map
    (fun c1 => allSteps3 (fun c => 2 ≤ c.left.length) c1 1217) = some true := by decide +kernel

/-! ## E7: two blocks of different widths -/

/-- The block of E1 with width `2^6` instead of `2^5`: 448 cells. -/
def bdE6 : BlockData := ⟨7, 5, 6, 4, [0, 2], [System4Elem.star, System4Elem.set []], 13, fun _ => 10⟩

/-- Block 0 of width `2^5`, every later block of width `2^6`. -/
def bdsH : Nat → BlockData := fun j => if j = 0 then bdE else bdE6

example : bdE6.cells.length = 448 := by decide +kernel

example : segCells bdsH 0 2 = bdE.cells ++ bdE6.cells := by decide +kernel

example : (tape bdsH 224, tape bdsH 225, tape bdsH 672, tape bdsH 673) = (0, 2, 0, 2) := by decide +kernel

example : truncI 673 (istart (tape bdsH)) = startFin bdsH 1 := by decide +kernel

example : biSize (startFin bdsH 1) = 674 := by decide +kernel

/-- Block 0 decodes at 335 with width 32 (as E4); block 1 enters at 225,
    crosses its five guards of 64 cells and decodes at 1113 with width 64;
    its exit at 1365 is on the last cell in state A, and the run leaves the
    finite tape at the next step. -/
example : (BiTM.nSteps wolfram23 (startFin bdsH 1) 335).map
    (fun c => (c.state, c.left.length, decodeW23 32 4 c)) = some (2, 161, some [false]) := by decide +kernel

example : (BiTM.nSteps wolfram23 (startFin bdsH 1) 1113).map
    (fun c => (c.state, c.left.length, decodeW23 64 4 c)) = some (2, 545, some [false]) := by decide +kernel

example : (BiTM.nSteps wolfram23 (startFin bdsH 1) 1365).map
    (fun c => (c.state, c.head, c.right, c.left.length)) = some (1, 0, [], 673) := by decide +kernel

example : (BiTM.nSteps wolfram23 (startFin bdsH 1) 1366).map biSize = some 675 := by decide +kernel

/-- On the infinite tape the run continues into block 2 (width 64 again). -/
example : (inSteps wolfram23 (istart (tape bdsH)) 1113).map
    (fun d => (d.state, d.left.length, decodeW23 64 4 (truncI 674 d))) = some (2, 545, some [false]) := by
  decide +kernel

example : (inSteps wolfram23 (istart (tape bdsH)) 1366).map
    (fun d => (d.state, d.left.length, d.head)) = some (2, 674, 2) := by decide +kernel

/-! ## E8: the side conditions of `BlockSpec`, the decode at `dt 0`, halting -/

/-- The machine-independent conditions of `BlockSpec` on `bdE`. -/
example : System4Config.WellFormed ⟨bdE.orig, 0, System4State.A⟩ := by decide +kernel
example : bdE.orig.getLast? ≠ some System4Elem.star := by decide +kernel
example : 3 ≤ bdE.n ∧ bdE.fuel + 3 ≤ 2 ^ bdE.w ∧ bdE.n < 2 ^ bdE.w := by decide +kernel

/-- The System 4 decode at `dt 0 = 10`, the shape `hdec` asks for: the head on
    the program's first set in state B, the sets up to the star decoding
    with the band 4 to the word `0` (the word `rep3_decode` transports to the
    System 3 decode of E2 at 160). -/
example : (System4.nSteps ⟨bdE.tape, 0, System4State.C⟩ 10).bind
    (fun c => (decodeS4 ⟨c.elems.drop c.active, 0, System4State.B⟩ 4).bind decodeBag) = some [false] := by
  decide +kernel

/-- The halting reading of the block index: for `tmH` of
    `Vectors/TMToCTSVectors.lean`, which halts after one step, the last defined
    step below `j` is `min j 1`. -/
example : (List.range 6).map (fun j =>
    Nat.findGreatest (fun i => (BiTM.nSteps tmH ⟨1, [], 0, []⟩ i).isSome = true) j)
    = [0, 1, 1, 1, 1, 1] := by decide

/-- The theorem applies to `tmH` from `1, [], 0, []`: its hypotheses are
    decidable and hold. -/
example : True := by
  have := wolfram23_infinite tmH (by decide) ⟨1, [], 0, []⟩
    ⟨by decide, fun a ha => by simp at ha, fun a ha => by simp at ha⟩ (by decide)
  trivial

end Tests
