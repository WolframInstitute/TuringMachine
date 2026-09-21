/-
  Tests.InfiniteVectors

  Regression tests of the block construction of `Smith.Infinite` (T6, M7) on
  a small program: the program of D9 (`Tests.SmithVectors`), `{0, 2} * {}`,
  whose System 4 run lasts 4 steps, exits in state C and never turns at its
  left end. The block around it has the guard parameter `n = 7` and `r = 5`
  guards, as `block_exists` would choose (`n = T4 + 3`, `r = T4 + 1`), the
  width `2^5` and the band 4.

  Everything closes by `decide +kernel` (kernel reduction, no extra axiom);
  nothing outside this file depends on it.

  Vectors:
    * E1  the System 4 run of the block: entry, exit, stuck alone
    * E2  the System 3 run of the block from `entry3`: decode, exit
    * E3  two blocks chained: `start3`, the decodes and the exit of each
    * E4  wolfram23 on `startFin`: the decodes, the size invariant, the exit
    * E5  the infinite tape: `tape`, `istart`, `truncI` decodes as `startFin`
-/

import Smith.Infinite

namespace Tests

open TM
open BiTM
open Smith

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

/-- No step before the exit moves left from an empty left tape. -/
example : (List.range 917).all (fun τ => (BiTM.nSteps wolfram23 (startFin bdsE 1) τ).all
    (fun c => c.left != [] || (wolfram23.transition c.state c.head).dir == Dir.R)) = true := by
  decide +kernel

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

/-- Past the exit of block 1 the infinite run enters block 2 instead of
    leaving the tape: at time 918 the head is on block 2's first cell, a 2. -/
example : (inSteps wolfram23 (istart (tape bdsE)) 918).map
    (fun d => (d.state, d.left.length, d.head)) = some (2, 450, 2) := by decide +kernel

end Tests
