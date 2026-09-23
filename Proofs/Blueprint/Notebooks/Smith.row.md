---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Sets as blocks of cells
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.row
Abstract: System 3 stores a set of integers as a block of 2^w cells, 1s and 2s. A scan of the block from left to right replaces each cell by the running parity of the 2s so far; the parity of the whole block after k scans says whether k is in the set. The block of a set is built from the rows of the rule 60 cellular automaton: a scan takes row i to row i - 1, so the XOR of the rows of the elements counts down to each of them.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, Smith.row]
Links: ["[Smith.row in the blueprint](https://wolframinstitute.github.io/TuringMachine/system4-to-system3/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## A scan

A block is a list of cells 1 and 2; read 2 as a bit 1 and 1 as a bit 0. A scan replaces each cell by the parity of the 2s up to and including it. That is what System 3's head does when it passes over a block in state B: the state it leaves in is the parity of the whole block.

## One-element sets

The blocks are built from the rows of the rule 60 cellular automaton started from a single 2 followed by 1s: each row is the previous one XOR itself shifted right by one cell, so cell `j` of row `i` is the binomial coefficient `C(i, j)` mod 2. The rows at width 32, 2 drawn dark:

```wl
ArrayPlot[CellularAutomaton[60, {{1}, 0}, {31, {0, 31}}], ImageSize -> 300]
```

A scan takes row `i` back to row `i - 1` (by Pascal's rule, the prefix XOR of row `i` is row `i - 1`), and only row 0, a single 2, has odd parity. So after `k` scans row `i` has odd parity exactly when `k = i`: the row counts down to its index.

## Any set

Scans and parities are linear, so the XOR of the rows of the elements of a set has, after `k` scans, odd parity exactly when `k` is in the set. Smith's block for the set adds the all-2 row, which is the last row of the window of `2^w`, and when the block would not start with a 2 also the row before it. The block of `{0, 2}` at width `2^3`:

```wl
ParityBlock[{0, 2}, 3]
```

Its successive scans, a 2 drawn dark, one scan per row:

```wl
ArrayPlot[NestList[Mod[Accumulate[#], 2] &, ParityBlock[{0, 2}, 3] - 1, 7], Mesh -> All, ImageSize -> 200]
```

The parity of each row is the membership of 0, 1, 2, ... in `{0, 2}`:

```wl
Mod[Total /@ NestList[Mod[Accumulate[#], 2] &, ParityBlock[{0, 2}, 3] - 1, 7], 2]
```

Those two added rows count down from the end of the window, so they change only the parities of the last two of the `2^w` scans; the sets of the emulation never get there, because the width is chosen above the length of the run. The block of `{1}`, for comparison:

```wl
Mod[Total /@ NestList[Mod[Accumulate[#], 2] &, ParityBlock[{1}, 3] - 1, 7], 2]
```
