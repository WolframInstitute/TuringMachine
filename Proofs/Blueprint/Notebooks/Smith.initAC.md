---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: How System 4 becomes System 3
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.initAC
Abstract: System 3 writes each set of the System 4 tape as a block of 2^w cells and each star as a 0, with a left end 0^h 2 2 1 and a closing 1. Its head scans a block in state B or C, which decrements the set, and leaves the block in the state given by the parity, which says whether the set held 0: exactly System 4's rule for a set.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, Smith.initAC]
Links: ["[Smith.initAC in the blueprint](https://wolframinstitute.github.io/TuringMachine/system4-to-system3/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## The tape

The System 4 tape `{0, 2} * {}`, the head on the first set in state A:

```wl
tape4 = <|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>
```

Its System 3 tape with blocks of width `2^3` and a left end of 3 zeros:

```wl
tape3 = System4ToSystem3[tape4, 3, 3]
```

Reading it from the left: the left end `000221`, the block of `{0, 2}` (its first cell under the head), a 0 for the star, the block of the empty set without its first cell, and the closing 1:

```wl
Join[Reverse[tape3["Left"]], {tape3["Head"]}, tape3["Right"]]
```

The blocks are those of the companion notebook on sets as blocks:

```wl
{ParityBlock[{0, 2}, 3], ParityBlock[{}, 3]}
```

## A System 4 step as a scan

System 3's head walks over a block in state B or C and replaces each cell by the running parity: after the scan the block is that of the set decremented, and the head leaves in B or C according to the parity of the block, that is according to whether the set held 0. That is System 4's rule for a set: decrement, and switch between B and C if a 0 was removed. Stars are 0 cells, which the head handles with the rules for 0.

The run of System 4:

```wl
System4EvolutionPlot[tape4, 10]
```

The run of System 3 on the tape; cells 1 gray, 2 black, the head red in state A, blue in B and orange in C:

```wl
System3EvolutionPlot[tape3, 150, ImageSize -> 360]
```

The head turns at the left end, scans the first block (the set `{0, 2}` holds 0, so it leaves in state C), steps over the 0 of the star, scans the next block, and leaves the tape to the right on the closing 1.

## A bigger tape

A System 4 tape with 19 elements and blocks of width 128, sampled:

```wl
System3EvolutionPlot[System4ToSystem3[System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1], 7, 120], 20000, ImageSize -> 420]
```
