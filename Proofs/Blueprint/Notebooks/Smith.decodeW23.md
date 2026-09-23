---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Reading the bag off wolfram23
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.decodeW23
Abstract: When wolfram23 is back at the left end of its tape in state B, the cells from the head to the first 0 are the blocks of the leading sets of System 4. Their XOR, read by parity scans, is the parity set, and its even elements x are the System 5 bag elements x/2 + 1.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, Smith.decodeW23]
Links: ["[Smith.decodeW23 in the blueprint](https://wolframinstitute.github.io/TuringMachine/conjecture0/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## The tape

A small System 5 program, as a System 4 tape with `f = 1`:

```wl
tape4 = System5ToSystem4[System5[{1, 3}, {{1}, {}}], 1]
```

Its wolfram23 tape has blocks of width `2^7` and a left end of 120 zeros; its length in cells:

```wl
Length[Flatten[Rest[System3ToWolfram23[System4ToSystem3[tape4, 7, 120]]]]]
```

The run of wolfram23, one row every 150 steps; the head is colored by the state:

```wl
Wolfram23EvolutionPlot[System3ToWolfram23[System4ToSystem3[tape4, 7, 120]], 60000, ImageSize -> 420]
```

## The decoder

At a time when wolfram23 is back at the left end of the tape in state B, the decoder takes the cells from the head up to the first 0, cuts them into blocks of `2^7`, XORs the blocks, reads the parity after each of the first scans (see the companion notebook on sets as blocks) and turns every even `x` with odd parity into the bag element `x / 2 + 1`. The System 4 tape decoded at its own left-end turns:

```wl
System4ToSystem5[#, 20] & /@ Values[System4Evolution[tape4, 1000, #["Active"] == 0 && #["State"] === "B" &]]
```

wolfram23 decoded at its first six returns to the left end in state B, 123 cells from the edge (the left end has 120 zeros and `221`):

```wl
Wolfram23ToSystem5[#, 7, 20] & /@ Values[Take[Wolfram23Evolution[System3ToWolfram23[System4ToSystem3[tape4, 7, 120]], 50000, #1 == 2 && #2 == 123 &], 6]]
```

The two agree, including the returns at which the leading sets are not a bag.
