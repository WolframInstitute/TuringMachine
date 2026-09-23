---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Wolfram's 2,3 Turing machine
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.wolfram23
Abstract: Two states and three colors: A0 -> 1RB, A1 -> 2LA, A2 -> 1LA, B0 -> 2LA, B1 -> 2RB, B2 -> 0RA. It never halts. Systems 3, 2 and 1 are Smith's relabelings of it: System 3 names the cells left of the head and the state differently, and each System 3 step is one or three steps of the machine.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, BiTM.wolfram23]
Links: ["[BiTM.wolfram23 in the blueprint](https://wolframinstitute.github.io/TuringMachine/machine-model/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## The machine

In state A reading 0 it writes 1, moves right and goes to B; reading 1 it writes 2 and moves left; reading 2 it writes 1 and moves left. In state B reading 0 it writes 2, moves left and goes to A; reading 1 it writes 2 and moves right; reading 2 it writes 0, moves right and goes to A. Its run from a blank tape, drawn by the built-in [`RulePlot`]() (rule 596440 in Wolfram's numbering):

```wl
RulePlot[TuringMachine[{596440, 2, 3}], {1, {{}, 0}}, 120, ImageSize -> 260]
```

The same run with the paclet's plot, the head red in state A and blue in state B:

```wl
Wolfram23EvolutionPlot[{1, {}, 0, {}}, 300, ImageSize -> 300]
```

## System 3 as wolfram23

Smith's System 3 is the same machine seen through a relabeling: the cells left of the head have 1 and 2 swapped, and so has the head cell in state A; System 3's third state C is state B with the head cell swapped. The wolfram23 configuration of a System 3 tape (the tape of `{0, 2} * {}` of the companion notebook):

```wl
tape3 = System4ToSystem3[<|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>, 3, 3]
```

```wl
System3ToWolfram23[tape3]
```

The run of System 3 and the run of wolfram23 from it, side by side; each System 3 step is one or three steps of wolfram23, so the second run is longer, but they pass through the same tapes up to the relabeling:

```wl
{System3EvolutionPlot[tape3, 30, ImageSize -> 220], Wolfram23EvolutionPlot[System3ToWolfram23[tape3], 60, ImageSize -> 220]}
```
