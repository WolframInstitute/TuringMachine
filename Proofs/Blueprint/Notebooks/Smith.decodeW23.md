---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Reading the bag off wolfram23
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.decodeW23
Abstract: At the times the proof schedules, when wolfram23 is back at the left end of its tape in state B, the blocks from the head to the first 0 decode to the bag that System 4 holds at the matching step.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, Smith.decodeW23]
Links: ["[Smith.decodeW23 in the blueprint](https://wolframinstitute.github.io/TuringMachine/conjecture0/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

A small System 5 program:

```wl
small = <|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>
```

A small System 4 tape run by wolfram23 on blocks of width 128, the run sampled:

```wl
Wolfram23EvolutionPlot[System3ToWolfram23[System4ToSystem3[System5ToSystem4[small, 1], 7, 120]], 60000, ImageSize -> 420]
```

The System 4 decodes each time its head is back at the left end in state B:

```wl
System4ToSystem5[#, 20] & /@ Values[System4Evolution[System5ToSystem4[small, 1], 1000, #["Active"] == 0 && #["State"] === "B" &]]
```

The wolfram23 decodes at its first six returns to the left end in state B:

```wl
Wolfram23ToSystem5[#, 7, 20] & /@ Values[Take[Wolfram23Evolution[
    System3ToWolfram23[System4ToSystem3[System5ToSystem4[small, 1], 7, 120]], 50000, #1 == 2 && #2 == 123 &], 6]]
```
