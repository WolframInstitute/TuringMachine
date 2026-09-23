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

The functions come from the paclet `WolframInstitute/TuringMachine`:

```wl
#| eval: false
PacletInstall["https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/WolframInstitute__TuringMachine.paclet"];
Needs["WolframInstitute`TuringMachine`"]
```

A small System 4 tape:

```wl
s4 = System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1]
```

Its configurations with the head back at the left end in state B:

```wl
events4 = System4Evolution[s4, 1000, #["Active"] == 0 && #["State"] === "B" &]
```

Their decodes:

```wl
System4ToSystem5[#, 20] & /@ Values[events4]
```

The wolfram23 configuration of the tape with blocks of width 128:

```wl
w23 = System3ToWolfram23[System4ToSystem3[s4, 7, 120]]
```

Its first six returns to the left end in state B:

```wl
events23 = Take[Wolfram23Evolution[w23, 50000, #1 == 2 && #2 == 123 &], 6]
```

Their decodes:

```wl
Wolfram23ToSystem5[#, 7, 20] & /@ Values[events23]
```
