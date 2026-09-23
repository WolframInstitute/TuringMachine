---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Smith's System 5 encoder
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.ctsToSystem5
Abstract: A cyclic tag system as a System 5 program: the working string becomes a bag of integers, each appendant four rules, repeated for a number of cycles.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, BiTM.ctsToSystem5]
Links: ["[BiTM.ctsToSystem5 in the blueprint](https://wolframinstitute.github.io/TuringMachine/cts-to-system5/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

Smith's cyclic tag system `1 10` on the working string `01` (p. 29):

```wl
cts = <|"Appendants" -> {{1}, {1, 0}}, "Data" -> {0, 1}, "Phase" -> 0|>
```

Smith's example of p. 29, the cyclic tag system `1 10` on the working string `01`, as a System 5 program for one cycle:

```wl
CyclicTagSystemToSystem5[cts, 1]
```

The run of the program for two cycles; each row is the bag at a step, red after a rule is popped:

```wl
System5EvolutionPlot[CyclicTagSystemToSystem5[cts, 2], 1000, ImageSize -> 420]
```
