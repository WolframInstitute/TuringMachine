---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The run of System 5
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.System5.step
Abstract: Every step decrements the bag and increments the rules; an element reaching 0 is removed and the next rule is merged into the bag with parity.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, BiTM.System5.step]
Links: ["[BiTM.System5.step in the blueprint](https://wolframinstitute.github.io/TuringMachine/cts-to-system5/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

Smith's System 5 program of p. 33:

```wl
program = <|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>
```

The run of Smith's program of p. 33: the bag drifts down by one per step, and each pop merges a rule into it:

```wl
System5EvolutionPlot[program, 20, ImageSize -> 420]
```
