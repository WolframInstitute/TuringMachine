---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The run of System 4
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.System4.step
Abstract: In state A the head moves left, deleting stars; at the left end it turns and sweeps right in states B and C, decrementing every set it passes.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, BiTM.System4.step]
Links: ["[BiTM.System4.step in the blueprint](https://wolframinstitute.github.io/TuringMachine/system5-to-system4/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

Smith's System 5 program of p. 33:

```wl
program = <|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>
```

The run of Smith's program of p. 33 as a System 4 tape with f = 2; the head sweeps left in state A and right in B and C, and each sweep deletes stars:

```wl
System4EvolutionPlot[System5ToSystem4[program, 2], 3000, ImageSize -> 420]
```
