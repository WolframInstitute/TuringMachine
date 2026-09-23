---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The System 4 tape of a System 5 program
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.system5ToSystem4
Abstract: The bag becomes one set, followed by f star and empty-set pairs and a block of 8f elements for each rule.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, BiTM.system5ToSystem4]
Links: ["[BiTM.system5ToSystem4 in the blueprint](https://wolframinstitute.github.io/TuringMachine/system5-to-system4/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

A small System 5 program:

```wl
small = <|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>
```

A one-rule program as a System 4 tape with f = 1: the bag set, a star and empty set, then the rule blocks:

```wl
System5ToSystem4[small, 1]["Elements"]
```

The run of the tape; stars are black, sets gray (empty ones light), and the active element is colored by the state (A red, B blue, C orange):

```wl
System4EvolutionPlot[System5ToSystem4[small, 1], 200, ImageSize -> 420]
```
