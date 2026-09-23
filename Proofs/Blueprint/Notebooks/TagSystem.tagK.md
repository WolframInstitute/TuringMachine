---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The Cocke-Minsky tag system
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration TagSystem.tagK
Abstract: A binary Turing machine as a 2-tag system: each configuration is a word spelling its two tape halves in unary, and every machine step is a few rounds of tag steps.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, TagSystem.tagK]
Links: ["[TagSystem.tagK in the blueprint](https://wolframinstitute.github.io/TuringMachine/tm-to-cts/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

A three-state binary machine that moves both ways:

```wl
machine = {{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}
```

Started on the tape `0 1 1`:

```wl
config = {1, {}, 0, {1, 1}}
```

The tag system of a three-state machine started on the tape `0 1 1`, run for its first four machine steps; each row is a tag word at its place in the queue, each color a kind of symbol:

```wl
TagSystemEvolutionPlot[TuringMachineToTagSystem[machine, config], 85, ImageSize -> 420]
```

The alphabet has `1 + 84 s` symbols for states below `s`:

```wl
Length[TuringMachineToTagSystem[machine]["Productions"]]
```
