---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: One machine step as tag rounds
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration TagSystem.tm_step_tag
Abstract: Each machine step is three rounds of tag steps for a move to the right and five for a move to the left; at the end of the rounds the tag word is the word of the next configuration.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, TagSystem.tm_step_tag]
Links: ["[TagSystem.tm_step_tag in the blueprint](https://wolframinstitute.github.io/TuringMachine/tm-to-cts/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
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

The length of the tag word along the run, the ends of the machine steps marked:

```wl
With[{tag = TuringMachineToTagSystem[machine, config, 4]},
    ListLinePlot[Length /@ TagSystemEvolution[tag, 85], GridLines -> {tag["TagTimes"], None}, ImageSize -> 420]]
```

At those tag times the words decode to the configurations of the machine:

```wl
With[{tag = TuringMachineToTagSystem[machine, config, 4]},
    TagSystemToTuringMachine[#, 3] & /@ TagSystemEvolution[tag, 85][[tag["TagTimes"] + 1]]]
```
