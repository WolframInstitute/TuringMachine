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

The functions come from the paclet `WolframInstitute/TuringMachine`:

```wl
#| eval: false
PacletInstall["https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/WolframInstitute__TuringMachine.paclet"];
Needs["WolframInstitute`TuringMachine`"]
```

The tag system of a three-state machine, with the tag times of its first four steps:

```wl
tag = TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}, 4]
```

The words at the tag times:

```wl
words = TagSystemEvolution[tag, 85][[tag["TagTimes"] + 1]]
```

Each decodes to the configuration of the machine after that many steps:

```wl
TagSystemToTuringMachine[#, 3] & /@ words
```

The word length along the run, the tag times marked:

```wl
ListLinePlot[Length /@ TagSystemEvolution[tag, 85], GridLines -> {tag["TagTimes"], None}, ImageSize -> 360]
```
