---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The tag time bound
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration TagSystem.tagTime_le
Abstract: n machine steps from a configuration with sz c explicit cells take at most n 15 2^(sz c + n) tag steps.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, TagSystem.tagTime_le]
Links: ["[TagSystem.tagTime_le in the blueprint](https://wolframinstitute.github.io/TuringMachine/universality/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet `WolframInstitute/TuringMachine`:

```wl
#| eval: false
PacletInstall["https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/WolframInstitute__TuringMachine.paclet"];
Needs["WolframInstitute`TuringMachine`"]
```

The tag system of a three-state machine with the tag times of its first six steps:

```wl
tag = TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}, 6]
```

The tag times against the bound, the configuration having two explicit cells:

```wl
ListLogPlot[{tag["TagTimes"], Table[n 15 2^(2 + n), {n, 0, 6}]}, Joined -> True, PlotLegends -> {"tag time", "bound"}, ImageSize -> 360]
```
