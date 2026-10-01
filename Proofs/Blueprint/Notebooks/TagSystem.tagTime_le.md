---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: How many tag steps a machine step takes
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration TagSystem.tagTime_le
Abstract: A machine step takes three rounds of the tag system (five for a move to the left), and a round takes as many tag steps as the word has symbol pairs, which is about the two tape halves written in unary: at most 15 2^(sz c) for a configuration with sz c explicit cells. The tape grows by at most a cell per step, so n steps take at most n 15 2^(sz c + n) tag steps.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, TagSystem.tagTime_le]
Links: ["[TagSystem.tagTime_le in the blueprint](https://wolframinstitute.github.io/TuringMachine/universality/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## Round lengths

The word of a configuration spells the left half `m` and the right number `N` in unary, so it has about `m + N` pairs and a round takes about that many steps. Both numbers are below `2^(sz c + 1)` for a configuration with `sz c` explicit cells. The machine of the companion notebooks:

```wl
machine = {{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}
```

Its tag system from `011`, with the tag times of six steps:

```wl
tag = TuringMachineToTagSystem[machine, {1, {}, 0, {1, 1}}, 6]
```

The machine's run, for the tape sizes:

```wl
TuringMachineEvolutionPlot[machine, {1, {}, 0, {1, 1}}, 6, ImageSize -> 240]
```

The tag times against the bound `15 n 2^(n + 2)` (two explicit cells to start with):

```wl
ListLogPlot[{tag["TagTimes"], Table[n 15 2^(2 + n), {n, 0, 6}]},
    Joined -> True, PlotMarkers -> Automatic, PlotLegends -> {"tag time", "bound"}, AxesLabel -> {"machine steps", None}, ImageSize -> 420]
```

The bound is exponential in the number of steps because the numbers are written in unary: this is the cost of the Cocke-Minsky construction, not of Smith's.
