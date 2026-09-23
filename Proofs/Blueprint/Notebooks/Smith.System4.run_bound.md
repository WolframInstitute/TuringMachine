---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The System 4 run bound
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.System4.run_bound
Abstract: System 4 always halts: a run from a tape of length L has at most (2L + 2)(L + 1) steps, by a measure that drops at every step.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, Smith.System4.run_bound]
Links: ["[Smith.System4.run_bound in the blueprint](https://wolframinstitute.github.io/TuringMachine/conjecture0/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

Smith's System 5 program of p. 33:

```wl
program = <|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>
```

The run lengths of the System 4 tapes of Smith's p. 33 program for f from 1 to 4, against the bound `(2 L + 2) (L + 1)`:

```wl
With[{ts = Table[System5ToSystem4[program, f], {f, 4}]},
    ListLogPlot[{Length[System4Evolution[#, 10^6]] - 1 & /@ ts, With[{l = Length[#["Elements"]]}, (2 l + 2) (l + 1)] & /@ ts},
        Joined -> True, PlotMarkers -> Automatic, PlotLegends -> {"run length", "bound"}, AxesLabel -> {"f", None}, ImageSize -> 420]]
```
