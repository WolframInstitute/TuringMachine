---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The System 5 run bound
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.System5.run_bound
Abstract: A System 5 run from the encoder's output with r rules and integers at most B has at most B 2^r steps.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, Smith.System5.run_bound]
Links: ["[Smith.System5.run_bound in the blueprint](https://wolframinstitute.github.io/TuringMachine/conjecture0/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

Smith's cyclic tag system `1 10` on the working string `01` (p. 29):

```wl
cts = <|"Appendants" -> {{1}, {1, 0}}, "Data" -> {0, 1}, "Phase" -> 0|>
```

The run lengths of the programs of Smith's p. 29 example for one to six cycles, against the bound `B 2^r`:

```wl
With[{ps = Table[CyclicTagSystemToSystem5[cts, n], {n, 6}]},
    ListLogPlot[{System5Evolution[#, Infinity, "Length"] & /@ ps, Max[Flatten[{#["Bag"], #["Rules"]}]] 2^Length[#["Rules"]] & /@ ps},
        Joined -> True, PlotMarkers -> Automatic, PlotLegends -> {"run length", "bound"}, AxesLabel -> {"cycles", None}, ImageSize -> 420]]
```
