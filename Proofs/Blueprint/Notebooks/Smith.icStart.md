---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The closed-form parameters
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.icStart
Abstract: The initial condition of the proof takes every run length from a bound, so that it is a definition that runs no system. The bounds are far larger than the runs.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, Smith.icStart]
Links: ["[Smith.icStart in the blueprint](https://wolframinstitute.github.io/TuringMachine/conjecture0/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

Smith's System 5 program of p. 33:

```wl
program = <|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>
```

The parameters of Smith's p. 33 program from its runs:

```wl
EmulationParameters[program]
```

The same in closed form:

```wl
EmulationParameters[program, "ClosedForm"]
```

Side by side, on a log scale:

```wl
With[{exact = EmulationParameters[program], closed = EmulationParameters[program, "ClosedForm"]},
    BarChart[Transpose[{Values[exact], Values[closed]}], ScalingFunctions -> "Log", ChartLabels -> {Placed[Keys[exact], Axis, Rotate[#, Pi/2] &], None},
        ChartLegends -> {"from the runs", "closed form"}, ImageSize -> 420]]
```
