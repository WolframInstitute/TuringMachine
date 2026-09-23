---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The initial condition without running anything
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.icStart
Abstract: Every parameter of the emulation (f, the band, the fuel, the block width) depends on how long the System 5 and System 4 runs last. The proof replaces each run length by a bound computed from the program itself, so the initial tape is a definition that runs no system. The bounds are much larger than the runs.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, Smith.icStart]
Links: ["[Smith.icStart in the blueprint](https://wolframinstitute.github.io/TuringMachine/conjecture0/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## Parameters from the runs

Smith's System 5 program of p. 33:

```wl
program = <|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>
```

The parameters taken from its actual runs: `T5` and `T4` are the lengths of the System 5 and System 4 runs, `f` the System 4 parameter, `Band` the decoder's band, `Fuel` what the System 3 blocks must hold, `w` the block width exponent:

```wl
EmulationParameters[program]
```

## Parameters from the bounds

The same with `T5` replaced by `B 2^r` and `T4` by `(2 L + 2) (L + 1)` (see the companion notebooks on the two run bounds); the other parameters follow by the same formulas:

```wl
EmulationParameters[program, "ClosedForm"]
```

Side by side on a log scale:

```wl
With[{exact = EmulationParameters[program], closed = EmulationParameters[program, "ClosedForm"]},
    BarChart[Transpose[{Values[exact], Values[closed]}], ScalingFunctions -> "Log",
        ChartLabels -> {Placed[Keys[exact], Axis, Rotate[#, Pi/2] &], None}, ChartLegends -> {"from the runs", "closed form"}, ImageSize -> 420]]
```

The block width exponent `w` is the bit length of the fuel, so the System 3 tape grows only linearly with the bounds.
