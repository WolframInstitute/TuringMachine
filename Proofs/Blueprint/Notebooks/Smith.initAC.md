---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The System 3 tape
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.initAC
Abstract: Each set of the System 4 tape becomes a block of 2^w cells whose parity scans give the set, each star a 0, with a left end 0^h 2 2 1 and a closing 1.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, Smith.initAC]
Links: ["[Smith.initAC in the blueprint](https://wolframinstitute.github.io/TuringMachine/system4-to-system3/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

The System 3 tape of `{0, 2} * {}` with blocks of width 8:

```wl
s3 = System4ToSystem3[<|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>, 3, 3]
```

Its run:

```wl
run = System3Evolution[s3, 120]
```

The run drawn, one row per step:

```wl
ArrayPlot[PadRight[Join[Reverse[#["Left"]], {#["Head"]}, #["Right"]] & /@ run], ColorRules -> {0 -> White, 1 -> LightGray, 2 -> Gray}, ImageSize -> 300]
```
