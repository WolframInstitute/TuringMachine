---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Wolfram's 2,3 Turing machine
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.wolfram23
Abstract: Two states and three colors: A0 -> 1RB, A1 -> 2LA, A2 -> 1LA, B0 -> 2LA, B1 -> 2RB, B2 -> 0RA. It never halts.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, BiTM.wolfram23]
Links: ["[BiTM.wolfram23 in the blueprint](https://wolframinstitute.github.io/TuringMachine/machine-model/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

The machine from a blank tape, drawn by the built-in [`RulePlot`]() (rule 596440 in Wolfram's numbering):

```wl
RulePlot[TuringMachine[{596440, 2, 3}], {1, {{}, 0}}, 200, ImageSize -> 300]
```

The configuration that emulates the System 4 tape `{0, 2} * {}`:

```wl
w23 = System3ToWolfram23[System4ToSystem3[<|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>, 3, 3]]
```

The machine's run from it:

```wl
run = Wolfram23Evolution[w23, 300]
```

The run drawn:

```wl
ArrayPlot[PadRight[Join[Reverse[#[[2]]], {#[[3]]}, #[[4]]] & /@ run], ColorRules -> {0 -> White, 1 -> LightGray, 2 -> Gray}, ImageSize -> 300]
```
