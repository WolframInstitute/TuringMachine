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

The System 4 tapes of Smith's p. 33 program for f from 1 to 3:

```wl
tapes = Table[System5ToSystem4[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>, f], {f, 3}]
```

Their run lengths:

```wl
Length[System4Evolution[#, 10^6]] - 1 & /@ tapes
```

The bounds `(2 L + 2) (L + 1)`:

```wl
With[{l = Length[#["Elements"]]}, (2 l + 2) (l + 1)] & /@ tapes
```
