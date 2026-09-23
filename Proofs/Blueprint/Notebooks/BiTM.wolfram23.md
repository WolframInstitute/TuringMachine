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

The System 4 tape `{0, 2} * {}`:

```wl
tape4 = <|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>
```

The machine from a blank tape, the head red in state A and blue in state B:

```wl
Wolfram23EvolutionPlot[{1, {}, 0, {}}, 300, ImageSize -> 360]
```

The machine on the tape that emulates the System 4 tape `{0, 2} * {}`:

```wl
Wolfram23EvolutionPlot[System3ToWolfram23[System4ToSystem3[tape4, 3, 3]], 300, ImageSize -> 420]
```
