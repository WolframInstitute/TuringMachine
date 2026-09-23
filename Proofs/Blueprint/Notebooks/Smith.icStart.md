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

The functions come from the paclet `WolframInstitute/TuringMachine`:

```wl
#| eval: false
PacletInstall["https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/WolframInstitute__TuringMachine.paclet"];
Needs["WolframInstitute`TuringMachine`"]
```

The parameters of Smith's p. 33 program from the runs:

```wl
EmulationParameters[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>]
```

The same in closed form:

```wl
EmulationParameters[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>, "ClosedForm"]
```
