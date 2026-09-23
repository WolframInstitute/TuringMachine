---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: How large IC is
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.IC
Abstract: The initial condition for n steps of a machine goes through every stage of the chain. The stages up to System 5 can be built; the later ones are far too large and are computed only in size.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, Smith.IC]
Links: ["[Smith.IC in the blueprint](https://wolframinstitute.github.io/TuringMachine/universality/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet `WolframInstitute/TuringMachine`:

```wl
#| eval: false
PacletInstall["https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/WolframInstitute__TuringMachine.paclet"];
Needs["WolframInstitute`TuringMachine`"]
```

The sizes for one step of a two-state machine that writes 1, moves right and halts:

```wl
EmulationSizes[{{1, 0} -> {0, 1, 1}}, {1, {}, 0, {}}, 1]
```
