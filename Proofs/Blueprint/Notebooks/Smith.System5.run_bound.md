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

The programs of a cyclic tag system for one to three cycles:

```wl
programs = Table[CyclicTagSystemToSystem5[<|"Appendants" -> {{1}, {1, 0}}, "Data" -> {0, 1}, "Phase" -> 0|>, n], {n, 3}]
```

Their run lengths:

```wl
System5Evolution[#, Infinity, "Length"] & /@ programs
```

The bounds `B 2^r`:

```wl
Max[Flatten[{#["Bag"], #["Rules"]}]] 2^Length[#["Rules"]] & /@ programs
```
