---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Smith's System 5 encoder
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.ctsToSystem5
Abstract: A cyclic tag system as a System 5 program: the working string becomes a bag of integers, each appendant four rules, repeated for a number of cycles.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, BiTM.ctsToSystem5]
Links: ["[BiTM.ctsToSystem5 in the blueprint](https://wolframinstitute.github.io/TuringMachine/cts-to-system5/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet `WolframInstitute/TuringMachine`:

```wl
#| eval: false
PacletInstall["https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/WolframInstitute__TuringMachine.paclet"];
Needs["WolframInstitute`TuringMachine`"]
```

Smith's example of p. 29, the cyclic tag system `1 10` on the working string `01`, for one cycle:

```wl
CyclicTagSystemToSystem5[<|"Appendants" -> {{1}, {1, 0}}, "Data" -> {0, 1}, "Phase" -> 0|>, 1]
```

For two cycles:

```wl
CyclicTagSystemToSystem5[<|"Appendants" -> {{1}, {1, 0}}, "Data" -> {0, 1}, "Phase" -> 0|>, 2]
```
