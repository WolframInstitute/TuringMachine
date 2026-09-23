---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The System 4 tape of a System 5 program
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.system5ToSystem4
Abstract: The bag becomes one set, followed by f star and empty-set pairs and a block of 8f elements for each rule.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, BiTM.system5ToSystem4]
Links: ["[BiTM.system5ToSystem4 in the blueprint](https://wolframinstitute.github.io/TuringMachine/system5-to-system4/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

A one-rule program with f = 1:

```wl
System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1]
```

Smith's program of p. 33 with f = 2:

```wl
s4 = System5ToSystem4[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>, 2]
```

The tape has `1 + 2 f + 8 f r` elements:

```wl
Length[s4["Elements"]]
```
