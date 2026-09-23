---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The run of System 4
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.System4.step
Abstract: In state A the head moves left, deleting stars; at the left end it turns and sweeps right in states B and C, decrementing every set it passes.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, BiTM.System4.step]
Links: ["[BiTM.System4.step in the blueprint](https://wolframinstitute.github.io/TuringMachine/system5-to-system4/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet `WolframInstitute/TuringMachine`:

```wl
#| eval: false
PacletInstall["https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/WolframInstitute__TuringMachine.paclet"];
Needs["WolframInstitute`TuringMachine`"]
```

The run of a small tape:

```wl
run = System4Evolution[System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1], 10^4]
```

The position of the head along it:

```wl
ListLinePlot[run[[All, "Active"]], ImageSize -> 360]
```

The steps at which the head is back at the left end in state B, with their configurations:

```wl
System4Evolution[System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1], 10^4, #["Active"] == 0 && #["State"] === "B" &]
```
