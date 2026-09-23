---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The run of System 5
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.System5.step
Abstract: Every step decrements the bag and increments the rules; an element reaching 0 is removed and the next rule is merged into the bag with parity.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, BiTM.System5.step]
Links: ["[BiTM.System5.step in the blueprint](https://wolframinstitute.github.io/TuringMachine/cts-to-system5/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet `WolframInstitute/TuringMachine`:

```wl
#| eval: false
PacletInstall["https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/WolframInstitute__TuringMachine.paclet"];
Needs["WolframInstitute`TuringMachine`"]
```

The run of Smith's program of p. 33:

```wl
run = System5Evolution[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>, 20]
```

The bag elements over time:

```wl
ListPlot[Catenate[MapIndexed[Thread[{First[#2] - 1, #1}] &, run[[All, "Bag"]]]], ImageSize -> 360, AxesLabel -> {"step", "element"}]
```
