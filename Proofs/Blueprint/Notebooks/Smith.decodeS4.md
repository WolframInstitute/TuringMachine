---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Reading the bag off System 4
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.decodeS4
Abstract: With the parameters of the proof, the leading sets of System 4, each time its head is back at the left end in state B, decode to the System 5 bags in order, then the decrements of a terminal phase.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, Smith.decodeS4]
Links: ["[Smith.decodeS4 in the blueprint](https://wolframinstitute.github.io/TuringMachine/system5-to-system4/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

A System 5 program with two rules:

```wl
program2 = <|"Bag" -> {2}, "Rules" -> {{1, 2}, {}}|>
```

The parameters of the emulation of a program with two rules:

```wl
EmulationParameters[program2]
```

The run of its System 4 tape with those parameters:

```wl
System4EvolutionPlot[System5ToSystem4[program2, EmulationParameters[program2]["f"]], 20000, ImageSize -> 420]
```

Each time the head is back at the left end in state B, the leading sets decode to a bag; consecutive repeats removed:

```wl
With[{p = EmulationParameters[program2]},
    First /@ Split[Sort /@ DeleteMissing[System4ToSystem5[#, p["Band"]] & /@
        Values[System4Evolution[System5ToSystem4[program2, p["f"]], 10^6, #["Active"] == 0 && #["State"] === "B" &]]]]]
```

The bags of the System 5 run:

```wl
Sort /@ System5Evolution[program2, 100][[All, "Bag"]]
```
