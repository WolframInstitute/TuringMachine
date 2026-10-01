---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Reading the bag off System 4
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.decodeS4
Abstract: Each time the head is back at the left end in state B, the sets before the first star together hold the System 5 bag: an integer x in an odd number of them, below the band, stands for the bag element x/2 + 1. With the proof's parameters these readings are the System 5 run, in order, followed by a few steps of a terminal phase.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, Smith.decodeS4]
Links: ["[Smith.decodeS4 in the blueprint](https://wolframinstitute.github.io/TuringMachine/system5-to-system4/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## The parameters

A System 5 program with two rules:

```wl
program = System5[{2}, {{1, 2}, {}}]
```

The parameters the proof takes for it: `f` (the tape's time budget) and the band `b` below which the decoder reads, among others:

```wl
params = EmulationParameters[program]
```

## The run

The run of its System 4 tape, sampled to 400 rows; the head zigzags from the left end into the tape:

```wl
System4EvolutionPlot[System5ToSystem4[program, params["f"]], 20000, ImageSize -> 420]
```

## Reading the bag

At every return of the head to the left end in state B, the decoder takes the sets before the first star, keeps the integers below the band that lie in an odd number of them, and reads each even integer `x` as the bag element `x / 2 + 1`; a reading with an odd integer is not a bag and is skipped. The readings along the run, consecutive repeats removed:

```wl
First /@ Split[Sort /@ DeleteMissing[System4ToSystem5[#, params["Band"]] & /@
    Values[System4Evolution[System5ToSystem4[program, params["f"]], 10^6, #["Active"] == 0 && #["State"] === "B" &]]]]
```

The bags of the System 5 run:

```wl
Sort /@ System5Evolution[program, 100][[All, "Bag"]]
```

The readings are the System 5 bags in order; the tape is run a little further than System 5 (the terminal phase of the proof), which only continues to decrement.
