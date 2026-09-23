---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Why System 4 always halts
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.System4.run_bound
Abstract: Every step of System 4 either deletes a star, turns the head round at a star or at the left end, or moves the head one element in its current direction. A measure built from the number of stars and the head position drops at every step, so a tape of length L halts within (2L + 2)(L + 1) steps.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, Smith.System4.run_bound]
Links: ["[Smith.System4.run_bound in the blueprint](https://wolframinstitute.github.io/TuringMachine/conjecture0/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## The measure

In state A the head moves left, in states B and C right. A leftward walk ends at a star, which is deleted, or at the left end, where the head turns round; a rightward sweep ends at a star in state B, which is deleted, or at the right end. So the phase, twice the number of stars plus one while the head moves left, never increases and drops whenever the direction changes, and within a phase the head only moves one way. Counting phases times positions gives a number below `(2 L + 2) (L + 1)` that drops at every step.

## Against real runs

The System 4 tapes of Smith's p. 33 program for `f` from 1 to 4:

```wl
tapes = Table[System5ToSystem4[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>, f], {f, 4}]
```

Their runs, one below the other; every run halts:

```wl
System4EvolutionPlot[#, 10^5, ImageSize -> 200] & /@ Take[tapes, 2]
```

The run lengths against the bound:

```wl
ListLogPlot[{Length[System4Evolution[#, 10^6]] - 1 & /@ tapes, With[{l = Length[#["Elements"]]}, (2 l + 2) (l + 1)] & /@ tapes},
    Joined -> True, PlotMarkers -> Automatic, PlotLegends -> {"run length", "bound"}, AxesLabel -> {"f", None}, ImageSize -> 420]
```
