---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The System 3 tape
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.initAC
Abstract: Each set of the System 4 tape becomes a block of 2^w cells whose parity scans give the set, each star a 0, with a left end 0^h 2 2 1 and a closing 1.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, Smith.initAC]
Links: ["[Smith.initAC in the blueprint](https://wolframinstitute.github.io/TuringMachine/system4-to-system3/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

The System 4 tape `{0, 2} * {}`:

```wl
tape4 = <|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>
```

A small System 5 program:

```wl
small = <|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>
```

The System 3 tape of the System 4 tape `{0, 2} * {}` with blocks of width 8:

```wl
System4ToSystem3[tape4, 3, 3]
```

Its run; cells 1 gray and 2 black, the head colored by the state:

```wl
System3EvolutionPlot[System4ToSystem3[tape4, 3, 3], 150, ImageSize -> 420]
```

A tape with blocks of width 128, the run sampled:

```wl
System3EvolutionPlot[System4ToSystem3[System5ToSystem4[small, 1], 7, 120], 20000, ImageSize -> 420]
```
