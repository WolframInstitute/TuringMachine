---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Reading the working string off the bag
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.decodeBag
Abstract: The sorted bag read in pairs: a gap of 1 is a 0, a gap of 2 a 1. Along the System 5 run the decoded strings are the run of the doubled cyclic tag system.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, Smith.decodeBag]
Links: ["[Smith.decodeBag in the blueprint](https://wolframinstitute.github.io/TuringMachine/cts-to-system5/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

Smith's cyclic tag system `1 10` on the working string `01` (p. 29):

```wl
cts = <|"Appendants" -> {{1}, {1, 0}}, "Data" -> {0, 1}, "Phase" -> 0|>
```

The run of the doubled cyclic tag system of Smith's p. 29 example, which has every bit twice:

```wl
CyclicTagSystemEvolutionPlot[<|"Appendants" -> {{1, 1}, {}, {1, 1, 0, 0}, {}}, "Data" -> {0, 0, 1, 1}, "Phase" -> 0|>, 12, ImageSize -> 420]
```

The System 5 run that emulates it:

```wl
System5EvolutionPlot[CyclicTagSystemToSystem5[cts, 2], 1000, ImageSize -> 420]
```

The bags decoded, consecutive repeats removed:

```wl
First /@ Split[DeleteMissing[System5ToCyclicTagSystem /@ System5Evolution[CyclicTagSystemToSystem5[cts, 2], 1000][[All, "Bag"]]]]
```

The working strings of the doubled cyclic tag system:

```wl
First /@ Split[CyclicTagSystemEvolution[<|"Appendants" -> {{1, 1}, {}, {1, 1, 0, 0}, {}}, "Data" -> {0, 0, 1, 1}, "Phase" -> 0|>, 8][[All, "Data"]]]
```
