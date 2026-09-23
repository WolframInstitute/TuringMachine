---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Reading the working string off the bag
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.decodeBag
Abstract: The sorted bag is read in pairs from the bottom: a gap of 1 is a 0, a gap of 2 a 1. Along the System 5 run the bags read back, in order, as the working strings of the doubled cyclic tag system.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, Smith.decodeBag]
Links: ["[Smith.decodeBag in the blueprint](https://wolframinstitute.github.io/TuringMachine/cts-to-system5/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## The decoder

Smith's example bag, the working string `01` doubled:

```wl
System5ToCyclicTagSystem[{1, 2, 3, 4, 5, 7, 8, 10}]
```

A gap of 3 is not a bit:

```wl
System5ToCyclicTagSystem[{1, 4}]
```

## Along a run

Smith's cyclic tag system with the appendants `1` and `10` on `01`:

```wl
cts = <|"Appendants" -> {{1}, {1, 0}}, "Data" -> {0, 1}, "Phase" -> 0|>
```

Its doubled system: every bit twice, every appendant doubled and followed by an empty one. Its run:

```wl
CyclicTagSystemEvolutionPlot[<|"Appendants" -> {{1, 1}, {}, {1, 1, 0, 0}, {}}, "Data" -> {0, 0, 1, 1}, "Phase" -> 0|>, 12]
```

The System 5 run of the encoded program:

```wl
System5EvolutionPlot[CyclicTagSystemToSystem5[cts, 2], 1000, ImageSize -> 420]
```

Its bags decoded, consecutive repeats removed:

```wl
First /@ Split[DeleteMissing[System5ToCyclicTagSystem /@ System5Evolution[CyclicTagSystemToSystem5[cts, 2], 1000][[All, "Bag"]]]]
```

The working strings of the doubled system, consecutive repeats removed; they are the same:

```wl
First /@ Split[CyclicTagSystemEvolution[<|"Appendants" -> {{1, 1}, {}, {1, 1, 0, 0}, {}}, "Data" -> {0, 0, 1, 1}, "Phase" -> 0|>, 8][[All, "Data"]]]
```
