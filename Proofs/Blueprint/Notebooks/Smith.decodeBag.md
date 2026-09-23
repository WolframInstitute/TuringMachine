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

The functions come from the paclet `WolframInstitute/TuringMachine`:

```wl
#| eval: false
PacletInstall["https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/WolframInstitute__TuringMachine.paclet"];
Needs["WolframInstitute`TuringMachine`"]
```

The System 5 program of Smith's p. 29 example for two cycles:

```wl
s5 = CyclicTagSystemToSystem5[<|"Appendants" -> {{1}, {1, 0}}, "Data" -> {0, 1}, "Phase" -> 0|>, 2]
```

Its run:

```wl
run = System5Evolution[s5, 1000]
```

The decoded bags, repeats removed:

```wl
First /@ Split[DeleteMissing[System5ToCyclicTagSystem /@ run[[All, "Bag"]]]]
```

The run of the doubled cyclic tag system, which has every bit twice:

```wl
CyclicTagSystemEvolution[<|"Appendants" -> {{1, 1}, {}, {1, 1, 0, 0}, {}}, "Data" -> {0, 0, 1, 1}, "Phase" -> 0|>, 8]
```
