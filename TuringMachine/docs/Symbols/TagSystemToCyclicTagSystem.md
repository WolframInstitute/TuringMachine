---
Template: Symbol
Name: TagSystemToCyclicTagSystem
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TagSystemToCyclicTagSystem
Keywords: [cyclic tag system, tag system, Cook, universality]
SeeAlso: [TuringMachineToTagSystem, CyclicTagSystemEvolution, CyclicTagSystemToTagSystem, CyclicTagSystemToSystem5]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[TagSystemToCyclicTagSystem]()[*tag*]</code> gives Cook's cyclic tag system that simulates the 2-tag system *tag*, with the encoding of its word.

## Details & Options

- A cyclic tag system is an association with keys `"Appendants"` (lists of bits, used cyclically), `"Data"` (the working string) and `"Phase"` (the index of the next appendant). A step deletes the first bit and, if it was 1, appends the current appendant; the phase then advances.
- A tag system over *k* symbols gives *k* appendants encoding its productions followed by *k* empty ones. A symbol is written as a block of *k* bits with a single 1.
- One cycle of the 2 *k* appendants carries out one tag step.
- It transcribes the Lean definition `TagSystem.tagToCTS, TagSystem.tagConfigToCTS` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

The number of appendants for the tag system of a two-state machine:

```wl
Length[TagSystemToCyclicTagSystem[TuringMachineToTagSystem[{{1, 0} -> {0, 1, 1}}, {1, {}, 0, {}}]]["Appendants"]]
```

---

The length of the working string:

```wl
Length[TagSystemToCyclicTagSystem[TuringMachineToTagSystem[{{1, 0} -> {0, 1, 1}}, {1, {}, 0, {}}]]["Data"]]
```

## Scope

At the end of every cycle the working string is the encoding of the next tag word:

```wl
With[{tag = TuringMachineToTagSystem[{{1, 0} -> {0, 1, 1}}, {1, {}, 0, {}}]},
    CyclicTagSystemToTagSystem[#["Data"], 169] & /@
        Values[CyclicTagSystemEvolution[TagSystemToCyclicTagSystem[tag], 338 * 6, #["Phase"] == 0 &]] ===
    TagSystemEvolution[tag, 6]]
```
