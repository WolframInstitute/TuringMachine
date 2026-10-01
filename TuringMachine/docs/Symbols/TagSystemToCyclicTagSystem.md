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

- The result is a <code>[CyclicTagSystem]()</code>, with the keys `"Appendants"` (lists of bits, used cyclically), `"Data"` (the working string) and `"Phase"` (the index of the next appendant). A step deletes the first bit and, if it was 1, appends the current appendant; the phase then advances.
- A tag system over *k* symbols gives *k* appendants encoding its productions followed by *k* empty ones. A symbol is written as a block of *k* bits with a single 1.
- One cycle of the 2 *k* appendants carries out one tag step.
- It transcribes the Lean definition `TagSystem.tagToCTS, TagSystem.tagConfigToCTS` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

The cyclic tag system of the tag system `a -> bc`, `b -> a`, `c -> aaa` on the word `baa`:

```wl
cts = TagSystemToCyclicTagSystem[TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}]]
```

There are twice as many appendants as symbols:

```wl
Length[cts["Appendants"]]
```

## Scope

The cyclic tag system:

```wl
cts = TagSystemToCyclicTagSystem[TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}]]
```

Its configurations at the start of every cycle:

```wl
starts = CyclicTagSystemEvolution[cts, 24, #["Phase"] == 0 &]
```

They decode to the run of the tag system:

```wl
CyclicTagSystemToTagSystem[#["Data"], 3] & /@ Values[starts]
```

The run of the tag system:

```wl
TagSystemEvolution[TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}], 4]
```

