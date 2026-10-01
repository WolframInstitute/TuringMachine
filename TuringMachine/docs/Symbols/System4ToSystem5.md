---
Template: Symbol
Name: System4ToSystem5
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System4ToSystem5
Keywords: [System 4, System 5, decoder, band]
SeeAlso: [System5ToSystem4, System5ToCyclicTagSystem, Wolfram23ToSystem5]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System4ToSystem5]()[*s4*, *b*]</code> decodes the leading sets of the System 4 tape *s4* below the band *b* to a System 5 bag.

## Details & Options

- The integers below *b* that lie in an odd number of the sets before the first star are read; each must be even, and `x` gives the bag element `x/2 + 1`. Otherwise the result is <code>[Missing]()</code>`["NotAnEncoding"]`.
- The decode is meaningful when the head has just turned at the left end, active element 0 in state `"B"`, and with the band <code>[EmulationParameters]()</code> gives.
- It transcribes the Lean definition `Smith.decodeS4` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

A freshly encoded System 4 tape:

```wl
s4 = System5ToSystem4[System5[{1, 3}, {{1}, {}}], 1]
```

Its leading set decodes to the bag:

```wl
System4ToSystem5[s4, 20]
```

## Scope

The configurations of a run at which the head is back at the left end in state B:

```wl
events = System4Evolution[System5ToSystem4[System5[{1, 3}, {{1}, {}}], 1], 1000, #["Active"] == 0 && #["State"] === "B" &]
```

Their decodes:

```wl
System4ToSystem5[#, 20] & /@ Values[events]
```

