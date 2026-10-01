---
Template: Symbol
Name: Wolfram23ToSystem5
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/Wolfram23ToSystem5
Keywords: [wolfram23, decoder, parity blocks, System 5]
SeeAlso: [System3ToWolfram23, System4ToSystem5, Wolfram23Evolution]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[Wolfram23ToSystem5]()[*config*, *w*, *b*]</code> decodes the blocks of width <code>2^*w*</code> from the head of the wolfram23 configuration *config* up to the first 0 to a System 5 bag, reading the band *b*.

## Details & Options

- The cells from the head to the first 0 on its right must be 1s and 2s forming whole blocks of <code>2^*w*</code> cells. Their XOR, read by *b* successive parity scans, gives the parity set, which must be even; `x` gives the bag element `x/2 + 1`. Otherwise the result is <code>[Missing]()</code>`["NotAnEncoding"]`.
- The decode is meaningful at the times the proof schedules: wolfram23 back at the left end of its tape in state B. At other times it may return a bag that is not a configuration of the emulated system.
- It transcribes the Lean definition `Smith.decodeBlocks` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

The initial wolfram23 tape of `{0, 2} * {}`:

```wl
w23 = System3ToWolfram23[System4ToSystem3[System4[{{0, 2}, "*", {}}], 3, 3]]
```

It decodes to the bag of the first set:

```wl
Wolfram23ToSystem5[w23, 3, 4]
```

## Scope

A small System 4 tape:

```wl
s4 = System5ToSystem4[System5[{1, 3}, {{1}, {}}], 1]
```

Its decodes each time the head is back at the left end in state B:

```wl
System4ToSystem5[#, 20] & /@ Values[System4Evolution[s4, 1000, #["Active"] == 0 && #["State"] === "B" &]]
```

The wolfram23 configuration of the tape with blocks of width 128:

```wl
w23 = System3ToWolfram23[System4ToSystem3[s4, 7, 120]]
```

Its first six returns to the left end in state B:

```wl
events = Take[Wolfram23Evolution[w23, 50000, #1 == 2 && #2 == 123 &], 6]
```

Their decodes, the same as System 4's:

```wl
Wolfram23ToSystem5[#, 7, 20] & /@ Values[events]
```

