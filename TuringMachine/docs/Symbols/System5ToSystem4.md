---
Template: Symbol
Name: System5ToSystem4
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System5ToSystem4
Keywords: [System 4, System 5, Smith, universality]
SeeAlso: [System4Evolution, System4ToSystem5, System4ToSystem3, EmulationParameters]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System5ToSystem4]()[*s5*, *f*]</code> gives the System 4 tape that emulates the System 5 program *s5* with the parameter *f*.

## Details & Options

- The result is a <code>[System4]()</code> tape, with the keys `"Elements"` (sets, given as lists of integers, and stars `"*"`), `"Active"` (the index of the active element, counting from 0) and `"State"` (`"A"`, `"B"` or `"C"`).
- The tape is the bag as one set, *f* star–empty-set pairs, and a block of `8 f` elements for each rule. It has `1 + 2 f + 8 f r` elements for *r* rules.
- The emulation is faithful when *f* is large enough; <code>[EmulationParameters]()</code> gives the value the proof uses, which exceeds twice the length of the System 5 run.
- It transcribes the Lean definition `BiTM.system5ToSystem4` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

The System 4 tape of a one-rule program with *f* = 1:

```wl
System5ToSystem4[System5[{1, 3}, {{1}, {}}], 1]
```

---

Smith's program of p. 33 with *f* = 2:

```wl
s4 = System5ToSystem4[System5[{2}, {{1, 4}, {1, 6}, {}, {}}], 2]
```

The tape has `1 + 2 f + 8 f r` elements:

```wl
Length[s4["Elements"]]
```

## Scope

A program with two rules:

```wl
s5 = System5[{2}, {{1, 2}, {}}]
```

The parameters of its emulation:

```wl
p = EmulationParameters[s5]
```

Its System 4 tape:

```wl
s4 = System5ToSystem4[s5, p["f"]]
```

The configurations with the head back at the left end in state B:

```wl
events = System4Evolution[s4, 10^6, #["Active"] == 0 && #["State"] === "B" &]
```

Their decodes are the System 5 bags in order, then a terminal phase:

```wl
First /@ Split[Sort /@ DeleteMissing[System4ToSystem5[#, p["Band"]] & /@ Values[events]]]
```

The System 5 run:

```wl
System5Evolution[s5, 100]
```

