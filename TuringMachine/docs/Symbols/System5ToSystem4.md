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

- A System 4 configuration is an association with keys `"Elements"` (sets, given as lists of integers, and stars `"*"`), `"Active"` (the index of the active element, counting from 0) and `"State"` (`"A"`, `"B"` or `"C"`).
- The tape is the bag as one set, *f* star–empty-set pairs, and a block of `8 f` elements for each rule. It has `1 + 2 f + 8 f r` elements for *r* rules.
- The emulation is faithful when *f* is large enough; <code>[EmulationParameters]()</code> gives the value the proof uses, which exceeds twice the length of the System 5 run.
- It transcribes the Lean definition `BiTM.system5ToSystem4` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

The System 4 tape of a one-rule program with *f* = 1:

```wl
System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1]["Elements"]
```

---

The length of the tape of Smith's example on p. 33 with *f* = 16:

```wl
Length[System5ToSystem4[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>, 16]["Elements"]]
```

## Scope

With the proof's parameters the System 4 decodes at the left end are the System 5 bags, then a terminal phase:

```wl
With[{p = EmulationParameters[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>]},
    DeleteDuplicates[Sort /@ DeleteMissing[System4ToSystem5[#, p["Band"]] & /@
        Values[System4Evolution[System5ToSystem4[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>, p["f"]], 10^6, #["Active"] == 0 && #["State"] === "B" &]]]]]
```
