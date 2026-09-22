---
Template: Symbol
Name: System4ToSystem3
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System4ToSystem3
Keywords: [System 3, System 4, parity blocks, Smith, universality]
SeeAlso: [System3Evolution, System3ToWolfram23, System5ToSystem4, Wolfram23ToSystem5]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System4ToSystem3]()[*s4*, *w*, *h*]</code> gives the System 3 tape that emulates the System 4 tape *s4*, with blocks of width `2^`*w* and a left end of *h* zeros.

## Details & Options

- *s4* must be an initial configuration: active element 0, state `"A"`, a set first.
- A System 3 configuration is an association with keys `"Left"` (cells left of the head, nearest first), `"Head"`, `"Right"` and `"State"`; cells are 0, 1 and 2.
- Each set becomes a block of `2^`*w* cells of 1s and 2s whose parity scans give the set's members; a star becomes a 0. The left end is `0^h 2 2 1` and a final 1 closes the tape.
- The emulation is faithful while the System 4 run, plus the band read by the decoder, fits in `2^`*w* − 3 scans and every set element is below `2^`*w*; the left end turns the head round *h* times.
- It transcribes the Lean definition `Smith.initAC, Smith.AC.toL` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

The System 3 tape of the System 4 tape `{0, 2} * {}` with blocks of width 8:

```wl
System4ToSystem3[<|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>, 3, 3]
```

---

Plot the first 60 steps of its run:

```wl
ArrayPlot[PadRight[Join[Reverse[#["Left"]], {#["Head"]}, #["Right"]] & /@ System3Evolution[System4ToSystem3[<|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>, 3, 3], 60]],
    ColorRules -> {0 -> White, 1 -> LightGray, 2 -> Gray}]
```
