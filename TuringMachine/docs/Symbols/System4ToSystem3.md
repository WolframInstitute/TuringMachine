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

<code>[System4ToSystem3]()[*s4*, *w*, *h*]</code> gives the System 3 tape that emulates the System 4 tape *s4*, with blocks of width <code>2^*w*</code> and a left end of *h* zeros.

## Details & Options

- *s4* must be an initial configuration: active element 0, state `"A"`, a set first.
- The result is a <code>[System3]()</code> tape, with the keys `"Left"` (cells left of the head, nearest first), `"Head"`, `"Right"` and `"State"`; cells are 0, 1 and 2.
- Each set becomes a block of <code>2^*w*</code> cells of 1s and 2s whose parity scans give the set's members; a star becomes a 0. The left end is *h* zeros followed by `221` and a final 1 closes the tape.
- The emulation is faithful while the System 4 run, plus the band read by the decoder, fits in <code>2^*w*</code> − 3 scans and every set element is below <code>2^*w*</code>; the left end turns the head round *h* times.
- It transcribes the Lean definition `Smith.initAC, Smith.AC.toL` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

The System 3 tape of the System 4 tape `{0, 2} * {}` with blocks of width 8:

```wl
s3 = System4ToSystem3[System4[{{0, 2}, "*", {}}], 3, 3]
```

Its run:

```wl
run = System3Evolution[s3, 60]
```

The run drawn:

```wl
ArrayPlot[PadRight[Join[Reverse[#["Left"]], {#["Head"]}, #["Right"]] & /@ run], ColorRules -> {0 -> White, 1 -> LightGray, 2 -> Gray}]
```

