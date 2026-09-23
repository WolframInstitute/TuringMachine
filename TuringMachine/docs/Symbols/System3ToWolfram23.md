---
Template: Symbol
Name: System3ToWolfram23
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System3ToWolfram23
Keywords: [wolfram23, Wolfram 2,3 Turing machine, relabeling, Smith]
SeeAlso: [Wolfram23Evolution, System4ToSystem3, Wolfram23ToSystem5]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System3ToWolfram23]()[*s3*]</code> gives the configuration of Wolfram's 2,3 Turing machine that corresponds to the System 3 configuration *s3*.

## Details & Options

- The result is `{q, left, head, right}` with `q = 1` (state A) or `2` (state B).
- Systems 3, 2, 1 and 0 differ by relabelings: System 3 swaps the cells 1 and 2 left of the head, and the head cell in state A; state C is state B with the head cell swapped. System 0 is Wolfram's machine.
- A System 3 step is one or three steps of wolfram23.
- It transcribes the Lean definition `Smith.phi3, Smith.phi2, Smith.toBi` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

The wolfram23 configuration of a System 3 tape:

```wl
w23 = System3ToWolfram23[System4ToSystem3[<|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>, 3, 3]]
```

The run of wolfram23 from it:

```wl
run = Wolfram23Evolution[w23, 150]
```

The run drawn:

```wl
ArrayPlot[PadRight[Join[Reverse[#[[2]]], {#[[3]]}, #[[4]]] & /@ run], ColorRules -> {0 -> White, 1 -> LightGray, 2 -> Gray}]
```

