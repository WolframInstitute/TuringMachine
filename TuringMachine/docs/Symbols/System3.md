---
Template: Symbol
Name: System3
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System3
Keywords: [System 3, parity blocks, Smith, universality, RulePlot]
SeeAlso: [System4ToSystem3, System3Evolution, System3EvolutionPlot, System3ToWolfram23, ParityBlock]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System3]()[<|"Left" -> {...}, "Head" -> *c*, "Right" -> {...}, "State" -> *s*|>]</code> is a tape of Smith's System 3, cells 0, 1 and 2, the head on the cell *c* in the state *s*, `"A"`, `"B"` or `"C"`.

<code>*s3*["*key*"]</code> gives a part of the tape *s3*.

## Details & Options

- `"Left"` lists the cells left of the head from the nearest outward, `"Right"` those right of it.
- A tape displays as <code>[RulePlot]()[*s3*]</code>: the cells with the head in the color of its state. A tape of more than 64 cells is drawn wrapped in rows of 64.
- <code>[Normal]()[*s3*]</code> gives the association. Every function of the paclet that takes a System 3 tape takes its association as well.

## Basic Examples

The System 3 tape of a small System 4 tape:

```wl
System4ToSystem3[System4[{{0, 2}, "*", {}}], 3, 3]
```

---

Its run:

```wl
System3EvolutionPlot[System4ToSystem3[System4[{{0, 2}, "*", {}}], 3, 3], 150]
```

## Scope

A tape with blocks of 128 cells, drawn wrapped:

```wl
System4ToSystem3[System5ToSystem4[System5[{1, 3}, {{1}, {}}], 1], 7, 120]
```

---

A tape given by its parts:

```wl
System3[<|"Left" -> {1, 2, 2}, "Head" -> 2, "Right" -> {1, 0, 1}, "State" -> "B"|>]
```

## Properties and Relations

The configuration of Wolfram's 2,3 machine for a System 3 tape:

```wl
System3ToWolfram23[System4ToSystem3[System4[{{0, 2}, "*", {}}], 3, 3]]
```
