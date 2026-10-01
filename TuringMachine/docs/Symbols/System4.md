---
Template: Symbol
Name: System4
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System4
Keywords: [System 4, sets, stars, Smith, universality, RulePlot]
SeeAlso: [System5ToSystem4, System4Evolution, System4EvolutionPlot, System4ToSystem3, System4ToSystem5]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System4]()[<|"Elements" -> {...}, "Active" -> *i*, "State" -> *s*|>]</code> is a tape of Smith's System 4: sets of integers and stars `"*"`, the element *i* (counting from 0) active in the state *s*, `"A"`, `"B"` or `"C"`.

<code>[System4]()[*elements*]</code> starts on the first element in state `"A"`.

<code>*s4*["*key*"]</code> gives a part of the tape *s4*.

## Details & Options

- A set is a list of integers. In state A the head moves left over sets; at the left end, or when it deletes a star, it turns to state B and moves right. Moving right in B or C it decrements every set it passes, and a set holding a 0 loses it and switches the state between B and C. A star reached in B is deleted and the head turns left in state A; a star reached in C stays, and the next set gains or loses a 1.
- A tape displays as <code>[RulePlot]()[*s4*]</code>: each set as a cell with its members, each star dark, the active element in the color of its state. A long tape is drawn wrapped, sets gray, empty sets light and stars dark.
- <code>[Normal]()[*s4*]</code> gives the association. Every function of the paclet that takes a System 4 tape takes its association as well.

## Basic Examples

A tape of two sets and a star:

```wl
System4[{{0, 2}, "*", {}}]
```

---

Its run:

```wl
System4EvolutionPlot[System4[{{0, 2}, "*", {}}], 6]
```

## Scope

The tape of a System 5 program:

```wl
System5ToSystem4[System5[{1, 3}, {{1}, {}}], 1]
```

---

A longer tape is drawn wrapped:

```wl
System5ToSystem4[System5[{1, 3}, {{1}, {}}], 4]
```

## Properties and Relations

The System 3 tape of a System 4 tape, each set a block of cells:

```wl
System4ToSystem3[System4[{{0, 2}, "*", {}}], 3, 3]
```
