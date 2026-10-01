---
Template: Symbol
Name: CyclicTagSystem
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/CyclicTagSystem
Keywords: [cyclic tag system, Cook, Smith, universality, RulePlot]
SeeAlso: [TagSystemToCyclicTagSystem, CyclicTagSystemEvolution, CyclicTagSystemEvolutionPlot, CyclicTagSystemToSystem5, TagSystem]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[CyclicTagSystem]()[<|"Appendants" -> {*a0*, *a1*, ...}, "Data" -> *bits*, "Phase" -> *p*|>]</code> is the cyclic tag system with the appendants *ai*, the working string *bits* and the phase *p*.

<code>[CyclicTagSystem]()[*apps*, *data*]</code> starts at phase 0.

<code>*cts*["*key*"]</code> gives a part of the cyclic tag system *cts*.

## Details & Options

- A step deletes the first bit of the working string and, if it was a 1, appends the appendant of the current phase; the phase then moves on to the next appendant, cyclically. The system halts when the working string is empty.
- A cyclic tag system displays as <code>[RulePlot]()[*cts*]</code>: a rule icon for each appendant, a 1 read above and the bits appended below, the current phase framed red, and the working string underneath. A large system is drawn as the array of its appendants and its working string.
- <code>[Normal]()[*cts*]</code> gives the association. Every function of the paclet that takes a cyclic tag system takes its association as well.

## Basic Examples

Smith's cyclic tag system with the appendants `1` and `10` on the working string `01`:

```wl
CyclicTagSystem[{{1}, {1, 0}}, {0, 1}]
```

---

Its run:

```wl
CyclicTagSystemEvolutionPlot[CyclicTagSystem[{{1}, {1, 0}}, {0, 1}], 12]
```

## Scope

Start at another phase:

```wl
CyclicTagSystem[{{1}, {1, 0}}, {0, 1}, 1]
```

---

Cook's encoding of a tag system, one block of bits per symbol:

```wl
TagSystemToCyclicTagSystem[TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}]]
```

---

The encoding of the tag system of a Turing machine, drawn as the array of its appendants:

```wl
TagSystemToCyclicTagSystem[TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}]]
```

## Properties and Relations

The parts of a cyclic tag system:

```wl
CyclicTagSystem[{{1}, {1, 0}}, {0, 1}]["Appendants"]
```

---

Smith's System 5 program for one cycle of its appendants:

```wl
CyclicTagSystemToSystem5[CyclicTagSystem[{{1}, {1, 0}}, {0, 1}], 1]
```
