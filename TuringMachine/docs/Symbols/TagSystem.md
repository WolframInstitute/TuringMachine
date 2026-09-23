---
Template: Symbol
Name: TagSystem
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TagSystem
Keywords: [tag system, 2-tag system, Cocke-Minsky, Smith, universality, RulePlot]
SeeAlso: [TuringMachineToTagSystem, TagSystemEvolution, TagSystemEvolutionPlot, TagSystemToCyclicTagSystem, CyclicTagSystem]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[TagSystem]()[<|"Productions" -> {*p0*, *p1*, ...}, "Word" -> *w*|>]</code> is the 2-tag system over the symbols 0, 1, ... with the production *pi* for the symbol *i*, started on the word *w*.

<code>[TagSystem]()[*prods*, *word*]</code> is <code>[TagSystem]()[<|"Productions" -> *prods*, "Word" -> *word*|>]</code>.

<code>*tag*["*key*"]</code> gives a part of the tag system *tag*.

## Details & Options

- A step reads the first symbol *i* of the word, deletes the first two symbols and appends *pi*. The system halts when the word has fewer than two symbols.
- A tag system displays as <code>[RulePlot]()[*tag*]</code>: a rule icon for each production, the symbol read above and the symbols appended below, and the word underneath. A system with more than 24 symbols draws the productions of the symbols its word reaches first.
- <code>[TuringMachineToTagSystem]()</code> adds the keys `"States"`, `"SymbolNames"`, which name the symbols in the drawings, and `"TagTimes"`.
- <code>[Normal]()[*tag*]</code> gives the association, and <code>*tag*["Properties"]</code> its keys. Every function of the paclet that takes a tag system takes its association as well.

## Basic Examples

A tag system over three symbols:

```wl
TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}]
```

---

Its run:

```wl
TagSystemEvolutionPlot[TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}], 10]
```

## Scope

The tag system of a Turing machine, its symbols named by their kind and state:

```wl
TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}]
```

---

The parts of a tag system:

```wl
TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}]["Properties"]
```

```wl
TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}]["Productions"]
```

## Properties and Relations

<code>[RulePlot]()</code> gives the drawing a tag system displays as:

```wl
RulePlot[TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}]]
```

---

Cook's cyclic tag system of a tag system:

```wl
TagSystemToCyclicTagSystem[TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}]]
```
