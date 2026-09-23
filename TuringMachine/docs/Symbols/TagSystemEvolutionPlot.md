---
Template: Symbol
Name: TagSystemEvolutionPlot
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TagSystemEvolutionPlot
Keywords: [evolution, plot, visualization, Smith, universality]
SeeAlso: [TagSystemEvolution, TuringMachineToTagSystem, CyclicTagSystemEvolutionPlot]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[TagSystemEvolutionPlot]()[*tag*, *n*]</code> plots the run of the 2-tag system *tag* for *n* steps.

## Details & Options

- Each row is the word after a step, drawn at its place in the queue: two symbols are deleted from the left each step, so the run slants to the right.
- The symbols of a tag system from <code>[TuringMachineToTagSystem]()</code> are colored by their kind (the 21 kinds of the Cocke–Minsky construction), others by their index; the pad symbol 0 is light gray.
- The run is the one <code>[TagSystemEvolution]()</code> gives; the row labels are the steps.

| option | default | effect |
|---|---|---|
| <code>"MaxRows"</code> | <code>400</code> | the most rows drawn; a longer run is sampled at evenly spaced steps while it runs |
| <code>[ImageSize]()</code> | <code>[Automatic]()</code> | the size of the plot |
| <code>[AspectRatio]()</code> | <code>1</code> | the ratio of height to width |

## Basic Examples

The run of the tag system `a -> bc`, `b -> a`, `c -> aaa` on `baa`:

```wl
TagSystemEvolutionPlot[<|"Productions" -> {{1, 2}, {0}, {0, 0, 0}}, "Word" -> {1, 0, 0}|>, 10]
```

## Scope

The tag system of a three-state machine during its first four steps:

```wl
TagSystemEvolutionPlot[TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}], 85]
```
