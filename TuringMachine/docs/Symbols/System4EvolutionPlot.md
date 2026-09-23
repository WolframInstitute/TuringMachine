---
Template: Symbol
Name: System4EvolutionPlot
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System4EvolutionPlot
Keywords: [evolution, plot, visualization, Smith, universality]
SeeAlso: [System4Evolution, System5ToSystem4, System3EvolutionPlot]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System4EvolutionPlot]()[*s4*, *n*]</code> plots the run of the System 4 tape *s4* for *n* steps.

## Details & Options

- Each row is the tape after a step: stars black, nonempty sets gray, empty sets light gray, and the active element red in state A, blue in B and orange in C.
- The run is the one <code>[System4Evolution]()</code> gives; the row labels are the steps.

| option | default | effect |
|---|---|---|
| <code>"MaxRows"</code> | <code>400</code> | the most rows drawn; a longer run is sampled at evenly spaced steps while it runs |
| <code>[ImageSize]()</code> | <code>[Automatic]()</code> | the size of the plot |
| <code>[AspectRatio]()</code> | <code>1</code> | the ratio of height to width |

## Basic Examples

A small System 4 tape:

```wl
System4EvolutionPlot[System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1], 200]
```

## Scope

Smith's program of p. 33 with *f* = 2, sampled:

```wl
System4EvolutionPlot[System5ToSystem4[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>, 2], 3000]
```
