---
Template: Symbol
Name: System3EvolutionPlot
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System3EvolutionPlot
Keywords: [evolution, plot, visualization, Smith, universality]
SeeAlso: [System3Evolution, System4ToSystem3, Wolfram23EvolutionPlot]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System3EvolutionPlot]()[*s3*, *n*]</code> plots the run of the System 3 tape *s3* for *n* steps.

## Details & Options

- Each row is the tape after a step: cells 1 gray, 2 black, 0 white, and the active cell red in state A, blue in B and orange in C.
- The run is the one <code>[System3Evolution]()</code> gives; the row labels are the steps.

| option | default | effect |
|---|---|---|
| <code>"MaxRows"</code> | <code>400</code> | the most rows drawn; a longer run is sampled at evenly spaced steps while it runs |
| <code>[ImageSize]()</code> | <code>[Automatic]()</code> | the size of the plot |
| <code>[AspectRatio]()</code> | <code>1</code> | the ratio of height to width |

## Basic Examples

The System 3 tape of `{0, 2} * {}`:

```wl
System3EvolutionPlot[System4ToSystem3[<|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>, 3, 3], 150]
```

## Scope

A tape with blocks of width 128, sampled:

```wl
System3EvolutionPlot[System4ToSystem3[System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1], 7, 120], 20000]
```
