---
Template: Symbol
Name: Wolfram23EvolutionPlot
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/Wolfram23EvolutionPlot
Keywords: [evolution, plot, visualization, Smith, universality]
SeeAlso: [Wolfram23Evolution, System3ToWolfram23, System3EvolutionPlot]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[Wolfram23EvolutionPlot]()[*config*, *n*]</code> plots the run of Wolfram's 2,3 machine from *config* for *n* steps.

## Details & Options

- Each row is the tape after a step, in absolute positions: cells 1 gray, 2 black, 0 white, the head red in state A and blue in state B.
- The run is computed on a mutable tape, so runs of millions of steps are practical.
- The run is the one <code>[Wolfram23Evolution]()</code> gives; the row labels are the steps.

| option | default | effect |
|---|---|---|
| <code>"MaxRows"</code> | <code>400</code> | the most rows drawn; a longer run is sampled at evenly spaced steps while it runs |
| <code>[ImageSize]()</code> | <code>[Automatic]()</code> | the size of the plot |
| <code>[AspectRatio]()</code> | <code>1</code> | the ratio of height to width |

## Basic Examples

The machine from a blank tape:

```wl
Wolfram23EvolutionPlot[{1, {}, 0, {}}, 300]
```

## Scope

The machine on a tape that emulates a small System 4 tape, sampled:

```wl
Wolfram23EvolutionPlot[System3ToWolfram23[System4ToSystem3[System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1], 7, 120]], 60000]
```
