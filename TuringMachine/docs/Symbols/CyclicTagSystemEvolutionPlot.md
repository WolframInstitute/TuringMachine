---
Template: Symbol
Name: CyclicTagSystemEvolutionPlot
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/CyclicTagSystemEvolutionPlot
Keywords: [evolution, plot, visualization, Smith, universality]
SeeAlso: [CyclicTagSystemEvolution, TagSystemToCyclicTagSystem, System5EvolutionPlot]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[CyclicTagSystemEvolutionPlot]()[*cts*, *n*]</code> plots the run of the cyclic tag system *cts* for *n* steps.

## Details & Options

- Each row is the working string after a step, drawn at its place in the queue: one bit is deleted from the left each step.
- Bits 1 are dark and 0 light; the rows where a cycle of the appendants starts (phase 0) are drawn in red.
- The run is the one <code>[CyclicTagSystemEvolution]()</code> gives; the row labels are the steps.

| option | default | effect |
|---|---|---|
| <code>"MaxRows"</code> | <code>400</code> | the most rows drawn; a longer run is sampled at evenly spaced steps while it runs |
| <code>[ImageSize]()</code> | <code>[Automatic]()</code> | the size of the plot |
| <code>[AspectRatio]()</code> | <code>1</code> | the ratio of height to width |

## Basic Examples

Smith's example with the appendants `1` and `10` on `01`:

```wl
CyclicTagSystemEvolutionPlot[CyclicTagSystem[{{1}, {1, 0}}, {0, 1}], 60]
```

## Scope

The cyclic tag system of a small tag system; every sixth row, where a cycle starts, is a tag word:

```wl
CyclicTagSystemEvolutionPlot[TagSystemToCyclicTagSystem[TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}]], 30]
```
