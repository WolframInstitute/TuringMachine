---
Template: Symbol
Name: System5EvolutionPlot
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System5EvolutionPlot
Keywords: [evolution, plot, visualization, Smith, universality]
SeeAlso: [System5Evolution, CyclicTagSystemToSystem5, System4EvolutionPlot]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System5EvolutionPlot]()[*s5*, *n*]</code> plots the run of the System 5 program *s5* for *n* steps.

## Details & Options

- Each row plots the bag elements at a step, the step increasing downward. The bag drifts down by one per step; the rows right after a rule is popped are drawn in red.
- The run is the one <code>[System5Evolution]()</code> gives; the row labels are the steps.

| option | default | effect |
|---|---|---|
| <code>"MaxRows"</code> | <code>400</code> | the most rows drawn; a longer run is sampled at evenly spaced steps while it runs |
| <code>[ImageSize]()</code> | <code>[Automatic]()</code> | the size of the plot |
| <code>[AspectRatio]()</code> | <code>1</code> | the ratio of height to width |

## Basic Examples

Smith's program of p. 33:

```wl
System5EvolutionPlot[System5[{2}, {{1, 4}, {1, 6}, {}, {}}], 20]
```

## Scope

The program of Smith's p. 29 example for two cycles:

```wl
System5EvolutionPlot[CyclicTagSystemToSystem5[CyclicTagSystem[{{1}, {1, 0}}, {0, 1}], 2], 1000]
```
