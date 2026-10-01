---
Template: Symbol
Name: TuringMachineEvolutionPlot
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineEvolutionPlot
Keywords: [evolution, plot, visualization, Turing machine, Smith, universality]
SeeAlso: [TuringMachineToTagSystem, TagSystemToTuringMachine, TagSystemEvolutionPlot]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[TuringMachineEvolutionPlot]()[*machine*, *config*, *n*]</code> plots the tape of the binary Turing machine *machine* started from the configuration *config* for *n* steps, or until it halts.

## Details & Options

- The machine is a list of rules `{q, a} -> {q', w, d}`: in state `q` reading `a`, write `w`, move by `d` (`1` right, `-1` left) and go to state `q'`; state `0` halts.
- The configuration is `{q, left, head, right}`, with `left` read outward from the head, as in <code>[TuringMachineToTagSystem]()</code>.
- Each row is the tape before a step; the tape grows with blank 0s where the head goes. The head cell is colored by the state, gray once the machine halts.
- A small run is drawn as a grid with every bit written in its cell; a larger one as an array plot with the head circled.

| option | default | effect |
|---|---|---|
| <code>"Labels"</code> | <code>[Automatic]()</code> | whether to write the bits in the cells; <code>[Automatic]()</code> does it for small runs |
| <code>[ImageSize]()</code> | <code>[Automatic]()</code> | the size of the plot |
| <code>[AspectRatio]()</code> | <code>1</code> | the ratio of height to width of the array plot |

## Basic Examples

A three-state machine that moves both ways, from the tape `011` with the head on the 0:

```wl
TuringMachineEvolutionPlot[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}, 6]
```

## Scope

A longer run is drawn as an array plot:

```wl
TuringMachineEvolutionPlot[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}, 60]
```

## Options

Write the bits in the cells of a longer run:

```wl
TuringMachineEvolutionPlot[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}, 20, "Labels" -> True]
```

## Properties and Relations

The word of the tag system of the machine decodes back to the starting configuration of the plot:

```wl
TagSystemToTuringMachine[TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}, 2]["Word"], 3]
```
