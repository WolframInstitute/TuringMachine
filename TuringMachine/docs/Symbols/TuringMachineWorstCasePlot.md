---
Template: Symbol
Name: TuringMachineWorstCasePlot
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineWorstCasePlot
Keywords: [Turing machine, one-sided, runtime, worst case, envelope, plot]
SeeAlso: [OneSidedTuringMachineRuntimePlot, OneSidedTuringMachineFunction, TuringMachineSteps]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[TuringMachineWorstCasePlot]()[{*number*, *s*, *k*}, {*min*, *max*}, *n*]</code> plots the running time of a one-sided Turing machine against its input, together with the worst-case runtime envelope across each input size.

## Details & Options

- The envelope (a step function) takes the maximum running time over all inputs of each length in base *k*, giving an upper bound on cost as the input grows; the underlying per-input runtimes come from <code>[OneSidedTuringMachineFunction]()</code> with the `"Steps"` property.
- The `"ShowEnvelope"` option toggles the envelope. Choose an input range in which every machine halts within *n* steps — non-halting inputs have infinite runtime and cannot be placed on the plot.

## Basic Examples

Plot the runtime of the *s*=3, *k*=2 rule 600720 with its worst-case envelope, over an input range it fully halts on:

```wl
TuringMachineWorstCasePlot[{600720, 3, 2}, {1, 9}, 200]
```
