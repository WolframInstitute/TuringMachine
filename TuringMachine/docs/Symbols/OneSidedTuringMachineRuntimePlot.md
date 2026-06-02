---
Template: Symbol
Name: OneSidedTuringMachineRuntimePlot
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/OneSidedTuringMachineRuntimePlot
Keywords: [Turing machine, one-sided, runtime, steps, plot]
SeeAlso: [OneSidedTuringMachineFunctionPlot, TuringMachineWorstCasePlot, OneSidedTuringMachineFunction]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[OneSidedTuringMachineRuntimePlot]()[{*number*, *s*, *k*}, {*min*, *max*}, *n*]</code> plots the running time (number of steps) of a one-sided Turing machine as a function of its input, over inputs *min* through *max* run for at most *n* steps.

<code>[OneSidedTuringMachineRuntimePlot]()[*steps*]</code> plots a precomputed list of step counts.

## Details & Options

- The step counts come from <code>[OneSidedTuringMachineFunction]()</code> with the `"Steps"` property; inputs on which the machine does not halt are shown as gaps.
- The `"ShowInfinity"` option marks the non-halting inputs explicitly. The value-versus-input companion is <code>[OneSidedTuringMachineFunctionPlot]()</code>, and <code>[TuringMachineWorstCasePlot]()</code> adds a worst-case envelope.

## Basic Examples

Plot how long the *s*=3, *k*=2 rule 600720 runs for inputs 1 through 50:

```wl
OneSidedTuringMachineRuntimePlot[{600720, 3, 2}, {1, 50}, 200]
```
