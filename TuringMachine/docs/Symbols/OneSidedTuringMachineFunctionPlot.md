---
Template: Symbol
Name: OneSidedTuringMachineFunctionPlot
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/OneSidedTuringMachineFunctionPlot
Keywords: [Turing machine, one-sided, function, value, plot]
SeeAlso: [OneSidedTuringMachineFunction, OneSidedTuringMachineRuntimePlot, OneSidedTuringMachinePlot]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[OneSidedTuringMachineFunctionPlot]()[{*number*, *s*, *k*}, {*min*, *max*}, *n*]</code> plots the output value of a one-sided Turing machine as a function of its input, over inputs *min* through *max* run for at most *n* steps.

<code>[OneSidedTuringMachineFunctionPlot]()[*values*]</code> plots a precomputed list of output *values*.

## Details & Options

- The values come from <code>[OneSidedTuringMachineFunction]()</code>; inputs on which the machine does not halt are shown as gaps.
- The companion <code>[OneSidedTuringMachineRuntimePlot]()</code> plots the running time instead of the value.

## Basic Examples

Plot the value computed by the *s*=3, *k*=2 rule 600720 for inputs 1 through 50:

```wl
OneSidedTuringMachineFunctionPlot[{600720, 3, 2}, {1, 50}, 200]
```
