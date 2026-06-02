---
Template: Symbol
Name: MultiwayTuringMachinePlot
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/MultiwayTuringMachinePlot
Keywords: [Turing machine, multiway, nondeterministic, value, plot]
SeeAlso: [MultiwayTuringMachineFunction, OneSidedTuringMachineFunctionPlot, MultiwayTuringMachineRules]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[MultiwayTuringMachinePlot]()[*rules*, *maxInput*, *n*]</code> plots the tape values reachable by the multiway Turing machine defined by the integer *rules* for inputs 1 through *maxInput*, run for at most *n* steps.

## Details & Options

- The reachable values come from <code>[MultiwayTuringMachineFunction]()</code>; inputs from which no branch halts are marked separately, so the plot doubles as a map of which inputs the multiway machine can resolve.
- *maxInput* and *n* both default to 10.

## Basic Examples

Plot the values reachable by the multiway machine built from rules 12 and 13 for inputs 1 through 6:

```wl
MultiwayTuringMachinePlot[{12, 13}, 6, 10]
```
