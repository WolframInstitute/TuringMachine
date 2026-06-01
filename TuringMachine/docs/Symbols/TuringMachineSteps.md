---
Template: Symbol
Name: TuringMachineSteps
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineSteps
Keywords: [Turing machine, enumeration, rule space, steps, halting time]
SeeAlso: [TuringMachineWidths, TuringMachineStepsWidths, TuringMachineOutput, OneSidedTuringMachineFunction]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[TuringMachineSteps]()[*s*, *k*, *n*, *maxInput*]</code> gives a matrix of step counts for halting machines, over every *s*-state, *k*-color rule and every input up to *maxInput* (running each for at most *n* steps).

## Details & Options

- The result is a rule-by-input matrix of halting times; the analogous tables for the output value and head width are <code>[TuringMachineOutput]()</code> and <code>[TuringMachineWidths]()</code>, and <code>[TuringMachineStepsWidths]()</code> pairs steps with width.

## Basic Examples

The shape of the step-count matrix for every 2-state, 2-color machine over a small range of inputs:

```wl
Dimensions[TuringMachineSteps[2, 2, 20, 2]]
```

<!-- => {4096, 2} -->
