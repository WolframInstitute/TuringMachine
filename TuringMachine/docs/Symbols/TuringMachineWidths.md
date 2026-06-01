---
Template: Symbol
Name: TuringMachineWidths
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineWidths
Keywords: [Turing machine, enumeration, rule space, width, head position]
SeeAlso: [TuringMachineSteps, TuringMachineStepsWidths, TuringMachineOutput, OneSidedTuringMachineFunction]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[TuringMachineWidths]()[*s*, *k*, *n*, *maxInput*]</code> gives a matrix of maximum head widths (the largest absolute head position reached) for halting *s*-state, *k*-color machines over every input up to *maxInput*.

## Details & Options

- The result is a rule-by-input matrix; a non-halting `{rule, input}` pair is recorded as `0`.
- The matching tables for halting time and output value are <code>[TuringMachineSteps]()</code> and <code>[TuringMachineOutput]()</code>; <code>[TuringMachineStepsWidths]()</code> pairs steps with width.

## Basic Examples

The shape of the width matrix for every 2-state, 2-color machine over a small range of inputs:

```wl
Dimensions[TuringMachineWidths[2, 2, 20, 2]]
```

<!-- => {4096, 2} -->
