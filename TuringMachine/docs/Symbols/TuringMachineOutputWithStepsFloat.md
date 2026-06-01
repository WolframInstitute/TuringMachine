---
Template: Symbol
Name: TuringMachineOutputWithStepsFloat
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineOutputWithStepsFloat
Keywords: [Turing machine, enumeration, rule space, numeric array, steps, output]
SeeAlso: [TuringMachineOutputWithSteps, TuringMachineOutputWithStepsWidthsFloat, TuringMachineOutput]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[TuringMachineOutputWithStepsFloat]()[*s*, *k*, *n*, *maxInput*]</code> gives a 3D numeric array of `{steps, output}` for every *s*-state, *k*-color rule and every input up to *maxInput*.

## Details & Options

- This is the packed-numeric counterpart of <code>[TuringMachineOutputWithSteps]()</code>: a regular `{rules, inputs, 2}` real array suited to bulk numeric processing and export.
- Non-halting entries are encoded numerically rather than as symbolic markers. Add the head width with <code>[TuringMachineOutputWithStepsWidthsFloat]()</code>.

## Basic Examples

The shape of the numeric `{steps, output}` array for every 2-state, 2-color machine over a small range of inputs:

```wl
Dimensions[TuringMachineOutputWithStepsFloat[2, 2, 20, 2]]
```

<!-- => {4096, 2, 2} -->
