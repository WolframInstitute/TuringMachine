---
Template: Symbol
Name: TuringMachineOutputWithStepsWidthsFloat
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineOutputWithStepsWidthsFloat
Keywords: [Turing machine, enumeration, rule space, numeric array, steps, output, width]
SeeAlso: [TuringMachineOutputWithStepsWidths, TuringMachineOutputWithStepsFloat, TuringMachineOutput]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[TuringMachineOutputWithStepsWidthsFloat]()[*s*, *k*, *n*, *maxInput*]</code> gives a 3D numeric array of shape `{rules, inputs, 3}` holding `{steps, value, width}` triples.

<code>[TuringMachineOutputWithStepsWidthsFloat]()[*s*, *k*, *n*, *minInput*, *maxInput*]</code> uses an explicit input range.

## Details & Options

- This is the packed-numeric counterpart of <code>[TuringMachineOutputWithStepsWidths]()</code>: a regular real array suited to bulk numeric processing and export.
- Non-halting entries are encoded as `{0.0, -1.0, 0.0}` rather than symbolic markers, keeping the array rectangular.

## Basic Examples

The shape of the numeric `{steps, value, width}` array for every 2-state, 2-color machine over a small range of inputs:

```wl
Dimensions[TuringMachineOutputWithStepsWidthsFloat[2, 2, 20, 2]]
```

<!-- => {4096, 2, 3} -->
