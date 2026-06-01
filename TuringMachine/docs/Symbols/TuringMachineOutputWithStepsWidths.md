---
Template: Symbol
Name: TuringMachineOutputWithStepsWidths
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineOutputWithStepsWidths
Keywords: [Turing machine, enumeration, rule space, steps, output, width]
SeeAlso: [TuringMachineOutput, TuringMachineOutputWithSteps, TuringMachineStepsWidths, TuringMachineOutputWithStepsWidthsFloat]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[TuringMachineOutputWithStepsWidths]()[*s*, *k*, *n*, *maxInput*]</code> gives a nested list of `{steps, output, width}` triples for halting machines, over every *s*-state, *k*-color rule and every input up to *maxInput*.

## Details & Options

- Each cell is the full `{steps, output, width}` summary of a halting machine; non-halting `{rule, input}` pairs are left as a non-halting marker.
- This combines <code>[TuringMachineSteps]()</code>, <code>[TuringMachineOutput]()</code>, and <code>[TuringMachineWidths]()</code> into one table; for a numeric (packed) array of the same triples use <code>[TuringMachineOutputWithStepsWidthsFloat]()</code>.

## Basic Examples

The shape of the `{steps, output, width}` table for every 2-state, 2-color machine over a small range of inputs:

```wl
Dimensions[TuringMachineOutputWithStepsWidths[2, 2, 20, 2]]
```

<!-- => {4096, 2, 3} -->
