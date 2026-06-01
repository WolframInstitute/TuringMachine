---
Template: Symbol
Name: TuringMachineOutputWithSteps
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineOutputWithSteps
Keywords: [Turing machine, enumeration, rule space, output, steps]
SeeAlso: [TuringMachineOutput, TuringMachineSteps, TuringMachineOutputWithStepsWidths, TuringMachineOutputWithStepsFloat]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[TuringMachineOutputWithSteps]()[*s*, *k*, *n*, *maxInput*]</code> gives a nested list where each cell is `{steps, output}` for a halting machine, over every *s*-state, *k*-color rule and every input up to *maxInput*.

<code>[TuringMachineOutputWithSteps]()[*s*, *k*, *n*, *minInput*, *maxInput*]</code> uses an explicit input range.

## Details & Options

- Each cell pairs the number of steps with the halted output value; a `{rule, input}` pair that does not halt within *n* steps is left as a non-halting marker.
- This is the `{steps, output}` companion of <code>[TuringMachineOutput]()</code>; for a numeric (packed) array of the same data use <code>[TuringMachineOutputWithStepsFloat]()</code>, and to add the head width use <code>[TuringMachineOutputWithStepsWidths]()</code>.

## Basic Examples

Pair the step count with the halted output for every 2-state, 2-color machine over a small range of inputs:

```wl
#| eval: false
TuringMachineOutputWithSteps[2, 2, 20, 2]
```
