---
Template: Symbol
Name: TuringMachineStepsWidths
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineStepsWidths
Keywords: [Turing machine, enumeration, rule space, steps, width]
SeeAlso: [TuringMachineSteps, TuringMachineWidths, TuringMachineOutputWithStepsWidths]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[TuringMachineStepsWidths]()[*s*, *k*, *n*, *maxInput*]</code> gives a list of `{steps, width}` pairs for halting *s*-state, *k*-color machines over every input up to *maxInput*.

## Details & Options

- Each cell pairs the halting time with the maximum head width, so it is the joint `{steps, width}` view of <code>[TuringMachineSteps]()</code> and <code>[TuringMachineWidths]()</code>.
- Add the output value with <code>[TuringMachineOutputWithStepsWidths]()</code>.

## Basic Examples

The shape of the `{steps, width}` table for every 2-state, 2-color machine over a small range of inputs:

```wl
Dimensions[TuringMachineStepsWidths[2, 2, 20, 2]]
```

<!-- => {4096, 2, 2} -->
