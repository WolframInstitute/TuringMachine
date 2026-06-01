---
Template: Symbol
Name: TuringMachineOutput
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineOutput
Keywords: [Turing machine, enumeration, rule space, output, halting]
SeeAlso: [TuringMachineSteps, TuringMachineWidths, TuringMachineOutputWithStepsWidths, OneSidedTuringMachineFunction]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[TuringMachineOutput]()[*s*, *k*, *n*, *maxInput*]</code> gives a nested list of halted outputs for every *s*-state, *k*-color rule and every input up to *maxInput*, running each machine for at most *n* steps.

<code>[TuringMachineOutput]()[*s*, *k*, *n*, *minInput*, *maxInput*]</code> uses an explicit input range.

## Details & Options

- The result is a rule-by-input array; a `{rule, input}` pair that does not halt within *n* steps is left as a non-halting marker rather than a value.
- This tabulates the whole rule space at once and is backed by a compiled Rust implementation; see <code>[TuringMachineSteps]()</code>, <code>[TuringMachineWidths]()</code>, and the combined <code>[TuringMachineOutputWithStepsWidths]()</code> for the matching step and width tables.

## Basic Examples

The shape of the output table for every 2-state, 2-color machine over a small range of inputs:

```wl
Dimensions[TuringMachineOutput[2, 2, 20, 2]]
```

<!-- => {4096, 2} -->

## Scope

Count how many `{rule, input}` pairs halt within 20 steps:

```wl
Count[TuringMachineOutput[2, 2, 20, 2], _Integer, {2}]
```

<!-- => 5432 -->
