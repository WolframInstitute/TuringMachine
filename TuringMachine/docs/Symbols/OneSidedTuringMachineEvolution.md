---
Template: Symbol
Name: OneSidedTuringMachineEvolution
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/OneSidedTuringMachineEvolution
Keywords: [Turing machine, one-sided, evolution, history, configurations]
SeeAlso: [OneSidedTuringMachinePlot, OneSidedTuringMachineFunction]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[OneSidedTuringMachineEvolution]()[{*number*, *s*, *k*}, *input*, *n*]</code> returns the step-by-step evolution of a one-sided Turing machine as a list of configurations, one per step, for at most *n* steps.

<code>[OneSidedTuringMachineEvolution]()[{*number*, *s*, *k*}, *input*, *n*, *width*]</code> sets the displayed tape width.

## Details & Options

- Each configuration is a `{head, tape}` pair: the head record (its state and position) together with the tape contents at that step.
- This is the underlying data that <code>[OneSidedTuringMachinePlot]()</code> renders; use it directly to post-process or analyze a machine's history.

## Basic Examples

The evolution of the *s*=3, *k*=2 rule 600720 on input 1, which halts after a few steps:

```wl
OneSidedTuringMachineEvolution[{600720, 3, 2}, 1, 16]
```

<!-- => a list of {head, tape} configurations, one per step -->
