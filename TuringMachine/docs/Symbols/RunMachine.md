---
Template: Symbol
Name: RunMachine
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/RunMachine
Keywords: [Turing machine, evolution, tape configuration, symbolic, inductive proof]
SeeAlso: [DecodeTuringMachineRules, CompressToRunLength, ShowTapeConfiguration, RenderConfiguration]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[RunMachine]()[*rules*, *inputBits*]</code> runs the symbolic Turing machine *rules* on *inputBits* and returns the list of left-nested tape configurations visited, one per step.

<code>[RunMachine]()[*rules*, *inputBits*, *maxSteps*]</code> runs for at most *maxSteps* steps.

## Details & Options

- *rules* is a list of symbolic transition rules, as produced by <code>[DecodeTuringMachineRules]()</code>.
- *inputBits* is a list of tape-color symbols, e.g. `{s1, s0, s1}`.
- Each configuration is a left-nested `seq[...]` term bounded by `end` on the left and, once the machine halts, terminated with the halt state `qH` and boundary `bnd`.
- *maxSteps* defaults to 200.

## Basic Examples

Run the binary-incrementer machine 453 on the tape `1 0 1`:

```wl
RunMachine[DecodeTuringMachineRules[453, 2, 2], {s1, s0, s1}]
```

## Scope

Render the halted configuration as a tape diagram:

```wl
RenderConfiguration[Last[RunMachine[DecodeTuringMachineRules[453, 2, 2], {s1, s0, s1}]]]
```
