---
Template: Symbol
Name: OneSidedTuringMachineFind
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/OneSidedTuringMachineFind
Keywords: [Turing machine, one-sided, search, inverse, enumeration]
SeeAlso: [OneSidedTuringMachineFunction, TuringMachineRuleCount, TuringMachineOutput]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[OneSidedTuringMachineFind]()[*rule*, *maxInput*, *n*, {*s*, *k*}]</code> finds all *s*-state, *k*-color rules that reproduce the outputs of *rule* for inputs 1 to *maxInput*, each within *n* steps.

<code>[OneSidedTuringMachineFind]()[{{*input*, *steps*, *value*}, …}, {*s*, *k*}]</code> finds the rules matching the given `{input, steps, value}` triples.

<code>[OneSidedTuringMachineFind]()[{*values*}, *n*, {*s*, *k*}]</code> finds the rules producing *values* for inputs 1, 2, …, each within *n* steps.

## Details & Options

- A target machine is `{number, s, k}`; the searched family is given by its own `{s, k}`, which defaults to `{2, 2}`.
- Targets may be specified as a reference rule, as `{input, steps, value}` triples, as `{steps, value}` pairs (with sequential inputs 1, 2, …), or as a bare list of output `values`.
- A list of `values` must be wrapped in an extra list to distinguish it from a `{number, s, k}` rule triple, e.g. `OneSidedTuringMachineFind[{Range[100] + 1}, 200]`.
- An optional final argument restricts the search to a specific list of rule numbers.

## Basic Examples

Rule 1500's own *s*=2, *k*=2 family reproduces its behavior on inputs 1 and 2, so the search contains the rule itself:

```wl
MemberQ[OneSidedTuringMachineFind[{{1, 3, 3}, {2, 1, 3}}, {2, 2}], 1500]
```

<!-- => True -->

## Scope

Count how many *s*=2, *k*=2 rules share that behavior:

```wl
Length[OneSidedTuringMachineFind[{{1, 3, 3}, {2, 1, 3}}, {2, 2}]]
```

<!-- => 132 -->
