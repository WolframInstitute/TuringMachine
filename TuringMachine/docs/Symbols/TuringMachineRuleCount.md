---
Template: Symbol
Name: TuringMachineRuleCount
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineRuleCount
Keywords: [Turing machine, enumeration, rules, counting]
SeeAlso: [TuringMachineRuleCases, OneSidedTuringMachineFunction, TuringMachineOutput]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[TuringMachineRuleCount]()[*s*, *k*]</code> gives the total number of distinct Turing machine rules with *s* states and *k* symbols.

## Details & Options

- This is the size of the rule space the enumeration number indexes: a rule assigns one of `s * k * 2` transitions (next state, written symbol, direction) to each of the `s * k` `{state, symbol}` configurations, giving `(s * k * 2) ^ (s * k)` rules.
- It is the range of valid rule numbers for the `{number, s, k}` specification used throughout the paclet.

## Basic Examples

The number of 2-state, 2-color machines:

```wl
TuringMachineRuleCount[2, 2]
```

<!-- => 4096 -->

## Scope

Adding a state grows the space sharply:

```wl
TuringMachineRuleCount[3, 2]
```

<!-- => 2985984 -->
