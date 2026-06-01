---
Template: Symbol
Name: TuringMachineRuleCases
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineRuleCases
Keywords: [Turing machine, transition table, rules, enumeration]
SeeAlso: [TuringMachineRuleCount, MultiwayTuringMachineRules, OneSidedTuringMachineFunction]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[TuringMachineRuleCases]()[{*number*, *s*, *k*}]</code> gives an association mapping each `{state, symbol}` to its transition triple `{nextState, writeSymbol, direction}`.

## Details & Options

- The argument is a `{number, s, k}` rule: its enumeration number together with the state and color counts.
- Each value is a single transition `{nextState, writeSymbol, direction}`, where `direction` is `-1` for left and `1` for right; this is the deterministic counterpart of <code>[MultiwayTuringMachineRules]()</code>, whose values are lists of triples.

## Basic Examples

The transition table of the *s*=2, *k*=2 rule 2:

```wl
TuringMachineRuleCases[{2, 2, 2}]
```

<!-- => <|{1,0}->{1,0,-1}, {1,1}->{1,0,-1}, {2,0}->{1,1,-1}, {2,1}->{1,0,-1}|> -->
