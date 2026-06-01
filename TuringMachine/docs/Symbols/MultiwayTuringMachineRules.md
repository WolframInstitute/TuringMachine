---
Template: Symbol
Name: MultiwayTuringMachineRules
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/MultiwayTuringMachineRules
Keywords: [Turing machine, multiway, nondeterministic, transition table, rules]
SeeAlso: [TuringMachineRuleCases, MultiwayTuringMachineFunction, MultiwayNonHaltedStatesLeft]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[MultiwayTuringMachineRules]()[*rules*, *s*, *k*]</code> gives an association mapping each `{state, symbol}` to a list of transition triples `{nextState, writeSymbol, direction}`.

<code>[MultiwayTuringMachineRules]()[*rules*]</code> assumes 2 states and 2 symbols.

## Details & Options

- A multiway machine is given by a list of integer rule numbers; each rule contributes its transitions, and the union is what makes the machine nondeterministic.
- A `{state, symbol}` that maps to more than one triple is a branching point: the machine can take any of those transitions. This is the multivalued counterpart of <code>[TuringMachineRuleCases]()</code>.

## Basic Examples

The transition table of the multiway machine built from rules 12 and 13 (2 states, 2 colors) — the `{2, 0}` cell carries two transitions:

```wl
MultiwayTuringMachineRules[{12, 13}, 2, 2]
```

<!-- => <|{1,0}->{{1,0,-1}}, {1,1}->{{1,0,-1}}, {2,0}->{{2,0,-1},{2,0,1}}, {2,1}->{{1,0,1}}|> -->
