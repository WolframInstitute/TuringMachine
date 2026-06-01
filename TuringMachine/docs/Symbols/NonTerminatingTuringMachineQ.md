---
Template: Symbol
Name: NonTerminatingTuringMachineQ
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/NonTerminatingTuringMachineQ
Keywords: [Turing machine, halting, cycle, nontermination, multiway]
SeeAlso: [MultiwayTuringMachineFunction, MultiwayNonHaltedStatesLeft, OneSidedTuringMachineFunction]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[NonTerminatingTuringMachineQ]()[*rules*, *input*, *n*]</code> gives `True` if the machine defined by the integer *rules* enters a cycle within *n* steps (assuming 2 states, 2 symbols).

<code>[NonTerminatingTuringMachineQ]()[*rules*, *s*, *k*, *input*, *n*]</code> specifies the number of states *s* and symbols *k*.

<code>[NonTerminatingTuringMachineQ]()[{*number*, *s*, *k*}, *input*, *n*]</code> checks a specific deterministic rule.

## Details & Options

- Returns `True` only when a repeated configuration (a cycle) is detected within the step bound; a machine that simply has not halted yet within *n* steps is not reported as non-terminating.
- The deterministic form takes a single `{number, s, k}` rule, while the list form treats the rule numbers as a multiway machine.

## Basic Examples

The multiway machine built from rules 12 and 13 does not cycle on input 2 within 20 steps:

```wl
NonTerminatingTuringMachineQ[{12, 13}, 2, 20]
```

<!-- => False -->

---

Check a specific deterministic rule instead:

```wl
NonTerminatingTuringMachineQ[{2, 2, 2}, 1, 20]
```

<!-- => False -->
