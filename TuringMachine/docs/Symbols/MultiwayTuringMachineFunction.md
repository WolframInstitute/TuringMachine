---
Template: Symbol
Name: MultiwayTuringMachineFunction
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/MultiwayTuringMachineFunction
Keywords: [Turing machine, multiway, nondeterministic, traversal, output]
SeeAlso: [MultiwayTuringMachineRules, MultiwayNonHaltedStatesLeft, NonTerminatingTuringMachineQ]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[MultiwayTuringMachineFunction]()[*rules*, *input*, *n*]</code> traverses the nondeterministic Turing machine defined by the list of integer *rules* on *input* for at most *n* steps (assuming 2 states, 2 symbols).

<code>[MultiwayTuringMachineFunction]()[{*rules*, *s*, *k*}, *input*, *n*]</code> specifies the number of states *s* and symbols *k*.

<code>[MultiwayTuringMachineFunction]()[{*rules*, *s*, *k*}, *input*, *target*, *n*]</code> stops early if the *target* output is found.

## Details & Options

- A multiway machine is given by a list of integer rule numbers; where their transitions disagree the traversal branches, so one input can lead to many histories.
- The result is a triple `{haltedValues, branches, cycleQ}`: the unique tape values reached from halted branches, the number of active branches at each step, and whether the traversal stopped on a detected cycle.
- `haltedValues` is empty when no branch halts within *n* steps (one-sided multiway machines often run without halting). Use <code>[MultiwayNonHaltedStatesLeft]()</code> and <code>[NonTerminatingTuringMachineQ]()</code> to probe the unhalted frontier.
- *input* may be a single integer or a list of integers, and the machine assumes 2 states and 2 colors unless the `{rules, s, k}` form is used.

## Basic Examples

Traverse the multiway machine built from rules 12 and 13 on input 2 for 6 steps — it runs without halting, so no tape values are collected, the single branch stays active each step, and no cycle is detected:

```wl
MultiwayTuringMachineFunction[{12, 13}, 2, 6]
```

<!-- => {{}, {1, 1, 1, 1, 1, 1, 1}, False} -->

## Scope

Pass several inputs at once; the branch count traces how the three initial histories merge as the traversal proceeds:

```wl
MultiwayTuringMachineFunction[{12, 13}, {1, 2, 3}, 6]
```

<!-- => {{}, {3, 3, 2, 1, 1, 1, 1}, False} -->
