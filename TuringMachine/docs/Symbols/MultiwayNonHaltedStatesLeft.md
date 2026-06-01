---
Template: Symbol
Name: MultiwayNonHaltedStatesLeft
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/MultiwayNonHaltedStatesLeft
Keywords: [Turing machine, multiway, nondeterministic, traversal, halting]
SeeAlso: [MultiwayTuringMachineFunction, MultiwayTuringMachineRules, NonTerminatingTuringMachineQ]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[MultiwayNonHaltedStatesLeft]()[*rules*, *input*, *n*]</code> gives the number of non-halted states left in the traversal queue after exploring the multiway machine *rules* for up to *n* steps (assuming 2 states, 2 symbols).

<code>[MultiwayNonHaltedStatesLeft]()[*rules*, *s*, *k*, *input*, *n*]</code> specifies the number of states *s* and symbols *k*.

## Details & Options

- A multiway machine is given by a list of integer rule numbers; its traversal branches wherever transitions disagree.
- The result is the size of the frontier — branches not yet halted — after *n* steps, so a value of `0` means every branch has halted within the bound.

## Basic Examples

After 5 steps the multiway machine built from rules 12 and 13 on input 2 has no unexplored branches:

```wl
MultiwayNonHaltedStatesLeft[{12, 13}, 2, 5]
```

<!-- => 0 -->
