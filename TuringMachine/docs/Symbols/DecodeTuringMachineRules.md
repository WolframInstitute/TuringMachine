---
Template: Symbol
Name: DecodeTuringMachineRules
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/DecodeTuringMachineRules
Keywords: [Turing machine, transition rules, decoding, symbolic, inductive proof]
SeeAlso: [RunMachine, CompressToRunLength, FindInductiveProof, TuringMachineRuleCases]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[DecodeTuringMachineRules]()[*number*, *s*, *k*]</code> decodes the Turing machine *number* (with *s* states and *k* colors) into a list of symbolic transition rules of the form <code>{*state*, *symbol*} -> {*newState*, *writeSymbol*, *direction*}</code>.

## Details & Options

- States are the symbols `qA`, `qB`, `qC`, `qD`; tape colors are `s0`, `s1`, `s2`, `s3`. These are the alphabet the rest of the inductive-proof machinery reasons over.
- *direction* is `1` or `-1`.
- The decoding wraps the `TuringMachineFromNumber` resource function and relabels its integer states and colors with these symbols.

## Basic Examples

Decode the two-state, two-color binary-incrementer machine 453:

```wl
DecodeTuringMachineRules[453, 2, 2]
```

<!-- => {{qA, s1} -> {qA, s0, -1}, {qA, s0} -> {qB, s1, 1}, {qB, s1} -> {qA, s0, -1}, {qB, s0} -> {qB, s0, 1}} -->
