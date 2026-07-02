---
Template: Symbol
Name: RuleSpacePanel
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/RuleSpacePanel
Keywords: [Turing machine, multiway, superposition, rule space, panel]
SeeAlso: [MultiwayRuleGraph, IslandsPanel, multiwaySystemFor]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[RuleSpacePanel]()[*ru*]</code> renders the <code>[MultiwayRuleGraph]()</code> (superposition / critical-pair rule space) of the Turing machine *ru*'s axioms plus induction hypothesis.

## Details & Options

- A convenience view over <code>[MultiwayRuleGraph]()</code> seeded from <code>[multiwaySystemFor]()</code>.
- Options include `"Generations"` (default 1), `"MaxNew"` (default 25), `"Oriented"`, `"Ordering"`, `"WellFormedOnly"`, `"Labeled"`, `"Height"`, and `"Width"`.

## Basic Examples

The rule space for the binary-incrementer machine 453:

```wl
RuleSpacePanel[453]
```
