---
Template: Symbol
Name: IslandsPanel
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/IslandsPanel
Keywords: [Turing machine, multiway, equational, panel, base case, step case]
SeeAlso: [MultiwayEquationalGraph, StatementPanel, TokenEventPanel, multiwaySystemFor]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[IslandsPanel]()[*ru*]</code> renders the multiway equational-rewrite cloud for one case of the Turing machine *ru*'s induction proof.

<code>[IslandsPanel]()[*ru*, *case*]</code> selects the case: `"Base"`, `"Step"`, `"StepRows"`, or `"CP"`.

## Details & Options

- Builds on <code>[MultiwayEquationalGraph]()</code>, seeding it with the axioms, induction hypothesis, and (for `"StepRows"`) derived-lemma rows drawn from <code>[multiwaySystemFor]()</code>.
- *case* defaults to `"Step"`; `"CP"` additionally rewrites with superposition (critical-pair) rules.
- Options include `"Steps"`, `"WellFormedOnly"`, `"Labeled"`, `"Axioms"` (`"Raw"` or the proof's axioms), `"Height"`, and `"Width"`.

## Basic Examples

The step-case cloud for the binary-incrementer machine 453:

```wl
IslandsPanel[453]
```

## Scope

The base-case cloud:

```wl
IslandsPanel[453, "Base"]
```
