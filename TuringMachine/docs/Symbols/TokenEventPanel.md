---
Template: Symbol
Name: TokenEventPanel
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TokenEventPanel
Keywords: [Turing machine, multiway, token-event, panel, derived lemma]
SeeAlso: [MultiwayTokenEventGraph, StatementPanel, IslandsPanel, multiwaySystemFor]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[TokenEventPanel]()[*ru*, *k*]</code> renders the multiway token-event graph for the Turing machine *ru*'s base or step case, seeded with the axioms plus the first *k* derived-lemma rows.

## Details & Options

- Builds on <code>[MultiwayTokenEventGraph]()</code>, so each rewrite step is drawn as an event fed by the axiom that drives it.
- Options include `"Case"` (`"Step"` or `"Base"`), `"Seeds"` (`"Equation"` or `"Pair"`), `"Steps"`, `"Labeled"`, `"CollapseAxioms"`, `"ShowAxioms"`, `"PinProof"`, `"Layout"`, `"Height"`, and `"Width"`.

## Basic Examples

The step-case token-event graph for the binary-incrementer machine 453:

```wl
TokenEventPanel[453, 0]
```
