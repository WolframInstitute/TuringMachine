---
Template: Symbol
Name: multiwaySystemFor
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/multiwaySystemFor
Keywords: [Turing machine, multiway, axioms, induction hypothesis, seeds]
SeeAlso: [cachedProofFor, multiwaySubProofCones, MultiwayEquationalGraph, IslandsPanel]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[multiwaySystemFor]()[*ru*]</code> bundles the axioms, induction hypothesis, derived-lemma rows, and base/step seed equations for the Turing machine *ru* into a single association.

## Details & Options

- The result has keys `"Axioms"`, `"IH"` (the induction hypothesis), `"Rows"` (derived-lemma axioms), `"StepEq"`, `"StepSeeds"`, `"BaseSeeds"`, and `"RawAxioms"` (the transition + boundary + run-length axioms before any derived lemmas).
- This is the shared input consumed by the multiway panel functions — <code>[IslandsPanel]()</code>, <code>[StatementPanel]()</code>, <code>[TokenEventPanel]()</code>, <code>[SettingsPanel]()</code>, and <code>[RuleSpacePanel]()</code>.
- The proof-derived entries come from <code>[cachedProofFor]()</code>; the result is memoized.

## Basic Examples

The parts available for the binary-incrementer machine 453:

```wl
Keys[multiwaySystemFor[453]]
```

<!-- => {"Axioms", "IH", "Rows", "StepEq", "StepSeeds", "BaseSeeds", "RawAxioms"} -->
