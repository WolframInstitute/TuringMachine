---
Template: Symbol
Name: MultiwayBothPanel
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/MultiwayBothPanel
Keywords: [Turing machine, multiway, induction, base case, step case, panel]
SeeAlso: [MultiwayTokenEventGraph, TokenEventPanel, MultiwayInductiveProofPanel]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[MultiwayBothPanel]()[*ru*]</code> renders side-by-side faded multiway token-event cones for the base and step cases of the Turing machine *ru*, captioned with the induction rule.

## Details & Options

- The left cone grows from the base statement (P₀) and the right from the step statement (Pₘ ⟹ Pₘ₊₁); the caption states the induction schema that combines them.
- Options include `"BaseSteps"` (default 6), `"StepSteps"` (default 8), `"Axioms"` (`"Raw"` or the proof's axioms), `"WellFormedOnly"`, `"Oriented"`, `"FadeOpacity"`, `"MaxStates"`, and `"Height"`.

## Basic Examples

The base and step cones for the binary-incrementer machine 453:

```wl
MultiwayBothPanel[453]
```
