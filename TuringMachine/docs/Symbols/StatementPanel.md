---
Template: Symbol
Name: StatementPanel
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/StatementPanel
Keywords: [Turing machine, multiway, geodesic, panel, derived lemma]
SeeAlso: [MultiwayGeodesicGraph, IslandsPanel, SettingsPanel, multiwaySystemFor]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[StatementPanel]()[*ru*, *k*]</code> renders the multiway geodesic graph between the base or step seed equations of the Turing machine *ru*, seeded with the axioms plus the first *k* derived-lemma rows.

## Details & Options

- Builds on <code>[MultiwayGeodesicGraph]()</code>; adding lemma rows (raising *k*) shortens the geodesic as the proof's derived steps become available.
- Options include `"Case"` (`"Step"` or `"Base"`), `"Seeds"` (`"Equation"` or `"Pair"`), `"Steps"`, `"Oriented"`, `"Labeled"`, `"WellFormedOnly"`, `"Height"`, and `"Width"`.

## Basic Examples

The step-case geodesic for the binary-incrementer machine 453 with no derived rows yet:

```wl
StatementPanel[453, 0]
```
