---
Template: Symbol
Name: SettingsPanel
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/SettingsPanel
Keywords: [Turing machine, multiway, geodesic, panel, step case, tuning]
SeeAlso: [StatementPanel, MultiwayGeodesicGraph, IslandsPanel]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[SettingsPanel]()[*ru*]</code> renders the multiway geodesic graph for the full step case of the Turing machine *ru* — its axioms, induction hypothesis, and all derived-lemma rows together.

## Details & Options

- A convenience view over <code>[MultiwayGeodesicGraph]()</code> with every derived row included, useful for trying out panel options before applying them elsewhere.
- Options include `"Steps"`, `"WellFormedOnly"`, `"CriticalPairs"`, `"Oriented"`, `"Ordering"`, `"Labeled"`, `"Height"`, and `"Width"`.

## Basic Examples

The full step-case geodesic for the binary-incrementer machine 453:

```wl
SettingsPanel[453]
```
