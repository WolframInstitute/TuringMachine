---
Template: Symbol
Name: MultiwayTokenEventGraph
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/MultiwayTokenEventGraph
Keywords: [Turing machine, multiway, token-event, rewriting, graph]
SeeAlso: [MultiwayEquationalGraph, MultiwayGeodesicGraph, MultiwayRuleGraph, TokenEventPanel]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[MultiwayTokenEventGraph]()[*axioms*, *seeds*, *steps*]</code> evolves a multiway rewrite cloud from *seeds* for *steps* generations in token-event form — state to event to state, with an axiom vertex feeding each event — and highlights the proof path between the seeds.

## Details & Options

- Each rewrite becomes an event vertex fed by the state it rewrites and the axiom it applies, making explicit which axiom drives each step.
- The following options can be given:

| option | default | description |
| --- | --- | --- |
| `"WellFormedOnly"` | `True` | keep only well-formed configurations |
| `"Labeled"` | `False` | draw labelled equation/axiom vertices instead of discs |
| `"CollapseAxioms"` | `False` | merge equal axiom applications into one vertex |
| `"ShowAxioms"` | `True` | draw the axiom vertices feeding events |
| `"HighlightStyle"` | `"Red"` | how the proof path is highlighted (`"Red"`, `"Fade"`, `"Wash"`) |
| `"MaxStates"` | `Infinity` | cap on the number of states explored |
| `"Oriented"` | `False` | rewrite downhill only |
| `"CriticalPairs"` | `False` | include superposition rules |
| `"ArrowSize"` | `0.011` | arrowhead size |

## Basic Examples

Token-event cloud connecting a ones run to its `s1`-appended form:

```wl
MultiwayTokenEventGraph[
   {ForAll[y, ones[zero, y] == y], ForAll[{m, y}, ones[succ[m], y] == seq[ones[m, y], s1]]},
   {ones[succ[zero], x], seq[x, s1]},
   3
]
```
