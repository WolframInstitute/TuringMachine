---
Template: Symbol
Name: MultiwayGeodesicGraph
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/MultiwayGeodesicGraph
Keywords: [Turing machine, multiway, geodesic, rewriting, shortest path, graph]
SeeAlso: [MultiwayEquationalGraph, MultiwayTokenEventGraph, StatementPanel, SettingsPanel]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[MultiwayGeodesicGraph]()[*axioms*, *seeds*, *steps*]</code> evolves a multiway rewrite cloud from *seeds* for *steps* generations and renders it with the geodesic (shortest) path between the seeds highlighted.

## Details & Options

- *axioms* is a list of equational axioms; *seeds* is a list of starting expressions (or a single expression, whose geodesic to a proved `True` is shown).
- The following options can be given:

| option | default | description |
| --- | --- | --- |
| `"CriticalPairs"` | `False` | include superposition (critical-pair) rules |
| `"WellFormedOnly"` | `True` | keep only well-formed configurations |
| `"ShowLength"` | `False` | label the graph with the geodesic length |
| `"Oriented"` | `False` | rewrite downhill only |
| `"Ordering"` | `"LeafCount"` | the term weight used when oriented |
| `"CloudUndirected"` | `False` | draw the surrounding cloud as undirected |
| `"VertexLabels"` | `Automatic` | label vertices with rendered terms |
| `"ArrowSize"` | `Automatic` | arrowhead size |
| `"CalloutMaxWidth"` | `240` | maximum width of seed callouts |

## Basic Examples

Show the geodesic between a two-cell ones run and its `s1`-appended form:

```wl
MultiwayGeodesicGraph[
   {ForAll[y, ones[zero, y] == y], ForAll[{m, y}, ones[succ[m], y] == seq[ones[m, y], s1]]},
   {ones[succ[zero], x], seq[x, s1]},
   3
]
```
