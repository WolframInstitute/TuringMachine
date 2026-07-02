---
Template: Symbol
Name: MultiwayEquationalGraph
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/MultiwayEquationalGraph
Keywords: [Turing machine, multiway, equational, rewriting, proof path, graph]
SeeAlso: [MultiwayGeodesicGraph, MultiwayTokenEventGraph, MultiwayRuleGraph, IslandsPanel]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[MultiwayEquationalGraph]()[*axioms*, *seeds*, *steps*]</code> evolves a multiway equational-rewrite cloud from *seeds* for *steps* generations and renders it as a graph, highlighting the equational proof path between the seed expressions.

## Details & Options

- *axioms* is a list of equational axioms; *seeds* is a list of the starting expressions (typically the two sides of a goal equation).
- Each axiom is turned into rewrite rules applied at every position; the cloud is the reachable term space, with the connecting proof path drawn in.
- The following options can be given:

| option | default | description |
| --- | --- | --- |
| `"CriticalPairs"` | `False` | also rewrite with superposition (critical-pair) rules |
| `"WellFormedOnly"` | `True` | keep only well-formed configurations |
| `"Oriented"` | `False` | rewrite downhill only, by a term-weight ordering |
| `"Ordering"` | `"LeafCount"` | the term weight (`"LeafCount"` or `"RunUnfold"`) |
| `"VertexLabels"` | `None` | label vertices with rendered terms |
| `"ArrowSize"` | `Automatic` | arrowhead size |
| `"CalloutMaxWidth"` | `240` | maximum width of seed callouts |

## Basic Examples

Evolve the cloud connecting a two-cell ones run to its `s1`-appended form:

```wl
MultiwayEquationalGraph[
   {ForAll[y, ones[zero, y] == y], ForAll[{m, y}, ones[succ[m], y] == seq[ones[m, y], s1]]},
   {ones[succ[zero], x], seq[x, s1]},
   3
]
```
