---
Template: Symbol
Name: multiwayDistance
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/multiwayDistance
Keywords: [Turing machine, multiway, distance, rewriting, graph distance]
SeeAlso: [MultiwayGeodesicGraph, MultiwayEquationalGraph, multiwaySystemFor]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[multiwayDistance]()[*lhs*, *rhs*, *axioms*, *steps*]</code> evolves a multiway rewrite cloud seeded at *lhs* and *rhs* for *steps* generations and returns the graph distance between them.

## Details & Options

- *lhs* and *rhs* are tape terms; *axioms* is the list of equational axioms driving the rewriting.
- The two seeds are rewritten in all ways for *steps* generations, and the distance is measured in the resulting undirected multiway graph. It is `Infinity` if the two remain disconnected within that many steps.
- A fourth option controls whether only well-formed configurations are kept (default `True`).

## Basic Examples

One rewrite step separates a two-cell ones run from its `s1`-appended form:

```wl
multiwayDistance[
   ones[succ[zero], x], seq[x, s1],
   {ForAll[{m, y}, ones[succ[m], y] == seq[ones[m, y], s1]], ForAll[y, ones[zero, y] == y]},
   4
]
```

<!-- => 1 -->
