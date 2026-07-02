---
Template: Symbol
Name: MultiwayRuleGraph
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/MultiwayRuleGraph
Keywords: [Turing machine, multiway, superposition, critical pair, rule space, graph]
SeeAlso: [MultiwayTokenEventGraph, MultiwayEquationalGraph, RuleSpacePanel]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[MultiwayRuleGraph]()[*axioms*]</code> builds the superposition (critical-pair) rule-space graph of an equational axiom set: each rule is a vertex, and superposing two rules to derive a new one is an event.

## Details & Options

- The following options can be given:

| option | default | description |
| --- | --- | --- |
| `"Generations"` | `1` | superposition depth |
| `"MaxNew"` | `25` | maximum new rules per generation |
| `"Oriented"` | `True` | orient rules by a term-weight ordering |
| `"Ordering"` | `"RunUnfold"` | the term weight (`"RunUnfold"` or `"LeafCount"`) |
| `"Labeled"` | `False` | draw labelled equation vertices instead of discs |
| `"WellFormedOnly"` | `False` | keep only well-formed critical pairs |
| `"VertexScaling"` | `"Density"` | how unlabelled vertex size adapts to node count |
| `"VertexScale"` | `1` | multiplier on the unlabelled vertex sizes |
| `"ArrowSize"` | `0.011` | arrowhead size |

## Basic Examples

The rule space of the two run-length definitions for `ones`:

```wl
MultiwayRuleGraph[{
   ForAll[y, ones[zero, y] == y],
   ForAll[{m, y}, ones[succ[m], y] == seq[ones[m, y], s1]]
}]
```
