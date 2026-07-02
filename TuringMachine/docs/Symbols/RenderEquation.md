---
Template: Symbol
Name: RenderEquation
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/RenderEquation
Keywords: [Turing machine, equation, tape, rendering, visualization, inductive proof]
SeeAlso: [RenderConfiguration, RenderAxiomGrid, RenderUniversalGoal, ShowTapeConfiguration]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[RenderEquation]()[*eqn*]</code> renders an equation between two tape configurations as tape-cell rows either side of an `=`.

<code>[RenderEquation]()[*eqn*, *split*]</code> with *split* `True` returns the triple `{*lhs*, "=", *rhs*}` instead of a single combined row.

## Details & Options

- *eqn* is an `Equal` (optionally wrapped in `ForAll`/`HoldForm`) between two `seq[...]` tape terms.
- Each side is rendered with <code>[RenderConfiguration]()</code>; free variables are drawn as labelled variable cells.
- An optional third argument gives the number of states *s* (default 2); the shared render-style options are also accepted.

## Basic Examples

Render one of the run-length axioms:

```wl
RenderEquation[ones[succ[n], y] == seq[ones[n, y], s1]]
```

## Options

Return the two sides and the equals sign separately, for placing in a grid:

```wl
RenderEquation[ones[succ[n], y] == seq[ones[n, y], s1], True]
```
