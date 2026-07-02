---
Template: Symbol
Name: RenderAxiomGrid
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/RenderAxiomGrid
Keywords: [Turing machine, axioms, grid, rendering, visualization, inductive proof]
SeeAlso: [RenderEquation, RenderConfiguration, RenderUniversalGoal]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[RenderAxiomGrid]()[*axioms*]</code> renders a list of `ForAll`-quantified axioms as a two-column grid of rendered equations, aligned on the `=`.

<code>[RenderAxiomGrid]()[*axioms*, *s*]</code> renders them for a machine with *s* states.

## Details & Options

- *axioms* is a list whose entries are equations or `ForAll` quantifications over equations between tape terms.
- Each row is produced by <code>[RenderEquation]()</code> in split form, so the left sides, the `=`, and the right sides line up in columns.
- *s* defaults to 2; the shared render-style options are accepted.

## Basic Examples

Render the two run-length definitions for `ones`:

```wl
RenderAxiomGrid[{
   ForAll[y, ones[zero, y] == y],
   ForAll[{m, y}, ones[succ[m], y] == seq[ones[m, y], s1]]
}]
```
