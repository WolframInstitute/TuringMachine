---
Template: Symbol
Name: RenderUniversalGoal
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/RenderUniversalGoal
Keywords: [Turing machine, universal, forall, goal, rendering, inductive proof]
SeeAlso: [RenderEquation, RenderAxiomGrid, RenderConfiguration, FindInductiveProof]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[RenderUniversalGoal]()[*var*, *eqn*]</code> renders <code>ForAll[*var*, *eqn*]</code> as a universal-quantifier glyph subscripted by *var*, followed by the rendered equation.

## Details & Options

- *eqn* is an `Equal` between two tape terms; *var* is the bound variable (typically the induction variable `n`).
- The quantifier glyph is sized and baseline-aligned to sit next to the tape-cell rows produced by <code>[RenderEquation]()</code>.
- The shared render-style options are accepted, including `"QuantifierSize"` and `"QuantifierTraditional"`.

## Basic Examples

Render the universally-quantified run-length identity:

```wl
RenderUniversalGoal[n, ones[succ[n], y] == seq[ones[n, y], s1]]
```
