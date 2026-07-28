---
Template: Symbol
Name: goalFor
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/goalFor
Keywords: [Turing machine, goal, inductive proof, statement]
SeeAlso: [cachedProofFor, forAllBody, RenderUniversalGoal, FindInductiveProof]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[goalFor]()[*ru*]</code> returns the goal equation of Turing machine *ru* — the universally quantified statement proved by induction, i.e. `cachedProofFor[ru]["Goal"]`.

## Details & Options

- The goal is a `ForAll`-quantified equation over the run-length variable; use <code>[forAllBody]()</code> to strip the quantifier and <code>[RenderUniversalGoal]()</code> to render it.

## Basic Examples

Render the universal goal of machine 453 with the quantifier variable renamed:

```wl
RenderUniversalGoal[m, forAllBody[goalFor[453]] /. n -> m]
```
