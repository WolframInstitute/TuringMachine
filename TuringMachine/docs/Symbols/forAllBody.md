---
Template: Symbol
Name: forAllBody
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/forAllBody
Keywords: [Turing machine, quantifier, ForAll, inductive proof, goal]
SeeAlso: [goalFor, RenderUniversalGoal, FindInductiveProof]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[forAllBody]()[*axiom*]</code> strips the `ForAll` quantifiers from *axiom*, returning its body.

## Details & Options

- Works through nested quantifiers: `forAllBody[ForAll[x, ForAll[y, body]]]` returns *body*.
- Handy for re-rendering a quantified goal or axiom with a different quantifier variable, or for feeding the bare equation to another renderer.

## Basic Examples

Take the body of machine 453's goal and rename its variable:

```wl
RenderUniversalGoal[m, forAllBody[goalFor[453]] /. n -> m]
```
