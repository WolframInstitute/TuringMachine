---
Template: Symbol
Name: unboundAxiom
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/unboundAxiom
Keywords: [Turing machine, axiom, boundary, tape, inductive proof]
SeeAlso: [boundaryAxiomsFor, transitionAxiomsFor, RenderAxiomGrid]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[unboundAxiom]()</code> is the axiom `ForAll[x, unbnd[seq[x, bnd]] == x]`, which strips the boundary marker `bnd` from a tape configuration.

## Details & Options

- It closes the boundary rewrite system produced by <code>[boundaryAxiomsFor]()</code> so that a configuration ending at the tape boundary can be reduced to its unbounded form.

## Basic Examples

```wl
unboundAxiom
```

Use it alongside the boundary axioms of a machine:

```wl
RenderAxiomGrid[Join[boundaryAxiomsFor[453], {unboundAxiom}]]
```
