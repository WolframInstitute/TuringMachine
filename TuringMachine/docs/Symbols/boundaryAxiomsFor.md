---
Template: Symbol
Name: boundaryAxiomsFor
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/boundaryAxiomsFor
Keywords: [Turing machine, axioms, boundary, inductive proof, equational rewriting]
SeeAlso: [transitionAxiomsFor, unboundAxiom, RenderAxiomGrid, FindInductiveProof]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[boundaryAxiomsFor]()[*ru*]</code> returns the boundary axioms of Turing machine *ru* as a list of `ForAll`-quantified equations: the rules that describe what happens when the head reaches the boundary marker of the (one-sided) tape.

## Details & Options

- *ru* is a machine number (interpreted as an *s*=2, *k*=2 machine).
- The boundary axioms are used together with <code>[transitionAxiomsFor]()</code> and <code>[unboundAxiom]()</code> to state the full rewrite system for the induction proof.

## Basic Examples

Render the boundary axioms of machine 453, together with the unbound axiom:

```wl
RenderAxiomGrid[Join[boundaryAxiomsFor[453], {unboundAxiom}]]
```
