---
Template: Symbol
Name: transitionAxiomsFor
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/transitionAxiomsFor
Keywords: [Turing machine, axioms, transition rules, inductive proof, equational rewriting]
SeeAlso: [boundaryAxiomsFor, DecodeTuringMachineRules, RenderAxiomGrid, FindInductiveProof]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[transitionAxiomsFor]()[*ru*]</code> returns the transition axioms of Turing machine *ru* as a list of `ForAll`-quantified equations between tape configurations.

## Details & Options

- *ru* is a machine number (interpreted as an *s*=2, *k*=2 machine).
- Each transition rule `{state, symbol} -> {newState, write, move}` becomes one equational axiom relating the tape configuration before and after the step.
- The result is one of the axiom sets fed to <code>[FindInductiveProof]()</code> and displayed by <code>[RenderAxiomGrid]()</code>.

## Basic Examples

Render the transition axioms of machine 453:

```wl
RenderAxiomGrid[transitionAxiomsFor[453]]
```
