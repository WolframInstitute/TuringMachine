---
Template: Symbol
Name: inductionProofGraph
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/inductionProofGraph
Keywords: [Turing machine, inductive proof, proof graph, token-event, graft]
SeeAlso: [proofGraph, cachedProofFor, FindInductiveProof, MultiwayInductiveProofPanel]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[inductionProofGraph]()[*p*]</code> builds the token-event proof graph (the fused base and step cases) for an inductive proof association *p*.

## Details & Options

- *p* is a proof association as returned by <code>[FindInductiveProof]()</code>, <code>[mergedProofFor]()</code>, or <code>[cachedProofFor]()</code>.
- Base-case and step-case token-event graphs are laid out side by side and joined through an induction node and a universally-quantified goal node.
- The following options can be given:

| option | default | description |
| --- | --- | --- |
| `"GraftDerived"` | `True` | graft each derived-axiom sub-proof onto its use site; `False` shows derived axioms as given (green) axioms |
| `"MergeAsAxiom"` | `False` | color grafted use sites as axioms rather than derived theorems |
| `"LemmaComponents"` | `All` | which lemma-case components to include |

- Vertices carry equation-box or event-disc shapes; use <code>[proofGraph]()</code> for a laid-out, styled rendering.

## Basic Examples

Build the proof graph for the binary-incrementer machine 453:

```wl
inductionProofGraph[cachedProofFor[453]]
```
