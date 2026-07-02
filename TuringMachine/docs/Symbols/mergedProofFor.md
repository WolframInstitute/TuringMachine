---
Template: Symbol
Name: mergedProofFor
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/mergedProofFor
Keywords: [Turing machine, inductive proof, proof strategy, sweep, boundary, scan-flip]
SeeAlso: [cachedProofFor, FindInductiveProof, multiwaySystemFor, proofGraph]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[mergedProofFor]()[*ru*]</code> derives the inductive proof association for the Turing machine *ru* by trying, in order, the sweep, boundary, and scan-flip proof strategies, and returning the first one that succeeds.

## Details & Options

- *ru* is a machine number; its state/color shape is looked up internally.
- Each strategy derives its own behavioral lemmas (carry, absorb, tail-peel, scan, flip) rather than assuming them, and hands the assembled goal and axioms to <code>[FindInductiveProof]()</code>.
- The result is the same association shape returned by <code>[FindInductiveProof]()</code>, extended with a `"LemmaProofs"` key holding the sub-proofs. If no strategy succeeds, the last failure is returned.
- <code>[cachedProofFor]()</code> wraps this and memoizes the result on disk.

## Basic Examples

Derive the proof for the binary-incrementer machine 453:

```wl
mergedProofFor[453]["Valid"]
```

<!-- => True -->
