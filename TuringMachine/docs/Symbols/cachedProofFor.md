---
Template: Symbol
Name: cachedProofFor
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/cachedProofFor
Keywords: [Turing machine, inductive proof, cache, memoization]
SeeAlso: [mergedProofFor, FindInductiveProof, proofGraph, multiwaySystemFor]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[cachedProofFor]()[*ru*]</code> returns the inductive proof association for the Turing machine *ru*, computing it with <code>[mergedProofFor]()</code> on the first call and caching the result on disk (and in memory) for subsequent calls.

## Details & Options

- The proof is the same association returned by <code>[mergedProofFor]()</code> / <code>[FindInductiveProof]()</code>, with keys such as `"Valid"`, `"Goal"`, `"BaseProof"`, `"StepProof"`, and `"LemmaProofs"`.
- The disk cache is a `.mx` file written next to the notebook (or the package), so a proof is searched at most once per machine.
- This is the accessor the proof-graph and multiway-panel functions call, so a machine's proof is shared across every view of it.

## Basic Examples

Fetch the cached proof for the binary-incrementer machine 453 and read its validity:

```wl
cachedProofFor[453]["Valid"]
```

<!-- => True -->

## Scope

The induction goal that was proved:

```wl
cachedProofFor[453]["Goal"]
```
