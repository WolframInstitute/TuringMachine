---
Template: Symbol
Name: FindInductiveProof
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/FindInductiveProof
Keywords: [Turing machine, inductive proof, equational proof, induction, FindEquationalProof]
SeeAlso: [mergedProofFor, cachedProofFor, proofGraph, inductionProofGraph]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[FindInductiveProof]()[*goal*, *axioms*]</code> proves <code>ForAll[*n*, *goal*]</code> by equational induction on `n`, returning an association describing the proof.

<code>[FindInductiveProof]()[*goal*, *axioms*, *t*]</code> time-constrains each proof search to *t* seconds.

## Details & Options

- *goal* is an `Equal` between two tape terms mentioning the induction variable `n`; *axioms* is a list of equational axioms (each an `Equal` or a `ForAll` over one).
- The base case (`n -> zero`) and the step case (`n -> succ[n]`, with *goal* itself added as the induction hypothesis) are each proved with the built-in `FindEquationalProof`.
- The result is an association with keys `"Valid"`, `"Goal"`, `"InductionVariable"`, `"Axioms"`, `"BaseGoal"`, `"StepGoal"`, `"IH"`, `"BaseProof"`, and `"StepProof"`. `"Valid"` is `True` only when both cases produced a `ProofObject`.
- *t* defaults to 30 seconds.

## Basic Examples

Prove that a one-cell-longer run of ones equals the run with a `s1` appended:

```wl
proof = FindInductiveProof[
   ones[succ[n], y] == seq[ones[n, y], s1],
   {ForAll[y, ones[zero, y] == y], ForAll[{m, y}, ones[succ[m], y] == seq[ones[m, y], s1]]},
   20
];
proof["Valid"]
```

<!-- => True -->

## Scope

The keys carried by the returned proof:

```wl
Keys[proof]
```

<!-- => {"Valid", "Goal", "InductionVariable", "Axioms", "BaseGoal", "StepGoal", "IH", "BaseProof", "StepProof"} -->
