---
Template: Symbol
Name: multiwaySubProofCones
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/multiwaySubProofCones
Keywords: [Turing machine, multiway, cone, sub-proof, superposition]
SeeAlso: [multiwayCloudOverlap, multiwaySystemFor, MultiwayInductiveProofPanel, cachedProofFor]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[multiwaySubProofCones]()[*ru*]</code> builds a bounded multiway rewrite cloud (a "cone") around each sub-proof of the induction proof for the Turing machine *ru*.

## Details & Options

- A cone is grown for the base case, the step case, and each grafted derived-lemma case; growth is confined to the term-size regime of the proof it envelops so the non-terminating rewrite system does not run away.
- The result is an association with keys `"ProofGraph"`, `"CaseList"`, and `"Cones"` (the per-case clouds).
- Options include `"MaxStates"`, `"SuperposeGenerations"`, `"Beam"`, `"MaxNew"`, `"SizeBound"`, `"SizeMargin"`, `"ThickenAroundProof"`, `"GraftDerived"`, and `"Axioms"` (`"Raw"` or the proof's axioms).
- This is the data <code>[multiwayCloudOverlap]()</code> measures and <code>[MultiwayInductiveProofPanel]()</code> embeds the proof into.

## Basic Examples

Build the cones for the binary-incrementer machine 453 and list the parts:

```wl
Keys[multiwaySubProofCones[453]]
```

<!-- => {"ProofGraph", "CaseList", "Cones"} -->
