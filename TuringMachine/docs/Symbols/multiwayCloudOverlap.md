---
Template: Symbol
Name: multiwayCloudOverlap
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/multiwayCloudOverlap
Keywords: [Turing machine, multiway, overlap, shared terms, confluence]
SeeAlso: [multiwaySubProofCones, MultiwayInductiveProofPanel, multiwaySystemFor]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[multiwayCloudOverlap]()[*ru*]</code> measures how the per-sub-proof multiway clouds of the Turing machine *ru* share terms.

## Details & Options

- The result is an association whose keys include `"Cones"`, `"ConeSizes"`, `"SharedTermCount"`, `"SharedTerms"`, `"SharingMultiplicity"` (terms shared by exactly *k* cones), `"MaxSharing"`, `"PairwiseOverlap"`, `"OverlapGraph"`, `"Components"`, and `"Connected"`.
- `"Connected" -> True` means every sub-proof cloud is tied to the others through shared terms — the sub-proofs meet in one confluent term space.
- Accepts the <code>[multiwaySubProofCones]()</code> options (`"MaxStates"`, `"GraftDerived"`, `"SuperposeGenerations"`, `"ThickenAroundProof"`, `"Axioms"`).

## Basic Examples

Measure the overlap for the binary-incrementer machine 453:

```wl
multiwayCloudOverlap[453]["Connected"]
```

<!-- => True -->
