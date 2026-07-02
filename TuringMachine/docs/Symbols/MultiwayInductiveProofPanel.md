---
Template: Symbol
Name: MultiwayInductiveProofPanel
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/MultiwayInductiveProofPanel
Keywords: [Turing machine, inductive proof, multiway, cloud, panel, embedding]
SeeAlso: [proofGraph, multiwaySubProofCones, multiwayCloudOverlap, inductionProofGraph]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[MultiwayInductiveProofPanel]()[*ru*]</code> draws the grafted inductive proof graph for the Turing machine *ru* at full opacity, embedded inside the faded multiway term-space cloud of all its sub-proofs.

## Details & Options

- The proof graph (from <code>[inductionProofGraph]()</code>) is placed inside the sub-proof cones (from <code>[multiwaySubProofCones]()</code>) so the proof is shown as a path through the surrounding rewrite space.
- The following options can be given:

| option | default | description |
| --- | --- | --- |
| `"GraftDerived"` | `True` | graft each derived-axiom sub-proof into the proof graph |
| `"PinProof"` | `True` | pin the proof at its own layout while the cloud arranges around it |
| `"BackgroundOpacity"` | `0.25` | opacity of the faded cloud |
| `"CloudCore"` | `2` | keep only the *k*-core of the cloud, dropping splaying tendrils |
| `"MaxStates"` | `500` | total cloud-state cap |
| `"DirectOverlap"` | `False` | grow `"MaxStates"` until the sub-proof clouds directly share terms |
| `"SizeBound"` | `Automatic` | confine the cloud to the proof's term-size regime |
| `"Labeled"` | `False` | draw labelled proof vertices instead of discs |
| `"Layout"` | `"SpringElectricalEmbedding"` | cloud layout |
| `"Width"` | `Automatic` | image width |

- With the default `"PinProof" -> True` the layout loads the `` WolframInstitute`Z3Link` `` paclet.
- The sub-proof-cone options of <code>[multiwaySubProofCones]()</code> (such as `"Beam"`, `"MaxNew"`, `"Oriented"`, and `"WellFormedOnly"`) are also accepted and passed through to the surrounding cloud.

## Basic Examples

The proof for the binary-incrementer machine 453, embedded in its multiway cloud:

```wl
MultiwayInductiveProofPanel[453]
```

## Options

Lay the proof out with a layered embedding, grow the cloud with `"DirectOverlap"` until the sub-proofs share terms, and tune the edge and vertex styling:

```wl
MultiwayInductiveProofPanel[453,
   "Layout" -> "LayeredDigraphEmbedding", "PinProof" -> False,
   "BackgroundOpacity" -> 0.3, "MaxStates" -> 20, "MaxNew" -> 40, "Beam" -> 40,
   "DirectOverlap" -> True, "Oriented" -> False, "WellFormedOnly" -> True,
   "CloudEdgeThickness" -> 1.0, "ProofEdgeThickness" -> 1.4,
   "InductionEdgeThickness" -> 1.4, "ProofEdgeColor" -> GrayLevel[0.0],
   "ArrowSize" -> 0.005, "ProofVertexScale" -> 0.25]
```
