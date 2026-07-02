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
| `"SizeBound"` | `Automatic` | confine the cloud to the proof's term-size regime |
| `"Labeled"` | `False` | draw labelled proof vertices instead of discs |
| `"Layout"` | `"SpringElectricalEmbedding"` | cloud layout |
| `"Width"` | `Automatic` | image width |

- With the default `"PinProof" -> True` the layout loads the `` WolframInstitute`Z3Link` `` paclet.

## Basic Examples

The proof for the binary-incrementer machine 453, embedded in its multiway cloud:

```wl
MultiwayInductiveProofPanel[453]
```
