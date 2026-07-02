---
Template: Symbol
Name: proofGraph
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/proofGraph
Keywords: [Turing machine, inductive proof, proof graph, layout, Z3, rendering]
SeeAlso: [inductionProofGraph, cachedProofFor, MultiwayInductiveProofPanel, FindInductiveProof]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[proofGraph]()[*ru*, *mode*]</code> renders the induction proof graph for the Turing machine *ru*, laid out and styled.

<code>[proofGraph]()[*p*, *mode*]</code> renders the proof graph for an already-built proof association *p*.

## Details & Options

- *mode* is `"Labelled"` (equation boxes) or `"Unlabelled"` (colored discs).
- With the default `"Layout" -> Automatic`, a custom Z3-based layered layout engine places the vertices and routes the edges; this loads the `` WolframInstitute`Z3Link` `` paclet on first use.
- Giving `"Layout"` a `GraphLayout` specification (e.g. `"LayeredDigraphEmbedding"`) uses Wolfram's own layout instead, with the same vertex shapes and edge colors.
- The full set of shared render-style options is accepted.

## Basic Examples

Render the unlabelled proof graph for the binary-incrementer machine 453:

```wl
proofGraph[453, "Unlabelled"]
```

## Options

Use a built-in Wolfram layout instead of the Z3 engine:

```wl
proofGraph[453, "Unlabelled", "Layout" -> "LayeredDigraphEmbedding"]
```
