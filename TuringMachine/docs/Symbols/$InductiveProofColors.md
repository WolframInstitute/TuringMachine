---
Template: Symbol
Name: $InductiveProofColors
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/$InductiveProofColors
Keywords: [Turing machine, inductive proof, colors, style, dark mode, LightDarkSwitched]
SeeAlso: [proofGraph, MultiwayInductiveProofPanel, RenderConfiguration, $PvsNPStyles]
RelatedGuides: [TuringMachine]
---

## Usage

`$InductiveProofColors` is the association of every color used by the proof-graph and multiway renderers, keyed by role.

## Details & Options

- Keys name roles such as `"AxiomBackground"`, `"AxiomFrame"`, `"TheoremBackground"`, `"TheoremFrame"`, `"InductionFill"`, `"EquationalEdge"`, `"PathHighlight"`, `"DefaultEventFill"`, and the tape-cell colors `"CellBackground"` / `"CellEdge"`.
- Each value is a `LightDarkSwitched[*light*, *dark*]` pair, so the graphics adapt to the notebook's light or dark theme.
- Read an entry to reuse the package's styling in your own graphics; every renderer here draws from this one association.

## Basic Examples

The available color roles:

```wl
Keys[$InductiveProofColors]
```

## Scope

The theme-switched color used for axiom vertex backgrounds:

```wl
$InductiveProofColors["AxiomBackground"]
```
