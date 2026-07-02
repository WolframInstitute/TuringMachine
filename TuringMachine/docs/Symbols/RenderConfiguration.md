---
Template: Symbol
Name: RenderConfiguration
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/RenderConfiguration
Keywords: [Turing machine, tape, configuration, rendering, visualization, inductive proof]
SeeAlso: [RenderEquation, RenderAxiomGrid, RenderUniversalGoal, ShowTapeConfiguration, CompressToRunLength]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[RenderConfiguration]()[*expr*]</code> renders a left-nested tape configuration *expr* as a row of tape-cell graphics.

<code>[RenderConfiguration]()[*expr*, *s*]</code> renders it for a machine with *s* states.

## Details & Options

- *expr* is a `seq[...]` configuration over the tape alphabet (`s0`, `s1`, run-length terms `ones[*n*]` / `zeros[*n*]`, state symbols `qA`..`qH`, and boundary markers `end` / `bnd`).
- Each cell becomes a colored square; a head/state cell becomes a state-indicator dial; run-length terms are drawn with a lifted exponent.
- *s* (the number of states, default 2) selects how many distinct state dials are drawn.
- Accepts the shared render-style options (font size, cell size, traditional form, and so on).

## Basic Examples

Render a short configuration:

```wl
RenderConfiguration[seq[seq[end, s1], s0]]
```

## Scope

Compress a run before rendering it:

```wl
RenderConfiguration[CompressToRunLength[seq[seq[seq[end, s1], s1], s0]]]
```
