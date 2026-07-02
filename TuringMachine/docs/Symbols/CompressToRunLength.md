---
Template: Symbol
Name: CompressToRunLength
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/CompressToRunLength
Keywords: [Turing machine, run-length, tape configuration, symbolic, compression]
SeeAlso: [RunMachine, RenderConfiguration, ShowTapeConfiguration]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[CompressToRunLength]()[*expr*]</code> compresses a left-nested tape configuration *expr* by collapsing each maximal run of `s0` or `s1` cells into a `zeros[*n*]` or `ones[*n*]` term.

## Details & Options

- *expr* is a `seq[...]` configuration, such as one of the steps returned by <code>[RunMachine]()</code>.
- Run-length terms `ones[*n*]` and `zeros[*n*]` are the compact form the inductive proofs and multiway renderers reason over.
- A single cell is left uncompressed; only runs of length two or more become run-length terms.

## Basic Examples

Collapse the two adjacent `s1` cells into a single `ones[2]` run:

```wl
CompressToRunLength[seq[seq[seq[end, s1], s1], s0]]
```

<!-- => seq[seq[end, ones[2]], s0] -->
