---
Template: Symbol
Name: onesRunDefinitions
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/onesRunDefinitions
Keywords: [Turing machine, run length, axioms, tape, inductive proof]
SeeAlso: [zerosRunDefinitions, CompressToRunLength, RenderAxiomGrid]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[onesRunDefinitions]()</code> is the list of run-length definitions of the `ones[n, ...]` constructor, as `ForAll`-quantified equations:

```
ForAll[y, ones[zero, y] == y]
ForAll[{m, y}, ones[succ[m], y] == seq[ones[m, y], s1]]
```

## Details & Options

- `ones[n, tail]` denotes a run of *n* copies of the `s1` tape symbol on top of `tail`; these two equations define it inductively over the Peano numeral *n*.
- Together with <code>[zerosRunDefinitions]()</code> they let a run-length-compressed configuration (see <code>[CompressToRunLength]()</code>) be expanded or matched during a proof.

## Basic Examples

```wl
RenderAxiomGrid[Join[onesRunDefinitions, zerosRunDefinitions]]
```
