---
Template: Symbol
Name: zerosRunDefinitions
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/zerosRunDefinitions
Keywords: [Turing machine, run length, axioms, tape, inductive proof]
SeeAlso: [onesRunDefinitions, CompressToRunLength, RenderAxiomGrid]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[zerosRunDefinitions]()</code> is the list of run-length definitions of the `zeros[n, ...]` constructor, as `ForAll`-quantified equations:

```
ForAll[y, zeros[zero, y] == y]
ForAll[{m, y}, zeros[succ[m], y] == seq[zeros[m, y], s0]]
```

## Details & Options

- `zeros[n, tail]` denotes a run of *n* copies of the `s0` tape symbol on top of `tail`; these two equations define it inductively over the Peano numeral *n*.
- The `s0` counterpart of <code>[onesRunDefinitions]()</code>.

## Basic Examples

```wl
RenderAxiomGrid[Join[onesRunDefinitions, zerosRunDefinitions]]
```
