---
Template: Symbol
Name: ParityBlock
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/ParityBlock
Keywords: [System 3, System 4, parity, rule 60, Smith, universality]
SeeAlso: [System4ToSystem3, System3Evolution, System3EvolutionPlot]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[ParityBlock]()[*set*, *w*]</code> gives Smith's block of <code>2^*w*</code> cells 1 and 2 that encodes the System 4 set *set* in System 3.

## Details & Options

- Reading 2 as a bit 1 and 1 as a bit 0, the block is the XOR of the rows `i` of the rule 60 cellular automaton started from a single 2, one for each member `i` of the set, and of the all-2 row; when that would not start with a 2 the row before the all-2 row is added too.
- A System 3 scan of a block replaces it by its prefix XOR. After `t` scans the block has odd parity exactly when `t` is in the set, for every `t` below <code>2^*w*</code> − 2.
- The elements of *set* must be below <code>2^*w*</code> − 2. <code>[System4ToSystem3]()</code> writes one block for each set of a System 4 tape.

## Basic Examples

The block of `{0, 2}` at width 8:

```wl
ParityBlock[{0, 2}, 3]
```

## Scope

The blocks of `{i}` for the first eight `i` at width 16, a 2 drawn dark:

```wl
ArrayPlot[Table[ParityBlock[{i}, 4] - 1, {i, 0, 7}], Mesh -> All]
```

## Properties and Relations

The parities of the successive scans read the set back:

```wl
Mod[Total /@ NestList[Mod[Accumulate[#], 2] &, ParityBlock[{0, 2}, 3] - 1, 5], 2]
```
