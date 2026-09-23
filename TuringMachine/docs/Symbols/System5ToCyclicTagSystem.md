---
Template: Symbol
Name: System5ToCyclicTagSystem
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System5ToCyclicTagSystem
Keywords: [System 5, bag, decoder, cyclic tag system]
SeeAlso: [CyclicTagSystemToSystem5, System4ToSystem5]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System5ToCyclicTagSystem]()[*bag*]</code> decodes the System 5 bag *bag* to the doubled cyclic tag working string.

## Details & Options

- The sorted bag is read in pairs above 0: a gap of 1 is a 0, a gap of 2 a 1. Anything else gives <code>[Missing]()</code>`["NotAnEncoding"]`.
- The result is the working string of the doubled cyclic tag system, in which every bit appears twice.
- It transcribes the Lean definition `Smith.decodeBag` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

The bag of Smith's example decodes to `0 0 1 1`, the doubled `01`:

```wl
System5ToCyclicTagSystem[{1, 2, 3, 4, 5, 7, 8, 10}]
```

---

A gap of 3 is not an encoding:

```wl
System5ToCyclicTagSystem[{1, 4}]
```

