---
Template: Symbol
Name: CyclicTagSystemToTagSystem
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/CyclicTagSystemToTagSystem
Keywords: [cyclic tag system, tag system, decoder, Cook]
SeeAlso: [TagSystemToCyclicTagSystem, TagSystemToTuringMachine]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[CyclicTagSystemToTagSystem]()[*data*, *k*]</code> decodes the cyclic tag working string *data* to the tag word over *k* symbols.

## Details & Options

- *data* must consist of whole blocks of *k* bits, each with a single 1; otherwise the result is <code>[Missing]()</code>`["NotAnEncoding"]`.
- It transcribes the Lean definition `TagSystem.tagWordDecode` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

Decode two blocks of four bits:

```wl
CyclicTagSystemToTagSystem[{0, 1, 0, 0, 0, 0, 0, 1}, 4]
```

---

A block with two 1s is not an encoding:

```wl
CyclicTagSystemToTagSystem[{1, 1, 0, 0}, 4]
```

