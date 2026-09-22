---
Template: Symbol
Name: TagSystemToTuringMachine
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TagSystemToTuringMachine
Keywords: [tag system, Turing machine, decoder, Cocke-Minsky]
SeeAlso: [TuringMachineToTagSystem, CyclicTagSystemToTagSystem]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[TagSystemToTuringMachine]()[*word*, *s*]</code> decodes the Cocke–Minsky tag word *word* of a machine with states below *s* to the machine configuration.

## Details & Options

- The configuration is given without trailing blanks on either side.
- A word that is not the word of a configuration gives <code>[Missing]()</code>`["NotAWord"]`; tag words between two tag times are not words of configurations.
- It transcribes the Lean definition `TagSystem.decodeWord` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

Decode the word of a configuration:

```wl
TagSystemToTuringMachine[TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {2, {1, 0}, 1, {0, 1, 0, 0}}]["Word"], 3]
```

---

A word from the middle of a round is not the word of a configuration:

```wl
TagSystemToTuringMachine[TagSystemEvolution[TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}], 5][[-1]], 3]
```
