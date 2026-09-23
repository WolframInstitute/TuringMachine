---
Template: Symbol
Name: CyclicTagSystemToSystem5
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/CyclicTagSystemToSystem5
Keywords: [System 5, cyclic tag system, Smith, universality, bag]
SeeAlso: [System5Evolution, System5ToCyclicTagSystem, System5ToSystem4, EmulationParameters]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[CyclicTagSystemToSystem5]()[*cts*, *n*]</code> gives Smith's System 5 program that emulates *n* cycles of the cyclic tag system *cts*.

## Details & Options

- The result is a <code>[System5]()</code> program, with the keys `"Bag"` (a list of integers) and `"Rules"` (a list of lists of integers). A step decrements every bag element and increments every rule entry; when an element reaches 0 it is removed and the first rule is merged into the bag with parity (an integer already present is removed).
- System 5 emulates the doubled cyclic tag system, whose working string has every bit twice and whose appendants are the doubled appendants each followed by an empty one. A bit becomes two pairs of bag integers, with gaps 1 for a 0 and 2 for a 1.
- Each appendant gives four rules; *n* cycles give `4 n` times the number of appendants.
- It transcribes the Lean definition `BiTM.ctsToSystem5` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

Smith's example of p. 29, the cyclic tag system with the appendants `1` and `10` on the working string `01`, for one cycle:

```wl
CyclicTagSystemToSystem5[CyclicTagSystem[{{1}, {1, 0}}, {0, 1}], 1]
```

## Scope

The program for two cycles:

```wl
s5 = CyclicTagSystemToSystem5[CyclicTagSystem[{{1}, {1, 0}}, {0, 1}], 2]
```

Its run:

```wl
run = System5Evolution[s5, 1000]
```

The bags decode to the doubled working strings, in order:

```wl
First /@ Split[DeleteMissing[System5ToCyclicTagSystem /@ run[[All, "Bag"]]]]
```

