---
Template: Symbol
Name: System5
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System5
Keywords: [System 5, bag, xor merge, Smith, universality, RulePlot]
SeeAlso: [CyclicTagSystemToSystem5, System5Evolution, System5EvolutionPlot, System5ToSystem4, EmulationParameters]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System5]()[<|"Bag" -> *bag*, "Rules" -> {*r1*, *r2*, ...}|>]</code> is a program of Smith's System 5 with the bag *bag* and the rules *ri*, lists of integers.

<code>[System5]()[*bag*, *rules*]</code> is <code>[System5]()[<|"Bag" -> *bag*, "Rules" -> *rules*|>]</code>.

<code>*s5*["*key*"]</code> gives a part of the program *s5*.

## Details & Options

- A step decrements every bag element and increments every rule entry. When an element reaches 0 it is removed and the first rule is merged into the bag with parity: an integer already in the bag is removed rather than added. The program halts when the bag or the rules run out.
- A program displays as <code>[RulePlot]()[*s5*]</code>: the bag and each rule on the number line, up to 16 rules.
- <code>[Normal]()[*s5*]</code> gives the association. Every function of the paclet that takes a System 5 program takes its association as well.

## Basic Examples

Smith's System 5 program of p. 33 of his paper:

```wl
System5[{2}, {{1, 4}, {1, 6}, {}, {}}]
```

---

Its run:

```wl
System5EvolutionPlot[System5[{2}, {{1, 4}, {1, 6}, {}, {}}], 20]
```

## Scope

The program that emulates one cycle of Smith's cyclic tag system:

```wl
CyclicTagSystemToSystem5[CyclicTagSystem[{{1}, {1, 0}}, {0, 1}], 1]
```

---

The parts of a program:

```wl
System5[{2}, {{1, 4}, {1, 6}, {}, {}}]["Rules"]
```

## Properties and Relations

The length of the run and the parameters of its emulation by Wolfram's 2,3 machine:

```wl
System5Evolution[System5[{2}, {{1, 4}, {1, 6}, {}, {}}], Infinity, "Length"]
```

```wl
EmulationParameters[System5[{2}, {{1, 4}, {1, 6}, {}, {}}]]
```

---

The System 4 tape of a program:

```wl
System5ToSystem4[System5[{1, 3}, {{1}, {}}], 1]
```
