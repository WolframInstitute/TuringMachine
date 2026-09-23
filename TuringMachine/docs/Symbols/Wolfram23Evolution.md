---
Template: Symbol
Name: Wolfram23Evolution
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/Wolfram23Evolution
Keywords: [wolfram23, Wolfram 2,3 Turing machine, evolution, universality]
SeeAlso: [System3ToWolfram23, Wolfram23ToSystem5, EmulationSizes]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[Wolfram23Evolution]()[*config*, *n*]</code> gives the configurations of Wolfram's 2,3 Turing machine from *config* for *n* steps.

<code>[Wolfram23Evolution]()[*config*, *n*, *crit*]</code> gives the rules *t* -> *c* for the steps *t* at which <code>*crit*[*q*, *p*]</code> is <code>[True]()</code>, *q* being the state and *p* the number of cells left of the head.

## Details & Options

- A configuration is `{q, left, head, right}` with `q = 1` (A) or `2` (B) and cells 0, 1, 2; cells beyond the lists are 0. The rules are `A0 → 1 R B`, `A1 → 2 L A`, `A2 → 1 L A`, `B0 → 2 L A`, `B1 → 2 R B`, `B2 → 0 R A`. The machine never halts.
- The form with *crit* runs on a mutable tape and builds a configuration only when *crit* holds, which makes runs of millions of steps practical.
- It follows `BiTM.wolfram23` and `BiTM.step` of the formal proof.

## Basic Examples

Twenty steps of wolfram23 from a blank tape:

```wl
run = Wolfram23Evolution[{1, {}, 0, {}}, 20]
```

## Scope

The configurations at which wolfram23 is in state B at the left end of an emulated System 4 tape:

```wl
Wolfram23Evolution[System3ToWolfram23[System4ToSystem3[<|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>, 3, 3]], 2000, #1 == 2 && #2 == 6 &]
```

