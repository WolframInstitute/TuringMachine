---
Template: Symbol
Name: System4Evolution
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System4Evolution
Keywords: [evolution, System 4 tape, Smith, universality]
SeeAlso: [System5ToSystem4, System4ToSystem5, System4ToSystem3, EmulationParameters]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System4Evolution]()[*s4*, *n*]</code> gives the configurations of the System 4 tape *s4* for *n* steps or until it halts.

<code>[System4Evolution]()[*s4*, *n*, *crit*]</code> gives the rules *t* -> *c* for the steps *t* whose configuration *c* satisfies *crit*, keeping only those.

## Details & Options

- A System 4 step acts on the active element: in state A the head moves left over sets and deletes a star; in states B and C it decrements a set (switching between B and C when the set contained 0) and moves right; a star in state B is deleted and the head turns left; a star in state C toggles 1 in the next set. The run stops when the head passes the right end.
- The form with *crit* stores only the selected configurations and suits long runs.
- It follows the Lean definition `BiTM.System4.step` of the formal proof.

## Basic Examples

The length of the run, counting the start:

```wl
Length[System4Evolution[System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1], 10^4]]
```

---

Plot the position of the head:

```wl
ListLinePlot[#["Active"] & /@ System4Evolution[System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1], 10^4]]
```

## Scope

The steps at which the head is back at the left end in state B:

```wl
Keys[System4Evolution[System5ToSystem4[<|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>, 1], 10^4, #["Active"] == 0 && #["State"] === "B" &]]
```
