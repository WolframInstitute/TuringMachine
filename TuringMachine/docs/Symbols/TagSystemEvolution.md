---
Template: Symbol
Name: TagSystemEvolution
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TagSystemEvolution
Keywords: [evolution, tag system, Smith, universality]
SeeAlso: [TuringMachineToTagSystem, TagSystemToTuringMachine, TagSystemToCyclicTagSystem, CyclicTagSystemEvolution]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[TagSystemEvolution]()[*tag*, *n*]</code> gives the words of the 2-tag system *tag* for *n* steps or until it halts.

<code>[TagSystemEvolution]()[*tag*, *n*, *crit*]</code> gives the rules *t* -> *c* for the steps *t* whose configuration *c* satisfies *crit*, keeping only those.

## Details & Options

- A 2-tag system is an association with keys `"Productions"` and `"Word"`: a step deletes the first two symbols and appends the production of the first. It halts when the word has fewer than two symbols.
- The form with *crit* stores only the selected configurations and suits long runs.
- It follows the Lean definition `TagSystem.Tag.step` of the formal proof.

## Basic Examples

The start of the run:

```wl
Take[TagSystemEvolution[TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}], 18], 4]
```

---

Visualize the run:

```wl
ArrayPlot[PadRight[TagSystemEvolution[TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}], 85]], ColorFunction -> "Rainbow"]
```

## Scope

The tag steps at which the word starts with the symbol 5:

```wl
Keys[TagSystemEvolution[TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}], 85, First[#] == 5 &]]
```
