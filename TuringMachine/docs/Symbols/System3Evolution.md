---
Template: Symbol
Name: System3Evolution
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System3Evolution
Keywords: [evolution, System 3 tape, Smith, universality]
SeeAlso: [System4ToSystem3, System3ToWolfram23, Wolfram23Evolution, System3EvolutionPlot]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System3Evolution]()[*s3*, *n*]</code> gives the configurations of the System 3 tape *s3* for *n* steps or until it halts.

<code>[System3Evolution]()[*s3*, *n*, *crit*]</code> gives the rules *t* -> *c* for the steps *t* whose configuration *c* satisfies *crit*, keeping only those.

## Details & Options

- System 3 is a lookahead machine: in some states its rule depends on the cell right of the head too, and rewrites both cells. The run stops when a rule would move off the tape.
- The form with *crit* stores only the selected configurations and suits long runs.
- It follows the Lean definitions `Smith.sys3` and `Smith.lstep` of the formal proof.

## Basic Examples

The run of the System 3 tape of `{0, 2} * {}`:

```wl
run = System3Evolution[System4ToSystem3[<|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>, 3, 3], 120]
```

The run drawn:

```wl
ArrayPlot[PadRight[Join[Reverse[#["Left"]], {#["Head"]}, #["Right"]] & /@ run], ColorRules -> {0 -> White, 1 -> LightGray, 2 -> Gray}]
```

## Scope

The configurations in state C:

```wl
System3Evolution[System4ToSystem3[<|"Elements" -> {{0, 2}, "*", {}}, "Active" -> 0, "State" -> "A"|>, 3, 3], 1000, #["State"] === "C" &]
```

