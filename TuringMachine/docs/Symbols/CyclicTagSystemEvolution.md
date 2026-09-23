---
Template: Symbol
Name: CyclicTagSystemEvolution
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/CyclicTagSystemEvolution
Keywords: [evolution, cyclic tag system, Smith, universality]
SeeAlso: [TagSystemToCyclicTagSystem, CyclicTagSystemToTagSystem, CyclicTagSystemToSystem5, TagSystemEvolution]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[CyclicTagSystemEvolution]()[*cts*, *n*]</code> gives the configurations of the cyclic tag system *cts* for *n* steps or until it halts.

<code>[CyclicTagSystemEvolution]()[*cts*, *n*, *crit*]</code> gives the rules *t* -> *c* for the steps *t* whose configuration *c* satisfies *crit*, keeping only those.

## Details & Options

- A step deletes the first bit of the working string and, if it was 1, appends the current appendant; the phase then advances. The run stops when the working string is empty.
- The form with *crit* stores only the selected configurations and suits long runs.
- It follows the Lean definition `TagSystem.CTS.step` of the formal proof.

## Basic Examples

The run of Smith's example `1 10` on `01`:

```wl
run = CyclicTagSystemEvolution[<|"Appendants" -> {{1}, {1, 0}}, "Data" -> {0, 1}, "Phase" -> 0|>, 12]
```

The working strings drawn:

```wl
ArrayPlot[PadRight[run[[All, "Data"]]]]
```

## Scope

The configurations at which a cycle begins:

```wl
CyclicTagSystemEvolution[<|"Appendants" -> {{1}, {1, 0}}, "Data" -> {0, 1}, "Phase" -> 0|>, 40, #["Phase"] == 0 &]
```

