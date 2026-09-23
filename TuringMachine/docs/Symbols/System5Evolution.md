---
Template: Symbol
Name: System5Evolution
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/System5Evolution
Keywords: [evolution, System 5 program, Smith, universality]
SeeAlso: [CyclicTagSystemToSystem5, System5ToCyclicTagSystem, System5ToSystem4, EmulationParameters, System5EvolutionPlot]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[System5Evolution]()[*s5*, *n*]</code> gives the configurations of the System 5 program *s5* for *n* steps or until it halts.

<code>[System5Evolution]()[*s5*, *n*, *crit*]</code> gives the rules *t* -> *c* for the steps *t* whose configuration *c* satisfies *crit*, keeping only those.

<code>[System5Evolution]()[*s5*, *n*, "Length"]</code> gives the number of steps the run takes, up to *n*.

## Details & Options

- System 5 halts when the bag or the list of rules is empty.
- The `"Length"` form computes the length of the run from the times at which bag elements reach 0, without building the configurations; it is fast on programs with thousands of rules. *n* may be <code>[Infinity]()</code>.
- The form with *crit* stores only the selected configurations and suits long runs.
- It follows the Lean definition `BiTM.System5.step` of the formal proof.

## Basic Examples

The run of Smith's program of p. 33:

```wl
System5Evolution[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>, 20]
```

---

The length of the run:

```wl
System5Evolution[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>, Infinity, "Length"]
```

## Scope

The configurations after the first rule has been used:

```wl
System5Evolution[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>, 20, Length[#["Rules"]] < 4 &]
```

