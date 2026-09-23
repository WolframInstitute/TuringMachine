---
Template: Symbol
Name: EmulationSizes
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/EmulationSizes
Keywords: [sizes, emulation, Smith, universality, Turing machine]
SeeAlso: [EmulationParameters, TuringMachineToTagSystem, CyclicTagSystemToSystem5]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[EmulationSizes]()[*machine*, *config*, *n*]</code> gives the size of every stage of the emulation of *n* steps of the binary Turing machine *machine* from *config* by wolfram23.

## Details & Options

- The keys are `"TagSymbols"`, `"TagWord"`, `"TagSteps"` (the tag time of *n* steps, and the number of cyclic tag cycles), `"CyclicTagData"`, `"Appendants"`, `"System5Rules"`, `"System5Integers"`, `"System5Steps"`, `"f"`, `"System4Elements"` and `"Wolfram23CellsAtLeast"`.
- The stages up to System 5 are built and System 5 is run; the System 4 and wolfram23 sizes are computed from the parameters without building those tapes. The wolfram23 size is a lower bound: it takes the System 4 run to be one sweep of its tape.

## Basic Examples

The sizes for one step of a two-state machine that halts:

```wl
EmulationSizes[{{1, 0} -> {0, 1, 1}}, {1, {}, 0, {}}, 1]
```

