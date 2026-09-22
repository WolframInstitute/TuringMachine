---
Template: Symbol
Name: EmulationParameters
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/EmulationParameters
Keywords: [parameters, closed form, Smith, universality, System 5]
SeeAlso: [System5ToSystem4, System4ToSystem3, EmulationSizes]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[EmulationParameters]()[*s5*]</code> gives the parameters of the emulation of the System 5 program *s5* by wolfram23, from the lengths of its System 5 and System 4 runs.

<code>[EmulationParameters]()[*s5*, "ClosedForm"]</code> gives them from the closed-form bounds on those runs, as the formal proof's initial condition does.

## Details & Options

- The keys are `"B"` (the largest integer of *s5*), `"T5"` (the System 5 run length), `"M"`, `"H"`, `"f"` (the System 4 parameter), `"Band"` (the band of the decoders), `"System4Length"`, `"T4"` (the System 4 run length), `"Fuel"` and `"w"` (the block width is `2^w`).
- In closed form `"T5"` is `B 2^r` for *r* rules and `"T4"` is `(2 L + 2)(L + 1)` for the System 4 length *L*; every other parameter is the same expression of these. These bounds define the initial condition `Smith.icStart` of the formal proof, which runs no system.
- `"w"` is the bit length of `Fuel + 3 f + 6`, so that the blocks hold the fuel and every set element.
- The exact form runs the System 4 tape, which is only practical for small programs.

## Basic Examples

The parameters of Smith's example from the exact runs:

```wl
Dataset[EmulationParameters[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>]]
```

---

The same from the closed-form bounds:

```wl
Dataset[EmulationParameters[<|"Bag" -> {2}, "Rules" -> {{1, 4}, {1, 6}, {}, {}}|>, "ClosedForm"]]
```
