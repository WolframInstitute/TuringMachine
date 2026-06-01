---
Template: Paclet
ResourceType: Paclet
Name: WolframInstitute/TuringMachine
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
Description: Tools for exploring and analyzing Turing machines
ContributedBy: Nik Murzin and Willem Nielsen
Keywords: [Turing machine, one-sided Turing machine, multiway, nondeterministic, enumeration, NKS]
MainGuide: Documentation/English/Guides/TuringMachine.nb
License: MIT
WolframVersion: 14.3+
Categories: [Symbolic & Numeric Computation]
Disclosures: [PacletDependencies]
Sources: ["Stephen Wolfram, A New Kind of Science (Wolfram Media, 2002), Notes for Chapter 12, Section 8 (One-Sided Turing Machines), p. 1143"]
SourceControlURL: https://github.com/WolframInstitute/TuringMachine
RelatedResources: [TuringMachineFromNumber, TuringMachineToNumber, TuringMachineImport, Wolfram/Lambda]
Links: ["[One-sided Turing machines — A New Kind of Science | Online (Note (d), p. 1143)](https://www.wolframscience.com/nks/notes-12-8--one-sided-turing-machines/)"]
---

## Details & Options

- A Turing machine is specified by its Wolfram enumeration number together with its state and color counts, written `{number, s, k}` — for example `{600720, 3, 2}` is rule 600720 with 3 states and 2 colors.
- The one-sided functions read a non-negative integer input off the tape, run the machine, and report the halting value, the number of steps taken, or the maximum tape width reached.
- A machine that does not halt within the given step bound reports `Infinity` / `Undefined` for the parts it could not resolve.
- The multiway functions explore nondeterministic machines, where a `{state, color}` pair may carry several transitions, and return all reachable configurations.
- A Rust backend (loaded from the paclet's `Binaries`) accelerates the bulk enumeration and search functions over whole rule spaces.

## Usage

The paclet identifies a Turing machine by its enumeration number and its `{s, k}` state/color counts. [OneSidedTuringMachineFunction]() runs a one-sided machine on an integer input and returns its halting value, step count, or tape width; [OneSidedTuringMachinePlot]() draws the space-time evolution; and [OneSidedTuringMachineFind]() searches for machines reproducing given outputs. The [MultiwayTuringMachineFunction]() family explores nondeterministic (multiway) machines, while [TuringMachineRuleCount]() and the [TuringMachineOutput]() primitives tabulate behavior across whole rule spaces.

## Basic Examples

Run the one-sided Turing machine defined by the *s*=3, *k*=2 rule 600720 on input 1 for at most 32 steps:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32]
```

---

Return the number of steps the machine took to terminate:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, "Steps"]
```

---

Return the maximum width the head spanned on the tape:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, "Width"]
```

---

Return the steps, value, and width together:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, All]
```

---

Plot the space-time evolution of the machine on input 1:

```wl
OneSidedTuringMachinePlot[{600720, 3, 2}, 1, {5, 3}]
```

## Scope

Evaluate a whole family of machines at once — every *s*=1, *k*=2 one-sided machine on inputs 1 through 8, each for up to 32 steps:

```wl
OneSidedTuringMachineFunction[{All, 1, 2}, {1, 8}, 32]
```

---

Count how many distinct Turing machine rules exist for a given number of states and colors:

```wl
TuringMachineRuleCount[3, 2]
```

## Options

Split a long evolution into several columns with the `"Columns"` option:

```wl
OneSidedTuringMachinePlot[{600720, 3, 2}, 106, 16, "Columns" -> 3]
```

---

Suppress the output label to show the bare space-time pattern:

```wl
OneSidedTuringMachinePlot[{600720, 3, 2}, 106, 16, "LabelOutput" -> False]
```

## Applications

Search the 2-state, 2-color rule space for the machines that reproduce a target behavior, given as `{input, steps, value}` triples:

```wl
Length[OneSidedTuringMachineFind[{{1, 3, 3}, {2, 1, 3}}, {2, 2}]]
```

<!-- => 132 -->

---

Compare how a single machine transforms several different inputs:

```wl
GraphicsRow[OneSidedTuringMachinePlot[{600720, 3, 2}, #, 16, "LabelOutput" -> False] & /@ {1, 3, 6}]
```

## Properties and Relations

The `All` property is exactly the `"Steps"`, `"Value"`, and `"Width"` properties assembled into a triple:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, All] === {OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, "Steps"], OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, "Value"], OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, "Width"]}
```

<!-- => True -->

---

The number of rows tabulated by the rule-space functions equals [TuringMachineRuleCount]():

```wl
TuringMachineRuleCount[2, 2] == Length[TuringMachineOutput[2, 2, 20, 2]]
```

<!-- => True -->

## Possible Issues

A machine that does not halt within `maxSteps` reports `Undefined` for its value:

```wl
OneSidedTuringMachineFunction[{3, 2, 2}, 1, 50]
```

<!-- => Undefined -->

---

With the `All` property the unresolved parts come back as `Infinity`:

```wl
OneSidedTuringMachineFunction[{3, 2, 2}, 1, 50, All]
```

<!-- => {Infinity, Undefined, Infinity} -->

## Neat Examples

The space-time patterns of three different 2-state, 2-color machines on the same input 1, halting at values 3, 2, and 7:

```wl
GraphicsRow[OneSidedTuringMachinePlot[{#, 2, 2}, 1, 16, "LabelOutput" -> False] & /@ {1500, 1505, 1507}]
```

## Hero Image

Two evolutions of the *s*=3, *k*=2 rule 600720 one-sided Turing machine, on inputs 10 and 106:

```wl
With[{
   evolution = Function[input,
      OneSidedTuringMachinePlot[{600720, 3, 2}, input, 16, "LabelOutput" -> False]]},
 ImageResize[
  Rasterize[
   Framed[
    Column[{
       Style["TuringMachine", 30, Bold, GrayLevel[0.15], FontFamily -> "Source Sans Pro"],
       Style["Exploring and analyzing Turing machines", 13, GrayLevel[0.45], FontFamily -> "Source Sans Pro"],
       Spacer[14],
       Row[{evolution[10], evolution[106]}, Spacer[24]]},
      Alignment -> Center, Spacings -> 1.0],
    Background -> GrayLevel[0.98], FrameMargins -> 30, FrameStyle -> GrayLevel[0.9], RoundingRadius -> 16],
   ImageResolution -> 144, Background -> None],
  {Automatic, 520}]]
```

## Author Notes

The paclet's Wolfram Language and Rust implementation and its worked examples are by Nik Murzin and Willem Nielsen. This Paclet Repository definition — its markdown source, metadata, and landing-page text — was drafted with help from Claude (Anthropic) and reviewed and edited by Nik Murzin. The one-sided Turing machine conventions follow Stephen Wolfram, *A New Kind of Science*, Note (d) for Section 12.8 (p. 1143).
