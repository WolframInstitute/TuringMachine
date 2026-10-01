---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Why System 5 halts, and how soon
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.System5.run_bound
Abstract: Every bag element counts down, so within B steps some element reaches 0 and a rule is used up; each pop can at most double the largest integer. With r rules and integers at most B the run is over within B 2^r steps. The bound is what lets the proof size its tape without running System 5.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, Smith.System5.run_bound]
Links: ["[Smith.System5.run_bound in the blueprint](https://wolframinstitute.github.io/TuringMachine/conjecture0/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## The argument

Take a program whose bag has no repeated elements, all positive, and whose rule entries are not negative (the encoder's output is such). If every integer is at most `B`, the smallest bag element reaches 0 within `B` steps and pops a rule, after which every integer is at most `2 B`. There are `r` rules, so after at most `B + 2 B + 4 B + ...` steps they are all used and the run halts: at most `B (2^r - 1)` steps.

## Against real runs

The programs of Smith's example with the appendants `1` and `10` on `01` for one to six cycles of its appendants:

```wl
programs = Table[CyclicTagSystemToSystem5[CyclicTagSystem[{{1}, {1, 0}}, {0, 1}], n], {n, 6}]
```

The largest integer `B` and the number of rules `r` of each:

```wl
{Max[Flatten[{#["Bag"], #["Rules"]}]], Length[#["Rules"]]} & /@ programs
```

The run lengths against `B 2^r`; the bound is far above the runs but grows only through `r`:

```wl
ListLogPlot[{System5Evolution[#, Infinity, "Length"] & /@ programs, Max[Flatten[{#["Bag"], #["Rules"]}]] 2^Length[#["Rules"]] & /@ programs},
    Joined -> True, PlotMarkers -> Automatic, PlotLegends -> {"run length", "bound"}, AxesLabel -> {"cycles", None}, ImageSize -> 420]
```
