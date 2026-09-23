---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: How large the initial condition is
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.IC
Abstract: The initial condition for n steps of a machine goes through every stage of the chain: tag system, cyclic tag system, System 5, System 4, System 3. Up to System 5 the stages can be built and run; the System 4 and wolfram23 tapes are far too large and are only counted.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, Smith.IC]
Links: ["[Smith.IC in the blueprint](https://wolframinstitute.github.io/TuringMachine/universality/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## The sizes

A two-state machine that writes 1, moves right and halts, one step:

```wl
EmulationSizes[{{1, 0} -> {0, 1, 1}}, {1, {}, 0, {}}, 1]
```

On a log scale, stage by stage:

```wl
With[{sizes = EmulationSizes[{{1, 0} -> {0, 1, 1}}, {1, {}, 0, {}}, 1]},
    BarChart[Values[sizes], ScalingFunctions -> "Log", ChartLabels -> Placed[Keys[sizes], Axis, Rotate[#, Pi/2] &], ImageSize -> 420]]
```

## Where the growth comes from

The tag system writes the tape in unary, so its word is exponential in the tape; the cyclic tag system spends `1 + 84 s` bits per tag symbol; System 5 spends four rules per appendant and cycle, and its run is long because every bit is a pair of integers that must count down. System 4 needs `f` above twice the System 5 run, and `8 f` elements per rule; wolfram23 needs blocks of `2^w` cells above the System 4 run. None of this is computed by running the machine: the proof's initial condition takes all of it from bounds.
