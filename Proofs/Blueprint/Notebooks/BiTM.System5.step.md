---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: One step of System 5
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.System5.step
Abstract: Every step decrements the bag and increments the rules. When an element reaches 0 it is removed and the first rule is merged into the bag with parity: an integer already present is removed rather than added.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, BiTM.System5.step]
Links: ["[BiTM.System5.step in the blueprint](https://wolframinstitute.github.io/TuringMachine/cts-to-system5/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## A program

Smith's System 5 program of p. 33: a bag `{2}` and four rules:

```wl
program = System5[{2}, {{1, 4}, {1, 6}, {}, {}}]
```

## Its run, step by step

Every configuration of the run:

```wl
System5Evolution[program, 20]
```

Step 1 decrements the bag to `{1}` and increments the rules to `{2, 5}, {2, 7}, {1}, {1}`. At step 2 the element reaches 0: it is removed and the first rule, now `{3, 6}`, becomes the bag. Two more steps count it down to `{1, 4}`; at step 5 the 1 reaches 0 and the next rule, now `{6, 11}`, joins what is left: the bag becomes `{3, 6, 11}`. The run halts when the rules are used up.

## The run drawn

The bag at every step, red right after a pop. Every element drifts left by one per step; each pop brings in a new rule:

```wl
System5EvolutionPlot[program, 20, ImageSize -> 420]
```

The length of the run:

```wl
System5Evolution[program, Infinity, "Length"]
```
