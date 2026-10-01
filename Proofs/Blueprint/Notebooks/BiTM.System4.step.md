---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: The five rules of System 4
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.System4.step
Abstract: System 4 is a tape of sets of integers and stars with a head in state A, B or C. In A the head walks left; at the left end it turns and sweeps right in B and C, decrementing every set it passes; stars are deleted as it goes, and a 0 in a set switches between B and C.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, BiTM.System4.step]
Links: ["[BiTM.System4.step in the blueprint](https://wolframinstitute.github.io/TuringMachine/system5-to-system4/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## The rules

The head sits on one element of the tape.

- In state A on a set the head moves left; at the left end it turns into state B instead.
- In state A on a star the star is deleted and the state becomes B.
- In state B or C on a set, every integer of the set is decremented and the head moves right; if the set contained 0, the 0 is removed and the state switches between B and C.
- In state B on a star the star is deleted and the head moves left into state A.
- In state C on a star the head moves onto the set to its right and toggles 1 in it (adds it if absent, removes it if present).

## A tiny tape

The tape `{0, 2} * {}`, the head on the first set in state A:

```wl
tape = System4[{{0, 2}, "*", {}}]
```

Its run, every element labeled with its contents; the active element is red in state A, blue in B and orange in C:

```wl
System4EvolutionPlot[tape, 10]
```

At the left end the head turns into B. It decrements `{0, 2}`: the 0 is removed, which switches the state to C, and the set becomes `{1}`. In state C the star is not deleted: the head steps onto the empty set and toggles 1 into it. The head then decrements `{1}` to `{0}` and runs off the right end in state C, where System 4 halts.

## A longer tape

The System 4 tape of a small System 5 program (see the companion notebook on the encoder):

```wl
tape2 = System5ToSystem4[System5[{1, 3}, {{1}, {}}], 1]
```

The first 25 steps, labeled. The head turns at the left end, sweeps right in state C past the stars, switches back to B at a set holding 0, deletes the next star and walks back left:

```wl
System4EvolutionPlot[tape2, 25]
```

The whole run of 100 steps: the head (colored) zigzags while the stars are used up, nine at the start and none at the end:

```wl
System4EvolutionPlot[tape2, 200, ImageSize -> 420]
```
