---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: How System 5 becomes System 4
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.system5ToSystem4
Abstract: The bag becomes the first set of the tape, each bag element e as the integer 2e - 2, followed by f star and empty-set pairs. Each System 5 rule becomes a block of 8f elements further right. The head sweeps back and forth; each sweep decrements the sets it passes, which is how the bag counts down, and a 0 reached in the leading sets brings the next rule block into play.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, BiTM.system5ToSystem4]
Links: ["[BiTM.system5ToSystem4 in the blueprint](https://wolframinstitute.github.io/TuringMachine/system5-to-system4/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## The encoding

A System 5 program with a bag and two rules:

```wl
program = <|"Bag" -> {1, 3}, "Rules" -> {{1}, {}}|>
```

Its System 4 tape with the parameter `f = 1`:

```wl
System5ToSystem4[program, 1]["Elements"]
```

The first set holds `2 e - 2` for every bag element `e`: here `0` and `4`. Then come `f` pairs of a star and an empty set. Each rule becomes a block of `8 f` elements: a star, the rule's set (all integers from 0 to `3 f`, with `2 k + f + 3` toggled for each rule entry `k`), `2 f` star and empty-set pairs, a star, the set of all integers from 0 to `3 f`, and `2 f - 2` more pairs. The tape has `1 + 2 f + 8 f r` elements for `r` rules:

```wl
Table[Length[System5ToSystem4[program, f]["Elements"]], {f, 1, 4}]
```

## The run

The run of the tape, every element labeled for the first 30 steps:

```wl
System4EvolutionPlot[System5ToSystem4[program, 1], 30]
```

The head sweeps right from the left end, decrementing every set it passes. A set holding 0 switches the state between B and C; in state B the next star is deleted and the head walks back to the left end, in state C the head steps over the star and toggles 1 in the set after it. So the sets count down sweep by sweep while the stars are used up, and the switches to C carry the rule blocks' integers into the sets they reach. The whole run:

```wl
System4EvolutionPlot[System5ToSystem4[program, 1], 200, ImageSize -> 420]
```

## Why f matters

The stars and empty sets are time: every sweep uses one of them up. With too small an `f` the tape runs out of them before the System 5 run is over and the emulation breaks down; the proof takes `f` above twice the length of the System 5 run (see the companion notebook on reading the bag off System 4).
