---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: A move to the left in five rounds
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration TagSystem.tm_step_tag
Abstract: A move to the right takes three rounds of the tag system, a move to the left five: the left number has to be halved and its low bit carried over to the right number. Every round reads the whole word once, so a round takes as many tag steps as the word has pairs.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, TagSystem.tm_step_tag]
Links: ["[TagSystem.tm_step_tag in the blueprint](https://wolframinstitute.github.io/TuringMachine/tm-to-cts/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## The machine and its tag system

The machine of the companion notebook, from `011`:

```wl
machine = {{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}
```

```wl
config = {1, {}, 0, {1, 1}}
```

Its first four steps: three moves to the right, then a move to the left:

```wl
TuringMachineEvolutionPlot[machine, config, 4, ImageSize -> 220]
```

The tag system with the tag times of those steps (its productions are too many to print):

```wl
tag = TuringMachineToTagSystem[machine, config, 4];
```

```wl
tag["TagTimes"]
```

## Round lengths

Each tag step deletes two symbols, so a round that reads a word of `2 p` symbols takes `p` steps. The length of the word along the run shows the rounds; the ends of the machine steps are marked:

```wl
ListLinePlot[Length /@ TagSystemEvolution[tag, 85], GridLines -> {tag["TagTimes"], None}, ImageSize -> 420]
```

The three steps to the right take 18, 14 and 16 tag steps; the step to the left takes 37:

```wl
Differences[tag["TagTimes"]]
```

## The move to the left

Before the fourth step the machine is in state 2 on a 0, with `111` on the left: `m = 7`, `N = 0`. The rule writes 1, moves left and goes to state 1. The first two rounds are those of every step: they copy the numbers and read the head bit. The remaining three halve the left number `m`, whose low bit becomes the new head cell, and double the right number with the written bit added. The run from tag time 48 to 85, every symbol labeled:

```wl
TagSystemEvolutionPlot[<|tag, "Word" -> TagSystemEvolution[tag, 48][[-1]]|>, 37]
```

The words at the two ends decode to the configurations before and after the step:

```wl
TagSystemToTuringMachine[TagSystemEvolution[tag, 85][[#]], 3] & /@ {49, 86}
```

## After the machine halts

The tag system does not stop when the machine does: it reads the halting row of the table like any other and goes on. The formal proof uses this: the run of the tag system lasts any budget, and its words at the tag times are the configurations as long as the machine runs. A machine that halts after one step:

```wl
halting = {{1, 0} -> {0, 1, 1}}
```

```wl
TuringMachineToTagSystem[halting, {1, {}, 0, {}}, 3]["TagTimes"]
```
