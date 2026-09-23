---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: How a tag system becomes a cyclic tag system
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration TagSystem.tagToCTS
Abstract: A cyclic tag system has only two symbols and no choice of production: it cycles through a fixed list of appendants. Cook writes each tag symbol as a block of bits with a single 1 and lets one cycle of the appendants read the first two blocks of the word.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, TagSystem.tagToCTS]
Links: ["[TagSystem.tagToCTS in the blueprint](https://wolframinstitute.github.io/TuringMachine/tm-to-cts/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## Cyclic tag systems

A cyclic tag system has a working string of bits and a list of appendants used in turn. A step deletes the first bit and, if it was a 1, appends the current appendant; then it moves on to the next appendant. Smith's example with the appendants `1` and `10` on the working string `01`:

```wl
cts = CyclicTagSystem[{{1}, {1, 0}}, {0, 1}]
```

Its run, every bit labeled; one bit leaves on the left each step, and the rows where the list of appendants starts over are shaded red:

```wl
CyclicTagSystemEvolutionPlot[cts, 12]
```

## Cook's encoding

A tag system over `k` symbols: here `k = 3`, with `0 -> 12`, `1 -> 0`, `2 -> 000` on the word `100`:

```wl
tag3 = TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}]
```

Each symbol `i` becomes a block of `k` bits with a single 1 at position `i`. The cyclic tag system has `2 k` appendants: the encodings of the `k` productions, then `k` empty ones:

```wl
cts3 = TagSystemToCyclicTagSystem[tag3]
```

## Why one cycle is one tag step

A cycle of the `2 k` appendants reads two blocks. While it reads the first block, the appendant in use at the block's single 1 is the production of that symbol, and only there is anything appended. While it reads the second block the appendants are empty, so the block is deleted without a trace. That is exactly a 2-tag step: read the first symbol, delete two, append its production. Two cycles of the run, every bit labeled:

```wl
CyclicTagSystemEvolutionPlot[cts3, 12]
```

At the start of every cycle the working string decodes, block by block, to the tag word:

```wl
CyclicTagSystemToTagSystem[#["Data"], 3] & /@ Values[CyclicTagSystemEvolution[cts3, 30, #["Phase"] == 0 &]]
```

The run of the tag system:

```wl
TagSystemEvolution[tag3, 5]
```

The tag word `0` is a single symbol, so the tag system halts there; the cyclic tag system goes on reading it.

## The cost

For the tag system of a Turing machine with states below `s` the alphabet has `1 + 84 s` symbols, so every symbol becomes a block of that many bits and the cyclic tag system has twice as many appendants. The sizes for one step of a two-state machine:

```wl
EmulationSizes[{{1, 0} -> {0, 1, 1}}, {1, {}, 0, {}}, 1]
```
