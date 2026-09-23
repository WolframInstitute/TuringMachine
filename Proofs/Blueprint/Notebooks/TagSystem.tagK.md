---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: How a Turing machine becomes a tag system
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration TagSystem.tagK
Abstract: A 2-tag system reads the first symbol of its word, deletes two symbols and appends a production. Cocke and Minsky write a Turing machine configuration as such a word, with the two halves of the tape spelled in unary, and turn every machine step into three or five rounds of tag steps.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, TagSystem.tagK]
Links: ["[TagSystem.tagK in the blueprint](https://wolframinstitute.github.io/TuringMachine/tm-to-cts/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## Tag systems

A 2-tag system has a word and a production for each symbol. A step reads the first symbol, deletes the first two symbols and appends the production of the one it read; the system halts when fewer than two symbols are left.

A tag system over the symbols `0`, `1`, `2` with the productions `0 -> 12`, `1 -> 0`, `2 -> 000`, started on the word `100`:

```wl
tag3 = <|"Productions" -> {{1, 2}, {0}, {0, 0, 0}}, "Word" -> {1, 0, 0}|>
```

Its run, each word drawn at its place in the queue: two symbols leave on the left, the production arrives on the right:

```wl
TagSystemEvolutionPlot[tag3, 10]
```

## The machine

A binary Turing machine with states 1 and 2 (state 0 halts). Each rule reads the state and the bit under the head, writes a bit, moves right (`1`) or left (`-1`) and changes state:

```wl
machine = {{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}
```

The configuration: state 1, nothing on the left, the head on a 0, and `11` to its right:

```wl
config = {1, {}, 0, {1, 1}}
```

Its first four steps; the head cell is colored by the state:

```wl
TuringMachineEvolutionPlot[machine, config, 4, ImageSize -> 220]
```

## A configuration as a word

The tag system does not keep a tape. It keeps two numbers: `m`, the left half of the tape read as a binary number with the nearest cell least significant, and `N`, the head cell plus twice the right half read the same way. For the configuration above:

```wl
{FromDigits[Reverse[config[[2]]], 2], config[[3]] + 2 FromDigits[Reverse[config[[4]]], 2]}
```

The word of a configuration in state `q` is `A x`, then `m` pairs `al x`, then `B x`, then `N` pairs `be x`, every symbol carrying the state `q` as a subscript; the numbers are written in unary. The tag system of the machine, with the tag times of its first four steps (it has a production for every symbol, too many to print):

```wl
tag = TuringMachineToTagSystem[machine, config, 4];
```

The word, symbol by symbol (`x` is the pad, subscripts are states):

```wl
tag["SymbolNames"][[tag["Word"] + 1]]
```

There is a symbol for each of 21 kinds, each state below `s` and up to two bits, and the pad, `1 + 84 s` in all:

```wl
Length[tag["Productions"]]
```

The productions of the symbols in this word; the pad has none:

```wl
With[{names = tag["SymbolNames"]},
    Grid[{names[[# + 1]], "\[RightArrow]", Row[names[[tag["Productions"][[# + 1]] + 1]], " "]} & /@ Union[tag["Word"]], Alignment -> Left]]
```

## One machine step, round by round

The first machine step writes 1, moves right and goes to state 2. The tag system carries it out in 18 steps, in three rounds; every symbol is labeled with its name:

```wl
TagSystemEvolutionPlot[tag, 18]
```

In the first round (steps 0 to 8) every pair of the word is read once: `A₁ x` becomes `P1₁ P0₁`, each `be₁ x` becomes one `r₁`, and `B₁ x` becomes `Q₁`. The unary count is copied, but at half the spacing. In the second round (steps 8 to 13) the `r` symbols are read in pairs, so the round sees `N` modulo 2, the bit under the head, and halves `N`; the bit is recorded in the superscript of the `E` and `F` symbols. In the third round (steps 13 to 18) the productions of those symbols apply the machine's rule for state 1 reading 0: they write the new state 2, the new left number `2 m + 1` (the written bit pushed onto the left half) and the new right number, `N` halved and rounded down.

At step 18 the word is the word of the next configuration:

```wl
TagSystemToTuringMachine[TagSystemEvolution[tag, 18][[-1]], 3]
```

The whole run of four machine steps; the tag times are where the words of the configurations appear:

```wl
TagSystemEvolutionPlot[tag, 85, "Labels" -> False]
```

```wl
tag["TagTimes"]
```
