---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Cook's cyclic tag system
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration TagSystem.tagToCTS
Abstract: A 2-tag system over k symbols as a cyclic tag system with 2k appendants: each symbol a block of k bits with a single 1, one appendant per production, then k empty ones. One cycle of the appendants is one tag step.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, TagSystem.tagToCTS]
Links: ["[TagSystem.tagToCTS in the blueprint](https://wolframinstitute.github.io/TuringMachine/tm-to-cts/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet `WolframInstitute/TuringMachine`:

```wl
#| eval: false
PacletInstall["https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/WolframInstitute__TuringMachine.paclet"];
Needs["WolframInstitute`TuringMachine`"]
```

The cyclic tag system of the tag system `a -> bc`, `b -> a`, `c -> aaa` on the word `baa`:

```wl
cts = TagSystemToCyclicTagSystem[<|"Productions" -> {{1, 2}, {0}, {0, 0, 0}}, "Word" -> {1, 0, 0}|>]
```

Its run for four cycles of the six appendants:

```wl
CyclicTagSystemEvolution[cts, 24]
```

At the start of every cycle the working string decodes to the next tag word:

```wl
CyclicTagSystemToTagSystem[#["Data"], 3] & /@ CyclicTagSystemEvolution[cts, 24][[1 ;; ;; 6]]
```

The run of the tag system, for comparison:

```wl
TagSystemEvolution[<|"Productions" -> {{1, 2}, {0}, {0, 0, 0}}, "Word" -> {1, 0, 0}|>, 4]
```

For the tag system of a Turing machine the cyclic tag system is large: 2 (1 + 84 s) appendants of up to thousands of bits. Their sizes for a three-state machine:

```wl
EmulationSizes[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}, 1]
```
