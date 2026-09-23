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

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

The tag system `a -> bc`, `b -> a`, `c -> aaa` on the word `baa`:

```wl
tag = <|"Productions" -> {{1, 2}, {0}, {0, 0, 0}}, "Word" -> {1, 0, 0}|>
```

The run of the tag system `a -> bc`, `b -> a`, `c -> aaa` on the word `baa`:

```wl
TagSystemEvolutionPlot[tag, 5, ImageSize -> 420]
```

The run of its cyclic tag system; the rows where a cycle of the six appendants starts are marked in red:

```wl
CyclicTagSystemEvolutionPlot[TagSystemToCyclicTagSystem[tag], 30, ImageSize -> 420]
```

The working strings at those rows decode to the tag words:

```wl
CyclicTagSystemToTagSystem[#["Data"], 3] & /@
    Values[CyclicTagSystemEvolution[TagSystemToCyclicTagSystem[tag], 30, #["Phase"] == 0 &]]
```
