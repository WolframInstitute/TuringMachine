---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: How a cyclic tag system becomes System 5
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration BiTM.ctsToSystem5
Abstract: System 5 keeps a bag of integers and a list of rules. Every step all bag elements count down and all rule entries count up; when an element reaches 0 the next rule is merged into the bag. Smith writes each bit of the working string as a pair of bag integers whose gap is the bit, and each appendant as rules that, merged at the right moments, append its bits.
Keywords: ["Wolfram 2,3 Turing machine", universality, Lean, BiTM.ctsToSystem5]
Links: ["[BiTM.ctsToSystem5 in the blueprint](https://wolframinstitute.github.io/TuringMachine/cts-to-system5/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

## System 5

A System 5 program is a bag of integers and a list of rules, each a list of integers. Every step decrements every bag element and increments every rule entry. When an element reaches 0 it is removed and the first rule is merged into the bag, an integer already present cancelling instead of appearing twice. The program halts when the bag or the rule list is empty.

## Bits as gaps

Smith emulates the doubled cyclic tag system, in which every bit of the working string appears twice (and each appendant is doubled and followed by an empty one). Each bit of the doubled string becomes a pair of integers `(x, x + 1)` for a 0 and `(x, x + 2)` for a 1. Smith's example with the appendants `1` and `10` on `01`:

```wl
cts = CyclicTagSystem[{{1}, {1, 0}}, {0, 1}]
```

Its System 5 program for one cycle of the appendants:

```wl
s5 = CyclicTagSystemToSystem5[cts, 1]
```

The bag on a number line: the working string `01` doubled is `0011`, the pairs `(1, 2)`, `(3, 4)` with gap 1 and `(5, 7)`, `(8, 10)` with gap 2:

```wl
NumberLinePlot[Interval /@ Partition[Sort[s5["Bag"]], 2], PlotRange -> {0, 12}, ImageSize -> 420]
```

## Appendants as rules

Each appendant becomes four rules: two that carry its bits and, for the empty appendant that follows it in the doubled system, two empty rules. The rules sit above the whole bag, so a merged rule lands at the end of the working string.

## Reading a bit

The smallest element `x` of the bag reaches 0 after `x` steps and pops the first rule. The second element of the same pair reaches 0 one or two steps later and pops the next. For a 0 bit (gap 1) the two pops put the same integers in the bag and they cancel: nothing is appended. For a 1 bit (gap 2) they put the same integers two apart, which are exactly the pairs of the appendant's bits: the appendant is appended. The run of the program for two cycles, the bag at every step, red right after a pop:

```wl
System5EvolutionPlot[CyclicTagSystemToSystem5[cts, 2], 1000, ImageSize -> 420]
```

The bags read back as the working strings of the doubled cyclic tag system, one pair of integers per bit:

```wl
First /@ Split[DeleteMissing[System5ToCyclicTagSystem /@ System5Evolution[CyclicTagSystemToSystem5[cts, 2], 1000][[All, "Bag"]]]]
```
