---
Template: ComputationalEssay
ResourceType: ComputationalEssay
Name: Smith's strings for one-element sets
Author: Wolfram Institute
Context: WolframInstitute`TuringMachine`
Date: 2026
Description: A computational footnote to the Lean declaration Smith.row
Abstract: The string for the set {i} at width n is row i of the rule 60 cellular automaton started from 2 1 1 ... 1: cell j is the binomial coefficient C(i, j) mod 2.
Keywords: [Wolfram 2,3 Turing machine, universality, Lean, Smith.row]
Links: ["[Smith.row in the blueprint](https://wolframinstitute.github.io/TuringMachine/system4-to-system3/)", "[The Lean proof](https://github.com/WolframInstitute/TuringMachine/tree/lean-proofs/Proofs)"]
---

The functions come from the paclet [WolframInstitute/TuringMachine](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).

The rows at width 32, 2 drawn dark:

```wl
ArrayPlot[Table[Boole[BitAnd[i, j] == j], {i, 0, 31}, {j, 0, 31}], ImageSize -> 300]
```

The same rows from rule 60:

```wl
ArrayPlot[CellularAutomaton[60, {{1}, 0}, {31, {0, 31}}], ImageSize -> 300]
```
