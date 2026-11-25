---
Template: TechNote
Name: SmithsUniversalityProof
Title: The Chain of Smith's Universality Proof
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/tutorial/SmithsUniversalityProof
Keywords: [Wolfram 2,3 Turing machine, universality, Alex Smith, tag system, cyclic tag system, System 5, System 4, System 3, TypeTheory, formal proof]
RelatedGuides: [TuringMachine]
RelatedTutorials: [ExploringOneSidedTuringMachines]
---

In 2007 Alex Smith proved that Wolfram's 2-state 3-color Turing machine, rule 596440 and here called *wolfram23*, is universal. The proof is a chain of emulations: every binary Turing machine is emulated by a 2-tag system (Cocke and Minsky), every 2-tag system by a cyclic tag system (Cook), and every cyclic tag system by wolfram23 through four intermediate systems of Smith's design, System 5 to System 3. The entire chain is formally proved in the Wolfram Language inside the `"WolframInstitute/TypeTheory"` paclet (`TypeTheoryEnvironment["Wolfram23"]`), checked by TypeTheory's kernel with no axioms.

This paclet has one function for each arrow of the chain, one for each way back, and an evolution function for each system. This tutorial walks along the chain on small examples, checks at every stage that the emulating system reproduces the emulated one, and inspects the corresponding formal simulation theorem from `"WolframInstitute/TypeTheory"` at each rung.

| arrow | encoder | decoder | TypeTheory theorem |
|---|---|---|---|
| Turing machine → 2-tag system | `TuringMachineToTagSystem` | `TagSystemToTuringMachine` | `"minskySimulation"` |
| 2-tag system → cyclic tag system | `TagSystemToCyclicTagSystem` | `CyclicTagSystemToTagSystem` | `"cookSimulation"` |
| cyclic tag system → System 5 | `CyclicTagSystemToSystem5` | `System5ToCyclicTagSystem` | `"system5Simulation"` |
| System 5 → System 4 | `System5ToSystem4` | `System4ToSystem5` | `"system4Simulation"` |
| System 4 → System 3 | `System4ToSystem3` | | `"system3Simulation"` |
| System 3 → wolfram23 | `System3ToWolfram23` | `Wolfram23ToSystem5` | `"wolfram23Simulates3"` |

Install and load `"WolframInstitute/TypeTheory"` from its deployed cloud resource, then load the verified proof environment for Wolfram's (2,3) machine:

```wl
PacletInstall[ResourceObject["https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Paclet/WolframInstitute/TypeTheory"]]
```

```wl
Needs["WolframInstitute`TypeTheory`"]
```

```wl
wolfram23 = TypeTheoryEnvironment["Wolfram23"]
```

## Definition

The examples: a three-state binary machine that moves both ways, started on the tape `011`; a small 2-tag system; Smith's cyclic tag system with the appendants `1` and `10` on the working string `01` (p. 29 of his paper); Smith's System 5 program of p. 33; and two small System 5 programs. Every system is an object that displays as the drawing of its rules and its starting state, which <code>[RulePlot]()</code> gives as well.

The machine, as rules `{q, a} -> {q', w, d}`, and its rule icons as a <code>[TuringMachine]()</code>:

```wl
machine = {{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}
```

```wl
RulePlot[TuringMachine[machine]]
```

Its starting configuration: state 1, nothing on the left, the head on a 0, `11` on the right:

```wl
config = {1, {}, 0, {1, 1}}
```

A 2-tag system over three symbols; each production is drawn below the symbol it belongs to, the word underneath:

```wl
tag3 = TagSystem[{{1, 2}, {0}, {0, 0, 0}}, {1, 0, 0}]
```

Smith's cyclic tag system; each appendant is appended when a 1 is read at its phase, the current phase framed red:

```wl
cts = CyclicTagSystem[{{1}, {1, 0}}, {0, 1}]
```

Smith's System 5 program and two small ones, the bag and every rule on the number line:

```wl
program = System5[{2}, {{1, 4}, {1, 6}, {}, {}}]
```

```wl
twoRules = System5[{2}, {{1, 2}, {}}]
```

```wl
small = System5[{1, 3}, {{1}, {}}]
```

## A Turing machine as a 2-tag system

A 2-tag system deletes the first two symbols of its word and appends the production of the first one. Cocke and Minsky's construction writes the two halves of the machine's tape as numbers, in unary, and moves the head by rounds that halve and double them. <code>[TuringMachineToTagSystem]()</code> builds the tag system; with a number of steps it also gives the tag times, at which the tag word is the word of the next configuration.

The tag system of the machine, with the tag times of its first four steps:

```wl
tag = TuringMachineToTagSystem[machine, config, 4]
```

The alphabet has `1 + 84 s` symbols for states below *s*:

```wl
Length[tag["Productions"]]
```

The run of the tag system during those four steps, drawn by <code>[TagSystemEvolutionPlot]()</code>: each row is a tag word at its place in the queue, each color a kind of symbol:

```wl
TagSystemEvolutionPlot[tag, 85]
```

At the tag times the words decode, by <code>[TagSystemToTuringMachine]()</code>, to the machine's configurations:

```wl
TagSystemToTuringMachine[#, 3] & /@ TagSystemEvolution[tag, 85][[tag["TagTimes"] + 1]]
```

In `wolfram23`, `"minskySimulation"` proves that Cocke and Minsky's 2-tag system forward-simulates every binary Turing machine (three tag rounds per right move, five per left move):

```wl
wolfram23["minskySimulation"]
```

## A 2-tag system as a cyclic tag system

A cyclic tag system deletes the first bit of its working string and, if the bit was 1, appends the current appendant; the appendants are used in turn. Cook's construction writes each tag symbol as a block of bits with a single 1 and gives one appendant for each symbol's production, then as many empty ones. One cycle of the appendants is one tag step. For the tag system of a Turing machine the cyclic tag system is large (the section on sizes below counts it), so the construction is shown on the tag system `a -> bc`, `b -> a`, `c -> aaa` started on `baa`.

The cyclic tag system:

```wl
cts3 = TagSystemToCyclicTagSystem[tag3]
```

Its run, drawn by <code>[CyclicTagSystemEvolutionPlot]()</code>; the rows where a cycle of the six appendants starts are marked in red:

```wl
CyclicTagSystemEvolutionPlot[cts3, 30]
```

Its configurations at the start of every cycle:

```wl
starts = CyclicTagSystemEvolution[cts3, 30, #["Phase"] == 0 &]
```

They decode, by <code>[CyclicTagSystemToTagSystem]()</code>, to the run of the tag system:

```wl
CyclicTagSystemToTagSystem[#["Data"], 3] & /@ Values[starts]
```

The run of the tag system, for comparison:

```wl
TagSystemEvolution[tag3, 5]
```

In `wolfram23`, `"cookSimulation"` proves Cook's emulation for any 2-tag system over `k` symbols, and `"machineToCyclicTag"` composes it with `"minskySimulation"` over the `84 s + 1` symbol alphabet:

```wl
wolfram23["cookSimulation"]
```

```wl
wolfram23["machineToCyclicTag"]
```

## A cyclic tag system as System 5

Smith's System 5 keeps a bag of integers and a list of rules. Every step decrements the bag and increments the rules; when a bag element reaches 0 it is removed and the next rule is merged into the bag, an integer already present cancelling. It emulates the *doubled* cyclic tag system, which has every bit of the working string twice and an empty appendant after each doubled one. A bit becomes two pairs of bag integers, with gaps 1 for a 0 and 2 for a 1.

Smith's example with the appendants `1` and `10` on `01`, for two cycles:

```wl
s5 = CyclicTagSystemToSystem5[cts, 2]
```

Its run, drawn by <code>[System5EvolutionPlot]()</code>: the bag at every step, red after a rule is popped:

```wl
System5EvolutionPlot[s5, 1000]
```

The bags decode, by <code>[System5ToCyclicTagSystem]()</code>, to the run of the doubled cyclic tag system:

```wl
First /@ Split[DeleteMissing[System5ToCyclicTagSystem /@ System5Evolution[s5, 1000][[All, "Bag"]]]]
```

The run of the doubled cyclic tag system, for comparison:

```wl
CyclicTagSystemEvolution[CyclicTagSystem[{{1, 1}, {}, {1, 1, 0, 0}, {}}, {0, 0, 1, 1}], 8]
```

Because a finite System 5 rule queue terminates when its rules run out, `"system5Simulation"` proves that System 5 forward-simulates any *fueled* cyclic tag system (carrying a remaining step budget) along `"system5Represents"`:

```wl
wolfram23["system5Simulation"]
```

The algebraic identity `"xorMergeAppendant"` drives the 1-bit pop: XOR-merging a rule pair's two shifted copies yields the doubled appendant's pairs directly:

```wl
wolfram23["xorMergeAppendant"]
```

## System 5 as System 4

System 4 is a tape of sets of integers and stars with a moving head. In state A the head moves left, deleting stars; at the left end it turns to state B and sweeps right, decrementing every set it passes and switching to state C and back each time a set contained 0. System 4 turns the bag into a set and each System 5 rule into a block of `8 f` elements. <code>[EmulationParameters]()</code> gives the parameter *f* and the band of the decoder that the proof uses; they come from the lengths of the runs.

The parameters for Smith's program of p. 33:

```wl
EmulationParameters[program]
```

A smaller program with two rules is shown in full. Its parameters:

```wl
params = EmulationParameters[twoRules]
```

Its System 4 tape has `1 + 2 f + 8 f r` elements:

```wl
Length[System5ToSystem4[twoRules, params["f"]]["Elements"]]
```

Its run, drawn by <code>[System4EvolutionPlot]()</code>: stars black, sets gray, the active element colored by the state (A red, B blue, C orange):

```wl
System4EvolutionPlot[System5ToSystem4[twoRules, params["f"]], 20000]
```

Each time the head is back at the left end in state B, the leading sets decode by <code>[System4ToSystem5]()</code> to a bag. In order, consecutive repeats removed, they are the System 5 bags, then the decrements of the terminal phase:

```wl
First /@ Split[Sort /@ DeleteMissing[System4ToSystem5[#, params["Band"]] & /@
    Values[System4Evolution[System5ToSystem4[twoRules, params["f"]], 10^6, #["Active"] == 0 && #["State"] === "B" &]]]]
```

The System 5 run, for comparison:

```wl
System5Evolution[twoRules, 100]
```

In `wolfram23`, `"system4Simulation"` proves that System 4 forward-simulates fueled System 5 for every parameter *f* large enough for the run:

```wl
wolfram23["system4Simulation"]
```

## System 4 as System 3 and wolfram23

System 3 writes each set as a block of `2^w` cells of 1s and 2s whose parity scans give the set's members, and each star as a 0. Its head carries out a System 4 step by scanning a block. Systems 3, 2, 1 and 0 differ only by relabelings of cells and states, and System 0 is wolfram23. The emulation is faithful while the System 4 run fits in the blocks, which needs `2^w` above the length of the run; with the proof's parameters `w` is 18 even for Smith's program of p. 33. The last arrows are therefore shown on a System 4 tape small enough to run: the tape of the program `small` with *f* = 1, not the proof's *f*. System 3 emulates any System 4 tape, so this one serves as well.

The System 4 tape:

```wl
s4small = System5ToSystem4[small, 1]
```

Its run:

```wl
System4EvolutionPlot[s4small, 200]
```

Its decodes at its left-end turns:

```wl
System4ToSystem5[#, 20] & /@ Values[System4Evolution[s4small, 1000, #["Active"] == 0 && #["State"] === "B" &]]
```

The run of its System 3 tape, with blocks of width `2^7` and a left end of 120 zeros, drawn by <code>[System3EvolutionPlot]()</code>; cells 1 are gray, 2 black, and the head is colored by the state:

```wl
System3EvolutionPlot[System4ToSystem3[s4small, 7, 120], 20000]
```

The tape has this many cells:

```wl
Length[System3ToWolfram23[System4ToSystem3[s4small, 7, 120]][[4]]] + 124
```

The run of wolfram23, drawn by <code>[Wolfram23EvolutionPlot]()</code> with one row every 150 steps; the head is red in state A and blue in state B:

```wl
Wolfram23EvolutionPlot[System3ToWolfram23[System4ToSystem3[s4small, 7, 120]], 60000]
```

The first six times wolfram23 is back at the left end of the tape in state B, 123 cells from the edge, the blocks right of the head decode by <code>[Wolfram23ToSystem5]()</code> to System 4's bags:

```wl
Wolfram23ToSystem5[#, 7, 20] & /@ Values[Take[Wolfram23Evolution[System3ToWolfram23[System4ToSystem3[s4small, 7, 120]], 50000, #1 == 2 && #2 == 123 &], 6]]
```

In `wolfram23`, `"system3Simulation"` proves that System 3 emulates fueled System 4 using width-`2^w` parity blocks (via the GF(2) Frobenius identity `"stepRIteratePow2"` and orthogonality `"parAtRowBits"`), and `"wolfram23Simulates3"` proves that wolfram23 follows System 3 through the relabelings `"phi3"` and `"phi2"` in 1 or 3 steps:

```wl
wolfram23["system3Simulation"]
```

```wl
wolfram23["wolfram23Simulates3"]
```

The derivation of `"system0Simulates3"` shows how the relabelings compose:

```wl
TypeTheoryProofTree[wolfram23["system0Simulates3"]["Term"]]
```

## How large the emulation is

Every encoder is a direct construction, but the sizes multiply. System 4 needs *f* above twice the length of the System 5 run, and wolfram23 needs blocks of width above the length of the System 4 run. <code>[EmulationSizes]()</code> runs the chain up to System 5 and computes the rest from the parameters.

The sizes for one step of a two-state machine that writes 1, moves right and halts:

```wl
EmulationSizes[{{1, 0} -> {0, 1, 1}}, {1, {}, 0, {}}, 1]
```

The headline theorems `"conjecture0Finite"` and `"wolfram23Universal"` take these parameters from the run lengths, as above, so their initial condition exists without writing out a closed-form bound. Closed-form upper bounds that run no system are far larger than the runs:

```wl
EmulationParameters[program, "ClosedForm"]
```

## The formal proof

In `TypeTheoryEnvironment["Wolfram23"]`, every arrow above is proved as a forward simulation and composed end-to-end inside TypeTheory's kernel. `"conjecture0Finite"` composes rungs 3 through 6 into Smith's finite-form Conjecture 0 for arbitrary cyclic tag systems:

```wl
wolfram23["conjecture0Finite"]
```

Composing `"machineToCyclicTag"` with `"conjecture0Finite"` and the computable four-layer decoder `"decodeTM"` yields `"wolfram23Universal"`: for every binary Turing machine whose states stay below `S`, every starting configuration with state below `S`, and every finite `n`-step run, there exist a state-A starting configuration of wolfram23, decoding parameters `w` and `b`, a strictly increasing schedule `times`, and a final time `T` such that the run stays confined to its tape through `T`, decodes via `"decodeTM"` to each configuration of the run (up to trailing blanks), and exits cleanly to the right in state A at `T + 1`:

```wl
wolfram23["wolfram23Universal"]
```

Both theorems rest on the kernel alone, with empty axiom closures:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["conjecture0Finite", wolfram23]]
```

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["wolfram23Universal", wolfram23]]
```

Smith's original paper is at [wolframscience.com/prizes/tm23](https://www.wolframscience.com/prizes/tm23/TM23Proof.pdf).
