---
Template: Guide
Name: TuringMachine
Title: Turing Machine
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/guide/TuringMachine
Description: Tools for exploring and analyzing Turing machines
Keywords: [Turing machine, one-sided Turing machine, multiway, nondeterministic, enumeration, NKS]
RelatedGuides: [ComputationalSystems]
Links: ["[One-sided Turing machines — A New Kind of Science | Online](https://www.wolframscience.com/nks/notes-12-8--one-sided-turing-machines/)"]
---

## Abstract

This paclet provides tools for exploring and analyzing Turing machines, with an emphasis on the *one-sided* machines studied in *A New Kind of Science*. A machine is identified by its Wolfram enumeration number together with its state and color counts, written `{number, s, k}`. From that compact specification the paclet runs a machine on integer inputs and reads off its halting value, step count, and tape width; visualizes its space-time evolution; tabulates the behavior of whole rule spaces (backed by a Rust implementation); searches for rules that reproduce a given behavior; and explores nondeterministic (multiway) machines.

## Functions

### One-sided Turing machines

- `OneSidedTuringMachineFunction` runs a one-sided machine on an integer input and returns its halting value, step count, or tape width
- `OneSidedTuringMachinePlot` visualizes the space-time evolution of a one-sided machine
- `OneSidedTuringMachineFind` finds the rules that reproduce a given set of outputs

### Rule enumeration

- `TuringMachineRuleCount` the number of distinct rules for given state and color counts
- `TuringMachineRuleCases` the transition table of a single deterministic rule

### Behavior over rule spaces

- `TuringMachineOutput` halted output values for every rule and input in a range
- `TuringMachineOutputWithSteps` halted `{steps, output}` for every rule and input
- `TuringMachineOutputWithStepsWidths` halted `{steps, output, width}` for every rule and input
- `TuringMachineSteps` step counts for halting machines
- `TuringMachineWidths` maximum head widths for halting machines
- `TuringMachineStepsWidths` `{steps, width}` pairs for halting machines
- `TuringMachineOutputWithStepsFloat` a numeric `{steps, output}` array
- `TuringMachineOutputWithStepsWidthsFloat` a numeric `{steps, output, width}` array

### Multiway (nondeterministic) machines

- `MultiwayTuringMachineRules` the multivalued transition table of a multiway machine
- `MultiwayTuringMachineFunction` all tape values reachable from halted states
- `MultiwayNonHaltedStatesLeft` how many states remain unexplored after a step bound
- `NonTerminatingTuringMachineQ` tests whether a machine enters a cycle within a step bound

### Visualization

- `OneSidedTuringMachineEvolution` the step-by-step `{head, tape}` history a plot is built from
- `OneSidedTuringMachineFunctionPlot` the output value as a function of the input
- `OneSidedTuringMachineRuntimePlot` the running time as a function of the input
- `TuringMachineWorstCasePlot` the runtime with a worst-case envelope across input sizes
- `MultiwayTuringMachinePlot` the values reachable by a multiway machine across inputs
- `$PvsNPStyles` the named colors and plot styles shared by the visualizations

## Smith's universality proof

Alex Smith's proof that Wolfram's 2,3 Turing machine is universal, formalized in Lean in the paclet repository, is a chain of emulations. Each system has its own head, displayed as the drawing of its rules and starting state; there is one function for each arrow of the chain, one for each way back, and an evolution function for each system.

### Systems

- `TagSystem` a 2-tag system, displayed as its productions and word
- `CyclicTagSystem` a cyclic tag system, displayed as its appendants and working string
- `System5` a program of Smith's System 5, displayed as its bag and rules on the number line
- `System4` a tape of Smith's System 4, displayed as its sets and stars
- `System3` a tape of Smith's System 3, displayed as its cells

### Encoders

- `TuringMachineToTagSystem` the Cocke–Minsky 2-tag system of a binary Turing machine, its word and its tag times
- `TagSystemToCyclicTagSystem` Cook's cyclic tag system of a 2-tag system
- `CyclicTagSystemToSystem5` Smith's System 5 program for a number of cycles of a cyclic tag system
- `System5ToSystem4` the System 4 tape of a System 5 program
- `System4ToSystem3` the System 3 tape of a System 4 tape, sets written as parity blocks
- `System3ToWolfram23` the wolfram23 configuration of a System 3 configuration

### Decoders

- `TagSystemToTuringMachine` the machine configuration of a tag word
- `CyclicTagSystemToTagSystem` the tag word of a cyclic tag working string
- `System5ToCyclicTagSystem` the doubled working string of a System 5 bag
- `System4ToSystem5` the System 5 bag of a System 4 tape
- `Wolfram23ToSystem5` the System 5 bag of a wolfram23 tape

### Evolution

- `TagSystemEvolution` the run of a 2-tag system
- `CyclicTagSystemEvolution` the run of a cyclic tag system
- `System5Evolution` the run of a System 5 program, or its length
- `System4Evolution` the run of a System 4 tape
- `System3Evolution` the run of a System 3 tape
- `Wolfram23Evolution` the run of Wolfram's 2,3 machine, or the configurations at selected steps

### Plots

- `TagSystemEvolutionPlot` the run of a 2-tag system, each word at its place in the queue
- `CyclicTagSystemEvolutionPlot` the run of a cyclic tag system, the starts of the cycles marked
- `System5EvolutionPlot` the bag of a System 5 program along its run
- `System4EvolutionPlot` the tape of System 4 along its run, the head colored by the state
- `System3EvolutionPlot` the tape of System 3 along its run
- `TuringMachineEvolutionPlot` the tape of a binary Turing machine along its run, the head colored by the state
- `Wolfram23EvolutionPlot` the tape of Wolfram's 2,3 machine along its run

### Parameters

- `EmulationParameters` the parameters of the emulation of a System 5 program, exact or in closed form
- `EmulationSizes` the size of every stage of the emulation of a Turing machine
- `ParityBlock` Smith's System 3 block of a System 4 set

## Inductive proofs

A separate `` WolframInstitute`TuringMachine`InductiveProofs` `` context proves, by equational induction, that a machine's tape-configuration semantics matches its intended behavior, and visualizes those proofs as graphs and multiway rewrite clouds.

### Symbolic machines and tape terms

- `DecodeTuringMachineRules` decodes a machine number into symbolic transition rules
- `RunMachine` runs a symbolic machine and returns the tape configurations it visits
- `CompressToRunLength` collapses runs of equal cells into run-length terms

### Proof search

- `FindInductiveProof` proves a goal by equational induction on a run-length variable
- `mergedProofFor` derives a machine's proof by trying the sweep, boundary, and scan-flip strategies
- `cachedProofFor` the on-disk-cached proof for a machine

### Rendering tapes and equations

- `RenderConfiguration` draws a tape configuration as a row of cells
- `RenderEquation` draws an equation between two tape configurations
- `RenderAxiomGrid` draws a list of axioms as an aligned grid
- `RenderUniversalGoal` draws a universally-quantified goal
- `ShowTapeConfiguration` draws a tape with the head inserted at a position
- `$InductiveProofColors` the theme-switched colors shared by the proof renderers

### Proof graphs

- `inductionProofGraph` the token-event proof graph fusing the base and step cases
- `proofGraph` a laid-out, styled rendering of a machine's proof graph

### Multiway rewrite clouds

- `multiwaySystemFor` the axioms, hypothesis, and seeds for a machine's proof
- `multiwaySubProofCones` a bounded multiway cloud around each sub-proof
- `multiwayCloudOverlap` measures how those sub-proof clouds share terms
- `multiwayDistance` the multiway graph distance between two tape terms
- `MultiwayEquationalGraph` a multiway equational-rewrite cloud with the proof path
- `MultiwayGeodesicGraph` a multiway cloud with the geodesic between seeds
- `MultiwayTokenEventGraph` a multiway cloud in state-event-state token form
- `MultiwayRuleGraph` the superposition (critical-pair) rule space of an axiom set

### Proof panels

- `IslandsPanel` the equational cloud for one case of a machine's proof
- `StatementPanel` the geodesic between a case's seeds, plus derived-lemma rows
- `TokenEventPanel` the token-event graph for a case, plus derived-lemma rows
- `MultiwayBothPanel` side-by-side base and step cones with the induction rule
- `SettingsPanel` the full step-case geodesic for a machine
- `RuleSpacePanel` the superposition rule space for a machine
- `MultiwayInductiveProofPanel` a machine's proof graph embedded in its multiway cloud
