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
