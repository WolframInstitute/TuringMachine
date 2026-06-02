---
Context: WolframInstitute`TuringMachine`
---

# TuringMachine

A Wolfram Language paclet for exploring and analyzing Turing machines, powered by
a Rust backend for high-performance enumeration and search.

📦 **Paclet Repository:** <https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/>

> The published [`README.md`](README.md) is generated from [`README-raw.md`](README-raw.md) with
> [MarkdownToNotebook](https://resources.wolframcloud.com/FunctionRepository/resources/MarkdownToNotebook/);
> its output images are live evaluations. Edit `README-raw.md` and regenerate — don't edit `README.md` by hand.

## Installation

```wolfram
#| eval: false
PacletInstall["WolframInstitute/TuringMachine"]
Needs["WolframInstitute`TuringMachine`"]
```

## Documentation

Full documentation — a guide page, a reference page for every symbol, and a
tutorial — ships with the paclet and is browsable on the
[Paclet Repository page](https://resources.wolframcloud.com/PacletRepository/resources/WolframInstitute/TuringMachine/).
The markdown sources live under [`TuringMachine/docs/`](TuringMachine/docs) and are
built into the paclet's documentation notebooks by
[`TuringMachine/build.wls`](TuringMachine/build.wls).

## Usage

A machine is identified by its Wolfram enumeration number together with its state
and color counts, written `{number, s, k}`. A bare integer is shorthand for a
2-state, 2-color machine.

### Deterministic (one-sided) machines

Run the *s*=3, *k*=2 rule 600720 on input 1 for at most 32 steps:

```wolfram
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32]
```

Return the steps, value, and width together as `{steps, value, width}`:

```wolfram
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, All]
```

A bare integer rule is treated as a 2-state, 2-color machine:

```wolfram
OneSidedTuringMachineFunction[2506, 1, 100]
```

Give the transition table explicitly, as `{state, symbol} -> {nextState, writeSymbol, direction}` (direction `1` = right, `-1` = left):

```wolfram
OneSidedTuringMachineFunction[{{1, 0} -> {1, 1, 1}, {1, 1} -> {1, 0, -1}}, 1, 100]
```

### Tabulating whole rule spaces

Count the distinct rules with 2 states and 2 colors:

```wolfram
TuringMachineRuleCount[2, 2]
```

Tabulate step counts for all 4096 two-state, two-color machines over inputs 1 through 100 (backed by Rust):

```wolfram
Dimensions[TuringMachineSteps[2, 2, 200, 100]]
```

See also `TuringMachineOutput`, `TuringMachineWidths`, and the combined `TuringMachineOutputWithStepsWidths` (and their numeric `...Float` variants).

### Nondeterministic (multiway) machines

A multiway machine is a list of integer rule numbers; where their transitions disagree, the machine branches. Search for a sequence of transitions turning input 0 into output 5 within 50 steps:

```wolfram
MultiwayTuringMachineSearch[{2506, 1953}, 0, 5, 50]
```

Count how many branches remain unexplored after 20 steps:

```wolfram
MultiwayNonHaltedStatesLeft[{2506, 1953}, 0, 20]
```

### Cycle detection

Rule 257 enters a cycle within 1000 steps on input 1:

```wolfram
NonTerminatingTuringMachineQ[257, 1, 1000]
```

Rule 2506 does not:

```wolfram
NonTerminatingTuringMachineQ[2506, 1, 1000]
```

### Visualization

Plot the space-time evolution — tape cells colored by symbol, the head a black marker:

```wolfram
OneSidedTuringMachinePlot[{600720, 3, 2}, 1, 16]
```

Plot the output value as a function of the input:

```wolfram
OneSidedTuringMachineFunctionPlot[{600720, 3, 2}, {1, 50}, 200]
```

Plot the running time as a function of the input:

```wolfram
OneSidedTuringMachineRuntimePlot[{600720, 3, 2}, {1, 50}, 200]
```

## Building from source

*Rust is provisioned automatically by the ExtensionCargo paclet. The required
paclets ship with Wolfram Language 15.0+. For earlier versions, install them first:*

```wolfram
#| eval: false
PacletInstall["https://www.wolframcloud.com/obj/nikm/ExternalEvaluate.paclet"]
PacletInstall["https://www.wolframcloud.com/obj/nikm/PacletExtensions.paclet"]
```

Ensure `wolframscript` is installed and on your `PATH`, then build the paclet —
this compiles the Rust extension, builds the `.paclet` archive, installs it, and
(if configured) copies the archive to the cloud:

```bash
./build.wls
```

Rebuild the documentation notebooks from the markdown sources:

```bash
wolframscript -f TuringMachine/build.wls
```
