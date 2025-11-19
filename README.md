# TuringMachineSearch

A Wolfram Language paclet for searching and analyzing Turing machines, powered by Rust for high performance.

## Build Instructions

To build this paclet, you need to have Rust installed.

1.  Ensure you have `wolframscript` installed and available in your path.
2.  Run the build script:

    ```bash
    ./build.wl
    ```

    This will:
    *   Compile the Rust extension.
    *   Build the paclet.
    *   Install the paclet.
    *   Copy the `.paclet` file to the cloud (if configured) or local directory.

## Usage

Load the package:

```wolfram
<< TuringMachineSearch`
```

### Deterministic Turing Machines

Run a specific Turing machine rule:

```wolfram
(* Run rule 2506 with input 1 for 100 steps *)
OneSidedTuringMachineFunction[2506, 1, 100]
```

Get specific properties:

```wolfram
(* Get the number of steps taken *)
OneSidedTuringMachineFunction[2506, 1, 100, "Steps"]

(* Get the maximum width of the tape visited *)
OneSidedTuringMachineFunction[2506, 1, 100, "MaxWidth"]

(* Get steps, value, and width *)
OneSidedTuringMachineFunction[2506, 1, 100, All]
```

Use explicit rules:

```wolfram
(* Define a rule explicitly: {state, symbol} -> {nextState, writeSymbol, direction} *)
(* Direction: 1 (Right), -1 (Left) *)
rule = {
    {1, 0} -> {1, 1, 1},
    {1, 1} -> {1, 0, -1}
};
OneSidedTuringMachineFunction[rule, 1, 100]
```

Get step counts for a range of rules:

```wolfram
(* Get step counts for 2-state, 2-symbol machines (rules 0 to 100) with input 1 *)
TuringMachineSteps[2, 2, 1000, {0, 100}]
```

### Non-Deterministic Turing Machines

Search for a path from input to output:

```wolfram
(* Define rules for a non-deterministic TM using a list of rule numbers *)
rules = {2506, 1953};

(* Search for a path from input 0 to output 101 within 50 steps *)
MultiwayTuringMachineSearch[rules, 0, 5, 50]
```

Analyze non-halted states:

```wolfram
(* Count non-halted states after 20 steps *)
MultiwayNonHaltedStatesLeft[rules, 0, 20]
```

### Cycle Detection

Check if a machine enters a cycle:

```wolfram
(* Check if rule 2506 cycles within 1000 steps on input 1 *)
NonTerminatingTuringMachineQ[2506, 1, 1000]
```

```wolfram
(* Check if rule 257 cycles within 1000 steps on input 1 *)
NonTerminatingTuringMachineQ[257, 1, 1000]
```
