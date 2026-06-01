---
Template: Symbol
Name: OneSidedTuringMachinePlot
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/OneSidedTuringMachinePlot
Keywords: [Turing machine, one-sided, evolution, plot, visualization]
SeeAlso: [OneSidedTuringMachineFunction, OneSidedTuringMachineFind]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[OneSidedTuringMachinePlot]()[*rule*, *input*, *n*]</code> generates a visualization of the space-time evolution of the one-sided Turing machine *rule* run on *input* for at most *n* steps.

## Details & Options

- The machine is given as `{number, s, k}`; each row is one step, with tape cells colored by their symbol value and the head drawn as a black marker whose orientation indicates the machine's current state.
- The following options can be given:

| `"Width"` | `"Maximum"` | width of the tape to display |
| `"LabelOutput"` | `True` | whether to label the output value |
| `"LabelInput"` | `False` | whether to label the input value |
| `"Columns"` | `1` | number of columns to split the evolution into |
| `"TerminationColumnColor"` | `GrayLevel[0.7]` | color of the termination column |
| `"PlotSize"` | `"Automatic"` | size of the plot |
| `ImageSize` | `50` | size of the image |

## Basic Examples

Plot the evolution of the *s*=3, *k*=2 rule 600720 on input 1:

```wl
OneSidedTuringMachinePlot[{600720, 3, 2}, 1, 16]
```

## Options

Drop the output label to show the bare evolution:

```wl
OneSidedTuringMachinePlot[{600720, 3, 2}, 1, 16, "LabelOutput" -> False]
```
