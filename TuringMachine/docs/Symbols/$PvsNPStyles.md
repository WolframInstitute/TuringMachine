---
Template: Symbol
Name: $PvsNPStyles
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/$PvsNPStyles
Keywords: [Turing machine, styles, colors, visualization, plot theme]
SeeAlso: [OneSidedTuringMachinePlot, OneSidedTuringMachineFunctionPlot, OneSidedTuringMachineRuntimePlot]
RelatedGuides: [TuringMachine]
---

## Usage

`$PvsNPStyles` is an association of named colors, color rules, and plot options shared by the package's visualization functions.

## Details & Options

- Keys include `"TuringMachineColorRules"` (the symbol-to-color rules used by <code>[OneSidedTuringMachinePlot]()</code>), `"FunctionValueColor"` and `"FunctionRuntimeColor"` (the accent colors for the value and runtime plots), and the `"FunctionValuePlotOptions"` / `"FunctionRuntimePlotOptions"` option lists.
- Read an entry to reuse the package's styling in your own graphics.

## Basic Examples

The available style keys:

```wl
Keys[$PvsNPStyles]
```

<!-- => {"FunctionValueColor", "FunctionRuntimeColor", "RuntimeTableColor", "ValueTableColor", "TuringMachineColorRules", "DistributionStyle", "FrameStyle", "MultiwayPathColorRules", "GridFrame", "FunctionValuePlotOptions", "FunctionRuntimePlotOptions"} -->

## Scope

The symbol-to-color rules used to paint the tape cells in the evolution plots:

```wl
$PvsNPStyles["TuringMachineColorRules"]
```
