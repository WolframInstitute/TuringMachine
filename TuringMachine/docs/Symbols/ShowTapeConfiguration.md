---
Template: Symbol
Name: ShowTapeConfiguration
Context: WolframInstitute`TuringMachine`InductiveProofs`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/ShowTapeConfiguration
Keywords: [Turing machine, tape, head, configuration, rendering, visualization]
SeeAlso: [RenderConfiguration, CompressToRunLength, RunMachine]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[ShowTapeConfiguration]()[*tape*, *headPos*, *state*]</code> renders *tape* (a list of cell symbols) with the head *state* inserted at position *headPos*, run-length compressed by default.

<code>[ShowTapeConfiguration]()[*config*]</code> renders an already-built left-nested `seq[...]` configuration directly.

## Details & Options

- *tape* is a list of tape-color symbols such as `{s1, s0, s1}`; *state* is a head symbol such as `qA`.
- The following options can be given:

| option | default | description |
| --- | --- | --- |
| `"Compress"` | `True` | run-length compress the configuration before rendering |
| `"ShowHead"` | `True` | insert the head/state cell into the tape |
| `"States"` | `2` | number of states, for drawing the state dial |

- The shared render-style options are also accepted.

## Basic Examples

Show the tape `1 0 1` with the head in state `qA` over the second cell:

```wl
ShowTapeConfiguration[{s1, s0, s1}, 2, qA]
```

## Options

Render the tape without inserting a head cell:

```wl
ShowTapeConfiguration[{s1, s0, s1}, 2, qA, "ShowHead" -> False]
```
