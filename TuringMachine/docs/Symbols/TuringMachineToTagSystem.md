---
Template: Symbol
Name: TuringMachineToTagSystem
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/TuringMachineToTagSystem
Keywords: [Turing machine, tag system, Cocke-Minsky, universality, Smith]
SeeAlso: [TagSystemEvolution, TagSystemToTuringMachine, TagSystemToCyclicTagSystem, EmulationSizes]
RelatedGuides: [TuringMachine]
RelatedTutorials: [SmithsUniversalityProof]
---

## Usage

<code>[TuringMachineToTagSystem]()[*machine*, *config*]</code> gives the Cocke–Minsky 2-tag system that simulates the binary Turing machine *machine*, with the tag word of the configuration *config*.

<code>[TuringMachineToTagSystem]()[*machine*, *config*, *n*]</code> also gives the tag times of the first *n* steps.

<code>[TuringMachineToTagSystem]()[*machine*]</code> gives the tag system alone.

## Details & Options

- A machine is a list of rules `{q, a} -> {q', w, d}`: in state `q` reading the bit `a`, write `w`, move right (`d = 1`) or left (`d = -1`), and go to state `q'`. State 0 halts; a missing rule sends the machine to state 0 writing 0 and moving right.
- A configuration is `{q, left, head, right}`, with *left* and *right* listed from the cell next to the head outward; cells beyond them are blank (0).
- The result is an association with keys `"Productions"` (the production of each tag symbol), `"Word"`, `"States"` and, with *n*, `"TagTimes"`.
- For a machine with states below *s* the alphabet has `1 + 84 s` symbols: a pad and one symbol for each of 21 kinds, state and two bits. A configuration becomes the word of the two numbers its tape halves spell, written in unary as symbol pairs.
- One step of the machine takes three rounds of tag steps for a move to the right and five for a move to the left. The tag times are the cumulative round lengths; at tag time *t_i* the tag word is the word of the *i*-th configuration.
- The tag system carries out the halting row too, so its run never stops; the tag times of a halted machine continue past its halt.
- It transcribes the Lean definition `TagSystem.tagK, TagSystem.word, TagSystem.tagTime` of the formal proof in the paclet repository (`Proofs/`), and the paclet tests compare the two on shared vectors.

## Basic Examples

The tag system of a three-state machine that moves both ways, started on the tape `0 1 1`, with the tag times of its first four steps:

```wl
tag = TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}, 4]
```

The word of the configuration:

```wl
tag["Word"]
```

The alphabet has `1 + 84 s` symbols for states below *s*:

```wl
Length[tag["Productions"]]
```

## Scope

The tag system with the tag times of four steps:

```wl
tag = TuringMachineToTagSystem[{{1, 0} -> {2, 1, 1}, {1, 1} -> {1, 0, -1}, {2, 0} -> {1, 1, -1}, {2, 1} -> {2, 1, 1}}, {1, {}, 0, {1, 1}}, 4]
```

At each tag time the tag word decodes to the configuration of the machine:

```wl
TagSystemToTuringMachine[#, 3] & /@ TagSystemEvolution[tag, 85][[tag["TagTimes"] + 1]]
```

---

The tag system alone:

```wl
TuringMachineToTagSystem[{{1, 0} -> {0, 1, 1}}]
```

