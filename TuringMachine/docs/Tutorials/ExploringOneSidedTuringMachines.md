---
Template: TechNote
Name: ExploringOneSidedTuringMachines
Title: Exploring One-Sided Turing Machines
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/tutorial/ExploringOneSidedTuringMachines
Keywords: [Turing machine, one-sided, enumeration, evolution, NKS]
RelatedGuides: [TuringMachine]
---

A *one-sided* Turing machine reads a non-negative integer off a tape that is
infinite in one direction, runs until it halts, and leaves an integer behind as
its output. Because every such machine is finite, the whole space of machines
with a given number of states and colors can be enumerated and indexed by a
single number — the convention used throughout *A New Kind of Science*. This
paclet takes that index, written `{number, s, k}`, as its basic description of a
machine and builds the rest of its tools on top of it.

## Specifying and running a machine

A machine is `{number, s, k}`: its enumeration number, its number of states *s*,
and its number of colors *k*. <code>[OneSidedTuringMachineFunction]()</code> runs
one for at most a given number of steps and returns the integer value left on the
tape.

Run the *s*=3, *k*=2 rule 600720 on input 1 for at most 32 steps:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32]
```

<!-- => 7 -->

## Steps, width, and everything at once

A fourth argument selects a property instead of the value. `"Steps"` is how many
steps the machine ran before halting:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, "Steps"]
```

<!-- => 5 -->

---

`"Width"` is the largest extent of tape the head ever visited:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, "Width"]
```

<!-- => 3 -->

---

`All` returns the `{steps, value, width}` triple together:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, All]
```

<!-- => {5, 7, 3} -->

A machine that has not halted by `maxSteps` reports `Infinity` / `Undefined` for
the parts that could not be resolved, so these properties double as a halting
test.

## Visualizing the evolution

<code>[OneSidedTuringMachinePlot]()</code> draws the space-time history — one row
per step, with tape cells colored by their symbol value and the head marked in
black (its orientation showing the machine's state):

```wl
OneSidedTuringMachinePlot[{600720, 3, 2}, 1, 16]
```

## Scanning a family of machines at once

Replacing the rule number with `All` evaluates an entire family. Here every
*s*=1, *k*=2 machine is run on inputs 1 through 8, giving a rule-by-input matrix
of outputs (`Undefined` where a machine did not halt):

```wl
OneSidedTuringMachineFunction[{All, 1, 2}, {1, 8}, 32]
```

The number of machines in a family is <code>[TuringMachineRuleCount]()</code>:

```wl
TuringMachineRuleCount[2, 2]
```

<!-- => 4096 -->

## Finding rules with a given behavior

The inverse question — *which* machines reproduce a given behavior — is
<code>[OneSidedTuringMachineFind]()</code>. Given a list of `{input, steps,
value}` triples it returns every rule of the requested `{s, k}` family that
matches. Rule 1500's own `{2, 2}` family contains it, of course, alongside other
rules with the same first two outputs:

```wl
MemberQ[OneSidedTuringMachineFind[{{1, 3, 3}, {2, 1, 3}}, {2, 2}], 1500]
```

<!-- => True -->

## Nondeterministic machines

When a `{state, color}` pair is allowed several transitions, the machine becomes
*multiway*: it branches into many possible histories.
<code>[MultiwayTuringMachineRules]()</code> shows the transition table, where the
ambiguous cell carries more than one triple:

```wl
MultiwayTuringMachineRules[{12, 13}, 2, 2]
```

<!-- => <|{1,0}->{{1,0,-1}}, {1,1}->{{1,0,-1}}, {2,0}->{{2,0,-1},{2,0,1}}, {2,1}->{{1,0,1}}|> -->

From there <code>[MultiwayTuringMachineFunction]()</code> collects every tape
value reachable from a halted branch, <code>[MultiwayNonHaltedStatesLeft]()</code>
counts the branches still waiting to be explored, and
<code>[NonTerminatingTuringMachineQ]()</code> tests whether the machine falls into
a cycle. Together with the rule-space tabulators
(<code>[TuringMachineOutput]()</code>, <code>[TuringMachineSteps]()</code>,
<code>[TuringMachineWidths]()</code>, and their combined variants) these cover the
everyday loop of enumerating machines, running them, and measuring how they
behave.
