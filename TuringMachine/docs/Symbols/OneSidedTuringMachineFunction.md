---
Template: Symbol
Name: OneSidedTuringMachineFunction
Context: WolframInstitute`TuringMachine`
Paclet: WolframInstitute/TuringMachine
URI: WolframInstitute/TuringMachine/ref/OneSidedTuringMachineFunction
Keywords: [Turing machine, one-sided, evolution, output, steps, width]
SeeAlso: [OneSidedTuringMachinePlot, OneSidedTuringMachineFind, TuringMachineRuleCount, TuringMachineOutput]
RelatedGuides: [TuringMachine]
---

## Usage

<code>[OneSidedTuringMachineFunction]()[*rule*, *input*, *n*]</code> runs the deterministic one-sided Turing machine *rule* on *input* for at most *n* steps and returns the integer value left on the tape.

<code>[OneSidedTuringMachineFunction]()[*rule*, *input*, *n*, *prop*]</code> returns the property *prop*: `"Value"`, `"Steps"`, `"Width"`, or `All`.

<code>[OneSidedTuringMachineFunction]()[{All, *s*, *k*}, {*min*, *max*}, *n*]</code> evaluates every rule of the *s*-state, *k*-color family over inputs *min* through *max*.

## Details & Options

- A machine is given as `{number, s, k}`: its Wolfram enumeration number, its number of states *s*, and its number of colors *k*.
- The property argument is `"Value"` (default), `"Steps"` (number of steps taken), `"Width"` (maximum tape width visited), or `All` (the triple `{steps, value, width}`).
- A machine that does not halt within *n* steps returns `Infinity` / `Undefined` for the parts that could not be resolved.
- Using `All` in place of the rule number, with a `{min, max}` input range, returns a rule-by-input matrix for the whole family.

## Basic Examples

Run the *s*=3, *k*=2 rule 600720 on input 1 for at most 32 steps:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32]
```

<!-- => 7 -->

---

Return the number of steps it took to halt:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, "Steps"]
```

<!-- => 5 -->

---

Return the maximum tape width the head spanned:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, "Width"]
```

<!-- => 3 -->

---

Return the steps, value, and width together:

```wl
OneSidedTuringMachineFunction[{600720, 3, 2}, 1, 32, All]
```

<!-- => {5, 7, 3} -->

## Scope

Evaluate a whole family at once — every *s*=1, *k*=2 machine on inputs 1 through 8:

```wl
OneSidedTuringMachineFunction[{All, 1, 2}, {1, 8}, 32]
```
