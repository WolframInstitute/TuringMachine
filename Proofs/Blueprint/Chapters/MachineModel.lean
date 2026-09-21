/-
  Blueprint.Chapters.MachineModel

  Chapter 2 of the blueprint: the two machine types (the two-way tape
  machine BiTM with implicit blanks and Smith's lookahead machines of
  Systems 0 to 3), Wolfram's machine in both, and the bridge that reads
  System 0 runs as wolfram23 runs.
-/

import Verso
import VersoManual
import VersoBlueprint
import TM.Defs
import BiTM.Basic
import BiTM.Wolfram23Valid
import Smith.Lookahead
import Smith.Wolfram23Bridge
import Smith.Conjecture0

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The machine model" =>

%%%
tag := "machine-model"
file := "machine-model"
htmlSplit := .never
%%%

# Orientation

Two machine types appear in the development. `BiTM` (`BiTM/Basic.lean`) is the
ordinary Turing machine on a two-way tape with implicit blanks; Wolfram's machine
and the simulated machines of
{ref "tm-to-cts"}[the chapter on the machine reduction] are both `BiTM`
machines. The lookahead machine type `LMachine`
(`Smith/Lookahead.lean`) reads the active cell and its right neighbour and may
rewrite both; Smith's Systems 1 to 3 need it (p. 4-5), and System 0 is Wolfram's
machine written in it. The bridge `Smith.toBi` (`Smith/Wolfram23Bridge.lean`)
carries System 0 runs to `BiTM.wolfram23` runs.

# Shared definitions

:::group "machine-model-shared"
The Turing machine vocabulary of `TM/Defs.lean` shared by every machine of the
development: directions, rules and machines.
:::

`TM/Defs.lean` holds three definitions. States and symbols are natural numbers;
state 0 is the halt state; `numStates` and `numSymbols` are documentation, never
read by the step function.

:::definition "TM.Dir" (parent := "machine-model-shared") (lean := "TM.Dir")
A direction of head movement: `L` (left) or `R` (right).
:::

:::definition "TM.Rule" (parent := "machine-model-shared") (lean := "TM.Rule")
A transition rule: the next state `nextState`, the symbol `write` to write, and
the direction `dir` ({uses "TM.Dir"}[]) to move. States and symbols are natural
numbers.
:::

:::definition "TM.Machine" (parent := "machine-model-shared") (lean := "TM.Machine")
A deterministic Turing machine: `numStates`, `numSymbols`, and
`transition : Nat → Nat → Rule`, the rule ({uses "TM.Rule"}[]) for a state and a
read symbol. State 0 is the halt state; `numStates` and `numSymbols` are
documentation, never read by the step function.
:::

# BiTM: configurations, steps, runs

:::group "machine-model-bitm"
The two-way tape machine `BiTM` with implicit blanks: configurations, the step,
runs, and the number of explicit cells.
:::

:::definition "BiTM.Config" (parent := "machine-model-bitm") (lean := "BiTM.Config")
A configuration `(state, left, head, right)`: the state, the cells left of the
head nearest first, the head cell, and the cells right of the head nearest
first. Cells are natural numbers, implicitly 0 beyond the two lists. State 0
means halted.
:::

:::definition "BiTM.readHead" (parent := "machine-model-bitm") (lean := "BiTM.readHead")
Reads a list of cells: its first cell and the rest, or 0 and the empty list
beyond its end.
:::

:::definition "BiTM.step" (parent := "machine-model-bitm") (lean := "BiTM.step")
One step of a machine ({uses "TM.Machine"}[]) on a configuration
({uses "BiTM.Config"}[]): `none` in state 0, and otherwise the rule
({uses "TM.Rule"}[]) for the state and the head cell is applied. Moving left
({uses "TM.Dir"}[]) pops `left` into the head by {uses "BiTM.readHead"}[] and
pushes the written symbol onto `right`; moving right symmetrically pops `right`
into the head and pushes the written symbol onto `left`.
:::

:::definition "BiTM.nSteps" (parent := "machine-model-bitm") (lean := "BiTM.nSteps")
`n` iterations of {uses "BiTM.step"}[], `none` as soon as a step is stuck.
:::

:::definition "Smith.biSize" (parent := "machine-model-bitm") (lean := "Smith.biSize")
The number of explicit cells of a configuration ({uses "BiTM.Config"}[]),
`left.length + 1 + right.length`. Defined in `Smith/Wolfram23Bridge.lean`.
:::

:::lemma_ "Smith.biSize_step" (parent := "machine-model-bitm") (lean := "Smith.biSize_step")
A step of any machine ({uses "BiTM.step"}[]) never decreases
{uses "Smith.biSize"}[]: if `BiTM.step tm cfg = some cfg'` then
`biSize cfg <= biSize cfg'`.
:::

:::proof "Smith.biSize_step"
Case on the direction of the rule. A move pops one cell from one side of the
zipper and pushes one cell onto the other side, so the count is unchanged when
the popped side is nonempty; when it is empty, {uses "BiTM.readHead"}[] returns
the implicit blank 0 and nothing is popped, so the count grows by one.
:::

So a step never decreases `biSize`, and a step onto an implicit blank increases
it by one. This is how "the head stays on the initial tape" is formalized in
{ref "conjecture0"}[the chapter on Conjecture 0] and
{ref "universality"}[the chapter on the composition]: `biSize` constant.

# Wolfram's machine

:::group "machine-model-wolfram23"
Wolfram's 2-state 3-colour machine as a `BiTM` machine, and the alphabet it
preserves.
:::

:::definition "BiTM.wolfram23" (parent := "machine-model-wolfram23") (lean := "BiTM.wolfram23")
Wolfram's machine as a {uses "TM.Machine"}[]: `numStates := 3` (0 is halt, 1 is
A, 2 is B), `numSymbols := 3` (the symbols 0, 1, 2), and the six rules
({uses "TM.Rule"}[]) `A,0 -> 1,R,B`, `A,1 -> 2,L,A`, `A,2 -> 1,L,A`,
`B,0 -> 2,L,A`, `B,1 -> 2,R,B`, `B,2 -> 0,R,A`, each read as the state and the
symbol before, then the written symbol, the move and the new state. Every other
(state, symbol) pair goes to state 0, writes 0 and moves right; that row is
unused.
:::

Entry by entry this is Wolfram's rule 596440 as published (`A0 -> 1RB`,
`A1 -> 2LA`, `A2 -> 1LA`, `B0 -> 2LA`, `B1 -> 2RB`, `B2 -> 0RA`) and Smith's
System 0 table on p. 3, whose four rows read: before (symbol, state), after
(symbol, new active position and state). The independent review of 2026-09-21
checked all six entries against both sources and the p. 47 trace. State 0 is
never entered from states 1 and 2, so the halt row is dead.

:::definition "BiTM.IsValidWolfram23Cfg" (parent := "machine-model-wolfram23") (lean := "BiTM.IsValidWolfram23Cfg")
A configuration ({uses "BiTM.Config"}[]) is valid for wolfram23 when its state
is 1 or 2, its head cell is below 3, and every cell of `left` and of `right` is
below 3.
:::

:::lemma_ "BiTM.step_wolfram23_preserves_valid" (parent := "machine-model-wolfram23") (lean := "BiTM.step_wolfram23_preserves_valid")
From a valid configuration ({uses "BiTM.IsValidWolfram23Cfg"}[]) the step
({uses "BiTM.step"}[]) of {uses "BiTM.wolfram23"}[] is `some cfg'` with `cfg'`
valid: the machine does not halt and does not leave the alphabet.
:::

:::proof "BiTM.step_wolfram23_preserves_valid"
The state is nonzero, so the step is `some`. For a state 1 or 2 and a head cell
below 3 the six rules give a next state 1 or 2 and a written symbol below 3
(`BiTM.wolfram23_nextState_in_range`, `BiTM.wolfram23_write_in_range`, by
`decide` on the six cases). In either direction the cell that
{uses "BiTM.readHead"}[] pops into the head is a cell of the old tape or the
blank 0, and the cell pushed onto the other side is the written symbol, so the
head and both lists stay below 3.
:::

:::lemma_ "BiTM.nSteps_wolfram23_preserves_valid" (parent := "machine-model-wolfram23") (lean := "BiTM.nSteps_wolfram23_preserves_valid")
From a valid configuration ({uses "BiTM.IsValidWolfram23Cfg"}[]) every run of
`n` steps ({uses "BiTM.nSteps"}[]) of {uses "BiTM.wolfram23"}[] is `some cfg'`
with `cfg'` valid: the machine never halts and never leaves the alphabet.
:::

:::proof "BiTM.nSteps_wolfram23_preserves_valid"
Induction on `n`, with {uses "BiTM.step_wolfram23_preserves_valid"}[] for each
step.
:::

# The lookahead machine type

:::group "machine-model-lookahead"
The machine type of Smith's Systems 0 to 3: states, rules, configurations, the
step, the four tables of p. 45 and the p. 47 check.
:::

:::definition "Smith.LState" (parent := "machine-model-lookahead") (lean := "Smith.LState")
The states `A`, `B`, `C` of Systems 0 to 3.
:::

:::definition "Smith.LRule" (parent := "machine-model-lookahead") (lean := "Smith.LRule")
A rule: `one st a d` rewrites the active cell to `a`, and `two st a b d`
rewrites the active cell to `a` and its right neighbour to `b`; in both shapes
the state becomes `st` ({uses "Smith.LState"}[]) and the head moves by one in
the direction `d` ({uses "TM.Dir"}[]). Symbols are `Fin 3`.
:::

:::definition "Smith.LMachine" (parent := "machine-model-lookahead") (lean := "Smith.LMachine")
A lookahead machine: a function `trans` from the state ({uses "Smith.LState"}[]),
the active cell and its right neighbour (`0` when there is none) to a rule
({uses "Smith.LRule"}[]), a one-cell rule (rewrite the active cell) or a
two-cell rule (rewrite both), with a move. These are the two rule shapes of
Smith's `sys0-3.pl` (p. 45).
:::

:::definition "Smith.LConfig" (parent := "machine-model-lookahead") (lean := "Smith.LConfig")
A configuration, the zipper `(left, head, right, state)` with `left` nearest
first and a state in {uses "Smith.LState"}[], like `BiTM.Config`
({bpref "BiTM.Config"}[]) but over `Fin 3`. `LConfig.toList` is the tape read
left to right and `LConfig.pos` the index of the head on it.
:::

:::definition "Smith.lstep" (parent := "machine-model-lookahead") (lean := "Smith.lstep")
One step of a machine ({uses "Smith.LMachine"}[]) on a configuration
({uses "Smith.LConfig"}[]): the rule ({uses "Smith.LRule"}[]) for the state, the
head cell and the right neighbour (`0` when `right` is empty) is applied,
rewriting the cell or cells it read and moving the head. The tape is finite and
never extended: the result is `none` when the move would leave either end of
the tape, and `none` for a two-cell rule with no right neighbour.
:::

:::definition "Smith.lnSteps" (parent := "machine-model-lookahead") (lean := "Smith.lnSteps")
`n` iterations of {uses "Smith.lstep"}[], `none` as soon as a step is `none`.
It is the `nSteps` of the step system `Smith.lsys M` whose step is `lstep M`
({uses "Smith.StepSys.nSteps"}[]).
:::

:::lemma_ "Smith.lnSteps_add" (parent := "machine-model-lookahead") (lean := "Smith.lnSteps_add")
Runs concatenate: `lnSteps M c (n + m)` ({uses "Smith.lnSteps"}[]) is the run of
`m` steps from the result of the run of `n` steps, and `none` when either is
`none`.
:::

:::proof "Smith.lnSteps_add"
This is `StepSys.nSteps_add` of `Smith/Simulation.lean` for the step system
`lsys M`.
:::

:::definition "Smith.exitRight" (parent := "machine-model-lookahead") (lean := "Smith.exitRight")
The exit to the right of a configuration ({uses "Smith.LConfig"}[]) under a
machine ({uses "Smith.LMachine"}[]): when a one-cell rule at the last cell
moves right, the state it enters and the tape after its write; `none`
otherwise. It records one-cell exits only and is used only by the p. 47 check.
:::

The four tables are transcribed from p. 45
({ref "systems-3-2-1-0"}[the chapter on Systems 3 to 0] for the relabelings
between them).

:::definition "Smith.sys0" (parent := "machine-model-lookahead") (lean := "Smith.sys0")
System 0, Wolfram's table as a lookahead machine ({uses "Smith.LMachine"}[]),
with one-cell rules only: `A0 -> B1>`, `A1 -> A2<`, `A2 -> A1<`, `B0 -> A2<`,
`B1 -> B2>`, `B2 -> A0>` (the new state, the written symbol, the move). The
rows for state C, never reached, are dead.
:::

:::definition "Smith.sys1" (parent := "machine-model-lookahead") (lean := "Smith.sys1")
System 1 ({uses "Smith.LMachine"}[]): System 0 with `B2` replaced by the three
two-cell rules `B20 -> A00>`, `B21 -> B12>`, `B22 -> B11>`.
:::

:::definition "Smith.sys2" (parent := "machine-model-lookahead") (lean := "Smith.sys2")
System 2 ({uses "Smith.LMachine"}[]): the table of p. 45 with the third state
C, entered by the two-cell rules on `B21` and `B22`.
:::

:::definition "Smith.sys3" (parent := "machine-model-lookahead") (lean := "Smith.sys3")
System 3 ({uses "Smith.LMachine"}[]): the table of p. 45, a relabeling of
System 2 with state C.
:::

:::definition "Smith.LMachine.OneIgnoresNeighbour" (parent := "machine-model-lookahead") (lean := "Smith.LMachine.OneIgnoresNeighbour")
A machine ({uses "Smith.LMachine"}[]) has this property when a one-cell rule
({uses "Smith.LRule"}[]) does not depend on the neighbour: if `trans st a b` is
a one-cell rule then `trans st a b' = trans st a b` for every `b'`.
:::

Every table satisfies `OneIgnoresNeighbour`, checked by `decide`
(`Smith.sys0_one`, `Smith.sys1_one`, `Smith.sys2_one`, `Smith.sys3_one`).

:::definition "Smith.traceP47" (parent := "machine-model-lookahead") (lean := "Smith.traceP47")
The 28 tapes of the `sys0-3.pl 0 N 00A00000` trace of p. 47. The trace is
reproduced tape for tape by `decide`: from `00A00000` (`Smith.cfgP47`, the head
on the third of seven cells in state A) the run of {uses "Smith.sys0"}[] gives
the 27 tapes with the head on the tape (`Smith.tapes`); after 26 steps the head
is on the last cell in state B; the 27th step leaves the tape
({uses "Smith.lnSteps"}[] is `none`); and {uses "Smith.exitRight"}[] gives
state B and the 28th line, the tape after the last write. The leftmost visit of
the run, cell 0 in state A after 12 steps, is checked as well.
:::

# The bridge to wolfram23

:::group "machine-model-bridge"
System 0 is wolfram23: the reading of lookahead configurations as `BiTM`
configurations, and the step, exit and run correspondences.
:::

:::definition "Smith.toBi" (parent := "machine-model-bridge") (lean := "Smith.toBi")
Reads a System 0 configuration ({uses "Smith.LConfig"}[]) as a `BiTM.Config`
({uses "BiTM.Config"}[]): A is state 1, B is state 2, C is state 3 (never
reached from A or B; `Smith.stateNat`), the symbols by `Fin.val`, and the
zipper is the same zipper.
:::

:::definition "Smith.ofBi" (parent := "machine-model-bridge") (lean := "Smith.ofBi")
Reads a `BiTM.Config` ({uses "BiTM.Config"}[]) as a System 0 configuration
({uses "Smith.LConfig"}[]): the cells by `Smith.toFin` (reduction modulo 3),
the state A when the state is 1 and B otherwise.
:::

:::lemma_ "Smith.toBi_ofBi" (parent := "machine-model-bridge") (lean := "Smith.toBi_ofBi")
On valid configurations ({uses "BiTM.IsValidWolfram23Cfg"}[])
{uses "Smith.ofBi"}[] is the inverse of {uses "Smith.toBi"}[]:
`toBi (ofBi cfg) = cfg`.
:::

:::proof "Smith.toBi_ofBi"
A cell below 3 is unchanged by reduction modulo 3 followed by `Fin.val`
(`Smith.map_val_toFin` for the two lists), and a state 1 or 2 goes to A or B
and back to 1 or 2.
:::

:::theorem "Smith.toBi_step" (parent := "machine-model-bridge") (lean := "Smith.toBi_step")
For a System 0 configuration `c` not in state C, if `lstep sys0 c = some c'`
({uses "Smith.lstep"}[], {uses "Smith.sys0"}[]) then
`BiTM.step wolfram23 (toBi c) = some (toBi c')` ({uses "BiTM.step"}[],
{uses "BiTM.wolfram23"}[], {uses "Smith.toBi"}[]): a System 0 step is a
wolfram23 step.
:::

:::proof "Smith.toBi_step"
Case analysis on the state, the head symbol and whether each side of the zipper
is empty. In every case the rule of `sys0` is the matching entry of `wolfram23`
and the zipper moves the same way on both sides; `simp` with the definitions
unfolded closes each case.
:::

:::theorem "Smith.toBi_exit" (parent := "machine-model-bridge") (lean := "Smith.toBi_exit")
For a System 0 configuration `c` not in state C, if `lstep sys0 c = none`
({uses "Smith.lstep"}[], {uses "Smith.sys0"}[]) then
`BiTM.step wolfram23 (toBi c)` ({uses "BiTM.step"}[], {uses "BiTM.wolfram23"}[],
{uses "Smith.toBi"}[]) is `some cfg'` with
`biSize cfg' = biSize (toBi c) + 1` ({uses "Smith.biSize"}[]): where System 0
is stuck, wolfram23 steps onto an implicit blank and the explicit tape grows by
one cell.
:::

:::proof "Smith.toBi_exit"
The same case analysis. `sys0` has one-cell rules only, so `lstep` is `none`
exactly when the move leaves the finite tape; on that side `toBi c` has the
empty list, so `BiTM.step` reads the implicit blank 0 by `BiTM.readHead` and
pushes the written symbol onto the other side, one explicit cell more.
:::

:::theorem "Smith.toBi_run" (parent := "machine-model-bridge") (lean := "Smith.toBi_run")
For a System 0 configuration `c` not in state C, if `lnSteps sys0 c n = some c'`
({uses "Smith.lnSteps"}[], {uses "Smith.sys0"}[]) then
`BiTM.nSteps wolfram23 (toBi c) n = some (toBi c')` ({uses "BiTM.nSteps"}[],
{uses "BiTM.wolfram23"}[], {uses "Smith.toBi"}[]) and `c'` is not in state C:
a System 0 run is a wolfram23 run.
:::

:::proof "Smith.toBi_run"
Induction on `n`. System 0 never enters state C from A or B
(`Smith.sys0_state`), so {uses "Smith.toBi_step"}[] applies at every step.
:::

A System 0 step is a wolfram23 step; where System 0 is stuck (the head would
leave the finite tape) wolfram23 steps onto an implicit blank and the explicit
tape grows by one. This is the only place the finite zipper meets the implicit
blanks, and it is where the exit condition of
{ref "conjecture0"}[the chapter on Conjecture 0] and
{ref "universality"}[the chapter on the composition] comes from. The exit step
itself, as a `BiTM` step, is the following computation; it lives in
`Smith/Conjecture0.lean`.

:::lemma_ "Smith.wolfram23_exit_step" (parent := "machine-model-bridge") (lean := "Smith.wolfram23_exit_step")
The exit step of {uses "BiTM.wolfram23"}[] ({uses "BiTM.step"}[]): from state 2
(B) on a 2 with nothing explicit to the right, the step writes 0, moves right
onto the implicit blank and enters state 1 (A):
`BiTM.step wolfram23 ⟨2, L, 2, []⟩ = some ⟨1, 0 :: L, 0, []⟩`.
:::

:::proof "Smith.wolfram23_exit_step"
By computation (`rfl`): the rule `B2 -> 0RA` and `BiTM.readHead []`.
:::

# Notes and caveats

- Direction conventions are consistent across `TM.Dir`, `BiTM.step` and
  `lstep`: `L` pops from `left`, `R` pops from `right`. The review checked this.
- `LMachine` passes `0` as the neighbour at the right end but `lstep` discards
  any two-cell result there. So at the end of the System 4 emulation (System 3
  head on the closing 1 in state C,
  {ref "conjecture0"}[the chapter on Conjecture 0]) `lstep sys3` and
  `exitRight sys3` are both `none`; the exit
  that the theorems report is realized after relabeling, by the `BiTM` step
  `Smith.wolfram23_exit_step` (`B2 -> 0RA` onto the implicit blank). The
  Lookahead header says so since 2026-09-22; `exitRight` records one-cell exits
  only and is used only by the p. 47 check.
- Two branches of `BiTM.System4.step`
  ({ref "system5-to-system4"}[the chapter on System 5 to System 4]) and none of
  the machine model here deviate from Smith's Perl programs; the machine model
  is faithful.

# Depends on

The modules of this chapter are `TM.Defs`, `BiTM.Basic`, `BiTM.Wolfram23Valid`,
`Smith.Lookahead` and `Smith.Wolfram23Bridge`; `Smith.wolfram23_exit_step` is
in `Smith.Conjecture0`. `Smith.lnSteps` is built on the step-system calculus of
`Smith/Simulation.lean`
({ref "cts-to-system5"}[the chapter on cyclic tag to System 5]). The results
at the end of `Smith/Wolfram23Bridge.lean` on the head
leaving every finite tape (`Smith.wolfram23_leaves`,
`Smith.wolfram23_not_periodic`) and the length bookkeeping `Smith.lnSteps_length`
are described in {ref "systems-3-2-1-0"}[the chapter on Systems 3 to 0] and
{ref "conjecture0"}[the chapter on Conjecture 0].
