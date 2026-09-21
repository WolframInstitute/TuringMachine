# 02. The machine model

## Orientation

Two machine types appear in the development. `BiTM` (`BiTM/Basic.lean`) is the
ordinary Turing machine on a two-way tape with implicit blanks; Wolfram's machine and
the simulated machines of chapter 03 are both `BiTM` machines. The lookahead machine
type `LMachine` (`Smith/Lookahead.lean`) reads the active cell and its right neighbour
and may rewrite both; Smith's Systems 1 to 3 need it (p. 4-5), and System 0 is
Wolfram's machine written in it. The bridge `[[Smith.toBi]]` (`Smith/Wolfram23Bridge.lean`)
carries System 0 runs to `[[BiTM.wolfram23]]` runs.

## Shared definitions

`TM/Defs.lean`: `[[TM.Dir]]` (`L`, `R`), `[[TM.Rule]]` (`nextState`, `write`, `dir`) and
`[[TM.Machine]]`: `numStates`, `numSymbols`, `transition : Nat -> Nat -> Rule`. States
and symbols are natural numbers; state 0 is the halt state; `numStates` and
`numSymbols` are documentation, never read by the step function.

## BiTM: configurations, steps, runs

`[[BiTM.Config]]` is `(state, left, head, right)` with `left` and `right` the cells
nearest the head first, implicitly 0 beyond the lists. `[[BiTM.readHead]]` reads a list,
returning 0 and the empty list beyond its end. `[[BiTM.step]]` returns `none` in state 0
and otherwise applies the rule: moving left pops `left` into the head and pushes the
written symbol onto `right`; moving right symmetrically. `[[BiTM.nSteps]]` iterates,
`none` as soon as a step is stuck.

`[[Smith.biSize]]` counts the explicit cells, `left.length + 1 + right.length`. A step
never decreases it (`[[Smith.biSize_step]]`), and a step onto an implicit blank
increases it by one. This is how "the head stays on the initial tape" is formalized in
chapters 08 and 09: `biSize` constant.

## Wolfram's machine

```lean
def wolfram23 : Machine where
  numStates := 3   -- 0=halt, 1=A, 2=B
  numSymbols := 3  -- 0, 1, 2
  transition := fun state sym =>
    match state, sym with
    | 1, 0 => { nextState := 2, write := 1, dir := Dir.R }  -- A,0 -> 1,R,B
    | 1, 1 => { nextState := 1, write := 2, dir := Dir.L }  -- A,1 -> 2,L,A
    | 1, 2 => { nextState := 1, write := 1, dir := Dir.L }  -- A,2 -> 1,L,A
    | 2, 0 => { nextState := 1, write := 2, dir := Dir.L }  -- B,0 -> 2,L,A
    | 2, 1 => { nextState := 2, write := 2, dir := Dir.R }  -- B,1 -> 2,R,B
    | 2, 2 => { nextState := 1, write := 0, dir := Dir.R }  -- B,2 -> 0,R,A
    | _, _ => { nextState := 0, write := 0, dir := Dir.R }  -- unused/halt
```

Entry by entry this is Wolfram's rule 596440 as published (A0 -> 1RB, A1 -> 2LA,
A2 -> 1LA, B0 -> 2LA, B1 -> 2RB, B2 -> 0RA) and Smith's System 0 table on p. 3, whose
four rows read: before (symbol, state), after (symbol, new active position and state).
The independent review of 2026-09-21 checked all six entries against both sources and
the p. 47 trace. State 0 is never entered from states 1 and 2, so the halt row is dead.

`[[BiTM.IsValidWolfram23Cfg]]`: state 1 or 2, head below 3, every cell below 3.
`[[BiTM.step_wolfram23_preserves_valid]]` and `[[BiTM.nSteps_wolfram23_preserves_valid]]`:
the machine never halts and never leaves the alphabet from a valid configuration.

## The lookahead machine type

```lean
inductive LState : Type
  | A : LState
  | B : LState
  | C : LState

inductive LRule : Type
  | one (st : LState) (a : Fin 3) (d : Dir) : LRule
  | two (st : LState) (a b : Fin 3) (d : Dir) : LRule

structure LMachine where
  trans : LState → Fin 3 → Fin 3 → LRule
```

`[[Smith.LMachine]]` reads the state, the active cell and its right neighbour (`0` when
there is none) and returns a one-cell rule (rewrite the active cell) or a two-cell rule
(rewrite both), with a move. These are the two rule shapes of Smith's `sys0-3.pl`
(p. 45). `[[Smith.LConfig]]` is the zipper `(left, head, right, state)` with `left`
nearest first, like `BiTM.Config` but over `Fin 3`. `[[Smith.lstep]]` is `none` when the
move would leave either end of the finite tape, and `none` for a two-cell rule with no
right neighbour; `[[Smith.lnSteps]]` iterates. `[[Smith.exitRight]]` records the state and
tape when a one-cell rule moves off the right end.

The four tables `[[Smith.sys0]]`, `[[Smith.sys1]]`, `[[Smith.sys2]]`, `[[Smith.sys3]]` are
transcribed from p. 45 (chapter 07 for the relabelings between them). `sys0` uses only
one-cell rules and is Wolfram's table; `sys1` replaces `B2` by three two-cell rules
`B20 -> A00>`, `B21 -> B12>`, `B22 -> B11>`; `sys2` and `sys3` add state C. Every table
satisfies `[[Smith.LMachine.OneIgnoresNeighbour]]` (a one-cell rule does not depend on
the neighbour), checked by `decide`, and the p. 47 trace of `sys0-3.pl 0 N 00A00000` is
reproduced tape for tape over its 27 steps (`[[Smith.traceP47]]`).

## The bridge to wolfram23

`[[Smith.toBi]]` reads a System 0 configuration as a `BiTM.Config`: A is state 1, B is
state 2, C is state 3 (never reached from A or B), symbols by `Fin.val`. `[[Smith.ofBi]]`
is the inverse on valid configurations (`[[Smith.toBi_ofBi]]`).

```lean
theorem toBi_step (c c' : LConfig) (hst : c.state ≠ C) (h : lstep sys0 c = some c') :
    BiTM.step wolfram23 (toBi c) = some (toBi c')

theorem toBi_exit (c : LConfig) (hst : c.state ≠ C) (h : lstep sys0 c = none) :
    ∃ cfg', BiTM.step wolfram23 (toBi c) = some cfg' ∧ biSize cfg' = biSize (toBi c) + 1

theorem toBi_run (c : LConfig) (hst : c.state ≠ C) (n : Nat) (c' : LConfig)
    (h : lnSteps sys0 c n = some c') :
    BiTM.nSteps wolfram23 (toBi c) n = some (toBi c') ∧ c'.state ≠ C
```

A System 0 step is a wolfram23 step; where System 0 is stuck (the head would leave the
finite tape) wolfram23 steps onto an implicit blank and the explicit tape grows by one.
This is the only place the finite zipper meets the implicit blanks, and it is where the
exit condition of chapters 08 and 09 comes from.

## Notes and caveats

- Direction conventions are consistent across `TM.Dir`, `BiTM.step` and `lstep`: `L`
  pops from `left`, `R` pops from `right`. The review checked this.
- `LMachine` passes `0` as the neighbour at the right end but `lstep` discards any
  two-cell result there. So at the end of the System 4 emulation (System 3 head on the
  closing 1 in state C, chapter 08) `lstep sys3` and `exitRight sys3` are both `none`;
  the exit that the theorems report is realized after relabeling, by the `BiTM` step
  `[[Smith.wolfram23_exit_step]]` (`B2 -> 0RA` onto the implicit blank). The Lookahead
  header says so since 2026-09-22; `exitRight` records one-cell exits only and is used
  only by the p. 47 check.
- Two branches of `[[BiTM.System4.step]]` (chapter 05) and none of the machine model
  here deviate from Smith's Perl programs; the machine model is faithful.

## Depends on

`TM.Defs`, `BiTM.Basic`, `BiTM.Wolfram23Valid`, `Smith.Lookahead`, `Smith.Wolfram23Bridge`.
