/-
  Blueprint.Chapters.OpenItems

  Chapter 11 of the blueprint: the open items, what is not proved and what
  the statements do not say. The chapter introduces no blueprint node; its
  declaration links resolve against the nodes of the other chapters.
-/

import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Open items" =>

%%%
tag := "open-items"
file := "open-items"
htmlSplit := .never
%%%

What is not proved, and what the statements do not say. Items are ordered by weight;
none is a soundness problem.

# Mathematics

- A size bound for the initial condition. `IC tm c n` ({bpref "Smith.IC"}[`Smith.IC`]) and `ITape tm c`
  ({bpref "Smith.ITape"}[`Smith.ITape`]) are definitions that run no system, but no theorem bounds
  `biSize (IC tm c n)` by a closed form `F tm c n`, or the cost of writing the tape
  down. The run bounds behind them ({bpref "Smith.System5.run_bound"}[`Smith.System5.run_bound`],
  {bpref "Smith.System4.run_bound"}[`Smith.System4.run_bound`], {bpref "TagSystem.tagTime_le"}[`TagSystem.tagTime_le`]) are coarser than Smith's
  `3^(n-1) M` and could be tightened.
- Binary machines. {bpref "TagSystem.WF"}[`TagSystem.WF`] covers two-symbol machines; the reduction of
  k-symbol machines, or a bridge to Mathlib's `Turing.TM0`, is not formalized.
- Event-based decoding times. The schedule is existential and nothing is said about
  `decodeTM` at other times; on the D9 tape `decodeW23` returns `some` at unscheduled
  times. The proof has a syntactic marker (wolfram23 back at the left end of the
  tape in state B, System 4 back on its first set in state B) that could be
  surfaced, and a clause "at every time up to `T` the decoder returns `none` or the
  latest scheduled configuration" would close it.
- One schedule for the infinite form. Each block of `ITape tm c` re-emulates the run
  from the start, so the decode of step `i` recurs in every block `k >= i`; the
  theorem gives one schedule per block.
- The halt row. `WF` constrains the never-executed row of state 0 because the tag
  productions keep applying `tm.transition 0 _` after halting. A wrapper under
  `forall q < numStates, 0 < q -> ...` via a `patch0` lemma
  (`nSteps (patch0 tm) = nSteps tm`) would remove the condition.

# Tests

- A positive {bpref "Smith.decodeTM"}[`Smith.decodeTM`] vector on a rendered tape. It needs a block of
  width at least `2^13`, whose rendering builds its parity rows by iteration, beyond
  `decide`.
