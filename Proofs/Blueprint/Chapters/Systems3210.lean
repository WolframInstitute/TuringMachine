/-
  Blueprint.Chapters.Systems3210

  Chapter 7 of the blueprint: the second half of T3, the relabelings of
  Systems 3, 2 and 1 down to System 0 as forward simulations and their
  composite, and T5, Smith's loop-freeness argument made in System 1 and
  carried to System 0 and to wolfram23.
-/

import Verso
import VersoManual
import VersoBlueprint
import Smith.Lookahead
import Smith.Systems123
import Smith.LoopFree
import Smith.Wolfram23Bridge
import BiTM.Wolfram23Valid

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "T3, second half, and T5: Systems 3, 2, 1, 0 and loop-freeness" =>

%%%
tag := "systems-3-2-1-0"
file := "systems-3-2-1-0"
htmlSplit := .never
%%%

# Orientation

Smith's Conjectures 0 to 3 differ only in the machine (p. 3-5). System 1 is
System 0 with the `B2` rule split by the right neighbour; System 2 adds a state C
that is state B with the active cell swapped; System 3 is System 2 with every cell
left of the head swapped. [`Smith/Systems123.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Systems123.lean) proves each relabeling as a
forward simulation in the direction the chain needs, from the higher system to the
lower. [`Smith/LoopFree.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/LoopFree.lean) and [`Smith/Wolfram23Bridge.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Wolfram23Bridge.lean) prove Smith's
loop-freeness argument (p. 21-22), T5. Loop-freeness is proved but not used by the
chain: the schedules of the chapters from
{ref "cts-to-system5"}[cyclic tag to System 5] to
{ref "system4-to-system3"}[System 4 to System 3] are explicit, so the run of each
finite initial condition is known to end without an appeal to it.

# The relabelings

:::group "relabelings"
The relabelings of Systems 3, 2 and 1 down to System 0 (p. 3-5) as forward
simulations, and their composite.
:::

:::definition "Smith.sw" (parent := "relabelings") (lean := "Smith.sw") (tags := "T3")
`sw` swaps the symbols 1 and 2 and fixes 0 (Smith's "subtracted from 3 (mod 3)").
:::

:::definition "Smith.phi2" (parent := "relabelings") (lean := "Smith.phi2") (tags := "T3")
The System 2 to System 1 relabeling of p. 4, on the zipper configurations
{uses "Smith.LConfig"}[]: a configuration `⟨L, a, R, C⟩` in state C becomes
`⟨L, sw a, R, B⟩`, state B with the active cell swapped by {uses "Smith.sw"}[];
every configuration in state A or B is unchanged.
:::

:::definition "Smith.phi3" (parent := "relabelings") (lean := "Smith.phi3") (tags := "T3")
The System 3 to System 2 relabeling of p. 5: every cell left of the head is swapped
by {uses "Smith.sw"}[] (`L.map sw`), and so is the head cell itself in state A;
in states B and C the head cell is kept. The cells right of the head and the state
are kept in every case.
:::

:::lemma_ "Smith.sys0_B2_three" (parent := "relabelings") (lean := "Smith.sys0_B2_three") (tags := "T3")
For `b = 1` or `b = 2`, three steps of {uses "Smith.sys0"}[] from `⟨L, 2, b :: R, B⟩`
reach `⟨1 :: L, sw b, R, B⟩` (in the run function {uses "Smith.lnSteps"}[]):
`B2 -> A0>`, then `A1 -> A2<` or `A2 -> A1<`, then `A0 -> B1>` (p. 4). This is
the System 0 reading of the System 1 rules `B21` and `B22`.
:::

:::proof "Smith.sys0_B2_three"
Both cases of `b`, and `R` empty or not, by unfolding the three steps against the
rule table of System 0.
:::

:::theorem "Smith.sys1_sys0_forwardSim" (parent := "relabelings") (lean := "Smith.sys1_sys0_forwardSim") (tags := "T3")
A {uses "Smith.ForwardSim"}[] from {uses "Smith.sys1"}[] to {uses "Smith.sys0"}[]
on the identity relation: System 0 emulates System 1 on the same configurations,
one step of System 1 being one or more steps of System 0. Conjectures 0 and 1 are
equivalent (p. 4), in the direction the chain uses.
:::

:::proof "Smith.sys1_sys0_forwardSim"
One System 1 step is one System 0 step, or three for `B21` and `B22`
({uses "Smith.sys0_B2_three"}[]). The one-step form is the helper
`Smith.sys1_sys0_step`, proved by splitting on the state, the head symbol and the
right neighbour and comparing the two rule tables; every rule other than `B2x`
is the same rule in both systems.
:::

:::lemma_ "Smith.phi2_step" (parent := "relabelings") (lean := "Smith.phi2_step") (tags := "T3")
One step of {uses "Smith.sys2"}[] is one step of {uses "Smith.sys1"}[] through
{uses "Smith.phi2"}[]: `lstep sys1 (phi2 c) = (lstep sys2 c).map phi2` for every
configuration `c` ({uses "Smith.lstep"}[]).
:::

:::proof "Smith.phi2_step"
Case analysis over the rule tables: split on the state, the head symbol, the right
neighbour (present or not) and the left tape (empty or not), and simplify each
case.
:::

:::theorem "Smith.sys2_sys1_forwardSim" (parent := "relabelings") (lean := "Smith.sys2_sys1_forwardSim") (tags := "T3")
A {uses "Smith.ForwardSim"}[] from {uses "Smith.sys2"}[] to {uses "Smith.sys1"}[]
along {uses "Smith.phi2"}[], that is, on the relation `c' = phi2 c`, one step to
one step. Conjectures 1 and 2 are equivalent (p. 4), in the direction the chain
uses.
:::

:::proof "Smith.sys2_sys1_forwardSim"
Directly from {uses "Smith.phi2_step"}[], with one target step for each source
step.
:::

:::lemma_ "Smith.phi3_step" (parent := "relabelings") (lean := "Smith.phi3_step") (tags := "T3")
One step of {uses "Smith.sys3"}[] is one step of {uses "Smith.sys2"}[] through
{uses "Smith.phi3"}[]: `lstep sys2 (phi3 c) = (lstep sys3 c).map phi3` for every
configuration `c` ({uses "Smith.lstep"}[]).
:::

:::proof "Smith.phi3_step"
The same case analysis as for `phi2`, over the rule tables of Systems 2 and 3.
:::

:::theorem "Smith.sys3_sys2_forwardSim" (parent := "relabelings") (lean := "Smith.sys3_sys2_forwardSim") (tags := "T3")
A {uses "Smith.ForwardSim"}[] from {uses "Smith.sys3"}[] to {uses "Smith.sys2"}[]
along {uses "Smith.phi3"}[], that is, on the relation `c' = phi3 c`, one step to
one step. Conjectures 2 and 3 are equivalent (p. 5), in the direction the chain
uses.
:::

:::proof "Smith.sys3_sys2_forwardSim"
Directly from {uses "Smith.phi3_step"}[], with one target step for each source
step.
:::

:::theorem "Smith.sys3_sys0_forwardSim" (parent := "relabelings") (lean := "Smith.sys3_sys0_forwardSim") (tags := "T3")
A {uses "Smith.ForwardSim"}[] from {uses "Smith.sys3"}[] to {uses "Smith.sys0"}[]
on the relation `c' = phi2 (phi3 c)` ({uses "Smith.phi2"}[], {uses "Smith.phi3"}[]):
System 0 emulates System 3 through `phi2 ∘ phi3`, one step of System 3 being one
or three steps of System 0. Conjecture 3 implies Conjecture 0 (p. 3-5). This
composite is what the chapter {ref "system4-to-system3"}[System 4 to System 3]
composes with, in {bpref "Smith.sys4_sys0_forwardSim"}[].
:::

:::proof "Smith.sys3_sys0_forwardSim"
Compose {uses "Smith.sys3_sys2_forwardSim"}[], {uses "Smith.sys2_sys1_forwardSim"}[]
and {uses "Smith.sys1_sys0_forwardSim"}[] with {uses "Smith.ForwardSim_comp"}[],
then rewrite the composed relation (two existentials over the intermediate
configurations) into the functional relation `c' = phi2 (phi3 c)` with the helper
`Smith.ForwardSim_congr`.
:::

The correspondences are also checked by `decide`: the 1-or-3 correspondence and
the two relabelings on every tape of one cell on each side of the head (all 81
choices of state and three cells). Negative instances on the same tapes show that
neither relabeling is the identity: without `phi3` (respectively `phi2`) on the
source configuration the one-step correspondence fails. `phi2` is many-to-one
(System 1 has no state C), so these are simulations, not bisimulations; the other
direction is not needed.

# Loop-freeness (T5)

:::group "loop-freeness"
Smith's loop-freeness argument (p. 21-22): the measure on System 1, the end of
every run of Systems 1 and 0 on a finite tape, and the transfer to wolfram23.
:::

Smith's argument (p. 21-22), made in System 1.

:::definition "Smith.V" (parent := "loop-freeness") (lean := "Smith.V") (tags := "T5")
Smith's sum (p. 22): `V c` is the sum of the positions, counted from 1 at the left
end of the tape, of the 0s of the tape of the configuration `c`
({uses "Smith.LConfig"}[]).
:::

:::definition "Smith.W" (parent := "loop-freeness") (lean := "Smith.W") (tags := "T5")
`W c` is {uses "Smith.V"}[] `c` without the contribution of the head cell in state
A (the `A0 -> B1>` step that must follow spends it). The helper `Smith.W_eq`
records the relation: `W c` is `V c` minus the position of the head cell (counted
from 1) when the state is A and the head reads 0, and `V c` otherwise.
:::

:::definition "Smith.phase" (parent := "loop-freeness") (lean := "Smith.phase") (tags := "T5")
The secondary measure on {uses "Smith.LConfig"}[]: in state A, the head position
plus the tape length, plus one (the tape length is added so that the change from
A to B decreases it too); in state B (and in state C, which the argument never
reaches), the number of cells to the right of the head. It measures how far the head can still go in its current direction before
it changes state.
:::

:::theorem "Smith.sys1_measure" (parent := "loop-freeness") (lean := "Smith.sys1_measure") (tags := "T5")
Every step of {uses "Smith.sys1"}[] ({uses "Smith.lstep"}[]) from a configuration
`c` whose state is not C, to a configuration `c'`, decreases the pair
`(W, phase)` lexicographically ({uses "Smith.W"}[], {uses "Smith.phase"}[]): either
`W c' < W c`, or `W c' = W c` and `phase c' < phase c`; and the state of `c'` is
not C either.
:::

:::proof "Smith.sys1_measure"
Rule by rule, after splitting on both neighbours (the left tape empty or not, the
right tape empty or not), the state and the head symbol, and unfolding `W` and
`phase`; each case closes by arithmetic. The step `B20` raises `V` by the head
position and lowers `W` by 1, which is Smith's "decreases to a lower value than
the value it increased from". On the run of p. 47 the source checks by `decide`
that `V` is not monotone along the System 0 run while `W` never increases along
the System 1 run of the same tape.
:::

:::lemma_ "Smith.run_ends_of_measure" (parent := "loop-freeness") (lean := "Smith.run_ends_of_measure") (tags := "T5")
A lexicographically decreasing measure ends every run: for a machine `M`
({uses "Smith.LMachine"}[]), a set of configurations `P` and measures `W`, `phase`
such that every step of `M` from a configuration in `P` lands in `P` and decreases
`(W, phase)` lexicographically, every configuration in `P` has some `n` with
`lnSteps M c n = none` ({uses "Smith.lnSteps"}[]).
:::

:::proof "Smith.run_ends_of_measure"
Induction on a bound `w` for `W c`, and inside it on a bound `f` for `phase c`.
If the step is `none` the run ends after one step; otherwise the next
configuration is in `P` with a smaller measure and the induction hypothesis gives
its run length, plus one.
:::

:::theorem "Smith.sys1_leaves" (parent := "loop-freeness") (lean := "Smith.sys1_leaves") (tags := "T5")
T5 for System 1: from every configuration whose state is not C, the run of
{uses "Smith.sys1"}[] ends, that is, there is an `n` with
`lnSteps sys1 c n = none` ({uses "Smith.lnSteps"}[]).
:::

:::proof "Smith.sys1_leaves"
{uses "Smith.run_ends_of_measure"}[] applied to `sys1`, the set of configurations
not in state C, and the measures `W`, `phase`, with {uses "Smith.sys1_measure"}[]
as the decrease hypothesis and the configuration's own `W c` and `phase c` as the
bounds.
:::

:::lemma_ "Smith.sys1_none_sys0" (parent := "loop-freeness") (lean := "Smith.sys1_none_sys0") (tags := "T5")
System 0 is stuck wherever System 1 is: if `lstep sys1 c = none` then
`lstep sys0 c = none` ({uses "Smith.lstep"}[], {uses "Smith.sys1"}[],
{uses "Smith.sys0"}[]).
:::

:::proof "Smith.sys1_none_sys0"
The one-cell rules are the same in both systems, and `B2` at the last cell, where
System 1's two-cell rule has no right neighbour, moves System 0 off the tape; by
cases on the state, the head symbol and both neighbours.
:::

:::lemma_ "Smith.run_ends_of_sim" (parent := "loop-freeness") (lean := "Smith.run_ends_of_sim") (tags := "T5")
A run of the target that ends when the source's run ends: for machines `M1`, `M0`
({uses "Smith.LMachine"}[]) such that every step of `M1` from `c` to `c'` is some
`k >= 1` steps of `M0` from `c` to `c'`, and `M0` is stuck wherever `M1` is, if
`lnSteps M1 c n = none` for some `n` then `lnSteps M0 c m = none` for some `m`
({uses "Smith.lnSteps"}[]).
:::

:::proof "Smith.run_ends_of_sim"
Induction on `n`. If `M1` is stuck at `c` so is `M0`; otherwise the `M1` step to
`c'` is `k` steps of `M0`, the induction hypothesis gives an `m` for `c'`, and the
runs concatenate by {uses "Smith.lnSteps_add"}[] to a run of length `k + m` that
is `none`.
:::

:::theorem "Smith.sys0_leaves" (parent := "loop-freeness") (lean := "Smith.sys0_leaves") (tags := "T5")
T5 for System 0, Wolfram's machine on a finite tape: from every configuration
whose state is not C, the run of {uses "Smith.sys0"}[] ends, that is, there is an
`n` with `lnSteps sys0 c n = none` ({uses "Smith.lnSteps"}[]).
:::

:::proof "Smith.sys0_leaves"
{uses "Smith.sys1_leaves"}[] gives the end of the System 1 run;
{uses "Smith.run_ends_of_sim"}[] transfers it along the 1-or-3 correspondence of
{uses "Smith.sys1_sys0_forwardSim"}[] (its one-step form `Smith.sys1_sys0_step`)
with {uses "Smith.sys1_none_sys0"}[] for the stuck configurations.
:::

:::theorem "Smith.sys0_not_periodic" (parent := "loop-freeness") (lean := "Smith.sys0_not_periodic") (tags := "T5")
No configuration of {uses "Smith.sys0"}[] whose state is not C is periodic: for
every period `p >= 1`, `lnSteps sys0 c p` is not `some c` ({uses "Smith.lnSteps"}[]).
:::

:::proof "Smith.sys0_not_periodic"
Suppose `lnSteps sys0 c p = some c`. Iterating with {uses "Smith.lnSteps_add"}[],
`lnSteps sys0 c (k * p) = some c` for every `k`. But {uses "Smith.sys0_leaves"}[]
gives an `n` with `lnSteps sys0 c n = none`, and a run that is `none` after `n`
steps is `none` after any later number of steps (the helper
`Smith.lnSteps_none_add`); `(n + 1) * p >= n + 1` gives the contradiction.
:::

Through the bridge of the chapter on the {ref "machine-model"}[machine model]:

:::theorem "Smith.wolfram23_leaves" (parent := "loop-freeness") (lean := "Smith.wolfram23_leaves") (tags := "T5")
T5 for Wolfram's machine: from every valid configuration `cfg`
({uses "BiTM.Config"}[], {uses "BiTM.IsValidWolfram23Cfg"}[]) the run of
{uses "BiTM.wolfram23"}[] ({uses "BiTM.nSteps"}[]) reaches, after some `n` steps,
a configuration `cfg'` with `biSize cfg' = biSize cfg + 1`
({uses "Smith.biSize"}[]), that is, with one more explicit cell: the head has
stepped off the initial finite tape.
:::

:::proof "Smith.wolfram23_leaves"
Read `cfg` as the System 0 configuration {uses "Smith.ofBi"}[] `cfg`, whose state
is not C (`Smith.ofBi_state`). {uses "Smith.sys0_leaves"}[] gives a run of System 0
that ends; the helper `Smith.lnSteps_none_decompose` splits it into `m` successful
steps to a configuration `c1` at which `lstep sys0` is `none`.
{uses "Smith.toBi_run"}[] transports the `m` steps to wolfram23 through
{uses "Smith.toBi"}[], {uses "Smith.toBi_exit"}[] gives the wolfram23 step from
`toBi c1` onto the blank right of the tape with one more explicit cell, and
{uses "Smith.toBi_ofBi"}[] identifies `toBi (ofBi cfg)` with `cfg` (this is where
validity is used). The size bookkeeping is {uses "Smith.lnSteps_length"}[]: a
System 0 run never changes the length of the tape, so `biSize (toBi c1)` is
`biSize cfg`. The wolfram23 run has length `m + 1`.
:::

:::theorem "Smith.wolfram23_not_periodic" (parent := "loop-freeness") (lean := "Smith.wolfram23_not_periodic") (tags := "T5")
No valid configuration `cfg` of {uses "BiTM.wolfram23"}[]
({uses "BiTM.IsValidWolfram23Cfg"}[]) is periodic: for every period `p >= 1`,
`BiTM.nSteps wolfram23 cfg p` is not `some cfg` ({uses "BiTM.nSteps"}[]).
:::

:::proof "Smith.wolfram23_not_periodic"
Suppose the run returns to `cfg` after `p` steps; then it returns to `cfg` after
`k * p` steps for every `k`. {uses "Smith.wolfram23_leaves"}[] gives an `n` and a
configuration `cfg'` after `n` steps with `biSize cfg' = biSize cfg + 1`. Take
`k = n + 1`: the run from `cfg'` of the remaining `(n + 1) * p - n` steps reaches
`cfg`, but {uses "Smith.biSize"}[] never decreases along a run
({uses "Smith.biSize_step"}[], iterated in the helper `Smith.biSize_nSteps`),
contradiction.
:::

From every valid configuration the wolfram23 run reaches a configuration with one
more explicit cell, that is, the head leaves the initial finite tape; and no valid
configuration is periodic, since `biSize` never decreases along a run. This is the
formal counterpart of the refutations in [`docs/REVIEW.md`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/docs/REVIEW.md) section 4.1 (the old
step-faithful predicates needed a periodic configuration) and settles, in Smith's
direction, what the old code base treated as open.

# Notes and caveats

- T5 is standalone. `grep` shows `sys0_leaves`, `wolfram23_leaves` and
  `wolfram23_not_periodic` are referenced only in [`Smith/LoopFree.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/LoopFree.lean) and
  [`Smith/Wolfram23Bridge.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Wolfram23Bridge.lean). [`docs/PLAN.md`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/docs/PLAN.md) section 2 used to say T6 "follows
  from T4 and T5"; the {ref "infinite-form"}[infinite form] does not use T5,
  because it has explicit exit times. Smith needs T5 because his Conjecture 0
  does not come with a schedule.
- The exit time is existential (bounded by the measure); no closed form is
  stated.
- [`Smith/Conjecture3.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Conjecture3.lean) used to import `LoopFree` only for {bpref "Smith.lnSteps_add"}[`Smith.lnSteps_add`];
  the lemma lives in [`Smith/Lookahead.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Lookahead.lean) since 2026-09-22 and the import is gone
  (the chapter on {ref "system4-to-system3"}[System 4 to System 3]).

# Depends on

The modules of this chapter are `Smith.Lookahead` (the machine type, the rule
tables of Systems 0 to 3 and `lnSteps_add`), `Smith.Systems123` (the
relabelings), `Smith.LoopFree` (the measure and T5 for Systems 1 and 0),
`Smith.Wolfram23Bridge` (T5 for wolfram23) and `BiTM.Wolfram23Valid` (the
validity predicate). The relabelings depend on the simulation calculus of the
chapter on {ref "cts-to-system5"}[cyclic tag to System 5] (`ForwardSim`,
`ForwardSim_comp`) and on the machine model of the chapter on the
{ref "machine-model"}[machine model] (`LConfig`, `lstep`, `lnSteps`, `sys0` to
`sys3`, `toBi`, `ofBi`, `biSize`); the bridge theorems also use `lnSteps_length`
of [`Smith/Wolfram23Bridge.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Wolfram23Bridge.lean), introduced in the chapter on
{ref "conjecture0"}[Conjecture 0].
