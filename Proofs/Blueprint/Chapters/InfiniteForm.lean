/-
  Blueprint.Chapters.InfiniteForm

  Chapter 10 of the blueprint: T6, the infinite form of Conjecture 0. The
  statement (introduced in the overview) read clause by clause, why the
  finite form does not chain, the construction (guarded System 4 blocks,
  the System 3 side, the chain, the infinite tape), the tests, and what
  remains existential.
-/

import Verso
import VersoManual
import VersoBlueprint
import Blueprint.Chapters.Overview
import Smith.Guards
import Smith.Infinite

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "T6: the infinite form" =>

%%%
tag := "infinite-form"
file := "infinite-form"
htmlSplit := .never
%%%

# Orientation

Smith's theorem, as he states it (p. 3 and p. 21-22), is the infinite form: a single
right-infinite initial condition from which System 0 emulates a two-colour cyclic tag
system for an infinite number of steps. The finite form of {ref "conjecture0"}[the
chapter on Conjecture 0] is his Conjecture 0; the infinite form is what he calls the
solution of the problem posed in the introduction, and it is the form that answers
the objection of {ref "universality"}[the chapter on the composition] that a
budget-indexed family of tapes is not one encoding.

This chapter states what is proved ([`Smith/Infinite.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Infinite.lean), [`Smith/Guards.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Guards.lean),
2026-09-22), describes the construction, and says what remains existential. The
narrative was written before the proof and guided it; the sections below were
reconciled with the source when the theorem landed.

# The statement

The statement is {bpref "Smith.wolfram23_infinite"}[] in {ref "overview"}[the
overview]. Read clause by clause:

- `tm`, `hwf`, `c`, `hv`, `hst` are as in the overview: a well-formed binary machine
  and a valid configuration with state in range. There is no budget and no hypothesis
  on halting.
- `t : Nat -> Nat` is the tape right of the head, a stream of cells, all 0, 1 or 2.
  `istart t` is the configuration `(state B, left [], head 2, right t)`: the head on a
  2 in state B at the left end. `IConfig` is a wolfram23 configuration whose right
  tape is a stream; `istep` and `inSteps` are {bpref "BiTM.step"}[`BiTM.step`] and {bpref "BiTM.nSteps"}[`BiTM.nSteps`] with the
  stream in place of the list (the left tape is a list with an implicit blank beyond,
  as in {bpref "BiTM.Config"}[`BiTM.Config`]).
- At every time the run is defined (`inSteps_valid`: wolfram23 never halts on a
  configuration whose cells are below 3, `IValid`) and does not move left from an
  empty left tape: the head never leaves the tape to the left, so the implicit blank
  on the left is never read and the tape is genuinely one-sided.
- For every `k`: a width `2^w`, a band `b`, a window `W` and times `times i`, the last
  of them later than `k` (the emulation advances along the tape). The times are
  strictly increasing on `i < k` for as long as the run of `tm` continues (if `tm`
  halts at step `m < k`, the clause is silent beyond `m`; in the proof the times are
  constant there). For every `i <= k` at which the run of `tm` is defined, wolfram23
  is in state B at `times i` and the infinite configuration, truncated to the `W`
  cells right of the head (`truncI`) or to any larger window, decodes by `decodeTM`
  to the `i`-th configuration without trailing blanks (`canon`). The "any larger
  window" clause says that the decoder, which reads up to the first 0 right of the
  head, has read the whole leading conglomerate: the window does not cut it.

One tape per machine and input, with no budget in the statement. The parameters `w`,
`b`, `W` and the schedule vary with `k`, as in Smith's construction (his `w_n` grows
along the tape, p. 25): block `k` re-emulates the run from the start with its own
width and band, so the decode of step `i` recurs in every block `k >= i`. What the
statement does not say is discussed under "What remains existential" below.

:::group "infinite_tape"
The infinite tape and its semantics: configurations with a stream to the right, their
agreement with finite configurations, the decoder on a window.
:::

:::definition "Smith.IConfig" (parent := "infinite_tape") (lean := "Smith.IConfig, Smith.istep, Smith.inSteps")
A wolfram23 configuration whose tape is infinite to the right: the state, the cells
left of the head nearest first (blank beyond, as in {uses "BiTM.Config"}[]), the head
cell, and the cells right of the head as a stream `Nat -> Nat`. `istep` is one step
with the semantics of {uses "BiTM.step"}[] (halt on state 0, a left move reads the
list, a right move consumes the first cell of the stream and shifts it), and
`inSteps` iterates it.
:::

:::definition "Smith.istart" (parent := "infinite_tape") (lean := "Smith.istart, Smith.IValid")
`istart t` is wolfram23 at the left end of the infinite tape `t`: state B on a 2 with
nothing to the left. A configuration is `IValid` when its state is A or B and every
cell, on the left, under the head and in the stream, is 0, 1 or 2.
:::

:::theorem "Smith.inSteps_valid" (parent := "infinite_tape") (lean := "Smith.inSteps_valid")
From an `IValid` configuration the run of wolfram23 is defined at every time and stays
`IValid`: {uses "BiTM.wolfram23"}[] never halts on cells below 3.
:::

:::proof "Smith.inSteps_valid"
Induction on the time; one step (`istep_valid`) is a case analysis on the six entries
of Wolfram's table, each of which writes a cell below 3 and moves to state A or B.
:::

:::definition "Smith.Agree" (parent := "infinite_tape") (lean := "Smith.Agree, Smith.truncI")
The finite configuration `c` agrees with the infinite one `d` when they have the same
state, left tape and head, and the explicit cells right of the head of `c` are the
first cells of the stream of `d`. `truncI W d` is the finite configuration made of
`d`'s state, left tape, head and the first `W` cells of its stream; it agrees with
`d`.
:::

:::theorem "Smith.agree_run" (parent := "infinite_tape") (lean := "Smith.agree_run")
A finite run that keeps its size ({uses "Smith.biSize"}[] constant, that is, never
reads an implicit blank) is matched step for step by the infinite run from an
agreeing configuration, the agreement holding at every step.
:::

:::proof "Smith.agree_run"
One step (`agree_step`): the only way a finite step differs from the infinite step is
by reading the blank right of the finite tape, which grows the size by one; the
hypothesis excludes it. Then induction.
:::

:::theorem "Smith.decodeTM_trunc" (parent := "infinite_tape") (lean := "Smith.decodeTM_trunc")
On an infinite configuration that agrees with a finite one whose right tape contains
a 0 and fits in the window `W`, {uses "Smith.decodeTM"}[] of the window is
`decodeTM` of the finite configuration.
:::

:::proof "Smith.decodeTM_trunc"
The decoder reads only the head and the cells right of it up to the first 0
(`decodeW23_append`, from {uses "Smith.decodeW23"}[]), and the window's cells are the
finite right tape followed by more of the stream.
:::

# Smith's argument and why the finite T4 does not chain

Smith (p. 22): concatenate the initial condition that emulates the cyclic tag system
for 1 step with the one for 2 steps, for 3 steps, and so on, and start with the
leftmost 0 of the first initial condition active in state A. Each finite emulation
runs, exits to the right onto the next initial condition's leftmost cell, a 0, in
state A, and that is the start condition of the next emulation. Any increasing
sequence of budgets works, and "what is in the initial tape to the left of that
doesn't matter, as it never becomes active." He needs loop-freeness (T5,
{ref "systems-3-2-1-0"}[the chapter on Systems 3 to 0]) only to know that each finite
emulation does exit; with the explicit schedules of the previous chapters the exit
time is known and T5 is not used.

The formal T4 does not chain by plain concatenation:

- Its head starts on the first cell of the first block, with the left end `0^m 2 2 1`
  to its left. Started on the leftmost 0 in state A, wolfram23 does `A0 -> 1RB`,
  `B0 -> 2LA`, `A1 -> 2LA` and is left of its starting cell after three steps.
- Smith's own Perl encoder has the same left end and he says so (p. 25-26): the
  `0^m 2 2 1` form "works, but doesn't allow the program to be chained after another
  program by concatenation." His concatenable left end (p. 12-13) is a sequence of
  repetitions `0 2^(2^w - 1)`, which the entering head converts to `2 2 1 2 1 ... 2 1 0`
  and which then supplies one turn per repetition.

So the blocks of the infinite tape are not T4's tapes.

# The construction

The key observation is that Smith's concatenable left end is, in System 4 terms, a
row of guard sets separated by stars in front of the encoder tape, and that the
hand-off between blocks is nothing but System 4's rule 5: the exit of a block leaves
the head on the next block's leading star in state C, and rule 5 carries it onto the
first guard set. So the infinite construction lives at the System 4 level and the
System 3 relation of {ref "system4-to-system3"}[the chapter on System 4 to System 3]
only has to tolerate arbitrary cells beyond the guards.

## The block on the System 4 side

:::group "guards"
The guarded System 4 tapes of [`Smith/Guards.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Guards.lean): the block, its entry through the
guards, the padded tracking of the program's run, one guard consumed per turn.
:::

:::definition "Smith.blockTape" (parent := "guards") (lean := "Smith.blockTape, Smith.preGuardPairs, Smith.preM")
A block with guard parameter `n` and `r` guards around the program `orig` is the
System 4 tape

```
star, ({1, n}, star)^(r - 1), {0, 1, n - 1}, orig
```

where `orig = set S0 :: rest` is the encoder tape of
{ref "system5-to-system4"}[the chapter on System 5 to System 4] for the program of the
block (`preGuardPairs n (r - 1)` are the `r - 1` guards `{1, n}` with their stars,
`preM n` the innermost guard `{0, 1, n - 1}`); {uses "BiTM.System4.step"}[] is the
step.
:::

:::definition "Smith.padCfg" (parent := "guards") (lean := "Smith.padCfg, Smith.guardPairs, Smith.merged")
The padded form of a program configuration `c` after `t` turns, with `Lc` to the left
and `Rc` to the right: `Lc`, then `guardPairs n (r - 1 - t)` (the remaining guards,
each `{n - 1}` followed by a star), then the sets `merged n t` (the guards whose stars
were deleted, each decremented once per turn since, and the innermost `{n - 2 - t}`),
then `c`'s elements and `Rc`, the head shifted by the length of what precedes `c`.
:::

:::theorem "Smith.entryRun" (parent := "guards") (lean := "Smith.entryRun, Smith.padCfg_entry")
The entry: the head arrives on the leading star in state C. Rule 5 toggles 1 in the
first guard (giving `{n}`), the scan in state C decrements it (giving `{n - 1}`, the
state staying C because 0 is absent), rule 5 again on the next star, and so on; the
innermost `{0, 1, n - 1}` becomes `{0, n - 1}` and its scan in state C toggles the
state to B and decrements it. After `2r` steps the head is on the program's first set
in state B: the tape is `star, ({n - 1}, star)^(r - 1), {n - 2}, orig`, which is
{uses "Smith.padCfg"}[] of `orig` after its first step, with no turn yet. On the way the
head is on the leading star only at time 0.
:::

:::proof "Smith.entryRun"
Induction on the number of guards; each guard pair takes two steps (`entryPair`), the
innermost one two more (`entryLast`), all by the step lemmas of System 4.
:::

:::theorem "Smith.pad_turn" (parent := "guards") (lean := "Smith.pad_turn, Smith.parMem_zero_merged")
A turn of the program (rule 1 at its leftmost element, state A) becomes, on the
guarded tape after `t` turns, a walk left over the merged sets, the deletion of the
next star (rule 2, state B) and a scan of the merged sets, none of which contains 0
while `t + 3 <= n`, so the head arrives back on the program's first element in state
B, exactly as the turn would have left it: `2t + 4` steps, the padded form now with
`t + 1` turns. The head never reaches the leading star.
:::

:::proof "Smith.pad_turn"
The merged sets are `{n - 1}, ..., {n - t}` and `{n - 2 - t}`, all without 0 while
`t + 3 <= n` (`parMem_zero_merged`), so the sweep in state B decrements each and keeps
the state; the walk left and the sweep are the run lemmas `moveLeft` and `sweep` of
System 4, and one guard pair must remain (`t + 2 <= r`).
:::

:::theorem "Smith.pad_schedule" (parent := "guards") (lean := "Smith.pad_step, Smith.pad_schedule")
Every rule of the program other than a turn is one step on both tapes (`pad_step`), so
a program run of `N` steps with `N + 1 <= r` and `N + 2 <= n` is tracked on the guarded
tape at strictly increasing times, the padded form carrying the number of turns so
far, and the head never on the leading star.
:::

:::proof "Smith.pad_schedule"
Induction on `N` with {uses "Smith.pad_turn"}[] for the turns and `pad_step` for the
other rules; before each turn at least one guard pair remains (`pad_turn` needs
`t + 2 <= r`, and `t <= N - 1 <= r - 2`), the leading star is never deleted, and the
head is never on it after time 0 (`PosRun`, the `SafeC` condition of
{uses "Smith.SafeC"}[]); with `r = T4 + 1` and `N = T4 - 1` one pair is still left after
the last possible turn.
:::

:::theorem "Smith.block_run" (parent := "guards") (lean := "Smith.block_run")
The block's System 4 run from its entry: for a program run of `T4 >= 1` steps that
exits in state C past its last element, with `T4 <= r` and `T4 + 1 <= n`, the block
reaches the padded exit configuration at some time `H`, the head is on the leading
star only at time 0 in state C (`SafeC` for every budget), and the program's
configurations after each step appear, padded, at strictly increasing times
`2r + padT i`.
:::

:::proof "Smith.block_run"
{uses "Smith.entryRun"}[] for the first `2r` steps, then {uses "Smith.pad_schedule"}[]
on the program's run after its first step.
:::

:::definition "Smith.BlockSpec" (parent := "guards") (lean := "Smith.BlockData, Smith.BlockSpec")
`BlockData` packages a block: `n`, `r`, `w`, `b`, the program `S0`, `rest`, the run
length `H` and the decoding times `dt`. `BlockSpec tm c k bd` is the specification a
block must meet to emulate the first `k` steps of `tm` from `c`: `3 <= n`,
`H + b + 3 <= 2^w`, `n < 2^w`, the program well formed and ending with a set, its
integers below `2^w`, `SafeC (H + b)` on the block tape, the exit in state C at `H`,
and strictly increasing decoding times `dt i <= H` at which the block tape is the
shape `rep3_decode` reads and the decode is the doubled cyclic tag word of the `i`-th
configuration.
:::

:::theorem "Smith.block_exists" (parent := "guards") (lean := "Smith.block_exists")
For every `k` at which the run of `tm` from `c` is defined there is a block meeting
{uses "Smith.BlockSpec"}[], with `n = T4 + 3`, `r = T4 + 1`,
`w = H + b + n + 3f + 6`.
:::

:::proof "Smith.block_exists"
{uses "TagSystem.tm_tag_forwardSim"}[] gives the tag steps `tt k` of the machine's run
and {uses "TagSystem.cts_of_tag"}[] the cyclic tag run of `2 (1 + 84 S) tt k` steps,
whose last word is nonempty; {uses "Smith.system4_emulation"}[] (the System 4 half of
T4) supplies the program: the encoder tape, its exit in state C after `T4` steps, and
the decoding events with their decodes. {uses "Smith.block_run"}[] pads it; the width
covers the fuel, the guard parameter and the program's integers.
:::

## The block on the System 3 side

:::group "block_sys3"
The System 3 tracking of one block through the relation `Rep3` with a junk left end,
and the exit shape that is the next block's entry.
:::

{bpref "Smith.Rep3"}[] of {ref "system4-to-system3"}[the chapter on System 4 to
System 3] takes a left end that is either the finite `0^m 2 2 1^t` or arbitrary junk
guarded by `SafeC`, and a right closing that is either the closing 1 or a 0 followed by
arbitrary cells ({bpref "Smith.Closing"}[]).

:::definition "Smith.entry3" (parent := "block_sys3") (lean := "Smith.entry3, Smith.BlockData.cells")
The System 3 configuration at the entry of a block: the head on a 0 in state A with a
0 to its left (whatever `L` lies beyond is never read), the block's cells
`BlockData.cells` (the rendering of {uses "Smith.Rep3"}[] followed by the closing 0)
and the rest `Rc` of the tape to its right.
:::

:::theorem "Smith.rep3_entry" (parent := "block_sys3") (lean := "Smith.rep3_entry, Smith.blockAC_OK")
For a block meeting {uses "Smith.BlockSpec"}[], the entry configuration stands in
{uses "Smith.Rep3"}[] (junk left end, closing 0 followed by `Rc`) with the System 4
block tape, with fuel `H + b`.
:::

:::proof "Smith.rep3_entry"
`blockAC_OK` discharges the side conditions of the abstract configuration at the
entry: the width covers the fuel, the guard parameter and the program's integers, the
items are well formed, the head is on the leading star in state C, and `SafeC` holds
for the fuel (from the specification).
:::

:::theorem "Smith.rep3_exit_zero" (parent := "block_sys3") (lean := "Smith.rep3_exit_zero")
At System 4's exit in state C with the head past the last element, a configuration in
{uses "Smith.Rep3"}[] with a closing `0 :: Rc` has the System 3 head on that 0 in state
A with a 0 to its left: the entry shape of the next block.
:::

:::proof "Smith.rep3_exit_zero"
Case analysis on the focus of the abstract configuration: only the `off` focus has the
head past the last element, and its rendering with the zero closing is the shape.
:::

:::theorem "Smith.block_sys3" (parent := "block_sys3") (lean := "Smith.block_sys3")
The System 3 run of a block from its entry, for any junk `L` and rest `Rc`: it reaches
the entry of the next block (the head on the closing 0 in state A) after at least one
step, and on the way, at strictly increasing times, its tapes decode by
{uses "Smith.decodeW23"}[] (through the relabelings and `toBi`) to the doubled cyclic
tag words of the first `k` configurations of the machine, with a 0 right of the head
and wolfram23 in state B.
:::

:::proof "Smith.block_sys3"
{uses "Smith.sys4_sys3_forwardSim"}[] over the block with fuel `H + b`, from
{uses "Smith.rep3_entry"}[]; at the decoding times {uses "Smith.rep3_decode"}[] reads
the word (the band `b` is below the remaining fuel), and at time `H`
{uses "Smith.rep3_exit_zero"}[] gives the exit shape. That shape is `entry3` of the next
block: the hand-off is an identity of configurations.
:::

## The chain and the finite prefixes

:::group "chain"
The blocks chained, the finite start of `k + 1` blocks, and the wolfram23 run on it.
:::

:::definition "Smith.segCells" (parent := "chain") (lean := "Smith.segCells, Smith.start3, Smith.startFin")
`segCells bd j n` is the cells of the blocks `j, ..., j + n - 1`. `start3 bd k` is the
System 3 start `([], 2, 0 :: cells of blocks 0..k, B)`: its first step `B20 -> A00>`
is the entry of block 0 with `L = []`. `startFin bd k` is the wolfram23 configuration
`(B, [], 2, 0 :: cells)`, the relabeling of `start3 bd k`.
:::

:::theorem "Smith.chain_sys3" (parent := "chain") (lean := "Smith.chain_sys3")
The System 3 run through the blocks `j, ..., j + n - 1`, entry to entry, in at least
`n` steps, each block `j` emulating `kk j` steps.
:::

:::proof "Smith.chain_sys3"
Induction on `n` with {uses "Smith.block_sys3"}[].
:::

:::theorem "Smith.stage_w23" (parent := "chain") (lean := "Smith.stage_w23")
On the finite tape of blocks `0, ..., k`, wolfram23 from `startFin bd k` decodes, at
strictly increasing times, to the first `kk k` configurations of the machine (a 0
right of the head, state B at each), the last time later than `k`, and keeps the size
of its explicit tape throughout.
:::

:::proof "Smith.stage_w23"
{uses "Smith.chain_sys3"}[] through blocks `0, ..., k - 1`, {uses "Smith.block_sys3"}[]
on block `k`, then {uses "Smith.sys3_sys0_forwardSim"}[] and {uses "Smith.toBi_run"}[]
relabel the System 3 run to the wolfram23 run; the size invariant is
`lnSteps_length`.
:::

## The infinite tape

:::definition "Smith.tape" (parent := "infinite_tape") (lean := "Smith.tape")
The stream: a 0, then the cells of all the blocks in order; cell `i + 1` is read off
the first `i + 1` blocks ({uses "Smith.segCells"}[]), which have at least `i + 1`
cells.
:::

:::theorem "Smith.startFin_agree" (parent := "infinite_tape") (lean := "Smith.startFin_agree")
`startFin bd k` agrees ({uses "Smith.Agree"}[]) with `istart (tape bd)`.
:::

:::proof "Smith.startFin_agree"
The prefixes of the stream are stable (`segCells_getElem?_of_le`), so the explicit
cells of the finite start are the first cells of the stream.
:::

:::theorem "Smith.stage_infinite" (parent := "chain") (lean := "Smith.stage_infinite")
On the infinite tape of a sequence of blocks, block `j` emulating the longest run of at
most `j` steps: for every `k`, the width and band of block `k`, the window
`W = biSize (startFin bd k)`, times with `k < times k`, strictly increasing while the
run of `tm` goes on, no left move from an empty left tape before `times k`, and the
decodes of the defined configurations `i <= k` at `times i`, in state B, on the window
and on every larger window.
:::

:::proof "Smith.stage_infinite"
{uses "Smith.stage_w23"}[] on the finite tape, transferred to the infinite one by
{uses "Smith.agree_run"}[] from {uses "Smith.startFin_agree"}[]; the decoder on the
window by {uses "Smith.decodeTM_trunc"}[], then `undbl_dbl` and
{uses "TagSystem.decodeCTS_word"}[] turn the doubled cyclic tag word into the
configuration (its validity along the run by `nSteps_valid`). "No left move from an
empty left tape" follows from the size invariant: a left move from `left = []` reads
the implicit blank and grows the size by one.
:::

:::proof "Smith.wolfram23_infinite"
Block `k` emulates the longest run of at most `k` steps: `m k` is `Nat.findGreatest` of
"step `i` exists" below `k`, and {uses "Smith.block_exists"}[] is applied to `m k`;
the blocks are chosen classically (`choose`). For a machine that halts at step `m`,
every block from `m` on reproduces the whole run; for one that does not halt,
`m k = k`. This is why the theorem needs no hypothesis on halting, where the finite
form needs the run to last the budget. The tape is {uses "Smith.tape"}[] of those
blocks; {uses "Smith.inSteps_valid"}[] gives that the run is defined at every time,
{uses "Smith.stage_infinite"}[] gives the per-`k` clauses, and its "no left move" clause
holds at every time because the schedule of block `k` ends after time `k` (each block
takes at least one System 3 step).
:::

# Tests

[`Vectors/InfiniteVectors.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Vectors/InfiniteVectors.lean) (E1-E8, all by kernel `decide`). E1-E5: D9's program
`{0, 2} * {}` in a block with `n = 7`, `r = 5`, width `2^5`, band 4. E1: the System 4
entry in 10 steps to `padCfg 7 5 0`, the exit at 13 as the padded exit configuration,
stuck alone at 14, `SafeC`. E2: the System 3 run from `entry3`, the decode at 160
(`[false]`, as D9), the exit at 224 in the shape of `rep3_exit_zero`. E3: two blocks
chained through `start3`, decodes at 161 and 385, exits at 225 and 449. E4: wolfram23
from `startFin`, decodes at 335 and 793, the exit at 917 on the last cell in state A,
size 450 kept through 917 steps and 451 at 918, the head on the first cell only at
time 0. E5: `tape` at the block boundaries, the truncation of the infinite start to
449 cells being `startFin bd 1`, the infinite run decoding on a window of 64 cells and
on the theorem's window 450 at 335 and 793 (window stability: at 335 the first 0 is
cell 31, the window of 30 cells does not decode, every window from 31 on decodes
alike), entering block 2 at 918, where the finite run leaves its tape, and the
left-end clause failing on the all-zero tape at time 12. E6: the program `{0} {0, 1} * {2}`, which turns once at its
left end, in a block with `n = 12`, `r = 10`, width `2^6`: the turn as `pad_turn`
states it (the program's configuration padded with no turn at block time 24, with one
turn `2 * 0 + 4` steps later, the innermost guard `{10}` merged as `{9}`), the exit at
31 as `padCfg 12 10 1`, the System 3 exit after 1218 steps, the head never back on the
leftmost cell. E7: two blocks of different widths (`2^5` then `2^6`): `segCells`,
`tape` at the boundaries, the decodes at 335 (width 32) and 1113 (width 64), the exit
at 1365 and the entry into block 2. E8: the machine-independent side conditions of
`BlockSpec` on the E1 block, the System 4 decode at `dt 0`, the halting reading of the
block index (`Nat.findGreatest` on the one-step machine `tmH` of
[`Vectors/TMToCTSVectors.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Vectors/TMToCTSVectors.lean)) and the theorem instantiated on `tmH`.

# What remains existential

- The tape is existential in the statement and, in the proof, block `k` is sized from
  the run lengths of the emulation of `k` steps (`T4`, `b`, `H`, `f` from the schedules
  of the previous chapters), as in the finite form. One tape per `(tm, c)` removes the
  dependence on the budget, but the size of block `k` is not given by a closed form,
  and the tape's definition uses the schedules classically (`choose`).
- The statement does not bound the work done by the encoder, and this is the
  objection that remains ({ref "universality"}[the chapter on the composition],
  {ref "open-items"}[open items] item 1). The conclusion template of the theorem is
  satisfied by machines that do nothing: an infinite tape can hold, for every `k`, the
  `k + 1` configurations of the run laid out in advance, and a machine that only moves
  right over it meets every clause; and since the statement is
  `forall tm c, exists t`, the same block machinery would even give one dovetailed
  tape for all machines and inputs. What distinguishes wolfram23 is the construction
  behind the proof (Smith's encoders, whose blocks are built from the machine's
  description and the run's bookkeeping, not from the run's configurations), not the
  statement. A closed-form construction with a size bound (item 1) is what would put
  that into the statement; it is the other half of Smith's p. 22-26.
- The times are existential, one schedule per block; there is no single schedule
  across blocks (each block starts the emulation over).
- Smith starts "with the leftmost 0 active in state A"; here the start is a 2 in state
  B whose first step `B2 -> 0, R, A` puts the head on the leading 0 of block 0 in state
  A with a 0 to its left, the shape the block relation needs. This is one extra cell
  and one extra step.

# Depends on

`Smith.Guards`, `Smith.Conjecture3` with `LeftEnd.junk` and `Closing.zero`
({ref "system4-to-system3"}[the chapter on System 4 to System 3]), `Smith.Conjecture0`
(`rep3_decode`, `rep3_exit`, `system4_emulation`, {ref "conjecture0"}[the chapter on
Conjecture 0]), `Smith.Universality` (`decodeTM`, `undbl`, {ref "universality"}[the
chapter on the composition]), `TagSystem.TMToCTS` (`tm_tag_forwardSim`,
`decodeCTS_word`, `step_valid`, {ref "tm-to-cts"}[the chapter on the machine
reduction]).
