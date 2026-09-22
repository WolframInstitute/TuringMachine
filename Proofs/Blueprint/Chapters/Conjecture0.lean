/-
  Blueprint.Chapters.Conjecture0

  Chapter 8 of the blueprint: T4, Smith's Conjecture 0 in finite form. The
  composition of the cyclic-tag-to-wolfram23 half of the chain, the pieces
  added to the links (the bound on System 5, the encoder tape, the terminal
  phase, the exit), the decoder of the wolfram23 tape, the run bounds of
  System 5 and System 4, the closed-form initial condition and its
  parameters, and the corrections to Smith's statement.
-/

import Verso
import VersoManual
import VersoBlueprint
import Smith.Conjecture0
import Smith.ClosedForm
import Smith.Wolfram23Bridge
import BiTM.XorMerge

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "T4: Conjecture 0 in finite form" =>

%%%
tag := "conjecture0"
file := "conjecture0"
htmlSplit := .never
%%%

# Orientation

[`Smith/Conjecture0.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Conjecture0.lean) and [`Smith/ClosedForm.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/ClosedForm.lean) compose the four chapters from
{ref "cts-to-system5"}[cyclic tag to System 5] through
{ref "system5-to-system4"}[System 5 to System 4],
{ref "system4-to-system3"}[System 4 to System 3] and
{ref "systems-3-2-1-0"}[Systems 3, 2, 1 and 0] into {bpref "Smith.conjecture0_closed"}[`Smith.conjecture0_closed`]:
for a two-colour cyclic tag system, an initial word and a budget, the finite
wolfram23 tape `icStart`, a definition computed from the System 5 program by
closed-form bounds ([`Smith/RunBounds.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/RunBounds.lean)), is one from which the run reproduces the working strings of the
cyclic tag run at strictly increasing times, read by the decoder
{bpref "Smith.decodeW23"}[`Smith.decodeW23`], stays on the tape until then, and afterwards steps onto the
cell right of the tape, a 0, in state A. This is Smith's Conjecture 0 (p. 4)
"for an arbitrary number of steps", with two corrections recorded below, and
with the initial condition produced as Smith produces it (p. 20-26): from a
priori bounds on the run lengths, without running any system.
{bpref "Smith.conjecture0_finite"}[`Smith.conjecture0_finite`], the form with an existential tape, is a
corollary.

# The statement

:::group "t4_conjecture0"
T4, the finite form of Conjecture 0: the composition of the links from cyclic
tag to wolfram23, the pieces added to them, and the decoder of the wolfram23
tape.
:::

:::theorem "Smith.conjecture0_closed" (parent := "t4_conjecture0") (lean := "Smith.conjecture0_closed") (tags := "T4")
For a two-colour cyclic tag system `C0`, an initial configuration `cfg` and a
budget `N` such that the run of `C0` from `cfg` lasts the
`C0.appendants.length * N` steps of the budget and ends in a configuration `c'`
whose word is nonempty, write `s = ctsToSystem5 C0 cfg N`
({uses "BiTM.ctsToSystem5"}[]), `start = icStart s` ({uses "Smith.icStart"}[], a
wolfram23 configuration, {uses "BiTM.Config"}[]), `w = icW s` and `b = icBand s`.
There are times `times i` and an exit time `T` such that:

- `start` is valid ({uses "BiTM.IsValidWolfram23Cfg"}[]) and in state A
  (`start.state = 1`);
- the times are strictly increasing on `[0, C0.appendants.length * N]` and at
  most `T`;
- at time `times i` the run of wolfram23 ({uses "BiTM.wolfram23"}[],
  {uses "BiTM.nSteps"}[]) from `start` is defined, and its configuration decodes
  by {uses "Smith.decodeW23"}[] with the parameters `2 ^ w` and `b` to
  `some (dbl ci.data)`, the doubled working string ({uses "Smith.dbl"}[]) of the
  `i`-th configuration `ci` of the cyclic tag run;
- for every time `τ ≤ T` the run is defined and `biSize` ({uses "Smith.biSize"}[])
  of its configuration equals `biSize start`;
- at time `T + 1` the configuration is `⟨1, L, 0, []⟩` with
  `L.length = biSize start`: state A, the `biSize start` cells of the tape to
  the left of the head, the head on a 0, and no explicit cell to its right.
:::

:::theorem "Smith.conjecture0_finite" (parent := "t4_conjecture0") (lean := "Smith.conjecture0_finite") (tags := "T4")
The same with `start`, `w` and `b` existential: for `C0`, `cfg`, `N` and `c'` as
in {uses "Smith.conjecture0_closed"}[] there are a wolfram23 configuration
`start`, a block width `2 ^ w`, a band `b`, times and an exit time with the
five clauses of that theorem.
:::

:::proof "Smith.conjecture0_finite"
{uses "Smith.conjecture0_closed"}[] with `start = icStart s`, `w = icW s`,
`b = icBand s`.
:::

The budget is `N` cycles of the appendants; the cyclic tag run must last the
`appendants.length * N` steps of the budget and leave a nonempty word (`hne`).
The decoder returns the doubled working string `dbl ci.data` (the chapter on
{ref "cts-to-system5"}[cyclic tag to System 5]); the chapter on
{ref "universality"}[the composition] undoubles it.

# The pieces

The links of the earlier chapters are composed with the following additions.

:::definition "Smith.Bound5" (parent := "t4_conjecture0") (lean := "Smith.Bound5")
`Bound5 s B`: every integer of the System 5 configuration `s`, in the bag and
in every rule, is at most `B`.
:::

:::lemma_ "Smith.Bound5_nSteps" (parent := "t4_conjecture0") (lean := "Smith.Bound5_nSteps")
The integers of a System 5 configuration grow by at most one per step: if
`Bound5 s B` holds and `j` steps of System 5 ({uses "BiTM.System5.step"}[]) from
`s` reach `s'`, then `Bound5 s' (B + j)`. This bounds the terminal decrements and
the band.
:::

:::proof "Smith.Bound5_nSteps"
Induction on `j` with the one-step case `Bound5_step`: a step subtracts one from
every bag element and adds one to every rule integer, and the pop merges the
first rule into the bag by `xorMerge` ({uses "BiTM.xorMerge"}[]), whose members
all come from one of its two arguments ({uses "BiTM.xorMerge_mem_or"}[]). A bound
`B` for the program itself is `exists_Bound5`, from `exists_int_bound`.
:::

:::lemma_ "BiTM.xorMerge_mem_or" (parent := "t4_conjecture0") (lean := "BiTM.xorMerge_mem_or")
Every member of `xorMerge xs ys` ({uses "BiTM.xorMerge"}[]) is a member of `xs` or
of `ys`.
:::

:::proof "BiTM.xorMerge_mem_or"
Induction on `ys`: inserting `y` by `xorInsert` adds or removes `y` and leaves
the membership of every other integer unchanged (`xorInsert_mem_other_iff`).
:::

{bpref "Smith.conjecture5_finite_exact"}[`Smith.conjecture5_finite_exact`] (the chapter on cyclic tag to System 5) gives an
empty rule list at the end of the budget, which the exit of the terminal phase of
T2 needs. {bpref "Smith.repS4_terminal"}[`Smith.repS4_terminal`] (the chapter on System 5 to System 4, proved in
[`Smith/Conjecture0.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Conjecture0.lean)): with the rules exhausted, System 4 decrements
({bpref "Smith.repS4_dStep"}[`Smith.repS4_dStep`]) until 1 is in the bag, then exits in state C
({bpref "Smith.repS4_exit"}[`Smith.repS4_exit`]), by induction on a bound of a bag element: if some bag
element is at most `M + 1`, at most `M` decrements happen before the exit.

:::lemma_ "Smith.RepS4_decode_band" (parent := "t4_conjecture0") (lean := "Smith.RepS4_decode_band")
The decoder of the System 5 to System 4 chapter ({uses "Smith.decodeS4"}[],
{uses "Smith.RepS4_decode"}[]) below any fixed band: if `c` stands in `RepS4`
({uses "Smith.RepS4"}[]) to `s` with parameters `f`, `j`, `h`, and the band `b`
lies under the debris (`b + 2 * j + 2 ≤ 2 * f`) and holds every bag position
(`2 * e - 2 < b` for every `e` in the bag), then `decodeS4 c b` returns a
permutation of the bag of `s`.
:::

:::proof "Smith.RepS4_decode_band"
The parity clause of `RepS4` describes every position `x` with
`x + 2 * j + 2 < 2 * f`, so every position below `b`: `x` is in the parity set of
the leading sets exactly when `x = 2 * e - 2` for a bag element `e`. All these
positions are even, `x / 2 + 1` recovers `e`, and the positions below `b` are
all of them by the second hypothesis; the bag has no duplicates, so the list the
decoder returns is a permutation of it.
:::

:::lemma_ "Smith.system5ToSystem4_wellFormed" (parent := "t4_conjecture0") (lean := "Smith.system5ToSystem4_wellFormed")
For `1 ≤ f` the encoder tape `system5ToSystem4 s f`
({uses "BiTM.system5ToSystem4"}[]) is well formed
({uses "BiTM.System4Config.WellFormed"}[]): its first element is not a star, no
two stars are adjacent, and no set has duplicates. This is one of the three
facts about the encoder tape that {uses "Smith.rep3_init"}[] needs.
:::

:::proof "Smith.system5ToSystem4_wellFormed"
The tape is the set `encodeBag s.bag` ({uses "BiTM.encodeBag"}[]), then the
starred empty pairs `starredEmptyPairs f`, then the encoding of each rule
(`encodeS5RuleToS4Elems`); each piece has no adjacent stars, the seams are a set
followed by a star or a set, and the sets are `encodeBag`, an `encRuleSet`, an
`allInts` block or empty, none with duplicates.
:::

:::lemma_ "Smith.system5ToSystem4_last_set" (parent := "t4_conjecture0") (lean := "Smith.system5ToSystem4_last_set")
For `1 ≤ f` the last element of the encoder tape `system5ToSystem4 s f`
({uses "BiTM.system5ToSystem4"}[]) is not a star. This is the second fact
{uses "Smith.rep3_init"}[] needs.
:::

:::proof "Smith.system5ToSystem4_last_set"
With no rules the tape ends with the last starred empty pair, whose last
element is a set; otherwise it ends with the encoding of the last rule, which
also ends with a set (`encodeS5RuleToS4Elems_getLast?`).
:::

:::lemma_ "Smith.system5ToSystem4_elem_lt" (parent := "t4_conjecture0") (lean := "Smith.system5ToSystem4_elem_lt")
If every bag entry of `s` lies in `[1, f)` and every rule entry in `[0, f)`,
then every integer `e` of every set of the encoder tape `system5ToSystem4 s f`
({uses "BiTM.system5ToSystem4"}[]) satisfies `0 ≤ e` and `e.toNat < 3 * f + 3`.
This is the third fact {uses "Smith.rep3_init"}[] needs: with `3 * f + 3 ≤ 2 ^ w`
every set integer lies below the block width.
:::

:::proof "Smith.system5ToSystem4_elem_lt"
Case analysis on the piece of the tape the set comes from: the bag set is an
`xorMerge` of shifted bag entries ({uses "BiTM.xorMerge_mem_or"}[]), the rule sets
are `xorMerge`s of an `allInts` block below `3 * f + 1` and shifted rule entries
(`rulePos`), and the empty pairs contribute nothing.
:::

:::lemma_ "Smith.rep3_exit" (parent := "t4_conjecture0") (lean := "Smith.rep3_exit")
At System 4's exit configuration (state C, head past the right end,
`active = elems.length`) the relation `Rep3 Closing.one` of the System 4 to
System 3 chapter ({uses "Smith.Rep3"}[], {uses "Smith.Closing"}[]) forces the
`off` focus, so the System 3 configuration is `⟨L, 1, [], C⟩`: the head on the
closing 1 in state C, nothing to its right.
:::

:::proof "Smith.rep3_exit"
Case analysis on the focus of the annotated configuration: with the focus on a
set or a star, `AC.to4` ({uses "Smith.AC.to4"}[]) puts the System 4 head inside
the tape, contradicting `active = elems.length`; the `off` focus gives state C
and the configuration in the shape claimed.
:::

After the relabelings the wolfram23 step from that configuration is
{bpref "Smith.wolfram23_exit_step"}[`Smith.wolfram23_exit_step`] (the chapter on the machine model): `B2 -> 0RA` onto
the implicit blank. This is Smith's exit condition, and it holds because
System 3's rule `C10 -> A00>` reads the implicit 0 as its right neighbour.

:::lemma_ "Smith.lnSteps_length" (parent := "t4_conjecture0") (lean := "Smith.lnSteps_length")
A run of any lookahead machine ({uses "Smith.LMachine"}[],
{uses "Smith.lnSteps"}[]) never changes the length of the tape: if `n` steps
from `c` reach `c'`, then `c'.toList.length = c.toList.length`. Systems 3 to 0
are lookahead machines, so the System 0 run of the theorem keeps its tape.
:::

:::proof "Smith.lnSteps_length"
Induction on `n` with the one-step case `lstep_length`.
:::

# The decoder

:::definition "Smith.decodeW23" (parent := "t4_conjecture0") (lean := "Smith.decodeW23")
`decodeW23 N b cfg`, for a wolfram23 configuration `cfg` ({uses "BiTM.Config"}[]):
the head cell and the cells right of it up to the first 0 are handed to
{uses "Smith.decodeBlocks"}[] with the block width `N` and the band `b`, and the
bag it returns is read by {uses "Smith.decodeBag"}[] as a working string.
:::

The head cell and the cells right of it up to the first 0 are the blocks of the
leading conglomerate (the star after the leading sets is a 0 standing in for the
first cell of the next set, so the run of nonzero cells is exactly `|K| * N`
long).

:::definition "Smith.decodeBlocks" (parent := "t4_conjecture0") (lean := "Smith.decodeBlocks")
`decodeBlocks N b cells` checks that the cells are 1s and 2s making up at least
one whole block of width `N`, XORs the blocks ({uses "Smith.xorBlocks"}[], on
the cells read as bits with 2 for true), takes the parity set of the XOR below
`b` ({uses "Smith.parAt"}[]), and reads it as the decoder of the System 5 to
System 4 chapter does: `x / 2 + 1` on an even set, `none` otherwise.
:::

:::definition "Smith.xorBlocks" (parent := "t4_conjecture0") (lean := "Smith.xorBlocks")
`xorBlocks N k l`: the XOR of the first `k` blocks of width `N` of the bit list
`l`; the all-false block of width `N` for `k = 0`.
:::

:::lemma_ "Smith.parAt_blocks" (parent := "t4_conjecture0") (lean := "Smith.parAt_blocks")
For blocks of width `N`, each decoding ({uses "Smith.Decodes"}[]) to a set on
the positions below `k`, the parity set of their XOR at a position `i < k` is
the parity membership `parMem` of `i` in the sets.
:::

:::proof "Smith.parAt_blocks"
Induction on the list of blocks: `parAt` of an XOR of blocks of equal length is
the XOR of the `parAt`s ({uses "Smith.parAt_xor"}[]), and `Decodes` gives the
parity of one block at `i` as membership in its set.
:::

:::lemma_ "Smith.rep3_decode" (parent := "t4_conjecture0") (lean := "Smith.rep3_decode")
At a System 4 configuration with the head on an element in state B that leads a
block of sets `K` followed by a star, the configuration one step after every
scheduled time of T2, `decodeW23 (2 ^ w) b` of the wolfram23 configuration
`toBi (phi2 (phi3 c3))` ({uses "Smith.toBi"}[], {uses "Smith.phi2"}[],
{uses "Smith.phi3"}[]) of a System 3 configuration `c3` standing in `Rep3`
({uses "Smith.Rep3"}[]) to it, for any band `b ≤ h + 1`, agrees with
`decodeS4` ({uses "Smith.decodeS4"}[]) of the block followed by `decodeBag`
({uses "Smith.decodeBag"}[]); the cells left of the head play no part.
Moreover a 0 lies right of the head and the wolfram23 state is B.
:::

:::proof "Smith.rep3_decode"
The focus of the annotated configuration must be `setB` on the first set; the
rendered tape right of the head is the cells of the blocks of `K`
({uses "Smith.renderR"}[]), all 1s and 2s, then the 0 of the star, so the
`takeWhile` of `decodeW23` cuts exactly there. `decodeBlocks_of_blocks` with
{uses "Smith.parAt_blocks"}[] turns the parity set of the XOR into `parMem` on
the sets of `K`, which is what `decodeS4` computes on the leading sets.
:::

The decoding times are therefore the T2 times plus one System 4 step, carried
to System 0 by the T3 schedule.

# The run bounds

:::group "t4_run_bounds"
Closed-form bounds on every run of System 5 and of System 4, which replace the
run lengths of the emulation in the parameters of the initial condition.
:::

:::lemma_ "Smith.System4.run_bound" (parent := "t4_run_bounds") (lean := "Smith.System4.run_bound, Smith.phi4, Smith.phi4_step")
System 4 always halts: a run of `n` steps from a configuration whose tape has
`L` elements has `n <= (2 L + 2) (L + 1)`.
:::

:::proof "Smith.System4.run_bound"
In state A the head moves left, in states B and C right. A leftward run ends
at a star (rule 2 deletes it) or at the left end (rule 1 turns round); a
rightward run ends at a star in state B (rule 4 deletes it) or at the right
end. So the phase `phase4`, twice the number of stars plus one in state A,
never increases and drops at every change of direction, and within a phase the
head moves monotonically; the offset `off4` is the head position while it
moves left and its distance to the right end while it moves right. The measure
`phi4 K c = phase4 c * K + off4 K c`, for `K` above the tape length, drops by
at least one at every step and never lets the tape grow (`phi4_step`, by
cases on the rules of {uses "BiTM.System4.step"}[]); it starts below
`(2 L + 2) (L + 1)`.
:::

:::lemma_ "Smith.System5.run_bound" (parent := "t4_run_bounds") (lean := "Smith.System5.run_bound, Smith.Inv5, Smith.maxInt5, Smith.Bound5_maxInt5")
System 5 halts from configurations whose bag is duplicate-free with positive
elements and whose rule entries are non-negative (`Inv5`, kept by every step
and true of the encoder's output, `Inv5_ctsToSystem5`): with `R` rules and
every integer at most `B` ({uses "Smith.Bound5"}[]), a run has at most
`B * 2 ^ R` steps. `maxInt5 s`, the largest integer of the program, is such a
`B`.
:::

:::proof "Smith.System5.run_bound"
Every step either pops a rule (a P-step) or decrements the bag and increments
the rules (a D-step) (`step5_cases`); a step raises the largest integer by at
most one (`Bound5_step`, as in {uses "Smith.Bound5_nSteps"}[]), and an empty bag
or an empty rule list halts. With every integer at most `B` the bag has an
element at most `B`, which forces a P-step within `B` steps (`run5_phase`, by
induction on `v` for an element at most `v`); after it one rule fewer is left
and every integer is at most `2 B`. Induction on the number of rules
(`run5_bound`) gives the bound `G5 B R`, with `G5 B (R + 1) = B + G5 (2 B) R`,
which is `B (2^R - 1)` (`G5_eq`).
:::

# The closed-form initial condition

:::definition "Smith.icStart" (parent := "t4_conjecture0") (lean := "Smith.icStart, Smith.icB, Smith.icT5, Smith.icM, Smith.icH, Smith.icF, Smith.icBand, Smith.icRest, Smith.icLen4, Smith.icT4, Smith.icFuel, Smith.icW")
The initial condition of T4 for a System 5 program `s`, computed from the text
of `s` alone: the parameters `icB` to `icW` of the table in the proof of
{uses "Smith.conjecture0_closed"}[], then the System 3 rendering
`initAC (icW s) (icFuel s) _ _` ({uses "Smith.initAC"}[]) of the System 4 tape
`system5ToSystem4 s (icF s)` ({uses "BiTM.system5ToSystem4"}[]), relabeled to
System 0 (`phi2 (phi3 _)`, {uses "Smith.phi2"}[], {uses "Smith.phi3"}[]) and read
as a wolfram23 configuration ({uses "Smith.toBi"}[]). No system is run: every
parameter is an arithmetic expression in `maxInt5 s`, the number of rules and
the length of the System 4 tape.
:::

# The System 4 emulation

:::proposition "Smith.system4_emulation" (parent := "t4_conjecture0") (lean := "Smith.system4_emulation")
The System 4 half of T4, shared with the infinite form. For `C0`, `cfg`, `N`
and `c'` as in the theorem and `s = ctsToSystem5 C0 cfg N`
({uses "BiTM.ctsToSystem5"}[]), there are an exit time `T4 <= icT4 s`
({uses "Smith.icStart"}[]) at which the System 4 run from the encoder tape
`system5ToSystem4 s (icF s)` ({uses "BiTM.system5ToSystem4"}[]) reaches a
configuration in state C with the head past the right end
(`active = elems.length`), and strictly increasing times `times i` with
`times i + 1 <= T4` such that one step after `times i` the System 4
configuration is `⟨sets K ++ star :: R, 0, B⟩` for a nonempty list of sets `K`
(the head on the first set in state B, a star after the leading conglomerate),
and `decodeS4` ({uses "Smith.decodeS4"}[]) of it below the band `icBand s`, read
by `decodeBag` ({uses "Smith.decodeBag"}[]), is the doubled working string
`dbl ci.data` ({uses "Smith.dbl"}[]) of the `i`-th cyclic tag configuration
`ci`. The encoder's facts with the parameter `icF s` (`1 <= icF s`, bag entries
in `[1, icF s)`, rule entries `k` with `k + 2 icH s < icF s`) are `icF_facts`.
:::

:::proof "Smith.system4_emulation"
The System 5 run of T1 exact ({uses "Smith.conjecture5_finite_exact"}[]) lasts
`t5 n` steps, at most `icT5 s` by {uses "Smith.System5.run_bound"}[]; every
inequality T2 ({uses "Smith.conjecture4_finite"}[]) and the terminal phase
({uses "Smith.repS4_terminal"}[]) put on their parameters holds for any value
at least the exact run length, so they hold with the bounds. At the end of the
budget the rule list is empty, and by {uses "Smith.Bound5_nSteps"}[] some bag
element is at most `icM s + 1`, which bounds the terminal decrements; the exit
time `T4 = t4 (t5 n) + k` is at most `icT4 s` by
{uses "Smith.System4.run_bound"}[]. At the T2 time `t4 (t5 i)` the tape stands
in `RepS4` ({uses "Smith.RepS4"}[]) with the head on the first set in state A;
one step (`step_setA_zero`) turns it to state B, and the star after the leading
sets is the first element of the starred empty pairs.
{uses "Smith.RepS4_decode_band"}[] reads the bag below the band and the
`Represents` relation of T1 ({uses "Smith.Represents"}[], `decodeBag_of_perm`)
reads the doubled working string off it.
:::

# The parameter choices, and what they mean

::::proof "Smith.conjecture0_closed"
The proof composes the finite forms by their schedules rather than by
`ForwardSim_comp` ({uses "Smith.ForwardSim_comp"}[]), because the fuel lives in
a different source system at each link. Write `n` for
`C0.appendants.length * N` and `s` for the System 5 program. Each parameter is
a closed form of `s` and of the ones before it; where the proof used to read
a run length off a schedule, it now uses a bound on it:

:::table +header
*
  * parameter
  * closed form
  * why
*
  * `icB s`
  * `maxInt5 s`, the largest integer of the program
  * a bound on the integers of the program ({uses "Smith.Bound5"}[], `Bound5_maxInt5`)
*
  * `icT5 s`
  * `icB s * 2 ^ s.rules.length`
  * above the System 5 run length `t5 n` ({uses "Smith.System5.run_bound"}[])
*
  * `icM s`
  * `icB s + icT5 s`
  * by {uses "Smith.Bound5_nSteps"}[] some bag element is at most `icM s + 1` at the end of the run, so at most `icM s` terminal decrements happen
*
  * `icH s`
  * `icT5 s + icM s + 1`
  * T2's budget: the run plus the terminal phase
*
  * `icF s`
  * `icB s + 2 * icH s + 2 * icT5 s + 5`
  * T2's bounds `e < f`, `k + 2 * H < f` and `2 * H < f` ({uses "Smith.conjecture4_finite"}[])
*
  * `icBand s`
  * `2 * icF s - 2 * icT5 s - 2`
  * the band lies under the debris for every `j ≤ t5 n` and above every bag position ({uses "Smith.RepS4_decode_band"}[])
*
  * `icT4 s`
  * `(2 L + 2) (L + 1)` for the length `L = icLen4 s` of `system5ToSystem4 s (icF s)`
  * above the System 4 exit time `T4` ({uses "Smith.System4.run_bound"}[])
*
  * `icFuel s`
  * `icT4 s + icBand s`
  * T3's fuel must cover the System 4 run and the band
*
  * `icW s`
  * `Nat.size (icFuel s + 3 * icF s + 6)`, the bit length
  * `x < 2 ^ Nat.size x` covers `h4 + 3 ≤ 2 ^ w` and `3 * f + 3 ≤ 2 ^ w` (every set element below the width); the block width `2 ^ w` is at most twice `h4 + 3 f + 6`, so the System 3 tape is linear, not exponential, in the System 4 data
:::

{uses "Smith.system4_emulation"}[] supplies the System 4 run, its exit at
`T4 <= icT4 s` and its decoding events.
The hypotheses of T3 ({uses "Smith.conjecture3_finite"}[]) on the encoder tape
are supplied by {uses "Smith.system5ToSystem4_wellFormed"}[],
{uses "Smith.system5ToSystem4_last_set"}[] and
{uses "Smith.system5ToSystem4_elem_lt"}[].

The tape `start` is `toBi` ({uses "Smith.toBi"}[]) of the relabeling
`phi2 (phi3 _)` ({uses "Smith.phi2"}[], {uses "Smith.phi3"}[]) of the System 3
tape `initAC w h4 _ _` ({uses "Smith.initAC"}[]) built from the encoder tape, which
is `icStart s` by definition; it is valid because its state is not C (`toBi_valid`, `phi2_state_ne_C`), and it is
in state A. With `times0` the T3 schedule, the decoding times are
`times0 (t4 (t5 i) + 1)`, one System 4 step after each T2 time; there
{uses "Smith.rep3_decode"}[] (through `rep3_decode_zero`) turns `decodeW23` into
`decodeS4` followed by `decodeBag`, and {uses "Smith.RepS4_decode_band"}[] with
the `Represents` relation of T1 ({uses "Smith.Represents"}[], `decodeBag_of_perm`)
gives the doubled working string. The exit time is `T = times0 T4`.

Confinement: the System 0 run ({uses "Smith.sys0"}[]) is defined at every time
up to `T` (`StepSys.nSteps_some_of_le`) and keeps its tape length
({uses "Smith.lnSteps_length"}[]); {uses "Smith.toBi_run"}[] carries it to the
wolfram23 run, and `biSize_toBi` turns the length into `biSize`. Exit: at `T4`
System 4 is at its exit configuration, so {uses "Smith.rep3_exit"}[] puts the
System 3 head on the closing 1 in state C; `phi_exit` relabels this to
`⟨L.map sw, 2, [], B⟩`, and the next wolfram23 step is
{uses "Smith.wolfram23_exit_step"}[] onto the implicit blank, which is the new
cell `0` right of the tape.
::::

The tape is thereby a definition of the program: the encoder does no
computation beyond writing down the encodings and evaluating these
expressions. This answers the Pratt-style objection the way Smith does (he
computes `f` and `w` from an a priori bound on the System 5 finish time,
`3^(n-1) M`, p. 20-21, and argues on p. 22-26 that the initial condition is
produced by an obviously non-universal algorithm). The bounds here are
coarser than Smith's (`B 2^R` for System 5, quadratic in the tape length for
System 4) but play the same role. The chapter on {ref "open-items"}[open
items] records this as item 1, done.

# Corrections to Smith's statement

- The head does not start on the leftmost cell of the tape but on the first cell
  of the first block, as in Smith's `s42s0-3.pl` output; the leftmost cell is a
  0, as the conjecture says, but the tape started on it in state A walks off its
  left end in three steps (the chapter on
  {ref "system4-to-system3"}[System 4 to System 3]). [`docs/PLAN.md`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/docs/PLAN.md) section 2 T4
  still says "started on its leftmost cell in state A" and must be corrected
  (the chapter on {ref "open-items"}[open items]).
- The run must be assumed to last the budget without emptying the word: an
  emptied word empties the System 5 bag, System 4 then sweeps forever and never
  exits.

# Notes and caveats

- "Never visits a cell outside the tape" is `biSize` constant, since a wolfram23
  step onto an implicit blank grows the explicit tape and the zipper run is
  defined ({bpref "Smith.lnSteps_length"}[`Smith.lnSteps_length`], {bpref "Smith.toBi_run"}[`Smith.toBi_run`]).
- The times `times` and `T` are existential (only the tape is in closed form),
  with no event in the wolfram23 run that marks them. Nothing is stated about `decodeW23` at other
  times; on the D9 test tape it returns `some` at several unscheduled times as
  well.
- The D9 vectors of [`Vectors/SmithVectors.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Vectors/SmithVectors.lean) exercise `decodeW23` on System 3
  tapes built by `initAC`, with negative instances (a state-A head, an odd parity
  position, a tape without whole blocks). No vector runs `conjecture0_closed` end
  to end; with `w = icW s` the block width of the smallest instance is far beyond
  `decide`. [`Vectors/ClosedFormVectors.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Vectors/ClosedFormVectors.lean) checks the run bounds against the exact run
  lengths on the programs of D1 and D4 and evaluates the closed-form parameters
  of D4.

# Depends on

The modules are [`Smith/Conjecture0.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Conjecture0.lean) (`Smith.Conjecture0`), which imports
`Smith.Conjecture3`, `Smith.ConjectureFive` and `Smith.Wolfram23Bridge`,
[`Smith/RunBounds.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/RunBounds.lean) (the run bounds) and [`Smith/ClosedForm.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/ClosedForm.lean) (the
closed-form initial condition, `system4_emulation` and the two statements). The
chapter depends on the four chapters from
{ref "cts-to-system5"}[cyclic tag to System 5] through
{ref "system5-to-system4"}[System 5 to System 4],
{ref "system4-to-system3"}[System 4 to System 3] and
{ref "systems-3-2-1-0"}[Systems 3, 2, 1 and 0], whose finite forms and relations
it composes, and on the {ref "machine-model"}[machine model] for the bridge from
System 0 to wolfram23.
