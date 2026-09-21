/-
  Blueprint.Chapters.System5ToSystem4

  Chapter 5 of the blueprint: T2, link C of the chain. The System 4 tape
  that `s52s4.pl` emits for a System 5 program emulates the System 5 run
  (Smith's "Conjecture 5 implies Conjecture 4"): the encoder, the relation
  `RepS4`, the run lemmas of the D-step and the P-step, the exit in state C,
  the decoder of the link, and the caveats (no finish-time bound, two
  unreachable branches of the step function).
-/

import Verso
import VersoManual
import VersoBlueprint
import BiTM.System4
import BiTM.System5ToSystem4
import Smith.System4Runs
import Smith.Conjecture4
import Smith.Conjecture0

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "T2: from System 5 to System 4" =>

%%%
tag := "system5-to-system4"
file := "system5-to-system4"
htmlSplit := .never
%%%

# Orientation

System 4 ([TM23Proof.pdf](https://www.wolframscience.com/prizes/tm23/TM23Proof.pdf) p. 16-18, `system4.pl` p. 33-35) is a tape of elements, each a
finite set of integers or a star, with a head and three states A, B and C. Five rules
({bpref "BiTM.System4.step"}[`BiTM.System4.step`]): in state A on a set the head moves left, turning round into
state B at the left end (rule 1); in state A on a star the star is deleted and the
state becomes B (rule 2); in state B or C on a set the set is decremented, the 0
removed and the state toggled if it was there, and the head moves right (rule 3); in
state B on a star the star is deleted and the head moves left into state A (rule 4);
in state C on a star the head moves onto the set to its right and toggles 1 in it
(rule 5). Smith's Conjecture 4 says a System 4 tape emulates a System 5 program. The
formal T2 is {bpref "Smith.conjecture4_finite"}[`Smith.conjecture4_finite`] in [`Smith/Conjecture4.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Conjecture4.lean), on top of the run
lemmas of [`Smith/System4Runs.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/System4Runs.lean).

:::group "t2_system5_to_system4"
T2, link C of the chain: the System 4 encoder `s52s4.pl`, the relation `RepS4` between
a System 4 tape and a System 5 configuration, the run lemmas, the exit in state C and
the decoder of the link.
:::

:::definition "BiTM.System4.step" (parent := "t2_system5_to_system4") (lean := "BiTM.System4.step")
One step of System 4 on a configuration, which is a list of elements (each a star or
a set of integers, held as a `List Int` read modulo 2 as in System 5), the index of
the active element and a state A, B or C: the five rules above, dispatched on the
state and on the kind of the active element. The result is `none` when the active
index is past the end of the tape (the halt) and in two branches that an encoder tape
never reaches (the notes below). `BiTM.System4.nSteps` iterates it.
:::

# The encoder and the relation

`BiTM.system5ToSystem4 s f` is `s52s4.pl`: the bag as one set of the even integers
`2e - 2` ({bpref "BiTM.encodeBag"}[`BiTM.encodeBag`]), then `f` pairs (star, empty set), then one block per
rule: star, the rule set `0..3f` toggled at `2k + f + 3` for each entry `k`, `2f`
pairs, star, the all-integers set `0..3f`, `2f - 2` pairs ({bpref "Smith.encBlock"}[`Smith.encBlock`],
{bpref "Smith.encRuleSet"}[`Smith.encRuleSet`], {bpref "Smith.rulePos"}[`Smith.rulePos`]). [`docs/REVIEW.md`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/docs/REVIEW.md) section 4.3 records two stars
the old transcription had dropped; {bpref "Smith.system5ToSystem4_eq"}[`Smith.system5ToSystem4_eq`] is the encoder as the
case `t = 0` of the parametrized blocks.

:::definition "BiTM.encodeBag" (parent := "t2_system5_to_system4") (lean := "BiTM.encodeBag")
The bag of a System 5 configuration as one System 4 set: each entry `e` is sent to
`2e - 2` and folded in with `BiTM.xorInsert`, so that an entry contributed twice
cancels, as the hash of `s52s4.pl` does. It is the {uses "BiTM.xorMerge"}[] of the
mapped bag into the empty set (`BiTM.encodeBag_eq_xorMerge`) and is `Nodup`
(`BiTM.encodeBag_nodup`).
:::

:::definition "Smith.rulePos" (parent := "t2_system5_to_system4") (lean := "Smith.rulePos")
`rulePos f t k = 2k + f + 3 - t`: the System 4 integer that stands for the System 5
rule entry `k` after `t` units of the running parameter of p. 17. A System 5 step
increases `k` by 1 while the tape integer is fixed, so `t` grows by 2 per step
(`Smith.rulePos_shift`).
:::

:::definition "Smith.encRuleSet" (parent := "t2_system5_to_system4") (lean := "Smith.encRuleSet")
The rule set of a rule block at parameter `t`: all of `0..3f` (`BiTM.allInts (3f + 1)`)
toggled, by {uses "BiTM.xorMerge"}[], at {uses "Smith.rulePos"}[] `f t k` for every
entry `k` of the rule.
:::

:::definition "Smith.encBlock" (parent := "t2_system5_to_system4") (lean := "Smith.encBlock, Smith.encBlocks")
One rule block at parameter `t`: a star, the set {uses "Smith.encRuleSet"}[] `r f t`,
`2f` star/empty pairs (`BiTM.starredEmptyPairs`), a star, the all-integers set
`0..3f`, and `2f - 2` star/empty pairs; `8f` elements for `f >= 1`. `Smith.encBlocks`
is the concatenation of the blocks of a rule list. One System 5 step adds 1 to every
rule entry and 2 to `t` and leaves the blocks unchanged (`Smith.encBlocks_shift`).
:::

:::definition "BiTM.system5ToSystem4" (parent := "t2_system5_to_system4") (lean := "BiTM.system5ToSystem4")
The encoder `s52s4.pl`, token for token with the Perl: state A, active index 0, and
the tape {uses "BiTM.encodeBag"}[] of the bag as one set, then `f` star/empty pairs,
then one block per rule (star, the rule set `0..3f` toggled at `2k + f + 3` for each
entry `k`, `2f` pairs, star, the all-integers set `0..3f`, `2f - 2` pairs). The two
stars that open the rule set and the all-integers set are the ones [`docs/REVIEW.md`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/docs/REVIEW.md)
section 4.3 found missing from the old transcription; without them the System 4 run
is observably different (the module header of [`BiTM/System5ToSystem4.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/BiTM/System5ToSystem4.lean)).
:::

:::lemma_ "Smith.system5ToSystem4_eq" (parent := "t2_system5_to_system4") (lean := "Smith.system5ToSystem4_eq")
{uses "BiTM.system5ToSystem4"}[] `s f` is the tape of the one-set block
`[encodeBag s.bag]`, then `f` star/empty pairs, then {uses "Smith.encBlock"}[] blocks
of `s.rules` at `t = 0`, with the head at 0 in state A: the encoder is the case `t = 0`
of the parametrized blocks.
:::

:::proof "Smith.system5ToSystem4_eq"
By unfolding. The per-rule encoder `BiTM.encodeS5RuleToS4Elems r f` is `encBlock r f 0`
because `2k + f + 3` is {uses "Smith.rulePos"}[] `f 0 k` (`Smith.encodeS5RuleToS4Elems_eq`).
:::

:::definition "Smith.parMem" (parent := "t2_system5_to_system4") (lean := "Smith.parMem")
Parity membership: `parMem x K` is true when `x` lies in an odd number of the sets of
the block `K`. This is membership in the symmetric difference of the block, Smith's
"one big merged set" of p. 16: in the conglomerate the parity counts, not the
individual sets. Decrementing every set of `K` (`Smith.decr`) shifts the parity set by
one (`Smith.parMem_map_decr`).
:::

:::definition "Smith.RepS4" (parent := "t2_system5_to_system4") (lean := "Smith.RepS4") (tags := "T2")
`RepS4 c s f j h` is Smith's "condition during execution" of p. 17 after `j` System 5
steps with `h` steps of budget left. There is a nonempty block `K` of sets, each
`Nodup` and made of nonnegative integers, such that:

- `c` is the tape `sets K`, then `f - 2j` star/empty pairs, then the rule blocks
  {uses "Smith.encBlock"}[] of `s.rules` at running parameter `t = 2j`, with the head
  at the left end in state A;
- `2j + 2h < f`;
- below the band: for every `x >= 0` with `x + 2j + 2 < 2f`, {uses "Smith.parMem"}[]
  `x K` agrees with "some `e` in the bag has `x = 2e - 2`";
- the bag is `Nodup` and every entry `e` has `1 <= e` and `e + j < f`;
- every rule is `Nodup` and every entry `k` has `0 <= k` and `k + j + 2h < f`.

The block `K` is the bag "conglomerate", whose symmetric difference is what counts.
The parity set of `K` agrees with the encoded bag below the band `2f - 2j - 2`; above
the band it is unconstrained, because the all-integers sets leave debris there that
never reaches the head within the budget. The budget bounds the rule entries so that
every integer popped into the bag stays under the band. The encoder tape
{uses "BiTM.system5ToSystem4"}[] `s f` stands in the relation at `j = 0` for every
budget `h` the bounds afford (`Smith.system5ToSystem4_repS4`).
:::

# The two step cases

[`Smith/System4Runs.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/System4Runs.lean) proves the runs. The focus lemmas state each rule on a tape
`L ++ e :: R` with the head on `e`, at index `L.length`.

:::lemma_ "Smith.step_setA" (parent := "t2_system5_to_system4") (lean := "Smith.step_setA")
Rule 1 away from the left end: on `L ++ set s :: R` with `L` nonempty, in state A, the
head moves to `L.length - 1` and stays in A ({uses "BiTM.System4.step"}[]). At the
left end the head turns round into state B (`Smith.step_setA_zero`).
:::

:::proof "Smith.step_setA"
Unfolding `System4.step` at index `L.length` of `L ++ set s :: R`: the rule for a set in state A moves left when the index is positive.
:::

:::lemma_ "Smith.step_starA" (parent := "t2_system5_to_system4") (lean := "Smith.step_starA")
Rule 2: on `L ++ star :: R` in state A the star is deleted and the head stays at
`L.length`, now on what was to the right of the star, in state B
({uses "BiTM.System4.step"}[]).
:::

:::proof "Smith.step_starA"
Unfolding `System4.step` at index `L.length` of `L ++ star :: R`: the rule for a star in state A erases it and enters state B.
:::

:::lemma_ "Smith.step_setB" (parent := "t2_system5_to_system4") (lean := "Smith.step_setB")
Rule 3 in state B: on `L ++ set s :: R` the set becomes `decrementSet s` (every
integer decremented, the 0 removed), the head moves to `L.length + 1`, and the state
is C if 0 was in `s` and B otherwise ({uses "BiTM.System4.step"}[]). `Smith.step_setC`
is the same in state C with B and C exchanged; `Smith.step_setBC` states both at once
with the flipped state.
:::

:::proof "Smith.step_setB"
Unfolding `System4.step` at index `L.length` of `L ++ set s :: R` in state B: the rule for a set decrements it, moves right, and toggles the state exactly when 0 was present.
:::

:::lemma_ "Smith.step_starB" (parent := "t2_system5_to_system4") (lean := "Smith.step_starB")
Rule 4: on `L ++ star :: R` with `L` nonempty, in state B, the star is deleted and the
head moves to `L.length - 1` in state A ({uses "BiTM.System4.step"}[]).
:::

:::proof "Smith.step_starB"
Unfolding `System4.step` at index `L.length` of `L ++ star :: R` in state B with `L` nonempty: the rule for a star in state B erases it, moves left and enters state A.
:::

:::lemma_ "Smith.step_starC" (parent := "t2_system5_to_system4") (lean := "Smith.step_starC")
Rule 5: on `L ++ star :: set s :: R` in state C the head moves to `L.length + 1`, onto
the set, which becomes `xorInsert 1 s`, and stays in C ({uses "BiTM.System4.step"}[]).
:::

:::proof "Smith.step_starC"
Unfolding `System4.step` at index `L.length` of `L ++ star :: set s :: R` in state C: the rule for a star in state C toggles 1 in the next set and moves onto it.
:::

On top of them, with an arbitrary context on both sides:

:::lemma_ "Smith.sweep" (parent := "t2_system5_to_system4") (lean := "Smith.sweep")
A sweep: on `L ++ sets K ++ R` with the head on the first set of `K`, in state B or C,
`K.length` steps take the head to the element after the block, with every set of `K`
decremented (`Smith.decr`) and the state flipped once per set that contained a 0,
that is, flipped by {uses "Smith.parMem"}[] `0 K`.
:::

:::proof "Smith.sweep"
Induction on `K`, one application of rule 3 ({uses "Smith.step_setB"}[], through
`Smith.step_setBC`) per set.
:::

:::lemma_ "Smith.moveLeft" (parent := "t2_system5_to_system4") (lean := "Smith.moveLeft")
In state A the head walks left across a block of adjacent sets: from index
`L.length + k` inside `sets K` (with `k < K.length`), `k` steps bring it to
`L.length`, still in state A.
:::

:::proof "Smith.moveLeft"
Induction on `K` with {uses "Smith.step_setA"}[].
:::

:::lemma_ "Smith.turn" (parent := "t2_system5_to_system4") (lean := "Smith.turn")
From the right end of the leftmost block `sets K` (nonempty), in state A, `K.length`
steps bring the head to the left end of the tape and turn it round into state B.
`Smith.turnFrom` starts from any position inside the block.
:::

:::proof "Smith.turn"
{uses "Smith.moveLeft"}[] to index 0, then rule 1 at the left end
(`Smith.step_setA_zero`).
:::

:::lemma_ "Smith.cPhase" (parent := "t2_system5_to_system4") (lean := "Smith.cPhase")
The C-phase: in state C the head runs through `g` star/empty pairs in `2g` steps,
toggling 1 into each empty set and decrementing it, so that every pair `* {}` becomes
`* {0}` (`Smith.starredZeroPairs`); the head ends after the last pair, still in state C.
:::

:::proof "Smith.cPhase"
Induction on `g`: {uses "Smith.step_starC"}[] toggles 1 into the empty set, and rule 3
in state C (`Smith.step_setC`) decrements it to `{0}` and moves on, the state
unchanged since the set held no 0.
:::

## The D-step

A System 5 step without a pop (1 not in the bag) is a D-step: two sweeps over the
conglomerate, one star removed and one empty set merged into it each time, `t` up by 2.

:::lemma_ "Smith.dStep" (parent := "t2_system5_to_system4") (lean := "Smith.dStep")
The D-step run (p. 17, "the bag didn't contain a 0"). From the tape `sets K0`, then
`g >= 2` star/empty pairs, then a rest `R'`, with the head at the left end in state A,
`K0` nonempty, and 0 in the parity set of neither `K0` nor its decrement,
`4 K0.length + 4` steps lead to the tape whose leftmost block is `K0` decremented
twice followed by two empty sets, then `g - 2` pairs, then `R'`, with the head at the
left end in state A: two stars are gone and their two empty sets have joined the
conglomerate.
:::

:::proof "Smith.dStep"
{uses "Smith.turn"}[] into state B, {uses "Smith.sweep"}[] the block (the state stays B
since {uses "Smith.parMem"}[] `0 K0` is false), delete the next star with
{uses "Smith.step_starB"}[], which merges the empty set behind it into the block, turn
again (`Smith.turnFrom`), sweep again, delete the next star, and walk back to the left
end ({uses "Smith.moveLeft"}[]).
:::

:::theorem "Smith.repS4_dStep" (parent := "t2_system5_to_system4") (lean := "Smith.repS4_dStep") (tags := "T2")
If {uses "Smith.RepS4"}[] `c s f j (h + 1)` holds and 1 is not in the bag of `s`, then
some `k >= 1` System 4 steps lead from `c` to a `c'` with `RepS4 c' s' f (j + 1) h`,
where `s'` is the System 5 step without a pop: the bag decremented and every rule
entry incremented.
:::

:::proof "Smith.repS4_dStep"
{uses "Smith.dStep"}[] with `K0` the conglomerate and `g = f - 2j >= 2`. The parity of
0 in `K0` is false by the band clause, since 1 is not in the bag; the parity of 0 in
the decremented block is that of 1 in `K0` (`Smith.parMem_map_decr`), which is odd and
so never `2e - 2`. The new conglomerate is `K0` decremented twice with two empty sets
appended; its parity set below the new band `2f - 2(j + 1) - 2` is the old one shifted
by 2, the encoding of the decremented bag; the pairs are `f - 2(j + 1)`; and the rule
blocks at `t = 2j` are the blocks of the incremented rules at `t = 2j + 2`
(`Smith.encBlocks_shift`). The bounds are arithmetic.
:::

## The P-step

A step with a pop is a P-step: the sweep leaves the conglomerate in state C, the head
crosses the pairs toggling 1s, enters the rule block, and two nested loops sweep the
rule set and the all-integers set back into the conglomerate; the XOR of the two
cancels everything except the entries of the rule at their shifted positions, which is
`xorMerge` of the rule into the bag. The relation is re-established with `j + 1`.

:::lemma_ "Smith.preLoop" (parent := "t2_system5_to_system4") (lean := "Smith.preLoop")
Macro A, the arrival at a rule block in state C (p. 17). With the head on a set `Z`
just left of `star :: set Rs :: (m star/empty pairs) ++ R'`, `m >= 2`, 0 in
`xorInsert 1 Rs` and 0 not in its decrement, 8 steps cross the star with a toggle of
1, decrement the set twice, delete the star on either side of it and merge one empty
set on the right: the tape becomes the block of four sets `Z`, `Rs` toggled at 1 and
decremented twice, and two empty sets, followed by `m - 2` pairs and `R'`, with the
head on the first empty set (one place left of the right end of the block) in state A.
:::

:::proof "Smith.preLoop"
Eight focus steps: rule 5 ({uses "Smith.step_starC"}[]), rule 3 in C on the toggled
set (`Smith.step_setC`, which flips to B because the 0 is there), rule 4 on the star
right of it ({uses "Smith.step_starB"}[]), rule 1 back onto the opening star
({uses "Smith.step_setA"}[]), rule 2 deleting it ({uses "Smith.step_starA"}[]), rule 3
in B on the set (no 0 now, {uses "Smith.step_setB"}[]) and on the empty set behind it,
and rule 4 on the next star.
:::

:::lemma_ "Smith.loopIter" (parent := "t2_system5_to_system4") (lean := "Smith.loopIter")
Macro B, one iteration of the loop (p. 17). The tape during the loop (`Smith.loopCfg`)
is a context `L0`, `n` star/`{0}` pairs, a star, a block `K` of at least two sets, `m`
star/empty pairs and a rest, with the head one place left of the right end of `K` in
state A. With `n >= 1`, `m >= 1` and 0 not in the parity set of `K`, `2 K.length + 1`
steps give the same shape with `n - 1` and `m - 1`, the block now `{0}`, then `K`
decremented, then an empty set.
:::

:::proof "Smith.loopIter"
Walk left over the block ({uses "Smith.moveLeft"}[]), rule 1 onto the star to its left
({uses "Smith.step_setA"}[]), rule 2 deleting it ({uses "Smith.step_starA"}[]), which
merges the `{0}` before it into the block, {uses "Smith.sweep"}[] the block in state B,
and rule 4 on the star to its right ({uses "Smith.step_starB"}[]), which merges the
empty set behind it.
:::

:::lemma_ "Smith.loopRun" (parent := "t2_system5_to_system4") (lean := "Smith.loopRun")
The loop, `n` iterations. The block during the loop is `Smith.loopK i R`: a `{0}`
merged from the padding, `i` empty sets, the set `R`, and `i + 2` empty sets. From the
loop shape with `n` star/`{0}` pairs, `n <= m`, and the block `loopK i R` such that
`R` decremented `i'` times contains 0 for every `i' < n`, some number of steps reaches
the loop shape with no `{0}` pairs left, the block `loopK (i + n)` of `R` decremented
`n` times, and `m - n` pairs.
:::

:::proof "Smith.loopRun"
Induction on `n` with {uses "Smith.loopIter"}[]; the parity of 0 in `loopK i R` is
membership of 0 in the current decrement of `R`.
:::

:::lemma_ "Smith.finalPass" (parent := "t2_system5_to_system4") (lean := "Smith.finalPass")
Macro C, the last pass of the loop (p. 17, "the last star is going to be removed to
its left"). From the loop shape with context `sets K0` (`K0` nonempty), no `{0}`
pairs, a block `K` of at least two sets with 0 not in its parity set, and `m >= 1`
pairs, `3 K.length + K0.length` steps merge the block with the leftmost block: the
tape is `sets (K0 ++ K decremented ++ [{}])`, then `m - 1` pairs, with the head at the
left end in state A.
:::

:::proof "Smith.finalPass"
As one loop iteration ({uses "Smith.moveLeft"}[], {uses "Smith.step_setA"}[],
{uses "Smith.step_starA"}[], {uses "Smith.sweep"}[], {uses "Smith.step_starB"}[]), but
the star deleted on the left was the last one between the two blocks, so they merge,
and the head then walks back to the left end of the tape.
:::

:::lemma_ "Smith.popPhase" (parent := "t2_system5_to_system4") (lean := "Smith.popPhase")
A pop phase (p. 17-18; both halves of the zero case have this shape). From the left
end in state A, with a 0 in the parity set of the nonempty conglomerate `K0`, then
`g >= 1` star/empty pairs, then `star :: set S`, then `m >= g + 2` pairs and a rest:
some `k >= 1` steps lead to the tape whose leftmost block is `K0` decremented, then
the loop block `loopK (g - 1)` of `S` toggled at 1 and decremented `g + 1` times, all
decremented once more, then an empty set, followed by `m - g - 2` pairs, with the head
at the left end in state A. The hypotheses ask that 0 be in `xorInsert 1 S`, not in
its first decrement, and in its decrements at each round of the loop and at the last
pass.
:::

:::proof "Smith.popPhase"
{uses "Smith.turn"}[] into B, {uses "Smith.sweep"}[] into C (the parity of 0 in `K0` is
true), the C-phase across the `g` pairs ({uses "Smith.cPhase"}[]), the pre-loop at the
block `* S` ({uses "Smith.preLoop"}[]), the loop `g - 1` times
({uses "Smith.loopRun"}[]), and the last pass ({uses "Smith.finalPass"}[]).
:::

:::theorem "Smith.repS4_pStep" (parent := "t2_system5_to_system4") (lean := "Smith.repS4_pStep") (tags := "T2")
If {uses "Smith.RepS4"}[] `c s f j (h + 1)` holds, the rules of `s` are `r :: rest` and
1 is in the bag, then some `k >= 1` System 4 steps lead from `c` to a `c'` with
`RepS4 c' s' f (j + 1) h`, where `s'` is the System 5 step with a pop: the bag
decremented with its 0 erased and the incremented rule `r` merged in by
{uses "BiTM.xorMerge"}[], and the rules `rest`, incremented.
:::

:::proof "Smith.repS4_pStep"
Two pop phases ({uses "Smith.popPhase"}[]), one at the rule set
{uses "Smith.encRuleSet"}[] `r f (2j)` and one at the all-integers set of the first
rule block {uses "Smith.encBlock"}[]. Below the band, the parity of the two merged
sets is the XOR of `0..3f` toggled at the shifted rule positions with `0..3f` itself,
which is the rule entries at their positions {uses "Smith.rulePos"}[]; merged into the
decremented conglomerate by {uses "Smith.parMem"}[] this is the `xorMerge` of the rule
into the bag. The `2f` and `2f - 2` pairs inside the block and the `f - 2j` pairs
before it supply the padding the two phases consume, leaving `f - 2(j + 1)` pairs;
the remaining blocks at `t = 2j` are the incremented rules at `t = 2j + 2`
(`Smith.encBlocks_shift`). The budget clause `k + j + 2h < f` on the rule entries keeps
every merged position under the new band.
:::

## The exit in state C

When the rules are exhausted and 1 is in the bag, the pop attempt finds no rule block:
the head sweeps the conglomerate in state C, crosses the remaining pairs, and leaves
the tape to the right in state C. This is the exit that the finite form of
Conjecture 0 needs ({ref "conjecture0"}[the chapter on Conjecture 0]).

:::theorem "Smith.repS4_exit" (parent := "t2_system5_to_system4") (lean := "Smith.repS4_exit") (tags := "T2")
If {uses "Smith.RepS4"}[] `c s f j h` holds with an empty rule list, 1 in the bag and
`j + 1 < f`, then after some `k` System 4 steps from `c` the configuration `c'` is in
state C with its active index equal to the length of its tape, and
{uses "BiTM.System4.step"}[] `c'` is `none`: the head has run off the right end of the
tape in state C, the exit condition of Conjecture 4 (p. 10 and p. 18).
:::

:::proof "Smith.repS4_exit"
With no rule block the tape is the conglomerate followed by `f - 2j` pairs. Rule 1 at
the left end turns the head into B; {uses "Smith.sweep"}[] crosses the conglomerate and
flips to C, since 1 in the bag puts 0 in the parity set; the C-phase
({uses "Smith.cPhase"}[]) crosses all the pairs, and the head stands past the end of
the tape, where the step is `none`.
:::

:::theorem "Smith.repS4_terminal" (parent := "t2_system5_to_system4") (lean := "Smith.repS4_terminal") (tags := "T2")
The exit without 1 in the bag yet (in [`Smith/Conjecture0.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Conjecture0.lean)). If
{uses "Smith.RepS4"}[] `c s f j (h + M)` holds with an empty rule list and some bag
entry at most `M + 1`, then after some `k` steps the configuration is in state C past
the right end of its tape with the step `none`, as in {uses "Smith.repS4_exit"}[].
:::

:::proof "Smith.repS4_terminal"
Induction on `M`. If 1 is in the bag, {uses "Smith.repS4_exit"}[] (the bag bound
`e + j < f` gives `j + 1 < f`). Otherwise one D-step ({uses "Smith.repS4_dStep"}[])
decrements the bag, the bounded entry drops to at most `M`, and the induction
hypothesis applies with one unit of budget less.
:::

# Formal statements

:::theorem "Smith.repS4_forwardSim" (parent := "t2_system5_to_system4") (lean := "Smith.repS4_forwardSim") (tags := "T2")
T2 as a {uses "Smith.ForwardSim"}[]: for every `f` and `h0`, the {uses "Smith.fueled"}[]
System 5 (one step of {uses "BiTM.System5.step"}[] per unit of fuel) is forward
simulated by System 4 under the relation that ties a fueled configuration `(s, n)` to
a System 4 configuration `c` when `n <= h0` and {uses "Smith.RepS4"}[]
`c s f (h0 - n) n`: the budget is the fuel, and the step count `j` of `RepS4` is the
fuel spent from `h0`.
:::

:::proof "Smith.repS4_forwardSim"
A fueled step with fuel `h + 1` is a System 5 step, which is `some` exactly when the
bag and the rule list are nonempty (`BiTM.System5_step_some_iff`). If 1 is in the bag
the step is the explicit pop (`BiTM.System5_step_explicit_pop`) and
{uses "Smith.repS4_pStep"}[] supplies the `k >= 1` System 4 steps; otherwise it is the
pure decrement (`BiTM.System5_step_pure_decrement`) and {uses "Smith.repS4_dStep"}[]
does.
:::

:::theorem "Smith.conjecture4_finite" (parent := "t2_system5_to_system4") (lean := "Smith.conjecture4_finite") (tags := "T2")
T2, the finite form of "Conjecture 5 implies Conjecture 4". For a System 5
configuration `s` with a `Nodup` bag of entries `1 <= e < f`, `Nodup` rules whose
entries satisfy `0 <= k` and `k + 2h < f`, and `2h < f`, and for a run of `n <= h`
System 5 steps from `s`, there are System 4 times `times 0 = 0 < times 1 < ... < times n`
at which the tape {uses "BiTM.system5ToSystem4"}[] `s f` stands in the relation
{uses "Smith.RepS4"}[] `_ si f i (h - i)` to the `i`-th System 5 configuration `si`.
:::

:::proof "Smith.conjecture4_finite"
{bpref "Smith.ForwardSim_nSteps"}[`Smith.ForwardSim_nSteps`] applied to {uses "Smith.repS4_forwardSim"}[] `f h`, from the
initial relation `Smith.system5ToSystem4_repS4` at fuel `h`, along the fueled run of
`n <= h` steps (`Smith.fueled_nSteps`).
:::

The decoder of the link reads the parity set of the leading conglomerate below a band
and maps `x` to `x / 2 + 1`, returning `none` if an odd integer is set.

:::definition "Smith.decodeS4" (parent := "t2_system5_to_system4") (lean := "Smith.decodeS4, Smith.leadSets") (tags := "T2, decoder")
`decodeS4 c b`: take the integers `0 <= x < b` in the parity set
({uses "Smith.parMem"}[]) of the leftmost block of adjacent sets of the tape
(`Smith.leadSets c.elems`); if they are all even, return them mapped through
`x / 2 + 1`, otherwise `none`.
:::

:::theorem "Smith.RepS4_decode" (parent := "t2_system5_to_system4") (lean := "Smith.RepS4_decode") (tags := "T2, decoder")
If {uses "Smith.RepS4"}[] `c s f j h` holds, then {uses "Smith.decodeS4"}[]
`c (2f - 2j - 2)` is `some l` with `l` a permutation of the bag of `s`: at a scheduled
time the decoder reads the System 5 bag, up to order.
:::

:::proof "Smith.RepS4_decode"
The leading block of the tape is the conglomerate `K` (`Smith.leadSets_sets`, since the
element after it is a star). Below the band the parity clause of the relation says the
parity set is exactly the `2e - 2` for `e` in the bag, all even and below the band by
the bag bound; `x / 2 + 1` inverts `e` to `2e - 2`, and the bag is `Nodup`, so the
result lists the bag in some order.
:::

{bpref "Smith.conjecture4_cts"}[`Smith.conjecture4_cts`] and {bpref "Smith.conjecture4_cts_exists_f"}[`Smith.conjecture4_cts_exists_f`] compose T1 and T2: the
System 4 tape of the `cy2s5.pl` output tracks the cyclic tag run for every large
enough `f`.

:::theorem "Smith.conjecture4_cts" (parent := "t2_system5_to_system4") (lean := "Smith.conjecture4_cts") (tags := "T1, T2")
Links B and C composed. For a cyclic tag system `C0`, a configuration `cfg`, a period
count `N`, and a run of `n <= C0.appendants.length * N` steps of `C0` from `cfg`,
there is an `L` (the number of System 5 steps the run takes) such that for every `f`
above every bag entry of {uses "BiTM.ctsToSystem5"}[] `C0 cfg N`, with `k + 2L < f` for
every rule entry `k` and `2L < f`, there are strictly increasing System 4 times from
`times 0 = 0` at which, for `i <= n`: the `i`-th cyclic tag configuration `ci` exists;
some `m` System 5 steps reach an `si` that {uses "Smith.Represents"}[] the doubled
configuration `dblCfg ci` of {uses "Smith.double"}[] `C0` with the remaining
budget `2 (C0.appendants.length * N - i)`; and the tape
{uses "BiTM.system5ToSystem4"}[] `(ctsToSystem5 C0 cfg N) f` after `times i` steps
stands in {uses "Smith.RepS4"}[] `_ si f m (L - m)`.
:::

:::proof "Smith.conjecture4_cts"
{uses "Smith.conjecture5_finite"}[] gives the System 5 schedule `t5` and the
representation; `L` is `t5 n`. The bag entries of `ctsToSystem5` are at least 1 and
the rule entries at least 3 and `Nodup` (`BiTM.ctsToSystem5_bag_ge_one`,
`BiTM.ctsToSystem5_rules_ge_three`, `BiTM.ctsToSystem5_rules_nodup`), so
{uses "Smith.conjecture4_finite"}[] applies with budget `L` and gives the System 4
schedule `t4`; the composed times are `t4 (t5 i)`, strictly increasing since both
schedules are (`Smith.strictMono_of_succ`).
:::

:::theorem "Smith.conjecture4_cts_exists_f" (parent := "t2_system5_to_system4") (lean := "Smith.conjecture4_cts_exists_f") (tags := "T1, T2")
The parameter `f` can always be chosen: under the hypotheses of
{uses "Smith.conjecture4_cts"}[] there are `L` and `f0` such that every `f >= f0`
admits the schedule and the relations of that theorem.
:::

:::proof "Smith.conjecture4_cts_exists_f"
Every list of integers is bounded (`Smith.exists_int_bound`); take `f0` above the
largest integer of the System 5 program plus twice the System 5 run length `L`, and
apply {uses "Smith.conjecture4_cts"}[].
:::

# Notes and caveats

The finish-time bound. Smith's T2 (p. 20-21) computes `f` from an a priori bound
`finishTime P <= 3^(n-1) M` on the System 5 run. That bound is not formalized:
{bpref "Smith.conjecture4_finite"}[`Smith.conjecture4_finite`] takes the System 5 run length `h` as its budget and
requires `k + 2h < f` on the rule entries and `2h < f`, a differently shaped
condition. [`docs/PLAN.md`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/docs/PLAN.md) section 2 still advertises `finishTime`; the M3 notes say it
is left undone. This is one of the ingredients of a closed-form initial condition
({ref "open-items"}[the chapter on open items]).

Two branches of {bpref "BiTM.System4.step"}[`BiTM.System4.step`] differ from `system4.pl`: rule 5 with the star
last returns `none` (the Perl autovivifies a set past the end), and rule 4 at index 0
returns `none` (the Perl reads the last element). Neither is reachable from an
encoder tape.

:::definition "BiTM.System4Config.WellFormed" (parent := "t2_system5_to_system4") (lean := "BiTM.System4Config.WellFormed")
A System 4 tape is well formed when its leftmost element is a set, no two stars are
adjacent, and every set is `Nodup`. `s52s4.pl` emits exactly such tapes; rule 5 of
{uses "BiTM.System4.step"}[] is only defined on them, and the parity reading of the
sets needs the `Nodup` clause. Every step preserves well-formedness
(`BiTM.System4_step_wellFormed`, `BiTM.System4_nSteps_wellFormed`): rules 1 and 3 do
not move stars, rules 2 and 4 delete a star whose two neighbours are not stars, rule 5
only rewrites a set, and a star is never deleted at index 0.
:::

Well-formedness rules out rule 4 at index 0, whose leftmost element would be a star.
Rule 5 with the star last needs, besides, that the last element of the tape is a set,
which holds of the encoder tape ({bpref "Smith.system5ToSystem4_last_set"}[`Smith.system5ToSystem4_last_set`], with
{bpref "Smith.system5ToSystem4_wellFormed"}[`Smith.system5ToSystem4_wellFormed`], in {ref "conjecture0"}[the chapter on Conjecture 0])
and which no rule disturbs, since no rule deletes a set.

The D4/D5/D7 vectors of [`Vectors/SmithVectors.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Vectors/SmithVectors.lean) run the p. 33 tape for 1904 System 4
steps and read the System 5 bag off it with {bpref "Smith.decodeS4"}[`Smith.decodeS4`] at the scheduled times,
with negative instances at unscheduled times.

# Depends on

The modules of this chapter are [`BiTM/System4.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/BiTM/System4.lean), [`BiTM/System5ToSystem4.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/BiTM/System5ToSystem4.lean),
[`Smith/System4Runs.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/System4Runs.lean) and [`Smith/Conjecture4.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Conjecture4.lean), with {bpref "Smith.repS4_terminal"}[`Smith.repS4_terminal`] in
[`Smith/Conjecture0.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Conjecture0.lean). The chapter builds on
{ref "cts-to-system5"}[the chapter on cyclic tag to System 5] for the simulation
calculus ({bpref "Smith.ForwardSim"}[`Smith.ForwardSim`], {bpref "Smith.fueled"}[`Smith.fueled`]), the System 5 step, {bpref "BiTM.xorMerge"}[`BiTM.xorMerge`] and,
for the composed statements, {bpref "Smith.conjecture5_finite"}[`Smith.conjecture5_finite`], {bpref "BiTM.ctsToSystem5"}[`BiTM.ctsToSystem5`] and
{bpref "Smith.Represents"}[`Smith.Represents`].
