/-
  Blueprint.Chapters.Universality

  Chapter 9 of the blueprint: T8, the composition. The decoder of the
  headline theorem, how T7 (machine to cyclic tag) is composed with T4
  (cyclic tag to wolfram23) into the proof of `Smith.wolfram23_universal_ic`
  (whose statement the overview owns), the tag bounds and the closed-form
  initial condition `IC`, and which of the referee's objections the
  statement answers and which it leaves open.
-/

import Verso
import VersoManual
import VersoBlueprint
import Smith.Universality
import Blueprint.Chapters.Overview

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "T8: the composition" =>

%%%
tag := "universality"
file := "universality"
htmlSplit := .never
%%%

# Orientation

[`Smith/Universality.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Universality.lean) composes T7
({ref "tm-to-cts"}[the chapter on the machine reduction]) with T4
({ref "conjecture0"}[the chapter on Conjecture 0]) into
{bpref "Smith.wolfram23_universal_ic"}[`Smith.wolfram23_universal_ic`], stated in full in {ref "overview"}[the overview].
This chapter records how the composition is made, what the decoder is, how the
initial condition `IC tm c n` is written down without running anything, and
which of the referee's objections the statement answers and which it does not.

# The decoder

:::group "composition"
The decoder of T8 and the composition of T7 with T4 into the proof of the
headline theorem.
:::

:::definition "Smith.undbl" (parent := "composition") (lean := "Smith.undbl") (tags := "T8")
`undbl` takes a list of bits to an optional list of bits: the empty list to
`some []`, a one-element list to `none`, and `a :: b :: rest` to `undbl rest`
with `a` put in front when `a = b`, to `none` otherwise. It is the partial
inverse of the doubling {uses "Smith.dbl"}[]: it inverts `dbl` on doubled words
and returns `none` elsewhere.
:::

:::lemma_ "Smith.undbl_dbl" (parent := "composition") (lean := "Smith.undbl_dbl") (tags := "T8")
For every list of bits `w`, {uses "Smith.undbl"}[] of {uses "Smith.dbl"}[] `w`
is `some w`.
:::

:::proof "Smith.undbl_dbl"
Induction on `w`: `dbl (a :: w)` is `a :: a :: dbl w`, whose first two entries
agree, so `undbl` strips the pair and recurses.
:::

:::definition "Smith.decodeTM" (parent := "composition") (lean := "Smith.decodeTM") (tags := "T8")
`decodeTM S N b` takes a wolfram23 configuration to an optional machine
configuration, the composite of three decoders: {uses "Smith.decodeW23"}[] with
block width `N` and band `b` reads the doubled cyclic tag word off the wolfram23
tape ({ref "conjecture0"}[the chapter on Conjecture 0]); {uses "Smith.undbl"}[]
undoubles it; {uses "TagSystem.decodeCTS"}[] with `S` states reads the machine
configuration off the cyclic tag word, taken as a cyclic tag configuration with
phase 0 ({ref "tm-to-cts"}[the chapter on the machine reduction]), up to trailing
blanks. If any stage fails the result is `none`.
:::

`decodeTM S N b` is a fixed function of `(S, N, b)` and of the cells from the
head up to the first 0 to its right; it does not see the machine, the input or
the run.

# The tag bounds

:::group "tag_bounds"
The tag side of the closed-form initial condition: the Cocke-Minsky tag system
runs for ever, and its time for `n` machine steps has a closed-form bound
([`TagSystem/TagBounds.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/TagSystem/TagBounds.lean)).
:::

:::definition "TagSystem.rawRun" (parent := "tag_bounds") (lean := "TagSystem.rawStep, TagSystem.rawRun, TagSystem.roundLen, TagSystem.tagTime")
`rawStep tm c` is the step of the machine with the halting state 0 treated as an
ordinary state (row 0 of the table, which {uses "TagSystem.WF"}[] keeps in range);
`rawRun tm c n` is its `n`-th iterate. `roundLen tm c` is the number of tag steps
the Cocke-Minsky tag system takes for one raw step from `c` (the round lengths of
{uses "TagSystem.tm_step_tag"}[]), and `tagTime tm c n` their sum over the first `n`
raw steps.
:::

:::lemma_ "TagSystem.rawRun_eq" (parent := "tag_bounds") (lean := "TagSystem.rawRun_eq, TagSystem.step_eq_rawStep, TagSystem.rawRun_valid")
While the machine runs, the raw run is its run: if `BiTM.nSteps tm c n = some c'`
({uses "BiTM.nSteps"}[]) then `rawRun tm c n = c'` ({uses "TagSystem.rawRun"}[]). Raw
steps keep a configuration valid with its state in range.
:::

:::proof "TagSystem.rawRun_eq"
Outside state 0, {uses "BiTM.step"}[] is `some (rawStep tm c)` (`step_eq_rawStep`);
induction on `n`.
:::

:::lemma_ "TagSystem.tag_rawRun" (parent := "tag_bounds") (lean := "TagSystem.tag_rawRun, TagSystem.raw_step_tag, TagSystem.tag_run_total")
From the word of a valid configuration `c` with state in range, the tag system
{uses "TagSystem.tagK"}[] reaches, after `tagTime tm c n` steps
({uses "TagSystem.rawRun"}[]), the word ({uses "TagSystem.word"}[]) of `rawRun tm c n`. In
particular the tag run is defined for every number of steps (`tag_run_total`): it
does not stop when the machine halts.
:::

:::proof "TagSystem.tag_rawRun"
The round lemmas of {ref "tm-to-cts"}[the machine reduction] are stated for any
state; only {uses "TagSystem.tm_step_tag"}[] needs `q != 0`, to unfold
`BiTM.step`. `raw_step_tag` is the same composition of rounds for the raw step,
whatever the state, in `roundLen` tag steps; induction on `n`.
:::

:::lemma_ "TagSystem.tagTime_le" (parent := "tag_bounds") (lean := "TagSystem.tagTime_le, TagSystem.roundLen_le, TagSystem.sz")
For a valid configuration `c` with state in range, with `sz c` the number of
explicit tape cells, `tagTime tm c n <= n * 15 * 2 ^ (sz c + n)`.
:::

:::proof "TagSystem.tagTime_le"
A round costs at most five passes over the tag word, whose halves are the numbers
`val left` and `head + 2 val right`, below `2 ^ sz c` and `2 ^ (sz c + 1)`
(`val_lt_two_pow`), so `roundLen c <= 15 * 2 ^ sz c`; a raw step grows the tape by
at most one cell (`sz_rawStep`), so the `i`-th raw configuration has
`sz <= sz c + i`; sum over `i < n`.
:::

# The closed-form initial condition

:::definition "Smith.IC" (parent := "composition") (lean := "Smith.IC, Smith.ICw, Smith.ICb, Smith.icN, Smith.icProg, Smith.ctsOf") (tags := "T8")
`ctsOf tm` is the cyclic tag system {uses "TagSystem.tagToCTS"}[] of the tag system
{uses "TagSystem.tagK"}[] `tm S` of T7, with `S = tm.numStates`. The budget is
`icN c n = n * 15 * 2 ^ (sz c + n)` cycles, the bound of
{uses "TagSystem.tagTime_le"}[]; `icProg tm c n` is the System 5 program
{uses "BiTM.ctsToSystem5"}[] `(ctsOf tm) (ctsOfCfg S c) (icN c n)`. The initial
condition is `IC tm c n = icStart (icProg tm c n)` ({uses "Smith.icStart"}[]), with the
width exponent `ICw tm c n = icW (icProg tm c n)` and the band
`ICb tm c n = icBand (icProg tm c n)`. Every part is an encoder applied to `tm`, `c`
and `n`, or an arithmetic expression in the sizes of their outputs.
:::

# The composition

The statement of the headline theorem is in the overview; its proof is the
composition below.

:::proof "Smith.wolfram23_universal_ic"
Write `S` for `tm.numStates`, `K = 1 + 84 S`, `N = icN c n`, and `c_i` for the
`i`-th configuration of the run, `BiTM.nSteps tm c i = some c_i`.

The tag run from `word c` is defined for every number of steps
({uses "TagSystem.tag_rawRun"}[]). The cyclic tag system `ctsOf tm` has `2 K`
appendants ({uses "TagSystem.tagToCTS_appendants_length"}[]) and makes exactly one
cycle of them per tag step ({uses "TagSystem.cts_of_tag"}[]): after `2 K t` cyclic tag
steps from {uses "TagSystem.ctsOfCfg"}[] `S c` its configuration encodes the tag word at
time `t` (`cts_run_tag`). So the cyclic tag run lasts the budget of `N` cycles, and
its last word is nonempty because the tag run goes on one step further, which needs
a word of at least two symbols.

So T4 in closed form, {uses "Smith.conjecture0_closed"}[], applies to `ctsOf tm`,
`ctsOfCfg S c` and `N`; its tape `icStart (icProg tm c n)` is `IC tm c n`
({uses "Smith.IC"}[]) and its width and band are `ICw` and `ICb`. It returns a
schedule `times'` on the cyclic tag steps and the exit time `T`. The schedule of T8
is `times i = times' (2 K tagTime tm c i)`: `tagTime` is strictly increasing
(`tagTime_strictMono`) and `tagTime tm c i <= tagTime tm c n <= N`
({uses "TagSystem.tagTime_le"}[]), so the times are strictly increasing on `[0, n]` and
at most `T`.

At cyclic tag time `2 K tagTime tm c i` the tag word is `word (rawRun tm c i)`
({uses "TagSystem.tag_rawRun"}[]), and `rawRun tm c i = c_i`
({uses "TagSystem.rawRun_eq"}[]), so the cyclic tag configuration is `ctsOfCfg S c_i`.
The decoders compose: {uses "Smith.decodeW23"}[] returns {uses "Smith.dbl"}[] of its
data, `undbl` returns the data ({uses "Smith.undbl_dbl"}[]), and `decodeCTS` returns
`canon c_i` ({uses "TagSystem.decodeCTS_word"}[], for a valid configuration with state
below `S`, `rawRun_valid`). So {uses "Smith.decodeTM"}[] `S (2^w) b` of the wolfram23
configuration at time `times i` is `some (canon c_i)` ({uses "TagSystem.canon"}[]). The
validity of the start, its state A, the confinement clause and the exit clause are
those of `conjecture0_closed`, unchanged.

Before the closed form the proof went through the forward simulation
{uses "TagSystem.tm_tag_forwardSim"}[] unrolled by {uses "Smith.ForwardSim_nSteps"}[],
whose tag schedule is existential; the raw run replaces it because it gives the tag
time as a function (`tagTime`) with a bound, and because it keeps the tag run going
past the budget whatever the machine does.
:::

# What the statement answers, and what it leaves open

Answered by the statement as it stands:

- The decoder is fixed and position-relative, and it is a left inverse of the
  encoders only at the scheduled times by the theorem; it is not a table lookup
  into `tm` or `c`.
- The times are strictly increasing, the machine configurations are those of the
  given run (`BiTM.nSteps tm c i = some ci`), and confinement and exit are stated
  and proved.
- No axiom beyond `propext`, `Classical.choice`, `Quot.sound`; no `sorry`; no
  `native_decide` in the cone.

Left open by the statement (the independent review of 2026-09-21;
{ref "open-items"}[the chapter on open items]):

- One tape per machine, configuration and budget `n`. The standard notion of
  universality asks for one encoding of `(M, x)` independent of the running time;
  the infinite form ({ref "infinite-form"}[the chapter on the infinite form],
  {bpref "Smith.wolfram23_infinite_ic"}[`Smith.wolfram23_infinite_ic`]) gives it: one right-infinite tape
  `ITape tm c` per `(M, x)` with the whole run decodable.
- The precomputed-tape objection (the conclusion template alone is met by a
  machine that only moves right over a tape on which the configurations have been
  laid out in advance) is answered by the closed form: the tape is the definition
  `IC tm c n` (or `ITape tm c`), which writes down encodings of the machine's
  description and evaluates closed-form bounds, and never runs the machine or the
  emulating systems (the chapter on open items, item 1, done). No theorem bounds
  the size of the tape or the cost of computing it; it is exponential in `n` and
  in the size of `c`, through the budget `icN c n`, and the System 5 bound
  `icT5` is exponential again in the number of rules.
- Binary machines only.
- Decoding up to `canon`, at existential times, with nothing said about other
  times.
- The name `wolfram23_universal` claims more than the statement, as did the
  phrase "universality in the literal sense" of the M8 notes in [`docs/PLAN.md`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/docs/PLAN.md)
  (since removed; the chapter on open items, item 17). The docstring of the
  theorem in the module ([`Smith/Universality.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Universality.lean)) states the
  `n`-step form correctly.

# Notes and caveats

- No regression vector runs `decodeTM` on encoder output and gets a
  configuration back: with `ICw` the block width is far beyond
  `decide`, and a positive instance on a rendered tape needs the doubled
  encoding of a configuration word, at least `2 * 4 * (1 + 84 S)` bits, hence a
  block of width at least `2^13` for `S = 2`, whose rendering builds its parity
  rows by iteration. `undbl` is covered by `undbl_dbl` and by the vectors of
  [`Vectors/TMToCTSVectors.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Vectors/TMToCTSVectors.lean) (it inverts `dbl`, rejects an odd word and a word
  that is not doubled); `decodeW23` by the D9 vectors of
  [`Vectors/SmithVectors.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Vectors/SmithVectors.lean); `decodeCTS`, and the last two stages of `decodeTM`
  on the doubled encoding of a configuration, by [`Vectors/TMToCTSVectors.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Vectors/TMToCTSVectors.lean). On
  the D9 positive tape `decodeTM` returns `none` because the word there has odd
  length (one symbol); on the D10 tape it passes `undbl` with the word `0`, which
  `decodeCTS 2` rejects ([`Vectors/SmithVectors.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Vectors/SmithVectors.lean) D10). A hand-picked positive
  instance for `decodeTM` is still wanted; the chapter on open items (item 9)
  records it as out of reach of `decide` on a rendered tape.
- [`docs/PLAN.md`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/docs/PLAN.md)'s M8 row named the type `BiTM.Machine`; the type is
  {bpref "TM.Machine"}[`TM.Machine`] (the row has since been corrected; the chapter on open items,
  item 18).

# Depends on

This chapter depends on the modules `Smith.Universality` and `TagSystem.TagBounds`,
and through them on {ref "tm-to-cts"}[the chapter on the machine reduction] (T7:
{bpref "TagSystem.tm_step_tag"}[`TagSystem.tm_step_tag`], {bpref "TagSystem.cts_of_tag"}[`TagSystem.cts_of_tag`],
{bpref "TagSystem.decodeCTS_word"}[`TagSystem.decodeCTS_word`]) and {ref "conjecture0"}[the chapter on Conjecture 0]
(T4: {bpref "Smith.conjecture0_closed"}[`Smith.conjecture0_closed`], {bpref "Smith.icStart"}[`Smith.icStart`], {bpref "Smith.decodeW23"}[`Smith.decodeW23`]).
