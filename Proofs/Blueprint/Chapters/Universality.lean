/-
  Blueprint.Chapters.Universality

  Chapter 9 of the blueprint: T8, the composition. The decoder of the
  headline theorem, how T7 (machine to cyclic tag) is composed with T4
  (cyclic tag to wolfram23) into the proof of `Smith.wolfram23_universal`
  (whose statement the overview owns), and which of the referee's
  objections the statement answers and which it leaves open.
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
{bpref "Smith.wolfram23_universal"}[`Smith.wolfram23_universal`], stated in full in {ref "overview"}[the overview].
This chapter records how the composition is made, what the decoder is, and
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

# The composition

The statement of the headline theorem is in the overview; its proof is the
composition below.

:::proof "Smith.wolfram23_universal"
Write `S` for `tm.numStates` and `c_i` for the `i`-th configuration of the run,
`BiTM.nSteps tm c i = some c_i`.

The tag-level simulation of T7, {uses "TagSystem.tm_tag_forwardSim"}[],
unrolled over the `n` steps of the run by {uses "Smith.ForwardSim_nSteps"}[],
gives a strictly increasing tag-level schedule `tt`: after `tt i` steps the tag
system {uses "TagSystem.tagK"}[] `tm S` holds the encoded configuration word
`(word c_i).map (enc S)` ({uses "TagSystem.word"}[], {uses "TagSystem.enc"}[]),
and `c_i` is valid with state below `S`.

The cyclic tag system {uses "TagSystem.tagToCTS"}[] of T7 has `2 (1 + 84 S)`
appendants ({uses "TagSystem.tagToCTS_appendants_length"}[]) and makes exactly
one cycle of them per tag step ({uses "TagSystem.cts_of_tag"}[]): after
`2 (1 + 84 S) tt i` cyclic tag steps from {uses "TagSystem.ctsOfCfg"}[] `S c`
its configuration is `ctsOfCfg S c_i`.

So T4, {uses "Smith.conjecture0_finite"}[], is applied to this cyclic tag
system, the configuration `ctsOfCfg S c` and the budget of `tt n` cycles: the
cyclic tag run of `2 (1 + 84 S) tt n` steps is the one T4 requires, and its last
word is the encoding of the last configuration word, nonempty because a
configuration word has at least four symbols ({uses "TagSystem.length_word"}[]).
T4 returns the tape `start`, the width `w`, the band `b`, a schedule `times'` on
the cyclic tag steps and the exit time `T`. The schedule of T8 is
`times i = times' (2 (1 + 84 S) tt i)`: it is strictly increasing on `[0, n]`
because `tt` and `times'` are, and it is at most `T` because `tt i <= tt n`.

At cyclic tag time `2 (1 + 84 S) tt i` the cyclic tag configuration is
`ctsOfCfg S c_i`, and the decoders compose: {uses "Smith.decodeW23"}[] returns
{uses "Smith.dbl"}[] of its data, `undbl` returns the data
({uses "Smith.undbl_dbl"}[]), and `decodeCTS` returns `canon c_i`
({uses "TagSystem.decodeCTS_word"}[], for a valid configuration with state below
`S`). So {uses "Smith.decodeTM"}[] `S (2^w) b` of the wolfram23 configuration at
time `times i` is `some (canon c_i)` ({uses "TagSystem.canon"}[]). The validity
of `start`, its state A, the confinement clause and the exit clause are those of
`conjecture0_finite`, unchanged.
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

- One tape per machine, configuration and budget `n`, with the tape sized in the
  proof from the run lengths of the emulating systems
  ({ref "conjecture0"}[the chapter on Conjecture 0]). The standard notion of
  universality asks for one
  encoding of `(M, x)` independent of the running time. The conclusion template
  is satisfied by a machine that only moves right over a tape on which the
  `n + 1` configurations have been laid out in advance; what distinguishes
  wolfram23 is the proof term (Smith's encoders), not the statement. The infinite
  form ({ref "infinite-form"}[the chapter on the infinite form], proved:
  {bpref "Smith.wolfram23_infinite"}[`Smith.wolfram23_infinite`]) removes the budget: one right-infinite tape per
  `(M, x)` with the whole run decodable. It does not remove the precomputed-tape
  objection, which applies to it in the same way (an infinite tape can hold the
  whole run in advance); only a closed-form initial condition with a size bound
  would (the chapter on open items, item 1, open).
- Binary machines only.
- Decoding up to `canon`, at existential times, with nothing said about other
  times.
- The name `wolfram23_universal` claims more than the statement, as did the
  phrase "universality in the literal sense" of the M8 notes in [`docs/PLAN.md`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/docs/PLAN.md)
  (since removed; the chapter on open items, item 17). The docstring of the
  theorem in the module (lines 52-60 of [`Smith/Universality.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Universality.lean)) states the
  `n`-step form correctly.

# Notes and caveats

- No regression vector runs `decodeTM` on encoder output and gets a
  configuration back: with the proof's `w` the block width is far beyond
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

This chapter depends on the module `Smith.Universality`, and through it on
{ref "tm-to-cts"}[the chapter on the machine reduction] (T7:
{bpref "TagSystem.tm_tag_forwardSim"}[`TagSystem.tm_tag_forwardSim`], {bpref "TagSystem.cts_of_tag"}[`TagSystem.cts_of_tag`],
{bpref "TagSystem.decodeCTS_word"}[`TagSystem.decodeCTS_word`]) and {ref "conjecture0"}[the chapter on Conjecture 0]
(T4: {bpref "Smith.conjecture0_finite"}[`Smith.conjecture0_finite`], {bpref "Smith.decodeW23"}[`Smith.decodeW23`]).
