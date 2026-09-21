/-
  Blueprint.Chapters.TMToCTS

  Chapter 3 of the blueprint: T7, from a binary Turing machine to a
  two-colour cyclic tag system with a decoder. A 2-tag system after Cocke
  and Minsky in a phase design of our own, carried onto a finite alphabet
  and then onto a cyclic tag system by Cook's encoding; the decoder; T7 in
  the finite form shared by every link; the caveats.
-/

import Verso
import VersoManual
import VersoBlueprint
import TagSystem.Basic
import TagSystem.TagRounds
import TagSystem.CockeMinsky
import TagSystem.TagToCTS
import TagSystem.TMToCTS
import Smith.Simulation
import BiTM.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "T7: from a binary Turing machine to a cyclic tag system" =>

%%%
tag := "tm-to-cts"
file := "tm-to-cts"
htmlSplit := .never
%%%

# Orientation

This link is independent of Smith's paper. It supplies what Smith's theorem
consumes: a two-colour cyclic tag system that simulates a given Turing machine,
with a decoder. It is a genuine construction, not an appeal to the literature: a
2-tag system after Cocke and Minsky (1964; Minsky 1967, section 14.6) in a phase
design of our own, carried onto a finite alphabet, then onto a cyclic tag system
by Cook's encoding (`TagSystem/TagToCTS.lean`, which predates the rebuild and is
used unchanged).

The class of machines is the binary machines: `TagSystem.WF` restricts the
transition table to bits and `TagSystem.ValidCfg` the tape to bits. A k-symbol
machine must be encoded in binary before this theorem applies; that reduction is
not formalized ({ref "open-items"}[the chapter on open items]).

# Rounds of a 2-tag system

:::group "t7_rounds"
A 2-tag system over any alphabet and its runs described by rounds
(`TagSystem/TagRounds.lean`, `TagSystem/Basic.lean`).
:::

`TagSystem/TagRounds.lean` treats a 2-tag system over any alphabet.

:::definition "TagSystem.stepP" (parent := "t7_rounds") (lean := "TagSystem.stepP")
The 2-tag step with productions `P`, on a word over any alphabet: read the first
symbol, delete the first two and append `P` of the symbol read. A word of fewer
than two symbols has no step.
:::

:::definition "TagSystem.nStepsP" (parent := "t7_rounds") (lean := "TagSystem.nStepsP")
`nStepsP P w n` iterates {uses "TagSystem.stepP"}[] `n` times from `w`; it is
`none` as soon as a step is undefined.
:::

:::definition "TagSystem.Tag.step" (parent := "t7_rounds") (lean := "TagSystem.Tag.step")
The step of a tag system `ts : Tag k` of `TagSystem/Basic.lean` on a word over
`Fin k`: read the first symbol, delete the first two, append `ts.productions` of
the symbol read.
:::

:::lemma_ "TagSystem.Tag.step_eq_stepP" (parent := "t7_rounds") (lean := "TagSystem.Tag.step_eq_stepP")
The step {uses "TagSystem.Tag.step"}[] is {uses "TagSystem.stepP"}[] with the
productions of the system: `ts.step w = stepP ts.productions w`.
:::

:::proof "TagSystem.Tag.step_eq_stepP"
By cases on the word: on fewer than two symbols both sides are `none`, and on
`a :: b :: rest` both are `some (rest ++ ts.productions a)`.
:::

A round processes the whole current word.

:::definition "TagSystem.passOut" (parent := "t7_rounds") (lean := "TagSystem.passOut")
`passOut P u` is the concatenation of the productions of every other symbol of
`u`, starting with the first.
:::

Two facts describe a round.

:::lemma_ "TagSystem.nStepsP_even" (parent := "t7_rounds") (lean := "TagSystem.nStepsP_even")
For a word `u` of even length `2 * n` and any pending tail `t`, `n` steps of
{uses "TagSystem.nStepsP"}[] take `u ++ t` to `t ++ passOut P u`
({uses "TagSystem.passOut"}[]): a word of even length is replaced by `passOut`
of it in half as many steps.
:::

:::proof "TagSystem.nStepsP_even"
Induction on `n`. Each step deletes one pair `a b` of `u` and appends `P a`,
which is the next block of `passOut P u`; the tail `t` is carried along in
front.
:::

:::lemma_ "TagSystem.nStepsP_odd" (parent := "t7_rounds") (lean := "TagSystem.nStepsP_odd")
For a word `u` of even length `2 * n` whose `passOut P u` is nonempty and a last
symbol `z`, `n + 1` steps of {uses "TagSystem.nStepsP"}[] take `u ++ [z]` to
`(passOut P (u ++ [z])).tail`: a word of odd length reads its last symbol
together with the first symbol of what was appended, so the result is
{uses "TagSystem.passOut"}[] of it without its first symbol.
:::

:::proof "TagSystem.nStepsP_odd"
The even round {uses "TagSystem.nStepsP_even"}[] on `u` with the pending tail
`[z]` leaves `z :: passOut P u` after `n` steps. One more step reads `z` and deletes with it
the first symbol of `passOut P u`, which exists by the hypothesis, and appends
`P z`; the result is `passOut P (u ++ [z])` without its first symbol.
:::

After an odd round the frame of the next round is shifted by one, and that round
reads the second of every pair. This one dropped symbol is the whole mechanism of
the construction. The computation lemmas give `passOut` on aligned pairs
(`TagSystem.passOut_pairs2`), on pairs read after a leading symbol
(`TagSystem.passOut_cons_pairs2`) and on runs of one symbol
(`TagSystem.passOut_cons_replicate_append`: a symbol, half the run rounded down,
then the rest read from its first or second symbol by the run's parity).

# The Cocke-Minsky construction

:::group "t7_cocke_minsky"
The 2-tag system that simulates a binary Turing machine, in three or five rounds
per machine step (`TagSystem/CockeMinsky.lean`).
:::

`TagSystem/CockeMinsky.lean`. The configuration `(q, left, head, right)` of the
machine is the word

```
A_q x (al_q x)^m B_q x (be_q x)^N,   m = val left,  N = head + 2 * val right,
```

with the scanned cell the lowest bit of the right number.

:::definition "TagSystem.Kind" (parent := "t7_cocke_minsky") (lean := "TagSystem.Kind")
The kinds of symbols, 21 of them: `A`, `al`, `B`, `be` of the configuration
word; `P1`, `P0`, `p`, `Q`, `r` after round 1; `E`, `e`, `F`, `f` after round 2;
`G`, `g`, `H`, `k` after round 3 of a move to the left; `I`, `i`, `J`, `j`
after round 4.
:::

:::definition "TagSystem.Sym" (parent := "t7_cocke_minsky") (lean := "TagSystem.Sym")
A symbol is the pad `x` (`none`; `TagSystem.X`) or a {uses "TagSystem.Kind"}[]
with a state and two bits: the scanned bit and the parity of the left number,
where the kind uses them.
:::

:::definition "TagSystem.val" (parent := "t7_cocke_minsky") (lean := "TagSystem.val")
A tape half read as a number, nearest cell least significant:
`val (a :: l) = a + 2 * val l`.
:::

:::definition "TagSystem.cword" (parent := "t7_cocke_minsky") (lean := "TagSystem.cword")
The configuration word of a state `q` and two numbers `m`, `N`:
`A_q x (al_q x)^m B_q x (be_q x)^N`, a word over {uses "TagSystem.Sym"}[] of
length `2 * (m + N + 2)` (`TagSystem.length_cword`).
:::

:::definition "TagSystem.word" (parent := "t7_cocke_minsky") (lean := "TagSystem.word")
The word of a configuration `c` ({uses "BiTM.Config"}[]) is
{uses "TagSystem.cword"}[] at the state of `c`, `m = val c.left` and
`N = c.head + 2 * val c.right` ({uses "TagSystem.val"}[]). The scanned cell is
the lowest bit of the right number.
:::

:::definition "TagSystem.ValidCfg" (parent := "t7_cocke_minsky") (lean := "TagSystem.ValidCfg")
A configuration ({uses "BiTM.Config"}[]) is valid when its tape holds bits: the
scanned cell is below 2 and so is every cell of the left and of the right half.
:::

:::lemma_ "TagSystem.length_word" (parent := "t7_cocke_minsky") (lean := "TagSystem.length_word")
The configuration word ({uses "TagSystem.word"}[]) has at least 4 symbols: the
tag system does not halt on it.
:::

:::proof "TagSystem.length_word"
The word is `A x ... B x ...`, of length `2 * (m + N + 2)`.
:::

One machine step is three or five rounds of the tag system.

:::definition "TagSystem.prod" (parent := "t7_cocke_minsky") (lean := "TagSystem.prod")
The productions of the tag system of a machine `tm` ({uses "TM.Machine"}[]) on
{uses "TagSystem.Sym"}[]: the pad produces nothing; `A -> P1 P0`, `al -> p p`,
`B -> Q`, `be -> r`; the round-2 productions split each symbol into a pair
indexed by the scanned bit (`P1 -> E1 E0`, `p -> e1 e0`, `Q -> F1 F0`,
`r -> f1 f0`, and `P0` produces nothing); the round-3 productions consult
`tm.transition` at `(q, h)` and write the next configuration word for a move to
the right, or `G`, `g`, `H`, `k` symbols for a move to the left; the round-4
productions split again by the parity of the left number; and the round-5
productions write the next configuration word. The production of the first
symbol read in round 3 (`E`) and in round 5 (`I`) carries a leading pad `x`
when the frame is shifted (`TagSystem.pad`).
:::

:::lemma_ "TagSystem.round1" (parent := "t7_cocke_minsky") (lean := "TagSystem.round1")
Round 1 (`A -> P1 P0`, `al -> p p`, `B -> Q`, `be -> r`): `m + N + 2` steps of
{uses "TagSystem.nStepsP"}[] with {uses "TagSystem.prod"}[] take
{uses "TagSystem.cword"}[] `q m N` to `P1 P0 (p p)^m Q r^N`, whose length
`2 * m + N + 3` has the parity of `N + 1`.
:::

:::proof "TagSystem.round1"
The even round {uses "TagSystem.nStepsP_even"}[] on the whole word, of even
length `2 * (m + N + 2)`, and the computation of {uses "TagSystem.passOut"}[]
on the aligned pairs.
:::

:::lemma_ "TagSystem.round2" (parent := "t7_cocke_minsky") (lean := "TagSystem.round2")
Round 2 reads `P1`, `m` of the `p`, `Q` and `N / 2` of the `r`: `m + N / 2 + 2`
steps take the word after {uses "TagSystem.round1"}[] to the pairs
`E1 E0 (e1 e0)^m F1 F0 (f1 f0)^(N / 2)` in the frame of `h = N mod 2`. When
`N` is even the round has odd length, its last read takes `E1` as its deleted
partner, and round 3 reads the second of every pair: every symbol read in round
3 knows the scanned bit `h`, and `N` has lost its lowest bit.
:::

:::proof "TagSystem.round2"
By the parity of `N`: {uses "TagSystem.nStepsP_odd"}[] (in its whole-word form
`TagSystem.nStepsP_odd'`) when `N` is even, the word having odd length
`2 * m + N + 3`, and {uses "TagSystem.nStepsP_even"}[] when `N` is odd; with
{uses "TagSystem.passOut"}[] on a run of `r` after a leading symbol
(`TagSystem.passOut_W1`).
:::

:::lemma_ "TagSystem.round3R" (parent := "t7_cocke_minsky") (lean := "TagSystem.round3R")
Round 3 executes the transition `(q, h) -> (q', w, d)`. For a move to the right
(`d = R`), `m + N / 2 + 2` steps take the word after {uses "TagSystem.round2"}[]
directly to the next configuration word
{uses "TagSystem.cword"}[] `q' (w + 2 * m) (N / 2)`, that is,
`A_q' x (al x)^(w + 2m) B x (be x)^(N/2)`.
:::

:::proof "TagSystem.round3R"
The pass {uses "TagSystem.passOut"}[] of the round-2 word is the next
configuration word, behind a leading pad when `h` is not set
(`TagSystem.passOut_W2` and the right-move productions of
{uses "TagSystem.prod"}[]). When `h` is set the word
has even length and the round is {uses "TagSystem.nStepsP_even"}[]; when it is
not, the word has odd length, the round is {uses "TagSystem.nStepsP_odd"}[]
(`TagSystem.nStepsP_odd'`), and the dropped first symbol is the pad.
:::

:::lemma_ "TagSystem.round3L" (parent := "t7_cocke_minsky") (lean := "TagSystem.round3L")
For a move to the left (`d = L`), `m + N / 2 + 2` steps take the word after
{uses "TagSystem.round2"}[] to `G g^m H H k^(4 (N/2))`.
:::

:::proof "TagSystem.round3L"
As for {uses "TagSystem.round3R"}[], with the left-move productions of
{uses "TagSystem.prod"}[]: {uses "TagSystem.passOut"}[] of the round-2 word is
`G g^m H H k^(4 (N/2))` behind a leading pad when `h` is not set, consumed by
the odd round ({uses "TagSystem.nStepsP_even"}[] or
{uses "TagSystem.nStepsP_odd"}[] by the parity of `h`).
:::

:::lemma_ "TagSystem.round4" (parent := "t7_cocke_minsky") (lean := "TagSystem.round4")
Round 4 halves `m` and reads its parity into the frame of round 5:
`m / 2 + 2 * (N / 2) + 2` steps take the word after {uses "TagSystem.round3L"}[]
to pairs `I1 I0 (i1 i0)^(m/2) J1 J0 (j1 j0)^(2 (N/2))` in the frame of
`b = m mod 2`.
:::

:::proof "TagSystem.round4"
By the parity of `m`, as in {uses "TagSystem.round2"}[]:
{uses "TagSystem.nStepsP_odd"}[] (`TagSystem.nStepsP_odd'`) when `m` is even
and {uses "TagSystem.nStepsP_even"}[] when it is odd, with
{uses "TagSystem.passOut"}[] on the two runs (`TagSystem.passOut_W3`).
:::

:::lemma_ "TagSystem.round5" (parent := "t7_cocke_minsky") (lean := "TagSystem.round5")
Round 5 writes the next configuration word of a move to the left:
`m / 2 + 2 * (N / 2) + 2` steps take the word after {uses "TagSystem.round4"}[]
to {uses "TagSystem.cword"}[] `q' (m / 2) (2 * w + b + 4 * (N / 2))`, that
is, `A_q' x (al x)^(m/2) B x (be x)^(2w + (m mod 2) + 4 (N/2))`.
:::

:::proof "TagSystem.round5"
As for {uses "TagSystem.round3R"}[]: {uses "TagSystem.passOut"}[] of the round-4
word is the next configuration word, behind a leading pad when `b` is not set
(`TagSystem.passOut_W4`); the round is {uses "TagSystem.nStepsP_even"}[] when
`b` is set and {uses "TagSystem.nStepsP_odd"}[] (`TagSystem.nStepsP_odd'`),
dropping the pad, when it is not.
:::

Whenever a round reads the second of each pair, the production of the first
symbol read carries a leading pad `x` that the odd round before it consumes, so
the tag word at the start of every machine step is exactly the configuration
word.

:::theorem "TagSystem.tm_step_tag" (parent := "t7_cocke_minsky") (lean := "TagSystem.tm_step_tag")
For a valid configuration `c` ({uses "TagSystem.ValidCfg"}[]) whose transition
writes a bit, and a step `c'` of the machine from `c` ({uses "BiTM.step"}[]),
there is a `k` with `1 <= k` such that `k` steps of {uses "TagSystem.nStepsP"}[]
with the productions {uses "TagSystem.prod"}[] take {uses "TagSystem.word"}[]
`c` to `word c'`.
:::

:::proof "TagSystem.tm_step_tag"
By cases on the direction of the transition. For a move to the right the rounds
{uses "TagSystem.round1"}[], {uses "TagSystem.round2"}[] and
{uses "TagSystem.round3R"}[] compose, with `k` the sum of their step counts
`m + N + 2`, `m + N / 2 + 2`, `m + N / 2 + 2`; for a move to the left the five
rounds {uses "TagSystem.round1"}[], {uses "TagSystem.round2"}[],
{uses "TagSystem.round3L"}[], {uses "TagSystem.round4"}[] and
{uses "TagSystem.round5"}[] compose, the last two of `m / 2 + 2 * (N / 2) + 2`
steps each. The scanned bit is `N mod 2` and the right number without it is
`val right`, since `c` is valid; the new configuration of
{uses "BiTM.step"}[] has the numbers the rounds produce (`TagSystem.step_R`,
`TagSystem.step_L`, `TagSystem.val_readHead`).
:::

The step counts are explicit in the proof. They grow with the numbers `m` and
`N`, that is, exponentially in the tape length. The construction was validated by
a Python simulation of random machines before it was proved.

# The finite alphabet and the cyclic tag system

:::group "t7_cts"
The tag system on the finite alphabet `Fin (1 + 84 * S)`, Cook's encoding into
a cyclic tag system, and the two forward simulations
(`TagSystem/TMToCTS.lean`, `TagSystem/TagToCTS.lean`).
:::

`TagSystem/TMToCTS.lean`.

:::definition "TagSystem.enc" (parent := "t7_cts") (lean := "TagSystem.enc")
`enc S` sends the symbols ({uses "TagSystem.Sym"}[]) whose state is below `S`
injectively into `Fin (1 + 84 * S)`: the pad to 0, a kind with a state and two
bits to `1 + ((kind index * S + state) * 4 + bits)`.
:::

:::definition "TagSystem.dec" (parent := "t7_cts") (lean := "TagSystem.dec")
`dec S` inverts {uses "TagSystem.enc"}[]: 0 is the pad, and any other index is
read back as a kind, a state below `S` and two bits.
:::

:::lemma_ "TagSystem.dec_enc" (parent := "t7_cts") (lean := "TagSystem.dec_enc")
For a kind, a state `q < S` and two bits, {uses "TagSystem.dec"}[] `S` after
{uses "TagSystem.enc"}[] `S` is the identity (and `TagSystem.dec_enc_X` for
the pad).
:::

:::proof "TagSystem.dec_enc"
Arithmetic on the index, which is below `1 + 84 * S` (`TagSystem.symIdx_lt`,
from the 21 kinds and the 4 bit patterns).
:::

:::definition "TagSystem.WordOK" (parent := "t7_cts") (lean := "TagSystem.WordOK")
`WordOK S w` says all states of the word `w` are below `S`
(`TagSystem.SymOK` on every symbol).
:::

:::lemma_ "TagSystem.prod_OK" (parent := "t7_cts") (lean := "TagSystem.prod_OK")
The productions {uses "TagSystem.prod"}[] preserve {uses "TagSystem.WordOK"}[]
`S` when the transitions do: if the next state from every state below `S` is
below `S`, then the production of a symbol with state below `S` is a word with
states below `S`.
:::

:::proof "TagSystem.prod_OK"
By cases on the kind of the symbol; every state in a production is the state of
the symbol or the next state of the transition.
:::

:::definition "TagSystem.tagK" (parent := "t7_cts") (lean := "TagSystem.tagK")
`tagK tm S` is the resulting `Tag (1 + 84 * S)`: the production of an index is
{uses "TagSystem.prod"}[] of its {uses "TagSystem.dec"}[], mapped by
{uses "TagSystem.enc"}[].
:::

:::lemma_ "TagSystem.nStepsP_enc" (parent := "t7_cts") (lean := "TagSystem.nStepsP_enc")
Runs are carried over: when the transitions keep the states below `S`, `k`
steps of {uses "TagSystem.nStepsP"}[] with the productions of
{uses "TagSystem.tagK"}[] `tm S` from the encoding of a word `w` with
{uses "TagSystem.WordOK"}[] `S` are the encoding of `k` steps with
{uses "TagSystem.prod"}[] from `w`.
:::

:::proof "TagSystem.nStepsP_enc"
Induction on `k`; one step commutes with the encoding (`TagSystem.stepP_enc`, by
{uses "TagSystem.dec_enc"}[] on the symbol read) and keeps `WordOK`
(`TagSystem.stepP_OK`, by {uses "TagSystem.prod_OK"}[]).
:::

Cook's encoding turns a tag system on `k` symbols into a cyclic tag system with
`2k` appendants.

:::definition "TagSystem.tagToCTS" (parent := "t7_cts") (lean := "TagSystem.tagToCTS")
The cyclic tag system of a tag system `ts` on `k > 0` symbols: symbol `i` is the
one-hot word of length `k` (`TagSystem.symbolEncode`; a tag word is the
concatenation, `TagSystem.tagWordEncode`), the first `k` appendants are the
encoded productions, the next `k` are empty (they consume the second deleted
symbol). `TagSystem.tagConfigToCTS` encodes a tag word as a cyclic tag
configuration at phase 0.
:::

:::lemma_ "TagSystem.tagToCTS_appendants_length" (parent := "t7_cts") (lean := "TagSystem.tagToCTS_appendants_length")
The cyclic tag system {uses "TagSystem.tagToCTS"}[] has exactly `2 * k`
appendants.
:::

:::proof "TagSystem.tagToCTS_appendants_length"
Two lists of length `k`.
:::

:::lemma_ "TagSystem.tagToCTS_simulation" (parent := "t7_cts") (lean := "TagSystem.tagToCTS_simulation")
One tag step is `2k` cyclic tag steps: if {uses "TagSystem.Tag.step"}[] takes
`cfg` to `cfg'`, then `2 * k` steps of {uses "TagSystem.tagToCTS"}[] take the
encoding of `cfg` to the encoding of `cfg'`.
:::

:::proof "TagSystem.tagToCTS_simulation"
The first `k` steps process the one-hot block of the first symbol `a`: its
single `true` fires appendant `a`, the encoded production. The next `k` steps
process the block of the second symbol `b`: its `true` fires appendant `k + b`,
which is empty. The phase returns to 0 modulo `2k`.
:::

:::lemma_ "TagSystem.cts_of_tag" (parent := "t7_cts") (lean := "TagSystem.cts_of_tag")
`k` tag steps are `2 * K * k` cyclic tag steps: for a tag system `ts` on
`K > 0` symbols, if `k` steps of {uses "TagSystem.nStepsP"}[] with
`ts.productions` take `w` to `w'`, then `2 * K * k` steps of
{uses "TagSystem.tagToCTS"}[] take the encoding of `w` to the encoding of `w'`.
:::

:::proof "TagSystem.cts_of_tag"
Induction on `k`, one step by {uses "TagSystem.tagToCTS_simulation"}[] through
{uses "TagSystem.Tag.step_eq_stepP"}[].
:::

:::definition "TagSystem.WF" (parent := "t7_cts") (lean := "TagSystem.WF")
A well-formed binary machine `tm` ({uses "TM.Machine"}[]): from every state
below `numStates` (the halt state 0 included), reading a bit, the machine writes
a bit and moves to a state below `numStates`. The predicate is decidable.
:::

:::lemma_ "TagSystem.step_valid" (parent := "t7_cts") (lean := "TagSystem.step_valid")
For a well-formed machine ({uses "TagSystem.WF"}[]), a step
({uses "BiTM.step"}[]) from a valid configuration ({uses "TagSystem.ValidCfg"}[])
with state below `numStates` is valid with state below `numStates`.
:::

:::proof "TagSystem.step_valid"
The written cell is a bit and the next state is below `numStates` by `WF`; the
cell moved onto is a cell of the tape or a blank.
:::

:::definition "TagSystem.ctsOfCfg" (parent := "t7_cts") (lean := "TagSystem.ctsOfCfg")
The encoding of a configuration as a cyclic tag configuration:
{uses "TagSystem.word"}[] `c`, mapped by {uses "TagSystem.enc"}[] `S`, encoded
as a cyclic tag configuration over `1 + 84 * S` symbols
(`TagSystem.tagConfigToCTS`).
:::

Both simulations are stated as forward simulations ({bpref "Smith.ForwardSim"}[],
the calculus of {ref "cts-to-system5"}[the chapter on cyclic tag to System 5])
between step systems ({bpref "Smith.StepSys"}[]): the machine is the step system
`TagSystem.tmSys tm` (its `nSteps` is `BiTM.nSteps`, `TagSystem.tmSys_nSteps`),
the cyclic tag system is `Smith.ctsSys` of it, and the tag system on the finite
alphabet is `TagSystem.tagSysK tm S`.

:::theorem "TagSystem.tm_cts_forwardSim" (parent := "t7_cts") (lean := "TagSystem.tm_cts_forwardSim")
For a well-formed machine `tm` ({uses "TagSystem.WF"}[]), the cyclic tag system
{uses "TagSystem.tagToCTS"}[] of {uses "TagSystem.tagK"}[] `tm tm.numStates`
forward-simulates ({uses "Smith.ForwardSim"}[]) the machine along the relation
"`c` is valid ({uses "TagSystem.ValidCfg"}[]), its state is below `numStates`,
and `d = ctsOfCfg tm.numStates c`" ({uses "TagSystem.ctsOfCfg"}[]).
:::

:::proof "TagSystem.tm_cts_forwardSim"
A step of the machine is `k >= 1` tag steps on `word c` by
{uses "TagSystem.tm_step_tag"}[] (the write is a bit by `WF`).
{uses "TagSystem.nStepsP_enc"}[] carries them onto the finite alphabet (the
states stay below `numStates` by `WF`, `TagSystem.WF_nxt`, and the configuration
word satisfies `WordOK`, `TagSystem.WordOK_cword`), and
{uses "TagSystem.cts_of_tag"}[] onto `2 * (1 + 84 * numStates) * k` cyclic tag
steps. {uses "TagSystem.step_valid"}[] keeps the relation.
:::

:::theorem "TagSystem.tm_tag_forwardSim" (parent := "t7_cts") (lean := "TagSystem.tm_tag_forwardSim")
For a well-formed machine `tm` ({uses "TagSystem.WF"}[]), the tag system
{uses "TagSystem.tagK"}[] `tm tm.numStates` on the finite alphabet
forward-simulates ({uses "Smith.ForwardSim"}[]) the machine along the relation
"`c` is valid ({uses "TagSystem.ValidCfg"}[]), its state is below `numStates`,
and `w` is {uses "TagSystem.word"}[] `c` mapped by {uses "TagSystem.enc"}[]
`tm.numStates`".
:::

:::proof "TagSystem.tm_tag_forwardSim"
As for {uses "TagSystem.tm_cts_forwardSim"}[] without the last transport:
{uses "TagSystem.tm_step_tag"}[], {uses "TagSystem.nStepsP_enc"}[] and
{uses "TagSystem.step_valid"}[].
:::

The tag-level simulation `TagSystem.tm_tag_forwardSim` is what
{ref "universality"}[the chapter on the composition] uses, because the number of
cyclic tag cycles must be the number of tag steps.

# The decoder

:::group "t7_decoder"
The decoder of the cyclic tag word, its completeness and the soundness of its
block stage; T7 in the finite form (`TagSystem/TMToCTS.lean`).
:::

`TagSystem.decodeCTS S d` reads the one-hot blocks of the cyclic tag word back
as tag symbols, the symbols as a configuration word, and the two numbers as tape
halves. It returns the configuration without trailing blanks.

:::definition "TagSystem.symbolDecode" (parent := "t7_decoder") (lean := "TagSystem.symbolDecode")
The symbol of a one-hot block: `symbolDecode k l` is the position of the single
`true` of `l` as an element of `Fin k`, and `none` unless `l` has length exactly
`k` and holds a single `true` (`TagSystem.symbolDecodeAux`).
:::

:::lemma_ "TagSystem.symbolDecode_sound" (parent := "t7_decoder") (lean := "TagSystem.symbolDecode_sound")
The block decoder {uses "TagSystem.symbolDecode"}[] accepts exactly the one-hot
blocks of length `k`: if `symbolDecode k l = some a` then
`l = symbolEncode k a`. (Completeness,
`TagSystem.symbolDecode_encode`: `symbolDecode k (symbolEncode k a) = some a`.)
:::

:::proof "TagSystem.symbolDecode_sound"
`l` has length `k` and `symbolDecodeAux` found its `true` at position `a` with
only `false` before and after it (`TagSystem.symbolDecodeAux_sound`), which is
the one-hot word of `a`.
:::

:::definition "TagSystem.tagWordDecode" (parent := "t7_decoder") (lean := "TagSystem.tagWordDecode")
The one-hot blocks of a cyclic tag word as tag symbols: `tagWordDecode k hk l`
splits `l` into blocks of length `k`, decodes each by
{uses "TagSystem.symbolDecode"}[], and is `none` unless `l` is a sequence of
whole blocks of length `k`, each one-hot.
:::

:::lemma_ "TagSystem.tagWordDecode_sound" (parent := "t7_decoder") (lean := "TagSystem.tagWordDecode_sound")
The word decoder {uses "TagSystem.tagWordDecode"}[] accepts exactly the
concatenations of one-hot blocks: if `tagWordDecode k hk l = some w` then
`l = tagWordEncode k w`.
(Completeness, `TagSystem.tagWordDecode_encode`:
`tagWordDecode k hk (tagWordEncode k w) = some w`.)
:::

:::proof "TagSystem.tagWordDecode_sound"
Induction along the blocks, each block by {uses "TagSystem.symbolDecode_sound"}[].
:::

:::definition "TagSystem.parseWord" (parent := "t7_decoder") (lean := "TagSystem.parseWord")
The state and the two numbers of a configuration word: `parseWord w` reads
`A_q x`, counts the pairs `al_q x` (`TagSystem.countPairs`), reads `B_q x` with
the same state, counts the pairs `be_q x`, and requires nothing to remain; it
returns `(q, m, N)`. On {uses "TagSystem.cword"}[] `q m N` it returns
`some (q, m, N)` (`TagSystem.parseWord_cword`).
:::

:::definition "TagSystem.natBits" (parent := "t7_decoder") (lean := "TagSystem.natBits")
The binary digits of a number, least significant first, without trailing zeros:
`natBits 0 = []` and `natBits n = n % 2 :: natBits (n / 2)` otherwise. It
inverts {uses "TagSystem.val"}[]: `val (natBits n) = n`
(`TagSystem.val_natBits`), and its digits are bits (`TagSystem.natBits_lt`).
:::

:::definition "TagSystem.canon" (parent := "t7_decoder") (lean := "TagSystem.canon")
A configuration ({uses "BiTM.Config"}[]) without trailing blanks on either side:
the same state and scanned cell, and each tape half replaced by
{uses "TagSystem.natBits"}[] of its {uses "TagSystem.val"}[].
:::

:::definition "TagSystem.decodeCTS" (parent := "t7_decoder") (lean := "TagSystem.decodeCTS")
The decoder of a cyclic tag configuration `d` with parameter `S`: the data of
`d` is read as tag symbols over `1 + 84 * S` by
{uses "TagSystem.tagWordDecode"}[], the symbols are mapped by
{uses "TagSystem.dec"}[] `S`, the word is parsed by {uses "TagSystem.parseWord"}[]
and the numbers `(q, m, N)` become the configuration with state `q`, left half
{uses "TagSystem.natBits"}[] `m`, scanned cell `N % 2` and right half
`natBits (N / 2)` (`TagSystem.decodeWord`, `TagSystem.cfgOfNums`).
:::

:::theorem "TagSystem.decodeCTS_word" (parent := "t7_decoder") (lean := "TagSystem.decodeCTS_word")
For a valid configuration `c` ({uses "TagSystem.ValidCfg"}[]) with state below
`S`, {uses "TagSystem.decodeCTS"}[] `S` of {uses "TagSystem.ctsOfCfg"}[] `S c`
is `some (canon c)` ({uses "TagSystem.canon"}[]).
:::

:::proof "TagSystem.decodeCTS_word"
The block stage inverts the one-hot encoding (`TagSystem.tagWordDecode_encode`),
{uses "TagSystem.dec"}[] inverts {uses "TagSystem.enc"}[] on a word with states
below `S` (`TagSystem.map_dec_enc`, from {uses "TagSystem.dec_enc"}[]),
{uses "TagSystem.parseWord"}[] reads `(q, val left, head + 2 * val right)` off
the configuration word (`TagSystem.parseWord_cword`), and since `head` is a bit,
`(head + 2 * val right) % 2 = head` and `(head + 2 * val right) / 2 = val right`.
:::

T7 in the finite form shared by every link:

:::theorem "TagSystem.t7_finite" (parent := "t7_decoder") (lean := "TagSystem.t7_finite") (tags := "T7")
For a well-formed machine `tm` ({uses "TagSystem.WF"}[]), a valid configuration
`c` ({uses "TagSystem.ValidCfg"}[]) with state below `numStates`, and a run of
`n` steps of `tm` from `c` ({uses "BiTM.nSteps"}[]), there is a schedule
`times : Nat -> Nat` with `times 0 = 0`, strictly increasing on `[0, n]`, such
that for every `i <= n` the `i`-th configuration `ci` of the run exists, the
cyclic tag system {uses "TagSystem.tagToCTS"}[] of {uses "TagSystem.tagK"}[]
`tm tm.numStates` reaches a configuration `di` at time `times i` from
{uses "TagSystem.ctsOfCfg"}[] `tm.numStates c`, and
{uses "TagSystem.decodeCTS"}[] `tm.numStates di = some (canon ci)`
({uses "TagSystem.canon"}[]).
:::

:::proof "TagSystem.t7_finite"
The lifting {uses "Smith.ForwardSim_nSteps"}[] applied to
{uses "TagSystem.tm_cts_forwardSim"}[] along the run gives the schedule and, at
each time, a cyclic tag configuration related to the `i`-th configuration of the
run, which is valid with state below `numStates`;
{uses "TagSystem.decodeCTS_word"}[] reads it back as `canon ci`.
:::

# Notes and caveats

- Binary machines only. `WF` quantifies over `s < 2` and never reads
  `numSymbols`; a machine with `numSymbols := 17` and junk on symbols 2 and up is
  `WF` if its bit rows are. The docs of `docs/PLAN.md` section 2 that say "every
  well-formed TM" overstate this ({ref "open-items"}[the chapter on open items]).
- The halt row. `BiTM.step` returns `none` in state 0 before consulting the
  table, but `WF` requires the row of state 0 to be in range, because the tag
  productions keep applying `tm.transition 0 _` after the machine has halted and
  `prod_OK` needs the states to stay bounded. A machine whose halt row is out of
  range can be patched without changing any run; the wrapper lemma is not written
  ({ref "open-items"}[the chapter on open items]).
- The tag system is stated for machine steps only; a halted machine makes none,
  and nothing relates the tag system's own halting to the machine's.
- `decodeCTS` is proved complete (it inverts the encoder:
  `TagSystem.decodeCTS_word`), and its block stage is also sound since
  2026-09-22: `TagSystem.symbolDecode` accepts exactly the one-hot blocks of
  length `k` (`TagSystem.symbolDecode_sound`) and `TagSystem.tagWordDecode`
  exactly their concatenations (`TagSystem.tagWordDecode_sound`), so a word with
  a short last block or a stray bit is rejected. The later stages
  (`decodeWord`, `cfgOfNums`) are used for completeness only. Only completeness
  is used by the headline.
- The header of `TagSystem/TagToCTS.lean` used to say the cyclic tag system has
  `k` appendants; the definition and its lemma say `2k` (the header does too
  since 2026-09-22), and the factor 2 is load-bearing in
  {ref "universality"}[the chapter on the composition].

# Depends on

This chapter depends on the modules `TagSystem.Basic`, `TagSystem.TagRounds`,
`TagSystem.CockeMinsky`, `TagSystem.TagToCTS`, `TagSystem.TMToCTS`,
`Smith.Simulation` (for `ForwardSim`) and `BiTM.Basic`. From the other chapters
it uses the machine model (`TM.Machine`, `BiTM.Config`, `BiTM.step`,
`BiTM.nSteps`) and the simulation calculus (`Smith.StepSys`, `Smith.ForwardSim`,
`Smith.ForwardSim_nSteps`).
