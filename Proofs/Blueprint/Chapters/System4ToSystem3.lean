/-
  Blueprint.Chapters.System4ToSystem3

  Chapter 6 of the blueprint: T3, first half, from System 4 to System 3.
  The parity theory of a block (Smith/ParityBlocks.lean), the runs of
  System 3 over a block (Smith/System3Runs.lean), the relation Rep3 with
  its side conditions, the per-rule lemmas, the initial tape and the
  forward simulation sys4_sys3_forwardSim, composed with the second half
  to sys4_sys0_forwardSim and conjecture3_finite (Smith/Conjecture3.lean).
-/

import Verso
import VersoManual
import VersoBlueprint
import Smith.ParityBlocks
import Smith.System3Runs
import Smith.Conjecture3

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "T3, first half: from System 4 to System 3" =>

%%%
tag := "system4-to-system3"
file := "system4-to-system3"
htmlSplit := .never
%%%

# Orientation

This is the deepest link of Smith's proof ([TM23Proof.pdf](https://www.wolframscience.com/prizes/tm23/TM23Proof.pdf) p. 6-15, Lemma 0, Lemma 1
and "why the initial condition works"). System 3 ({bpref "Smith.sys3"}[`Smith.sys3`], a lookahead machine
of {ref "machine-model"}[the chapter on the machine model]) emulates System 4 with
each set represented by a block of `2^w` cells of 1s and 2s and each star by a 0
that stands in for a neighbouring cell. Three modules: [`Smith/ParityBlocks.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/ParityBlocks.lean)
(the parity theory of a block), [`Smith/System3Runs.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/System3Runs.lean) (the runs of System 3 over
a block), [`Smith/Conjecture3.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Conjecture3.lean) (the relation, the per-rule lemmas, the initial
tape, T3). The result is {bpref "Smith.sys4_sys3_forwardSim"}[`Smith.sys4_sys3_forwardSim`], and with
{ref "systems-3-2-1-0"}[the chapter on Systems 3 to 0] {bpref "Smith.sys4_sys0_forwardSim"}[`Smith.sys4_sys0_forwardSim`]
and {bpref "Smith.conjecture3_finite"}[`Smith.conjecture3_finite`].

:::group "parity-blocks"
The parity theory of a block of 1s and 2s: the scan transducer, the rows of the
rule-60 automaton and Smith's Lemma 1 (Smith/ParityBlocks.lean).
:::

:::group "system3-runs"
The runs of System 3 over a block: the walk, the turn, the star and the three
scans (Smith/System3Runs.lean).
:::

:::group "system4-system3"
The relation between System 4 and System 3 configurations, its side conditions,
the per-rule lemmas, the initial tape and T3 (Smith/Conjecture3.lean).
:::

# Parity blocks

:::definition "Smith.Bits" (parent := "parity-blocks") (lean := "Smith.Bits")
A block of 1s and 2s as a list of bits, `2` being `true`.
:::

:::definition "Smith.scanFrom" (parent := "parity-blocks") (lean := "Smith.scanFrom")
The prefix-XOR transducer of a System 3 scan in state B or C over a
{uses "Smith.Bits"}[]: from the entering state `s` (state B is `false`, state C is
`true`), each bit `b` is replaced by `s ^^ b`, and that value is the state carried
to the next bit; the empty block is left empty.
:::

:::definition "Smith.T" (parent := "parity-blocks") (lean := "Smith.T")
Smith's operator, the scan in state B: `T = scanFrom false` ({uses "Smith.scanFrom"}[]).
:::

:::lemma_ "Smith.scanC_eq_T_toggle" (parent := "parity-blocks") (lean := "Smith.scanC_eq_T_toggle")
The scan in state C of a nonempty block is the scan in state B ({uses "Smith.T"}[])
of the block with its first bit toggled: `scanFrom true (a :: x) = T ((!a) :: x)`
({uses "Smith.scanFrom"}[]). This is Smith's sublemmas 5 to 8 of Lemma 0 in one line.
:::

:::proof "Smith.scanC_eq_T_toggle"
Unfold `T` and `scanFrom` one step: the first output bit is `!a` on both sides and
the state carried to the tail is `!a` on both sides.
:::

:::definition "Smith.parAt" (parent := "parity-blocks") (lean := "Smith.parAt")
`parAt x k` is the parity of the block `x` after `k` scans in state B: the number of
2s modulo 2 of `T^[k] x` ({uses "Smith.T"}[]).
:::

:::lemma_ "Smith.parAt_xor" (parent := "parity-blocks") (lean := "Smith.parAt_xor")
The parity set {uses "Smith.parAt"}[] is linear in the block: for blocks `x` and `y`
of the same length, `parAt (xorB x y) k = (parAt x k ^^ parAt y k)`, where `xorB`
is the pointwise XOR.
:::

:::proof "Smith.parAt_xor"
`T` commutes with the pointwise XOR of blocks of equal length, hence so does every
iterate of `T`, and the parity of a pointwise XOR is the XOR of the parities.
:::

:::definition "Smith.stepR" (parent := "parity-blocks") (lean := "Smith.stepR")
One row of the rule-60 cellular automaton: a block XOR its shift to the right by one
cell (a 1 coming in at the left, the last cell dropped), `stepR x = xorB (shiftR x) x`.
:::

:::definition "Smith.row" (parent := "parity-blocks") (lean := "Smith.row")
Smith's strings for the one-element sets (p. 8), the rows of the rule-60 automaton:
`row n 0` is the block `2 1 1 ... 1` of length `n`, a single 2, and `row n (i + 1)`
is `row n i` XOR its shift ({uses "Smith.stepR"}[]). One scan takes `row n (i + 1)`
back to `row n i`.
:::

:::lemma_ "Smith.stepR_iterate_two_pow" (parent := "parity-blocks") (lean := "Smith.stepR_iterate_two_pow")
The Frobenius identity of the rule-60 automaton over GF(2): for every `w` and every
block `x`, the `2^w`-fold iterate of {uses "Smith.stepR"}[] is `x` XOR its
`2^w`-fold shift, `stepR^[2 ^ w] x = xorB (shiftR^[2 ^ w] x) x`.
:::

:::proof "Smith.stepR_iterate_two_pow"
Induction on `w`. For `w + 1` the `2^(w+1)`-fold iterate is the `2^w`-fold iterate
applied twice; by the induction hypothesis, the commutation of `stepR` with the shift
and the linearity of both in the block, the result is `x` XOR two copies of the
`2^w`-fold shift of `x` XOR the `2^(w+1)`-fold shift of `x`, and the two copies
cancel. At width `2^w` the `2^w`-fold shift empties the block, so the rows of width
`2^w` have period `2^w`.
:::

:::lemma_ "Smith.parAt_row" (parent := "parity-blocks") (lean := "Smith.parAt_row")
Smith's Lemma 1: for `i` and `k` below `2^w`, the parity of {uses "Smith.row"}[]
`row (2 ^ w) i` after `k` scans ({uses "Smith.parAt"}[]) is `true` exactly when
`k = i`.
:::

:::proof "Smith.parAt_row"
Within width `n`, the parity of `row n j` is odd exactly when `j = 0`, the single 2.
For `k` at most `i`, `k` scans take `row n i` to `row n (i - k)`. For `k` above `i`,
the scans pass through `row n 0`, and one scan of `row n 0` is `row n (2^w - 1)`,
the all-2s block, by the periodicity of {uses "Smith.stepR_iterate_two_pow"}[]; the
remaining scans walk down from there and do not reach `row n 0` again within the
window of `2^w` scans.
:::

So the block of a set is the XOR of the rows of its elements, and by the linearity
of `parAt` it has the parity of the set's membership on each of the next `2^w`
scans. This is the whole of "Lemma 1" and of the choice of `w`.

# The runs of System 3

The run lemmas of [`Smith/System3Runs.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/System3Runs.lean) are stated as equations on
`Smith.lnSteps sys3`, the `n`-step run of System 3 of
{ref "machine-model"}[the chapter on the machine model].

:::lemma_ "Smith.walkLeft" (parent := "system3-runs") (lean := "Smith.walkLeft")
Lemma 0.1: in state A the head walks left over 1s and 2s unchanged (`A1 -> A1<`,
`A2 -> A2<`) onto the first other cell. From a nonzero cell `a` with `p` nonzero
cells left of it and then the cell `z`, the run of `p + 1` steps of
{uses "Smith.sys3"}[] ({uses "Smith.lnSteps"}[]) puts the head on `z` in state A,
with the walked cells and `a` now on the right in their order.
:::

:::proof "Smith.walkLeft"
Induction on the walked cells, one step of `sys3` each, all cases by computation.
:::

:::lemma_ "Smith.turnA" (parent := "system3-runs") (lean := "Smith.turnA")
`A0 -> B2>`: at a 0 in state A, one step of {uses "Smith.sys3"}[]
({uses "Smith.lstep"}[]) turns the 0 into a 2 and moves the head right in state B.
:::

:::proof "Smith.turnA"
By the table of `sys3`: the rule for state A on 0 is `one B 2 R`, and `lstep` applies it.
:::

:::lemma_ "Smith.starB" (parent := "system3-runs") (lean := "Smith.starB")
`B0 -> A2<`: at a 0 in state B, one step of {uses "Smith.sys3"}[] turns the 0 into
a 2 and moves the head left in state A.
:::

:::proof "Smith.starB"
By the table of `sys3`: the rule for state B on 0 is `one A 2 L`, and `lstep` applies it when there is a cell to the left.
:::

:::lemma_ "Smith.scanBlock" (parent := "system3-runs") (lean := "Smith.scanBlock")
A scan over a block followed by a nonzero cell: from the cell `a` of the block
`a :: x` in the state `s` (B for `false`, C for `true`), the run of
`x.length + 1` steps of {uses "Smith.sys3"}[] leaves `scanFrom s (a :: x)`
({uses "Smith.scanFrom"}[]) behind and lands on the nonzero cell in the state given
by the parity, `s ^^ parity (a :: x)`.
:::

:::proof "Smith.scanBlock"
Induction on `x`. One scanning step inside a block replaces the cell `a`, followed
by a cell that is not a 0, by `s ^^ a` and moves right in the state `s ^^ a`; the
last step lands on the nonzero cell.
:::

:::lemma_ "Smith.scanBlock0B" (parent := "system3-runs") (lean := "Smith.scanBlock0B")
A scan over a block followed by a 0, when the exit state is B (the entering state
XOR the parity of the block is `false`): the same run as {uses "Smith.scanBlock"}[]
leaves `scanFrom s (a :: x)` behind and lands on the 0 in state B.
:::

:::proof "Smith.scanBlock0B"
As for `scanBlock`; the last cell of the block followed by a 0, with exit parity
`false`, is written as in the interior and the head lands on the 0 in state B.
:::

:::lemma_ "Smith.scanBlock0C" (parent := "system3-runs") (lean := "Smith.scanBlock0C")
A scan over a block followed by a 0, when the exit state would be C (the entering
state XOR the parity of the block is `true`): the run of `x.length + 1` steps of
{uses "Smith.sys3"}[] leaves `scanFrom s (a :: x)` behind except for its last cell,
a 2, which becomes a 0, and lands on the 0 in state A (`B20 -> A00>`,
`C10 -> A00>`). These are the two 0s of Smith's star active in state C, p. 11 and
13.
:::

:::proof "Smith.scanBlock0C"
As for {uses "Smith.scanBlock"}[]; the last cell of the block followed by a 0, with
exit parity `true`, would become a 2 and instead becomes a 0, the head landing on
the 0 in state A.
:::

# The relation

Rather than a predicate on pairs of tapes, an abstract configuration carries the
items on both sides of the head, the ends of the tape, the System 4 state and a
focus; both the System 4 and the System 3 configuration are computed from it.

:::definition "Smith.Focus" (parent := "system4-system3") (lean := "Smith.Focus")
What the head is on: `setA xl b xr S`, state A on the cell `b` of the block
`xl.reverse ++ b :: xr` of the set `S`, held as a zipper; `setB x0 x' S`, state B
or C on the first cell `x0` of the block `x0 :: x'` of `S`; `setT x1 x' S`, System 4
in state C right after rule 5, on the second cell `x1` of the block
`true :: x1 :: x'` in System 3's state B; `star`, on a star; `off`, System 4's head
past its tape.
:::

:::definition "Smith.AC" (parent := "system4-system3") (lean := "Smith.AC")
An abstract configuration: the items left of the head (nearest first), the items
right of it, the left end ({uses "Smith.LeftEnd"}[]), the right end
({uses "Smith.Closing"}[]), the System 4 state and the focus ({uses "Smith.Focus"}[]).
An item is a set with its block (a {uses "Smith.Bits"}[]) or a star.
:::

:::definition "Smith.AC.to4" (parent := "system4-system3") (lean := "Smith.AC.to4")
The System 4 configuration of an {uses "Smith.AC"}[]: the items left of the head,
reversed, then the set or star at the head unless the focus is `off`, then the
items right of it, each item as its System 4 element; the active position is the
number of items left of the head; the state is the System 4 state.
:::

:::definition "Smith.renderR" (parent := "system4-system3") (lean := "Smith.renderR")
The cells of the items right of the head, left to right: a set gives its block,
without its first cell when a star precedes it (the flag records whether one does);
a star gives a 0.
:::

:::definition "Smith.renderL" (parent := "system4-system3") (lean := "Smith.renderL")
The cells of the items left of the head, nearest first: a set gives its block
reversed, without its last cell when a star follows it (the flag records whether
one does); a star gives a 0.
:::

:::definition "Smith.AC.toL" (parent := "system4-system3") (lean := "Smith.AC.toL")
The System 3 configuration ({uses "Smith.LConfig"}[]) of an {uses "Smith.AC"}[]:
the cells left of the head are the block cells left of the focus, then
{uses "Smith.renderL"}[] of the left items, then the left end; the cells right of
it are the block cells right of the focus, then {uses "Smith.renderR"}[] of the
right items, then the right end; the head cell and the System 3 state follow the
focus: the block cell in state A for `setA`, the first cell in state B or C for
`setB`, the second cell in state B with a 2 left of it for `setT`, a 0 for `star`
(with the neighbouring set's replaced cell dropped on the side the star stands for,
and an extra 0 to the left in state A when System 4 is in state C), and the closing
cell for `off`.
:::

:::definition "Smith.Decodes" (parent := "system4-system3") (lean := "Smith.Decodes")
`Decodes x S k`: the block `x` decodes to the set `S` on its next `k` scans, that
is for every `j` below `k`, {uses "Smith.parAt"}[] `x j` is `true` exactly when `j`
is in `S`.
:::

:::definition "Smith.LeftOK" (parent := "system4-system3") (lean := "Smith.LeftOK")
The star-side rule for the items left of the head, nearest first: a star stands in
the place of the last cell of the set beyond it, which is a 2; two stars are never
adjacent; the leftmost item is a set, or, when the left end is junk (the flag), a
star that is never reached.
:::

:::definition "Smith.RightOK" (parent := "system4-system3") (lean := "Smith.RightOK")
The star-side rule for the items right of the head, left to right: a star stands
in the place of the first cell of the set after it, which is a 2; two stars are
never adjacent; the last item is a set.
:::

:::definition "Smith.HeadLastTrue" (parent := "system4-system3") (lean := "Smith.HeadLastTrue")
The first item of a list of items is a set whose block ends in a 2: the condition
on the items left of a star at the head in state A or C, which stands in the place
of that cell.
:::

:::definition "Smith.HeadFirstTrue" (parent := "system4-system3") (lean := "Smith.HeadFirstTrue")
The first item of a list of items is a set whose block begins with a 2: the
condition on the items right of a star at the head in state B or C, which stands in
the place of that cell.
:::

:::definition "Smith.FocusOK" (parent := "system4-system3") (lean := "Smith.FocusOK")
The side conditions on a {uses "Smith.Focus"}[] for width `N`, `k` scans, the
junk flag, the System 4 state and the items on both sides: `setA` requires state A
and a sound item (a block of width `N` that {uses "Smith.Decodes"}[] to its set,
which has no duplicates); `setB` requires a state other than A and a sound item;
`setT` requires state C, a block `true :: x1 :: x'` of width `N` that decodes to
the set with 1 toggled (`xorInsert 1 S`; the skipped first cell, a 2, is what turns
"toggle 1, then decrement" into one scan); `star` requires, in state A,
{uses "Smith.HeadLastTrue"}[] on the left items and a set first on the right, in
state B a set first on the left and {uses "Smith.HeadFirstTrue"}[] on the right,
and in state C `HeadLastTrue` on the left (or no left item at all with a junk left
end) and `HeadFirstTrue` on the right; `off` requires nothing.
:::

:::definition "Smith.SafeC" (parent := "system4-system3") (lean := "Smith.SafeC")
`SafeC h c4`: within the next `h` System 4 steps ({uses "BiTM.System4.step"}[]
iterated by `System4.nSteps`) the head is on the leftmost element only in state C.
Rule 1 at the leftmost element (the turn) and rule 4 there (stuck) are the only
steps that would look at what lies left of the tape; rules 2, 3 and 5 do not.
:::

:::definition "Smith.LeftEnd" (parent := "system4-system3") (lean := "Smith.LeftEnd")
The left end of the tape beyond the items: either `zeros m t`, the string
`0^m 2 2 1^t` of Smith's Perl programs (p. 44), one 0 turned into a 2 by every
turn; or `junk L`, arbitrary cells. Its condition with `h` System 4 steps left is
`h <= m` and `1 <= t` for `zeros m t`, and {uses "Smith.SafeC"}[] `h c4` for
`junk L`: no turn and no rule 4 ever looks at what lies left of the tape. The junk
case exists for the infinite form
({ref "infinite-form"}[the chapter on the infinite form]).
:::

:::definition "Smith.Closing" (parent := "system4-system3") (lean := "Smith.Closing")
The right end of the tape beyond the items: `one`, the closing 1 of the finite
tape, on which the head stops when System 4 leaves its tape; or `zero Rc`, a 0
followed by arbitrary cells, the next block of the infinite form, on which the head
lands as on a star.
:::

:::definition "Smith.AC.OK" (parent := "system4-system3") (lean := "Smith.AC.OK")
The side conditions `a.OK w h` of an {uses "Smith.AC"}[] for width `2^w`, `h` being
the number of System 4 steps left:

- `h + 3 <= 2^w`;
- the left end ({uses "Smith.LeftEnd"}[]) satisfies its condition for `h` steps
  from `a.to4`;
- every item on either side is sound: its block has width `2^w` and
  {uses "Smith.Decodes"}[] to its set, which has no duplicates, on the next `h + 1`
  scans;
- the star-side rule: {uses "Smith.LeftOK"}[] on the left items (with the junk
  flag of the left end) and {uses "Smith.RightOK"}[] on the right items; a star
  left of the head, or at the head in state A or C, stands in the place of the last
  cell of the set before it, which is a 2; a star right of the head, or at the head
  in state B or C, stands in the place of the first cell of the set after it, which
  is a 2 ({uses "Smith.HeadLastTrue"}[], {uses "Smith.HeadFirstTrue"}[];
  {uses "Smith.renderL"}[] and {uses "Smith.renderR"}[] drop the replaced cell);
- the head shape: {uses "Smith.FocusOK"}[] for width `2^w` and `h + 1` scans.
:::

:::definition "Smith.Rep3" (parent := "system4-system3") (lean := "Smith.Rep3")
The relation of the link: `Rep3 rc c3 c4 w h` says that the System 3 configuration
`c3` and the System 4 configuration `c4` come from one {uses "Smith.AC"}[] `a`
with right end `rc` ({uses "Smith.Closing"}[]) satisfying the side conditions
{uses "Smith.AC.OK"}[] `w h`, with `c3 = a.toL` ({uses "Smith.AC.toL"}[]) and
`c4 = a.to4` ({uses "Smith.AC.to4"}[]).
:::

The star-side rule and the transient shape were found and validated by a Python
checker of the relation along `system4.pl` runs before anything was proved; the
checker's first version had the active set on the wrong side of the rule.

# The per-rule lemmas

:::definition "Smith.Matches" (parent := "system4-system3") (lean := "Smith.Matches")
The conclusion of every per-rule lemma: `Matches w h rc c3 c4'` says that a run of
{uses "Smith.sys3"}[] from `c3` of at least one step ({uses "Smith.lnSteps"}[])
reaches the `toL` ({uses "Smith.AC.toL"}[]) of an {uses "Smith.AC"}[] with right
end `rc` whose `to4` ({uses "Smith.AC.to4"}[]) is `c4'` and which satisfies
{uses "Smith.AC.OK"}[] `w h`.
:::

:::lemma_ "Smith.turnRun" (parent := "system4-system3") (lean := "Smith.turnRun")
The turn at the left end: from the cell `b` of the block `xl.reverse ++ b :: xr`
in state A, with the left end `0^(m' + 1) 2 2 1^t` beyond the block, the run of
`xl.length + 2 * t + 6` steps of {uses "Smith.sys3"}[] walks left, turns the
nearest 0 into a 2, scans back over `2 2 1^t`, which becomes `2 1 1^t`, and lands
on the first cell of the block in state B, the left end now being
`0^m' 2 2 1^(t + 1)`.
:::

:::proof "Smith.turnRun"
First {uses "Smith.walkLeft"}[] over the block cells, the `1^t` and the two 2s onto
the nearest 0; then {uses "Smith.turnA"}[]; then the scan back in state B over
`2 2 1^t` followed by the nonzero first cell of the block
({uses "Smith.scanBlock"}[]), whose prefix XOR is `2 1 1^t` with exit state B.
:::

:::definition "Smith.landing" (parent := "system4-system3") (lean := "Smith.landing")
The System 3 configuration reached by a scan that left the block `z` behind and
exits with parity `e` (state C when `e`), with the cells `L` left of the block, the
items `rs` right of it and the right end `rc` ({uses "Smith.Closing"}[]): on the
first cell of the next set in the exit state; on the closing 1 in the exit state;
or, at a star's 0 or the 0 of `Closing.zero`, on the 0 in state B when `e` is
`false`, and with the last cell of `z` turned into a 0 and the head on the 0 in
state A when `e` is `true`.
:::

:::lemma_ "Smith.scanRun" (parent := "system4-system3") (lean := "Smith.scanRun")
A scan of {uses "Smith.sys3"}[] from the cell `a` over the rest `x` of a block,
followed by {uses "Smith.renderR"}[] of items whose blocks are nonempty and then the
right end, takes `x.length + 1` steps and lands as {uses "Smith.landing"}[] says,
with the block `scanFrom s (a :: x)` ({uses "Smith.scanFrom"}[]) left behind and
the exit parity `s ^^ parity (a :: x)`.
:::

:::proof "Smith.scanRun"
Case analysis on the first item right of the block and on the right end: a set or
the closing 1 is a nonzero cell, {uses "Smith.scanBlock"}[]; a star or the 0 of
`Closing.zero` is a 0, {uses "Smith.scanBlock0B"}[] or {uses "Smith.scanBlock0C"}[]
according to the exit parity.
:::

:::definition "Smith.afterScan" (parent := "system4-system3") (lean := "Smith.afterScan")
The {uses "Smith.AC"}[] after a scan: the block `z` with its new set `S'` joins the
left items, the right items lose their first element, and the focus is on it: `off`
when there was none, `setB` on the first cell of the next set, or `star`.
:::

:::lemma_ "Smith.Decodes_parity" (parent := "system4-system3") (lean := "Smith.Decodes_parity")
The first scan decides `0 in S`: if the block {uses "Smith.Decodes"}[] to `S` on at
least one scan, its parity is `true` exactly when `0` is in `S`. This is what makes
System 3's exit state agree with System 4's toggle.
:::

:::proof "Smith.Decodes_parity"
The instance of `Decodes` at scan 0 says the block's parity at position 0 is the membership of 0 in `S` (`parAt_zero`).
:::

:::lemma_ "Smith.Decodes_T" (parent := "system4-system3") (lean := "Smith.Decodes_T")
A scan in state B decodes the decremented set: if `x` {uses "Smith.Decodes"}[] to a
duplicate-free `S` on `k + 1` scans, then `T x` ({uses "Smith.T"}[]) decodes to
`decr S` (the set of `e - 1` for `e` in `S` other than 0) on `k` scans.
:::

:::proof "Smith.Decodes_T"
A scan shifts the parity set down by one, `parAt (T x) j = parAt x (j + 1)`, and
`j` is in `decr S` exactly when `j + 1` is in `S`.
:::

:::lemma_ "Smith.Decodes_scanC" (parent := "system4-system3") (lean := "Smith.Decodes_scanC")
The scan in state C decodes the decremented set too (Smith's Corollary 0): for a
block `a :: x` of width `2^w` that {uses "Smith.Decodes"}[] to a duplicate-free `S`
on `k + 1` scans with `k + 1 < 2^w`, `scanFrom true (a :: x)`
({uses "Smith.scanFrom"}[]) decodes to `decr S` on `k` scans.
:::

:::proof "Smith.Decodes_scanC"
By {uses "Smith.scanC_eq_T_toggle"}[] the scan in state C is `T` of the block with
its first bit toggled. Toggling the first bit is XOR with `row n 0`
({uses "Smith.row"}[]), whose parity is at scan 0 only ({uses "Smith.parAt_row"}[],
{uses "Smith.parAt_xor"}[]), so after the scan the parities at scans `1` to `k` are
those of {uses "Smith.Decodes_T"}[].
:::

:::lemma_ "Smith.Decodes_transient" (parent := "system4-system3") (lean := "Smith.Decodes_transient")
The skipped-cell scan after rule 5: for a block `true :: x` of width `2^w` that
{uses "Smith.Decodes"}[] to `xorInsert 1 S` (the duplicate-free `S` with 1 toggled)
on `k + 1` scans with `k + 1 < 2^w`, the block `true :: scanFrom false x` (the
first bit kept, the rest scanned from state B; {uses "Smith.scanFrom"}[]) decodes to
`decr S` on `k` scans. The result is `2 :: T tail`, and toggling 1 before the
decrement is toggling 0 after it.
:::

:::proof "Smith.Decodes_transient"
Write the result as the toggle of the first bit of `T (false :: x)`, and the given
block as the toggle of the first bit of `false :: x`; both toggles are XOR with
`row n 0` and change the parity at scan 0 only ({uses "Smith.parAt_row"}[],
{uses "Smith.parAt_xor"}[]). The membership bookkeeping: `j` is in `decr S` exactly
when `j + 1` is in `S`, and `j + 1` is in `xorInsert 1 S` exactly when it is in `S`
unless `j = 0`, where the toggle at scan 0 of the result compensates.
:::

:::proposition "Smith.ac_step" (parent := "system4-system3") (lean := "Smith.ac_step")
Every System 4 step ({uses "BiTM.System4.step"}[]) from the `to4` of an
{uses "Smith.AC"}[] `a` satisfying {uses "Smith.AC.OK"}[] `w (h + 1)` is matched
({uses "Smith.Matches"}[] `w h`) by a run of System 3 from `a.toL`.
:::

:::proof "Smith.ac_step"
Case analysis on the focus and the state. Each System 4 rule is matched by a
System 3 run to the `toL` of a new `AC` whose `to4` is the System 4 result: rule 1
by {uses "Smith.walkLeft"}[] over `p + 1` cells onto the previous block's last cell
or a star's 0, or, at the left end, {uses "Smith.turnRun"}[] (`p + 2t + 6` steps:
walk, `turnA`, scan back over `2 2 1^t`, which becomes `2 1 1^t`); rule 2 by one
{uses "Smith.turnA"}[]; rule 4 by one {uses "Smith.starB"}[]; rule 5 by one `turnA`
onto the second cell of the next block; rule 3 by {uses "Smith.scanRun"}[], a scan
of `2^w` cells (or `2^w - 1` from `setT`), landing on the closing cell, the next
block's first cell, or a star ({uses "Smith.landing"}[], {uses "Smith.afterScan"}[]).
The parity side is {uses "Smith.Decodes_T"}[] for the scan in state B,
{uses "Smith.Decodes_scanC"}[] for the scan in state C,
{uses "Smith.Decodes_transient"}[] for the skipped-cell scan after rule 5 and
{uses "Smith.Decodes_parity"}[] for the agreement of the exit state with System 4's
toggle. The focus `off` has no System 4 step. The side conditions of the new
abstract configuration for `h` steps follow from those for `h + 1`: the left end's
condition steps down with the budget, the items keep decoding on one scan fewer,
and the star-side rule is preserved by each move.
:::

# The initial tape

:::definition "Smith.encSet" (parent := "system4-system3") (lean := "Smith.encSet")
Smith's block of a set (`s42s0-3.pl`): the XOR of the rows ({uses "Smith.row"}[])
of the elements and of the last row `row N (N - 1)`, the all-2s block, plus the
row `N - 2` when the first cell would otherwise be a 1.
:::

:::lemma_ "Smith.firstTrue_encSet" (parent := "system4-system3") (lean := "Smith.firstTrue_encSet")
The first cell of {uses "Smith.encSet"}[] `(2 ^ w) S` is a 2, so that a star may
stand in its place.
:::

:::proof "Smith.firstTrue_encSet"
Either the base block already begins with a 2, or the row `2^w - 2` is added, and
that row begins with a 2.
:::

:::lemma_ "Smith.Decodes_encSet" (parent := "system4-system3") (lean := "Smith.Decodes_encSet")
For a duplicate-free `S` whose elements are nonnegative and below `2^w`, and
`k + 2 <= 2^w`, {uses "Smith.encSet"}[] `(2 ^ w) S` {uses "Smith.Decodes"}[] to `S`
on `k` scans.
:::

:::proof "Smith.Decodes_encSet"
By {uses "Smith.parAt_xor"}[] and {uses "Smith.parAt_row"}[] the base block has
the membership parity of `S` on every scan below `2^w - 1`, the last row having its
parity at scan `2^w - 1` only; the optional row `2^w - 2` has its parity at scan
`2^w - 2` only. Both extra rows are outside the window of `k` scans.
:::

:::definition "Smith.initAC" (parent := "system4-system3") (lean := "Smith.initAC")
`initAC w h S0 rest` is the {uses "Smith.AC"}[] of the well-formed initial tape for
the System 4 configuration with elements `set S0 :: rest`, active position 0 and
state A: no item left of the head, the elements of `rest` as items with their
blocks {uses "Smith.encSet"}[] `(2 ^ w)`, the left end `0^h 2 2 1`
({uses "Smith.LeftEnd"}[] `zeros h 1`), closing 1 ({uses "Smith.Closing"}[] `one`),
and the head on the first cell of the block of `S0` in state A
({uses "Smith.Focus"}[] `setA`).
:::

:::lemma_ "Smith.rep3_init" (parent := "system4-system3") (lean := "Smith.rep3_init")
The initial condition of the link: under `h + 3 <= 2^w`, a well-formed System 4
configuration ({uses "BiTM.System4Config.WellFormed"}[]) with elements
`set S0 :: rest`, whose last element is not a star and whose set elements are all
nonnegative and below `2^w`, stands in {uses "Smith.Rep3"}[] `Closing.one` with the
`toL` of {uses "Smith.initAC"}[] `w h S0 rest`, for width `w` and `h` steps left.
:::

:::proof "Smith.rep3_init"
The `to4` of `initAC` is the System 4 configuration by computation, and its side
conditions hold: the width bound is the hypothesis, the left end `zeros h 1` allows
`h` turns, every block is `encSet` and decodes to its set on `h + 1` scans by
{uses "Smith.Decodes_encSet"}[] (with `h + 3 <= 2^w`), the star-side rule on the
right items follows from well-formedness (no adjacent stars) and the last element
not being a star, with {uses "Smith.firstTrue_encSet"}[] for the cell each star
stands for.
:::

# Formal statements

:::theorem "Smith.sys4_sys3_forwardSim" (parent := "system4-system3") (lean := "Smith.sys4_sys3_forwardSim") (tags := "T3")
For every width `w` and right end `rc` ({uses "Smith.Closing"}[]), System 3
({uses "Smith.sys3"}[]) tracks the fuelled System 4 ({uses "Smith.fueled"}[] of the
step system of {uses "BiTM.System4.step"}[]) through {uses "Smith.Rep3"}[] as a
forward simulation ({uses "Smith.ForwardSim"}[]): the relation between a pair
(System 4 configuration, fuel `h`) and a System 3 configuration `c` is
`Rep3 rc c c4 w h`, the fuel being the budget of scans the blocks are good for.
:::

:::proof "Smith.sys4_sys3_forwardSim"
Unfold `Rep3` to an abstract configuration `a` with `a.OK w h`. With fuel 0 the
fuelled system has no step. With fuel `h + 1` a step of the fuelled system is a
System 4 step from `a.to4` with the fuel dropping to `h`, and {uses "Smith.ac_step"}[]
gives the matching System 3 run of at least one step to the `toL` of an `AC`
satisfying `OK w h` whose `to4` is the result, which is `Rep3` again.
:::

:::theorem "Smith.sys4_sys0_forwardSim" (parent := "system4-system3") (lean := "Smith.sys4_sys0_forwardSim") (tags := "T3")
For every width `w` and right end `rc`, System 0 ({uses "Smith.sys0"}[]) tracks the
fuelled System 4 ({uses "Smith.fueled"}[]) as a forward simulation
({uses "Smith.ForwardSim"}[]) through the relation: the System 0 configuration is
`phi2 (phi3 c3)` ({uses "Smith.phi2"}[], {uses "Smith.phi3"}[]) for some `c3` in
{uses "Smith.Rep3"}[] `rc` with the System 4 configuration, for width `w` and the
fuel.
:::

:::proof "Smith.sys4_sys0_forwardSim"
The composition ({uses "Smith.ForwardSim_comp"}[]) of
{uses "Smith.sys4_sys3_forwardSim"}[] with the relabeling simulation
{uses "Smith.sys3_sys0_forwardSim"}[] of
{ref "systems-3-2-1-0"}[the chapter on Systems 3 to 0], the composed relation
rewritten by `ForwardSim_congr`.
:::

:::theorem "Smith.conjecture3_finite" (parent := "system4-system3") (lean := "Smith.conjecture3_finite") (tags := "T3")
T3 in finite form. Let `h + 3 <= 2^w`, let the System 4 configuration with elements
`set S0 :: rest`, active position 0 and state A be well-formed
({uses "BiTM.System4Config.WellFormed"}[]), with last element not a star and every
set element nonnegative and below `2^w`, and let its run of `n <= h` System 4 steps
(`System4.nSteps`) be defined. Then there are times with `times 0 = 0`, strictly
increasing on `[0, n]`, such that for every `i <= n` the `i`-th System 4
configuration `ci` exists and the run of {uses "Smith.sys0"}[]
({uses "Smith.lnSteps"}[]) of `times i` steps from `phi2 (phi3 (initAC w h S0 rest).toL)`
({uses "Smith.phi2"}[], {uses "Smith.phi3"}[], {uses "Smith.initAC"}[]) is
`phi2 (phi3 c3i)` for a System 3 configuration `c3i` with
{uses "Smith.Rep3"}[] `Closing.one c3i ci w (h - i)`: the tapes stand in `Rep3` with
the budget counting down.
:::

:::proof "Smith.conjecture3_finite"
Apply {uses "Smith.ForwardSim_nSteps"}[] to {uses "Smith.sys4_sys0_forwardSim"}[]
`w Closing.one`, with the initial relation from {uses "Smith.rep3_init"}[] and the
fuelled run of `n <= h` steps obtained from the System 4 run; the fuel at step `i`
is `h - i`.
:::

# Notes and caveats

- The width condition is `h + 3 <= 2^w`, weaker than Smith's `2^w >= 3f`, because
  the fuel, not `f`, bounds the scans; the link to `f` is made in
  {ref "conjecture0"}[the chapter on Conjecture 0], where `2^w` must also exceed
  every set element.
- The head of the initial tape is on the first cell of the first block, not on
  Smith's leftmost 0. Started on its leftmost 0 in state A, the tape `0^m 2 2 1 ...`
  walks off its left end in three steps. This is why the finite form does not chain
  by plain concatenation ({ref "infinite-form"}[the chapter on the infinite form]).
- `Rep3` is stated on the System 3 tape and leaves the swap of the cells left of the
  head to `phi3` ({ref "systems-3-2-1-0"}[the chapter on Systems 3 to 0]), so
  Smith's `s42s0-3.pl 3` output is `phi3` of `initAC`'s tape.
- T3 does not use loop-freeness: [`Smith/Conjecture3.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Conjecture3.lean) used to import
  [`Smith/LoopFree.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/LoopFree.lean) only for the generic run lemma {bpref "Smith.lnSteps_add"}[`Smith.lnSteps_add`], which
  lives in [`Smith/Lookahead.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Lookahead.lean) since 2026-09-22.
- The D8 vectors of [`Vectors/SmithVectors.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Vectors/SmithVectors.lean) run a six-step System 4 program
  through System 3 by `decide`.

# Depends on

The modules `Smith.ParityBlocks`, `Smith.System3Runs`, `Smith.Conjecture3` and
`Smith.Lookahead`; {ref "system5-to-system4"}[the chapter on System 5 to System 4]
for `System4.step`, `decr` and `xorInsert`;
{ref "systems-3-2-1-0"}[the chapter on Systems 3 to 0] for `phi2` and `phi3`.

In the graph, the nodes of this chapter use these nodes of other chapters:

- {bpref "Smith.sys3"}[`Smith.sys3`], {bpref "Smith.sys0"}[`Smith.sys0`], {bpref "Smith.lstep"}[`Smith.lstep`], {bpref "Smith.lnSteps"}[`Smith.lnSteps`] and {bpref "Smith.LConfig"}[`Smith.LConfig`]
  from {ref "machine-model"}[the chapter on the machine model];
- {bpref "Smith.ForwardSim"}[`Smith.ForwardSim`], {bpref "Smith.ForwardSim_comp"}[`Smith.ForwardSim_comp`], {bpref "Smith.ForwardSim_nSteps"}[`Smith.ForwardSim_nSteps`] and
  {bpref "Smith.fueled"}[`Smith.fueled`] from {ref "cts-to-system5"}[the chapter on cyclic tag to System 5];
- {bpref "BiTM.System4.step"}[`BiTM.System4.step`] and {bpref "BiTM.System4Config.WellFormed"}[`BiTM.System4Config.WellFormed`] from
  {ref "system5-to-system4"}[the chapter on System 5 to System 4];
- {bpref "Smith.phi2"}[`Smith.phi2`], {bpref "Smith.phi3"}[`Smith.phi3`] and {bpref "Smith.sys3_sys0_forwardSim"}[`Smith.sys3_sys0_forwardSim`] from
  {ref "systems-3-2-1-0"}[the chapter on Systems 3 to 0].
