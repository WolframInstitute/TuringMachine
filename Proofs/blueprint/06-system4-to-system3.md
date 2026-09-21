# 06. T3, first half: from System 4 to System 3

## Orientation

This is the deepest link of Smith's proof (TM23Proof.pdf p. 6-15, Lemma 0, Lemma 1 and
"why the initial condition works"). System 3 (`[[Smith.sys3]]`, a lookahead machine of
chapter 02) emulates System 4 with each set represented by a block of `2^w` cells of 1s
and 2s and each star by a 0 that stands in for a neighbouring cell. Three modules:
`Smith/ParityBlocks.lean` (the parity theory of a block), `Smith/System3Runs.lean` (the
runs of System 3 over a block), `Smith/Conjecture3.lean` (the relation, the per-rule
lemmas, the initial tape, T3). The result is `[[Smith.sys4_sys3_forwardSim]]`, and with
chapter 07 `[[Smith.sys4_sys0_forwardSim]]` and `[[Smith.conjecture3_finite]]`.

## Parity blocks

A block of 1s and 2s is a `[[Smith.Bits]]` (`2` is `true`). A System 3 scan in state B
or C is the prefix-XOR transducer

```lean
def scanFrom : Bool → Bits → Bits
  | _, [] => []
  | s, b :: xs => (s ^^ b) :: scanFrom (s ^^ b) xs
```

`[[Smith.T]] = scanFrom false` is Smith's operator (the scan in state B), and the scan in
state C is the scan in state B of the block with its first bit toggled
(`[[Smith.scanC_eq_T_toggle]]`; Smith's sublemmas 5 to 8 of Lemma 0 in one line).
`[[Smith.parAt]] x k` is the parity of the block after `k` scans, and it is linear in the
block (`[[Smith.parAt_xor]]`). Smith's strings for the one-element sets (p. 8) are the
rows `[[Smith.row]] n i` of the rule-60 cellular automaton: `row n 0` is a single 2, and
`row n (i + 1)` is `row n i` XOR its shift (`[[Smith.stepR]]`). One scan takes
`row n (i + 1)` back to `row n i`. At width `2^w` the rows have period `2^w`, by the
Frobenius identity

```lean
theorem stepR_iterate_two_pow (w : Nat) (x : Bits) :
    stepR^[2 ^ w] x = xorB (shiftR^[2 ^ w] x) x
```

(an induction on `w`, with the `2^w`-fold shift emptying the block), which gives Smith's
Lemma 1:

```lean
theorem parAt_row (w i k : Nat) (hi : i < 2 ^ w) (hk : k < 2 ^ w) :
    parAt (row (2 ^ w) i) k = decide (k = i)
```

So the block of a set is the XOR of the rows of its elements, and it has the parity of
the set's membership on each of the next `2^w` scans. This is the whole of "Lemma 1"
and of the choice of `w`.

## The runs of System 3

`Smith/System3Runs.lean`: `[[Smith.walkLeft]]` (in state A the head walks left over 1s
and 2s unchanged onto the first other cell, Lemma 0.1), `[[Smith.turnA]]` (`A0 -> B2>`),
`[[Smith.starB]]` (`B0 -> A2<`), `[[Smith.scanBlock]]` (a scan over a block followed by a
nonzero cell leaves `scanFrom s` of the block behind and exits in the state given by the
parity), `[[Smith.scanBlock0B]]` and `[[Smith.scanBlock0C]]` (a scan followed by a 0: an
exit in B lands on the 0 in state B; an exit that would be in C turns the last cell,
a 2, into a 0 and lands on the 0 in state A; these are the two 0s of Smith's star
active in state C, p. 11 and 13).

## The relation

Rather than a predicate on pairs of tapes, an abstract configuration `[[Smith.AC]]`
carries the items left of the head (nearest first), the items right of it, the left end,
the right end, the System 4 state and a focus (`[[Smith.Focus]]`, what the head is on).
Both the System 4 configuration `[[Smith.AC.to4]]` and the System 3 configuration
`[[Smith.AC.toL]]` are computed from it, and

```lean
def Rep3 (rc : Closing) (c3 : LConfig) (c4 : System4Config) (w h : Nat) : Prop :=
  ∃ a : AC, a.rc = rc ∧ a.OK w h ∧ c3 = a.toL ∧ c4 = a.to4
```

says that a pair of configurations comes from an `AC` satisfying the side conditions
`[[Smith.AC.OK]] w h`, `h` being the number of System 4 steps left:

- every block has width `2^w` and decodes to its set on the next `h + 1` scans
  (`[[Smith.Decodes]]`), and `h + 3 <= 2^w`;
- the star-side rule: a star left of the head, or at the head in state A or C, stands in
  the place of the last cell of the set before it, which is a 2; a star right of the
  head, or at the head in state B or C, stands in the place of the first cell of the set
  after it, which is a 2 (`[[Smith.LeftOK]]`, `[[Smith.RightOK]]`, `[[Smith.HeadLastTrue]]`,
  `[[Smith.HeadFirstTrue]]`; `[[Smith.renderL]]` and `[[Smith.renderR]]` drop the replaced
  cell);
- the head shapes (`[[Smith.FocusOK]]`): `setA`, state A anywhere in the block, held as a
  zipper; `setB`, state B or C on the first cell; `setT`, System 4 in state C right after
  rule 5 with System 3 in state B on the second cell, the block decoding to the set with
  1 toggled (the skipped first cell, a 2, is what turns "toggle 1, then decrement" into
  one scan); `star`; `off`, System 4's head past its tape.
- the left end (`[[Smith.LeftEnd]]`): either `zeros m t`, the string `0^m 2 2 1^t` of
  Smith's Perl programs (p. 44), one 0 turned into a 2 by every turn, with `h <= m`; or
  `junk L`, arbitrary cells, allowed when `[[Smith.SafeC]] h c4` holds: within the next
  `h` System 4 steps the head is on the leftmost element only in state C, so no turn and
  no rule 4 ever looks at what lies left of the tape. The junk case exists for the
  infinite form (chapter 10).
- the right end (`[[Smith.Closing]]`): `one`, the closing 1 of the finite tape, on which
  the head stops when System 4 leaves its tape; or `zero Rc`, a 0 followed by arbitrary
  cells, the next block of the infinite form, on which the head lands as on a star.

The star-side rule and the transient shape were found and validated by a Python checker
of the relation along `system4.pl` runs before anything was proved; the checker's first
version had the active set on the wrong side of the rule.

## The per-rule lemmas

Each System 4 rule is matched by a System 3 run to the `toL` of a new `AC` whose `to4`
is the System 4 result (`[[Smith.Matches]]`, `[[Smith.ac_step]]`): rule 1 by
`walkLeft` over `p + 1` cells onto the previous block's last cell or a star's 0, or, at
the left end, `[[Smith.turnRun]]` (`p + 2t + 6` steps: walk, `turnA`, scan back over
`2 2 1^t`, which becomes `2 1 1^t`); rule 2 by one `turnA`; rule 4 by one `starB`; rule 5
by one `turnA` onto the second cell of the next block; rule 3 by `[[Smith.scanRun]]`, a
scan of `2^w` cells (or `2^w - 1` from `setT`), landing on the closing cell, the next
block's first cell, or a star (`[[Smith.landing]]`, `[[Smith.afterScan]]`).

The parity side: `[[Smith.Decodes_T]]` (a scan in state B decodes the decremented set),
`[[Smith.Decodes_scanC]]` (the scan in state C too, because toggling the first bit is XOR
with `row n 0`, whose parity is at scan 0 only), `[[Smith.Decodes_transient]]` (the
skipped-cell scan after rule 5: the first bit is kept, so the result is `2 :: T tail`,
and toggling 1 before the decrement is toggling 0 after it), and
`[[Smith.Decodes_parity]]` (the first scan decides `0 in S`, which makes System 3's exit
state agree with System 4's toggle).

## The initial tape

`[[Smith.encSet]]` is Smith's block (`s42s0-3.pl`): the XOR of the rows of the elements
and of the last row (all 2s), plus the row `2^w - 2` when the first cell would be a 1;
the two extra rows have their parity at scans `2^w - 1` and `2^w - 2`, outside the
window, and make the first cell a 2 so that a star may stand in its place
(`[[Smith.firstTrue_encSet]]`, `[[Smith.Decodes_encSet]]`). `[[Smith.initAC]] w h S0 rest`
is the abstract configuration of a well-formed tape with the head on the first cell of
the first block in state A, left end `0^h 2 2 1`, closing 1; `[[Smith.rep3_init]]` is the
initial condition under `h + 3 <= 2^w`, no star last, every set element below `2^w`.

## Formal statements

```lean
theorem sys4_sys3_forwardSim (w : Nat) (rc : Closing) :
    ForwardSim (fueled system4Sys) (lsys sys3) (fun p c => Rep3 rc c p.1 w p.2)

theorem sys4_sys0_forwardSim (w : Nat) (rc : Closing) :
    ForwardSim (fueled system4Sys) (lsys sys0)
      (fun p c0 => ∃ c3, Rep3 rc c3 p.1 w p.2 ∧ c0 = phi2 (phi3 c3))

theorem conjecture3_finite (w h n : Nat) (S0 : List Int) (rest : List System4Elem)
    (hN : h + 3 ≤ 2 ^ w)
    (hwf : System4Config.WellFormed ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩)
    (hlast : (System4Elem.set S0 :: rest).getLast? ≠ some System4Elem.star)
    (hb : ∀ S, System4Elem.set S ∈ System4Elem.set S0 :: rest → ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ w)
    (hn : n ≤ h) (c' : System4Config)
    (hrun : System4.nSteps ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩ n = some c') :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ i, i < n → times i < times (i + 1)) ∧
      ∀ i, i ≤ n → ∃ ci c3i, System4.nSteps ⟨System4Elem.set S0 :: rest, 0, System4State.A⟩ i = some ci ∧
        lnSteps sys0 (phi2 (phi3 (initAC w h S0 rest).toL)) (times i) = some (phi2 (phi3 c3i)) ∧
        Rep3 Closing.one c3i ci w (h - i)
```

## Notes and caveats

- The width condition is `h + 3 <= 2^w`, weaker than Smith's `2^w >= 3f`, because the
  fuel, not `f`, bounds the scans; the link to `f` is made in chapter 08, where `2^w`
  must also exceed every set element.
- The head of the initial tape is on the first cell of the first block, not on Smith's
  leftmost 0. Started on its leftmost 0 in state A, the tape `0^m 2 2 1 ...` walks off
  its left end in three steps. This is why the finite form does not chain by plain
  concatenation (chapter 10).
- `Rep3` is stated on the System 3 tape and leaves the swap of the cells left of the
  head to `phi3` (chapter 07), so Smith's `s42s0-3.pl 3` output is `phi3` of `initAC`'s
  tape.
- T3 does not use loop-freeness: `Smith/Conjecture3.lean` used to import
  `Smith/LoopFree.lean` only for the generic run lemma `[[Smith.lnSteps_add]]`, which
  lives in `Smith/Lookahead.lean` since 2026-09-22.
- The D8 vectors of `Tests/SmithVectors.lean` run a six-step System 4 program through
  System 3 by `decide`.

## Depends on

`Smith.ParityBlocks`, `Smith.System3Runs`, `Smith.Conjecture3`, `Smith.Lookahead`,
chapter 05 (`System4.step`, `decr`, `xorInsert`), chapter 07 (`phi2`, `phi3`).
