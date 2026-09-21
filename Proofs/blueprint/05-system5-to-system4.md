# 05. T2: from System 5 to System 4

## Orientation

System 4 (TM23Proof.pdf p. 16-18, `system4.pl` p. 33-35) is a tape of elements, each a
finite set of integers or a star, with a head and three states. Five rules
(`[[BiTM.System4.step]]`): in state A on a set the head moves left, turning round into
state B at the left end (rule 1); in state A on a star the star is deleted and the state
becomes B (rule 2); in state B or C on a set the set is decremented, the 0 removed and
the state toggled if it was there, and the head moves right (rule 3); in state B on a
star the star is deleted and the head moves left into state A (rule 4); in state C on a
star the head moves onto the set to its right and toggles 1 in it (rule 5). Smith's
Conjecture 4 says a System 4 tape emulates a System 5 program. The formal T2 is
`[[Smith.conjecture4_finite]]`.

## The encoder and the relation

`[[BiTM.system5ToSystem4]] s f` is `s52s4.pl`: the bag as one set of the even integers
`2e - 2` (`[[BiTM.encodeBag]]`), then `f` pairs (star, empty set), then one block per
rule: star, the rule set `0..3f` toggled at `2k + f + 3` for each entry `k`, `2f` pairs,
star, the all-integers set `0..3f`, `2f - 2` pairs (`[[Smith.encBlock]]`,
`[[Smith.encRuleSet]]`, `[[Smith.rulePos]]`). `docs/REVIEW.md` section 4.3 records two
stars the old transcription had dropped; `[[Smith.system5ToSystem4_eq]]` is the encoder
as the case `t = 0` of the parametrized blocks.

```lean
def RepS4 (c : System4Config) (s : System5Config) (f j h : Nat) : Prop :=
  ∃ K : List (List Int),
    K ≠ [] ∧
    (∀ S ∈ K, S.Nodup ∧ ∀ x ∈ S, 0 ≤ x) ∧
    c = ⟨sets K ++ starredEmptyPairs (f - 2 * j) ++ encBlocks s.rules f (2 * j), 0, A⟩ ∧
    2 * j + 2 * h < f ∧
    (∀ x : Int, 0 ≤ x → x + 2 * j + 2 < 2 * f →
      parMem x K = decide (∃ e ∈ s.bag, x = 2 * e - 2)) ∧
    s.bag.Nodup ∧
    (∀ e ∈ s.bag, 1 ≤ e ∧ e + j < f) ∧
    (∀ r ∈ s.rules, r.Nodup ∧ ∀ k ∈ r, 0 ≤ k ∧ k + j + 2 * h < f)
```

This is Smith's "condition during execution" of p. 17 after `j` System 5 steps with
`h` steps of budget left: the head is at the left end in state A; the tape is a block
of adjacent sets `K` (the bag "conglomerate", whose symmetric difference is what
counts, `[[Smith.parMem]]`), then `f - 2j` star/empty pairs, then the rule blocks at
running parameter `t = 2j`. The parity set of `K` agrees with the encoded bag below the
band `2f - 2j - 2`; above the band it is unconstrained, because the all-integers sets
leave debris there that never reaches the head within the budget. The budget bounds
the rule entries so that every integer popped into the bag stays under the band.

## The two step cases

`Smith/System4Runs.lean` proves the runs. The focus lemmas (`[[Smith.step_setA]]`,
`[[Smith.step_setB]]`, `[[Smith.step_starA]]`, `[[Smith.step_starB]]`, `[[Smith.step_starC]]`
and the rest) state each rule on a tape `L ++ e :: R` with the head on `e`. On top:
`[[Smith.sweep]]` (state B or C across a block of adjacent sets decrements them all and
the state flips by the parity membership of 0), `[[Smith.moveLeft]]` and `[[Smith.turn]]`
(state A back to the left end), `[[Smith.cPhase]]` (state C across star/empty pairs
toggles 1 into each empty set).

A System 5 step without a pop (1 not in the bag) is a D-step (`[[Smith.dStep]]`,
`[[Smith.repS4_dStep]]`): two sweeps over the conglomerate, one star removed and one empty
set merged into it, `t` up by 2. A step with a pop is a P-step (`[[Smith.repS4_pStep]]`):
the sweep leaves the conglomerate in state C, the head crosses the pairs toggling 1s,
enters the rule block, and two nested loops (`[[Smith.preLoop]]`, `[[Smith.loopIter]]`,
`[[Smith.loopRun]]`, `[[Smith.finalPass]]`, `[[Smith.popPhase]]`) sweep the rule set and the
all-integers set back into the conglomerate; the XOR of the two cancels everything
except the entries of the rule at their shifted positions, which is `xorMerge` of the
rule into the bag. The relation is re-established with `j + 1`.

When the rules are exhausted and 1 is in the bag, the pop attempt finds no rule block:
the head sweeps the conglomerate in state C, crosses the remaining pairs, and leaves the
tape to the right in state C (`[[Smith.repS4_exit]]`). This is the exit that the finite
form of Conjecture 0 needs (chapter 08).

## Formal statements

```lean
theorem repS4_forwardSim (f h0 : Nat) :
    ForwardSim (fueled system5Sys) system4Sys
      (fun p c => p.2 ≤ h0 ∧ RepS4 c p.1 f (h0 - p.2) p.2)

theorem conjecture4_finite (s : System5Config) (f h n : Nat)
    (hbag : s.bag.Nodup) (hbag1 : ∀ e ∈ s.bag, 1 ≤ e ∧ e < f)
    (hrules : ∀ r ∈ s.rules, r.Nodup ∧ ∀ k ∈ r, 0 ≤ k ∧ k + 2 * h < f)
    (hf : 2 * h < f) (hn : n ≤ h) (s' : System5Config) (hrun : System5.nSteps s n = some s') :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ i, i < n → times i < times (i + 1)) ∧
      ∀ i, i ≤ n → ∃ si ci, System5.nSteps s i = some si ∧
        System4.nSteps (system5ToSystem4 s f) (times i) = some ci ∧ RepS4 ci si f i (h - i)

theorem repS4_exit (c : System4Config) (s : System5Config) (f j h : Nat)
    (hrep : RepS4 c s f j h) (hr : s.rules = []) (h1 : (1 : Int) ∈ s.bag) (hjf : j + 1 < f) :
    ∃ k c', System4.nSteps c k = some c' ∧ c'.state = C ∧
      c'.active = c'.elems.length ∧ System4.step c' = none
```

The decoder of the link reads the parity set of the leading conglomerate below a band
and maps `x` to `x / 2 + 1`, returning `none` if an odd integer is set:

```lean
def decodeS4 (c : System4Config) (b : Nat) : Option (List Int) :=
  let xs := ((List.range b).map (fun (i : Nat) => (i : Int))).filter
    (fun x => parMem x (leadSets c.elems))
  if xs.all (fun x => x % 2 = 0) then some (xs.map (fun x => x / 2 + 1)) else none

theorem RepS4_decode (c : System4Config) (s : System5Config) (f j h : Nat)
    (hrep : RepS4 c s f j h) :
    ∃ l, decodeS4 c (2 * f - 2 * j - 2) = some l ∧ l.Perm s.bag
```

`[[Smith.conjecture4_cts]]` and `[[Smith.conjecture4_cts_exists_f]]` compose T1 and T2:
the System 4 tape of the `cy2s5.pl` output tracks the cyclic tag run for every large
enough `f`.

## Notes and caveats

- The finish-time bound. Smith's T2 (p. 20-21) computes `f` from an a priori bound
  `finishTime P <= 3^(n-1) M` on the System 5 run. That bound is not formalized:
  `conjecture4_finite` takes the System 5 run length `h` as its budget and requires
  `k + 2h < f` on the rule entries and `2h < f`, a differently shaped condition.
  `docs/PLAN.md` section 2 still advertises `finishTime`; the M3 notes say it is left
  undone. This is one of the ingredients of a closed-form initial condition (chapter 11).
- Two branches of `System4.step` differ from `system4.pl`: rule 5 with the star last
  returns `none` (the Perl autovivifies a set past the end), and rule 4 at index 0
  returns `none` (the Perl reads the last element). Neither is reachable from an
  encoder tape: `[[BiTM.System4Config.WellFormed]]` (leftmost element a set, no adjacent
  stars, sets `Nodup`) is preserved by every step and rules out both.
- The D4/D5/D7 vectors of `Tests/SmithVectors.lean` run the p. 33 tape for 1904 System 4
  steps and read the System 5 bag off it with `decodeS4` at the scheduled times, with
  negative instances at unscheduled times.

## Depends on

`BiTM.System4`, `BiTM.System5ToSystem4`, `Smith.System4Runs`, `Smith.Conjecture4`,
chapter 04.
