# 07. T3, second half, and T5: Systems 3, 2, 1, 0 and loop-freeness

## Orientation

Smith's Conjectures 0 to 3 differ only in the machine (TM23Proof.pdf p. 3-5). System 1
is System 0 with the `B2` rule split by the right neighbour; System 2 adds a state C
that is state B with the active cell swapped; System 3 is System 2 with every cell left
of the head swapped. `Smith/Systems123.lean` proves each relabeling as a forward
simulation in the direction the chain needs, from the higher system to the lower.
`Smith/LoopFree.lean` and `Smith/Wolfram23Bridge.lean` prove Smith's loop-freeness
argument (p. 21-22), T5. Loop-freeness is proved but not used by the chain: the
schedules of chapters 04 to 06 are explicit, so the run of each finite initial
condition is known to end without an appeal to it.

## The relabelings

`[[Smith.sw]]` swaps 1 and 2 and fixes 0.

```lean
def phi2 : LConfig → LConfig
  | ⟨L, a, R, C⟩ => ⟨L, sw a, R, B⟩
  | c => c

def phi3 : LConfig → LConfig
  | ⟨L, a, R, A⟩ => ⟨L.map sw, sw a, R, A⟩
  | ⟨L, a, R, st⟩ => ⟨L.map sw, a, R, st⟩
```

`[[Smith.sys1_sys0_forwardSim]]` is on the identity relation: one System 1 step is one
System 0 step, or three for `B21` and `B22` (`[[Smith.sys0_B2_three]]`: `B2 -> A0>`, then
`A1 -> A2<` or `A2 -> A1<`, then `A0 -> B1>`). `[[Smith.sys2_sys1_forwardSim]]` is along
`phi2`, one step to one step (`[[Smith.phi2_step]]`:
`lstep sys1 (phi2 c) = (lstep sys2 c).map phi2`), and `[[Smith.sys3_sys2_forwardSim]]`
along `phi3` (`[[Smith.phi3_step]]`). The composite is what chapter 06 composes with:

```lean
theorem sys3_sys0_forwardSim :
    ForwardSim (lsys sys3) (lsys sys0) (fun c c' => c' = phi2 (phi3 c))
```

The correspondences are also checked by `decide` on every three-cell tape, with
negative instances showing that neither relabeling is the identity. `phi2` is
many-to-one (System 1 has no state C), so these are simulations, not bisimulations; the
other direction is not needed.

## Loop-freeness (T5)

Smith's argument (p. 21-22), made in System 1. `[[Smith.V]] c` is the sum of the
positions, counted from 1, of the 0s of the tape; `[[Smith.W]] c` is `V c` without the
head cell in state A (the `A0 -> B1>` step that must follow spends it); `[[Smith.phase]] c`
is the head position plus the tape length in state A, and the number of cells to the
right in state B.

```lean
theorem sys1_measure (c c' : LConfig) (hst : c.state ≠ C) (h : lstep sys1 c = some c') :
    (W c' < W c ∨ (W c' = W c ∧ phase c' < phase c)) ∧ c'.state ≠ C
```

Every System 1 step from a configuration in state A or B decreases `(W, phase)`
lexicographically, checked rule by rule after splitting on both neighbours (`B20`
raises `V` by the head position and lowers `W` by 1, which is Smith's "decreases to a
lower value than the value it increased from"). `[[Smith.run_ends_of_measure]]` turns
such a measure into the end of the run, so `[[Smith.sys1_leaves]]`; System 0 is stuck
wherever System 1 is (`[[Smith.sys1_none_sys0]]`), and `[[Smith.run_ends_of_sim]]`
transfers along the 1-or-3 correspondence:

```lean
theorem sys0_leaves (c : LConfig) (hst : c.state ≠ C) : ∃ n, lnSteps sys0 c n = none

theorem sys0_not_periodic (c : LConfig) (hst : c.state ≠ C) (p : Nat) (hp : 1 ≤ p) :
    lnSteps sys0 c p ≠ some c
```

Through the bridge of chapter 02:

```lean
theorem wolfram23_leaves (cfg : BiTM.Config) (hv : IsValidWolfram23Cfg cfg) :
    ∃ n cfg', BiTM.nSteps wolfram23 cfg n = some cfg' ∧ biSize cfg' = biSize cfg + 1

theorem wolfram23_not_periodic (cfg : BiTM.Config) (hv : IsValidWolfram23Cfg cfg) (p : Nat)
    (hp : 1 ≤ p) : BiTM.nSteps wolfram23 cfg p ≠ some cfg
```

From every valid configuration the wolfram23 run reaches a configuration with one more
explicit cell, that is, the head leaves the initial finite tape; and no valid
configuration is periodic, since `biSize` never decreases along a run. This is the
formal counterpart of the refutations in `docs/REVIEW.md` section 4.1 (the old
step-faithful predicates needed a periodic configuration) and settles, in Smith's
direction, what the old code base treated as open.

## Notes and caveats

- T5 is standalone. `grep` shows `sys0_leaves`, `wolfram23_leaves` and
  `wolfram23_not_periodic` are referenced only in `Smith/LoopFree.lean` and
  `Smith/Wolfram23Bridge.lean`. `docs/PLAN.md` section 2 used to say T6 "follows from
  T4 and T5"; the infinite form (chapter 10) does not use T5, because it has explicit
  exit times. Smith needs T5 because his Conjecture 0 does not come with a schedule.
- The exit time is existential (bounded by the measure); no closed form is stated.
- `Smith/Conjecture3.lean` used to import `LoopFree` only for `[[Smith.lnSteps_add]]`;
  the lemma lives in `Smith/Lookahead.lean` since 2026-09-22 and the import is gone
  (chapter 06).

## Depends on

`Smith.Lookahead`, `Smith.Systems123`, `Smith.LoopFree`, `Smith.Wolfram23Bridge`,
`BiTM.Wolfram23Valid`.
