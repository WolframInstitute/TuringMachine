# 04. T1: from a cyclic tag system to System 5

## Orientation

System 5 (TM23Proof.pdf p. 16-17, `system5.pl` p. 30-32) is Smith's first abstraction:
a bag of integers and a list of rules, each rule a list of integers. Every step
decrements the bag and increments the rules; when a 0 appears in the bag it is removed
and the first rule is XOR-merged into the bag (`[[BiTM.System5.step]]`,
`[[BiTM.xorMerge]]`). Smith's Conjecture 5 says a System 5 program emulates a cyclic
tag system for an arbitrary number of steps. The formal T1 is `[[Smith.conjecture5_finite]]`
and its rule-counting variant `[[Smith.conjecture5_finite_exact]]`.

This chapter also introduces the simulation calculus shared by every link.

## The simulation calculus

`Smith/Simulation.lean`. A step system `[[Smith.StepSys]]` is a partial step function;
`[[Smith.StepSys.nSteps]]` iterates it. A forward simulation is

```lean
def ForwardSim {S : Type u} {T : Type v}
    (MS : StepSys S) (MT : StepSys T) (R : S → T → Prop) : Prop :=
  ∀ s t, R s t → ∀ s', MS.step s = some s' →
    ∃ k, 1 ≤ k ∧ ∃ t', MT.nSteps t k = some t' ∧ R s' t'
```

`[[Smith.ForwardSim_comp]]` composes along relational composition, and
`[[Smith.ForwardSim_nSteps]]` lifts to a run of `n` source steps, producing an
`[[Smith.IsSimSchedule]]`: strictly increasing target times `times 0 = 0 < times 1 < ...`
with the relation holding at each. Budgets live in the source system through
`[[Smith.fueled]]`, a state paired with a step count that decreases by one per step and
is stuck at zero; the relations of chapters 04 to 06 are indexed by the remaining fuel.

The clause `1 <= k` forbids a target that stands still. It does not by itself make a
simulation meaningful: a relation that ignores the source is a `ForwardSim` for any
target that never gets stuck. The content of each link is in its relation, which is a
decoder graph or an encoding invariant, and the headline conclusions are stated as
decoder equalities. `docs/PLAN.md` section 6 says this; the Simulation header should
say it too (chapter 11).

## Doubling

Smith emulates the doubled cyclic tag system: `[[Smith.double]] C` has the doubled
appendants (`[[Smith.dbl]]` repeats every bit), and `[[Smith.dblCfg]]` doubles the word
and the phase. One original step is two doubled steps
(`[[Smith.double_forwardSim_fueled]]`, on `fueled` systems so that one unit of original
budget is two appendants).

## The relation

```lean
def Represents (s : System5Config) (C : CTS) (c : CTSConfig) (budget : Nat) : Prop :=
  (∃ a : List Int, pairsAsc 0 c.data a = true ∧ s.bag.Perm (pairsOf c.data a)) ∧
  (∃ (i : Int) (rest : List (List Int)),
      (∀ x ∈ s.bag, x + 3 ≤ i) ∧
      s.rules = (ruleBlocks (appendantsFrom C c.phase budget) i).1 ++ rest)
```

This is Smith's "acceptable initial condition" of p. 19, not equality with the encoder
output. The bag is, up to permutation, a list of pairs `(x, x + gap b)` with gap 1 for a
0 bit and 2 for a 1 bit, one pair per bit of the working string, at strictly increasing
starts (`[[Smith.pairsOf]]`, `[[Smith.pairsAsc]]`, `[[Smith.gap]]`). The rules begin with the
canonical blocks of the next `budget` appendants from the current phase
(`[[Smith.ruleBlocks]]`, `[[Smith.appendantsFrom]]`, two rules per appendant with
`r1 = r2 + 2`), laid out from a counter `i` at least 3 above every bag element, followed
by anything (`rest`). The encoder `[[BiTM.ctsToSystem5]]` (Smith's `cy2s5.pl`, p. 28-29)
satisfies it with `rest = []` (`[[Smith.ctsToSystem5_represents]]`).

## The step lemmas

`Smith/Conjecture5.lean` proves the per-step lemma in the two cases of the head bit. For
a 0 head (`[[Smith.represents_step_false_time]]`): the bag's minimum `x` reaches 0 after
`x` decrements, pops the first rule, the pair's second element pops the second rule one
step later, and `r1 = r2 + 2` makes the two contributions cancel under `xorMerge`, so
the bag is the rest of the old bag shifted down by `x + 1`. For a 1 head
(`[[Smith.represents_step_true_time]]`): pops at `x` and `x + 2`; the two pops deposit the
second rule's integers shifted by `x` and by `x + 2`, which together are the canonical
pairs of the doubled appendant (`[[Smith.perm_append_shuffle]]`,
`[[Smith.encodeAppendant_snd_bag_perm]]`). Both lemmas pin the step count
(`k = x + gap b`) and, since milestone M6, also return that exactly two rules were
consumed. `[[Smith.represents_step_double]]` packages both cases for a doubled system,
where the appendant appended is `dbl a` for some `a`
(`[[Smith.double_currentAppendant_dbl]]`), the one place the doubling is used.

## Formal statements

```lean
theorem cts_system5_forwardSim (C0 : CTS) :
    ForwardSim (fueled (ctsSys C0)) system5Sys
      (fun p s => Represents s (double C0) (dblCfg p.1) (2 * p.2))

theorem conjecture5_finite (C0 : CTS) (cfg : CTSConfig) (N n : Nat)
    (hn : n ≤ C0.appendants.length * N) (c' : CTSConfig)
    (hrun : C0.nSteps cfg n = some c') :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ j, j < n → times j < times (j + 1)) ∧
      ∀ j, j ≤ n → ∃ cj sj, C0.nSteps cfg j = some cj ∧
        System5.nSteps (ctsToSystem5 C0 cfg N) (times j) = some sj ∧
        Represents sj (double C0) (dblCfg cj)
          (2 * (C0.appendants.length * N - j))

def RepresentsExact (s : System5Config) (C : CTS) (c : CTSConfig) (b : Nat) : Prop :=
  Represents s C c b ∧ s.rules.length = 2 * b

theorem conjecture5_finite_exact (C0 : CTS) (cfg : CTSConfig) (N n : Nat)
    (hn : n ≤ C0.appendants.length * N) (c' : CTSConfig)
    (hrun : C0.nSteps cfg n = some c') :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ j, j < n → times j < times (j + 1)) ∧
      ∀ j, j ≤ n → ∃ cj sj, C0.nSteps cfg j = some cj ∧
        System5.nSteps (ctsToSystem5 C0 cfg N) (times j) = some sj ∧
        Represents sj (double C0) (dblCfg cj) (2 * (C0.appendants.length * N - j)) ∧
        sj.rules.length = 2 * (2 * (C0.appendants.length * N - j))
```

The exact variant is what T4 needs: at the end of the budget the rule list is empty,
which is the terminal event of the System 4 emulation (chapter 05). `Represents` alone
leaves the rules beyond the budget unconstrained.

The decoder of this link is `[[Smith.decodeBag]]` (sort the bag, read the gaps as bits);
`[[Smith.Represents_decode]]` says it returns the working string, and
`[[Smith.conjecture5_decode]]` is T1 in decoded form. `Represents` is functional in the
working string: one bag represents at most one string.

## Notes and caveats

- The times are pinned by pop events in the step lemmas (the run lasts `x + gap b`
  steps), but `conjecture5_finite` exposes only the existential schedule.
- `System5.step` is `none` when the bag or the rule list is empty. The review ran
  Smith's `system5.pl` and found the Lean and Perl runs agree step for step on the p. 31
  example (36 iterations); the difference from Smith's prose about the terminal step is
  routed around on the System 4 side (`[[Smith.repS4_terminal]]`, chapter 05).
- The p. 29 program (`cy2s5.pl 3 01 1 10`) is run through both step cases by `decide`
  in `Smith/Conjecture5.lean` and `Tests/SmithVectors.lean` (D1 to D3).

## Depends on

`Smith.Simulation`, `Smith.Doubling`, `Smith.Represents`, `Smith.System5Runs`,
`Smith.Conjecture5`, `Smith.ConjectureFive`, `BiTM.System5`, `BiTM.CTSToSystem5`,
`BiTM.XorMerge`, `TagSystem.Basic`.
