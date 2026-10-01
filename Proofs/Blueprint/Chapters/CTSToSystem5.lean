/-
  Blueprint.Chapters.CTSToSystem5

  Chapter 4 of the blueprint: T1, from a cyclic tag system to System 5.
  Introduces the simulation calculus shared by every link (step systems,
  forward simulation, schedules, fuel), the doubling trick, the relation
  `Represents`, the two per-step lemmas, and the finite form of Smith's
  Conjecture 5 with its rule-counting and decoded variants.
-/

import Verso
import VersoManual
import VersoBlueprint
import Blueprint.Notebook
import TagSystem.Basic
import BiTM.XorMerge
import BiTM.System5
import BiTM.CTSToSystem5
import Smith.Simulation
import Smith.Doubling
import Smith.Represents
import Smith.System5Runs
import Smith.Conjecture5
import Smith.ConjectureFive

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Blueprint (notebook)

#doc (Manual) "T1: from a cyclic tag system to System 5" =>

%%%
tag := "cts-to-system5"
file := "cts-to-system5"
htmlSplit := .never
%%%

# Orientation

System 5 (p. 16-17, `system5.pl` p. 30-32) is Smith's first abstraction: a bag of
integers and a list of rules, each rule a list of integers. Every step decrements
the bag and increments the rules; when a 0 appears in the bag it is removed and the
first rule is XOR-merged into the bag ({bpref "BiTM.System5.step"}[`BiTM.System5.step`], {bpref "BiTM.xorMerge"}[`BiTM.xorMerge`]).
Smith's Conjecture 5 says a System 5 program emulates a cyclic tag system for an
arbitrary number of steps. The formal T1 is {bpref "Smith.conjecture5_finite"}[`Smith.conjecture5_finite`] and its
rule-counting variant {bpref "Smith.conjecture5_finite_exact"}[`Smith.conjecture5_finite_exact`].

This chapter also introduces the simulation calculus shared by every link.

:::group "simulation_calculus"
The emulation calculus of the Simulation module, shared by every link of the chain:
step systems, forward simulation, schedules and fuel.
:::

:::group "cts_to_system5"
T1: System 5 emulates a doubled cyclic tag system. The encoder, the relation, the
per-step lemmas and the finite form of Conjecture 5.
:::

# The simulation calculus

[`Smith/Simulation.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Simulation.lean). A step system is a partial step function, and `nSteps`
iterates it.

:::definition "Smith.StepSys" (parent := "simulation_calculus") (lean := "Smith.StepSys")
A step system on a type `S` is a partial step function `step : S → Option S`;
`none` marks the stuck states.
:::

:::definition "Smith.StepSys.nSteps" (parent := "simulation_calculus") (lean := "Smith.StepSys.nSteps")
`M.nSteps s n` iterates the step of a step system `M` ({uses "Smith.StepSys"}[])
`n` times from `s`; it is `none` as soon as one step is stuck.
:::

:::definition "Smith.ForwardSim" (parent := "simulation_calculus") (lean := "Smith.ForwardSim")
A forward simulation from a step system `MS` to a step system `MT`
({uses "Smith.StepSys"}[]) along a relation `R` between their states: whenever
`R s t` and `MS.step s = some s'`, there are `k` with `1 <= k` and `t'` with
`MT.nSteps t k = some t'` ({uses "Smith.StepSys.nSteps"}[]) and `R s' t'`. One
source step is matched by a run of at least one target step that re-establishes
the relation.
:::

:::lemma_ "Smith.ForwardSim_comp" (parent := "simulation_calculus") (lean := "Smith.ForwardSim_comp")
Forward simulations ({uses "Smith.ForwardSim"}[]) compose along relational
composition: from `ForwardSim MS MT R` and `ForwardSim MT MU R'` follows
`ForwardSim MS MU (Rcomp R R')`, where `Rcomp R R' s u` says that some `t` has
`R s t` and `R' t u`.
:::

:::proof "Smith.ForwardSim_comp"
The first simulation matches a source step by `k >= 1` steps of `MT`; the weak
lifting `Smith.ForwardSim_nSteps_weak` of the second matches those `k` steps by at
least `k` steps of `MU` that end in the composite relation.
:::

:::definition "Smith.IsSimSchedule" (parent := "simulation_calculus") (lean := "Smith.IsSimSchedule")
A schedule `times : Nat → Nat` witnessing that `MT` tracks `n` steps of `MS`
through `R` from `s` and `t`: `times 0 = 0`; `times j < times (j + 1)` for every
`j < n`; and for every `j <= n` both runs are defined, `MS.nSteps s j = some sj`
and `MT.nSteps t (times j) = some tj` ({uses "Smith.StepSys.nSteps"}[]), with
`R sj tj`. The target times are strictly increasing,
`times 0 = 0 < times 1 < ...`, with the relation holding at each.
:::

:::lemma_ "Smith.ForwardSim_nSteps" (parent := "simulation_calculus") (lean := "Smith.ForwardSim_nSteps")
A forward simulation ({uses "Smith.ForwardSim"}[]) lifts to a run of `n` source
steps: from `R s t` and `MS.nSteps s n = some s'` there is a schedule `times` with
`IsSimSchedule MS MT R s t n times` ({uses "Smith.IsSimSchedule"}[]).
:::

:::proof "Smith.ForwardSim_nSteps"
Induction on `n`: the schedule of the first `n` steps is extended by the `k >= 1`
target steps that the simulation supplies for the last source step.
:::

:::definition "Smith.fueled" (parent := "simulation_calculus") (lean := "Smith.fueled")
The fuelled system of a step system `M` ({uses "Smith.StepSys"}[]): its states are
pairs of a state of `M` and a step count, one step of `M` costs one unit of fuel,
and at fuel 0 the system is stuck. Budgets live in the source system through
`fueled`: `ForwardSim` quantifies over every source step, so a relation that
carries a finite budget cannot satisfy it once the budget runs out, the source
stepping on while the target is exhausted; `fueled` makes the budget part of the
source system instead of part of the relation.
:::

The relations of this chapter and of the two following ones (the
{ref "system5-to-system4"}[chapter on System 5 to System 4] and the
{ref "system4-to-system3"}[chapter on System 4 to System 3]) are indexed by the
remaining fuel.

The clause `1 <= k` forbids a target that stands still. It does not by itself make
a simulation meaningful: a relation that ignores the source is a `ForwardSim` for
any target that never gets stuck. The content of each link is in its relation,
which is a decoder graph or an encoding invariant, and the headline conclusions
are stated as decoder equalities. [`docs/PLAN.md`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/docs/PLAN.md) section 6 and the docstring of `ForwardSim` in
[`Smith/Simulation.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Simulation.lean) say this.

# Doubling

Smith emulates the doubled cyclic tag system (p. 18).

:::definition "Smith.dbl" (parent := "cts_to_system5") (lean := "Smith.dbl")
`dbl w` repeats every bit of a binary word `w`: `dbl (b :: w) = b :: b :: dbl w`.
:::

:::definition "Smith.double" (parent := "cts_to_system5") (lean := "Smith.double")
`double C` is the doubled cyclic tag system of `C` (a `TagSystem.CTS`): its
appendants are the doubled appendants ({uses "Smith.dbl"}[]), each followed by a
blank appendant, so it has twice as many appendants as `C`.
:::

:::definition "Smith.dblCfg" (parent := "cts_to_system5") (lean := "Smith.dblCfg")
`dblCfg c` doubles a cyclic tag configuration: the working string becomes
`dbl c.data` ({uses "Smith.dbl"}[]) and the phase becomes `2 * c.phase`.
:::

:::lemma_ "Smith.double_forwardSim_fueled" (parent := "cts_to_system5") (lean := "Smith.double_forwardSim_fueled")
One original step is two doubled steps: the relation `q = (dblCfg p.1, 2 * p.2)`
({uses "Smith.dblCfg"}[]) is a forward simulation ({uses "Smith.ForwardSim"}[])
from the fuelled ({uses "Smith.fueled"}[]) cyclic tag system `C` to the fuelled
doubled system `double C` ({uses "Smith.double"}[]). It is stated on `fueled`
systems so that one unit of original budget is two appendants.
:::

:::proof "Smith.double_forwardSim_fueled"
By `Smith.double_nSteps_two`: two steps of the doubled system from `dblCfg c` are
one step of `C` from `c`, the halting case included (the doubled working string is
empty exactly when the original one is). The functional relation is lifted to the
fuelled systems by `Smith.ForwardSim_fueled_of_fun`.
:::

# The relation

:::definition "Smith.gap" (parent := "cts_to_system5") (lean := "Smith.gap")
The gap between the two bag integers of one bit of the working string: 1 for a 0
bit and 2 for a 1 bit (p. 19).
:::

:::definition "Smith.pairsOf" (parent := "cts_to_system5") (lean := "Smith.pairsOf")
`pairsOf w a` is the bag of a working string `w` given the lower integer of each
bit: the `i`-th bit contributes `a i` and `a i + gap (w i)`
({uses "Smith.gap"}[]).
:::

:::definition "Smith.pairsAsc" (parent := "cts_to_system5") (lean := "Smith.pairsAsc")
`pairsAsc lo w a` says that the starts `a` are strictly increasing and leave room
for the gaps ({uses "Smith.gap"}[]): `lo` is below the first start, and the pair
of one bit ends strictly below the start of the next. It is `Bool`-valued, hence
decidable, and it is false when `w` and `a` differ in length.
:::

:::definition "Smith.appendantsFrom" (parent := "cts_to_system5") (lean := "Smith.appendantsFrom")
`appendantsFrom C phase n` lists the appendants a cyclic tag system `C` reads at
the `n` consecutive phases starting at `phase`.
:::

:::definition "Smith.ruleBlocks" (parent := "cts_to_system5") (lean := "Smith.ruleBlocks")
`ruleBlocks ws i` lays out the rule pairs of a list `ws` of (doubled) appendants
from the counter `i`, threading the counter: two System 5 rules per appendant, the
pair `encodePaired w i` of p. 19 read two bits at a time (a pair of 0s contributes
`i, i + 1` to the second rule and advances the counter by 4, a pair of 1s
contributes `i, i + 3` and advances it by 6), with `r1 = r2 + 2` elementwise. It
returns the rules and the counter after them.
:::

:::definition "Smith.Represents" (parent := "cts_to_system5") (lean := "Smith.Represents")
`Represents s C c budget` relates a System 5 configuration `s`
(`BiTM.System5Config`, a bag and a rule list) to a configuration `c` of a cyclic
tag system `C` with a budget of appendants. The bag clause: there are starts `a`
with `pairsAsc 0 c.data a` ({uses "Smith.pairsAsc"}[]) such that `s.bag` is a
permutation of `pairsOf c.data a` ({uses "Smith.pairsOf"}[]). The rules clause:
there are a counter `i` and a tail `rest` such that `x + 3 <= i` for every `x` in
the bag and `s.rules = (ruleBlocks (appendantsFrom C c.phase budget) i).1 ++ rest`
({uses "Smith.ruleBlocks"}[], {uses "Smith.appendantsFrom"}[]).
:::

This is Smith's "acceptable initial condition" of p. 19, not equality with the
encoder output. The bag is, up to permutation, a list of pairs `(x, x + gap b)`
with gap 1 for a 0 bit and 2 for a 1 bit, one pair per bit of the working string,
at strictly increasing starts. The rules begin with the canonical blocks of the
next `budget` appendants from the current phase, two rules per appendant with
`r1 = r2 + 2`, laid out from a counter `i` at least 3 above every bag element,
followed by anything (`rest`). Both clauses are relations, existential in the
starts, the counter and the tail, which is what lets the relation survive a
System 5 step. Doubling is a precondition: `encodePaired` reads an appendant two
bits at a time and drops a trailing odd bit, so the rules clause is meaningful
only for `C = double C0`, and every statement about `Represents` is over a doubled
system.

:::definition "BiTM.xorMerge" (parent := "cts_to_system5") (lean := "BiTM.xorMerge")
`xorMerge xs ys` merges two integer lists under parity semantics: each `y` of `ys`
in turn is removed from the bag if it is present and added if it is not.
:::

:::definition "BiTM.System5.step" (parent := "cts_to_system5") (lean := "BiTM.System5.step")
One step of System 5 (`system5.pl`, p. 30): every bag element is decremented and
every rule element incremented. If the bag or the rule list is empty the step is
`none`. If a 0 now appears in the bag, it is removed, and the first rule is
XOR-merged into the bag ({uses "BiTM.xorMerge"}[]) and dropped from the rule
list; otherwise the step is the pure decrement. `BiTM.System5.nSteps` iterates it.
:::

:::notebook "BiTM.System5.step"
:::

:::definition "BiTM.ctsToSystem5" (parent := "cts_to_system5") (lean := "BiTM.ctsToSystem5")
The encoder, Smith's `cy2s5.pl` (p. 28-29). `ctsToSystem5 C cfg N` has as bag the
working string of `cfg` doubled bit by bit into pairs from the counter 1, and as
rules `N` full cycles over the appendants of `C` starting at the appendant the
next step of `C` reads, each original appendant as a block of four System 5
rules (the two rules of its doubled appendant and the two empty rules of the
blank appendant that follows it).
:::

:::notebook "BiTM.ctsToSystem5"
:::

:::lemma_ "Smith.ctsToSystem5_represents" (parent := "cts_to_system5") (lean := "Smith.ctsToSystem5_represents")
The encoder output represents the doubled system: `ctsToSystem5 C cfg N`
({uses "BiTM.ctsToSystem5"}[]) satisfies `Represents`
({uses "Smith.Represents"}[]) with the doubled system `double C`
({uses "Smith.double"}[]), the doubled configuration `dblCfg cfg`
({uses "Smith.dblCfg"}[]) and the budget `2 * (C.appendants.length * N)`, the
number of appendants of the doubled system times the number of cycles, with
`rest = []`. Neither `1 <= N` nor a nonempty working string is needed.
:::

:::proof "Smith.ctsToSystem5_represents"
The bag of the encoder is `pairsOf (dbl cfg.data)` at the starts the Perl counter
produces from 1 ({uses "Smith.pairsOf"}[], {uses "Smith.pairsAsc"}[]), and its
rules are the canonical blocks of the rotated appendant list from the counter
after the working string plus 2 ({uses "Smith.ruleBlocks"}[],
{uses "Smith.appendantsFrom"}[]), a counter that is at least 3 above every bag
integer, with the empty tail.
:::

# The step lemmas

[`Smith/Conjecture5.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Conjecture5.lean) proves the per-step lemma in the two cases of the head
bit: one step of a doubled cyclic tag system is emulated by `x + gap b` steps of
System 5, where `x` is the smallest bag integer and `b` the leading bit of the
working string (p. 19-20). In both cases the first `x - 1` steps are pure
decrements and step `x` pops the first rule of the leading pair, which lands
above the whole bag and is therefore appended.

:::lemma_ "Smith.represents_step_false_time" (parent := "cts_to_system5") (lean := "Smith.represents_step_false_time")
The 0-head case. If `s` represents ({uses "Smith.Represents"}[]) the configuration
with working string `false :: w` at phase `p` with budget `n + 1`, then there are
`k` and a bag element `x >= 1` below every bag element with `k = x + 1`, and
`System5.nSteps s k` ({uses "BiTM.System5.step"}[]) is some `s'` that represents
the configuration with working string `w` at phase
`(p + 1) % C.appendants.length` with budget `n`, with exactly two rules fewer:
`s'.rules.length + 2 = s.rules.length`.
:::

:::proof "Smith.represents_step_false_time"
The bag's minimum `x` reaches 0 after `x` decrements and pops the first rule of
the leading pair, which lands above the whole bag and is appended by `xorMerge`
({uses "BiTM.xorMerge"}[]). The pair's second element pops the second rule one
step later, and `r1 = r2 + 2` ({uses "Smith.ruleBlocks"}[]) makes the two
contributions cancel under `xorMerge`, so the bag is the rest of the old bag
shifted down by `x + 1`, and the rule list is the remaining blocks in the same
canonical layout from the counter shifted up by `x + 1`. The decomposition of
`Represents` at a nonempty working string is `Smith.Represents_cons_decomp`; the
run up to and including the first pop is `Smith.System5_run_to_first_pop`.
:::

:::lemma_ "Smith.represents_step_true_time" (parent := "cts_to_system5") (lean := "Smith.represents_step_true_time")
The 1-head case. If the appendant of `C` at phase `p` is a doubled word `dbl a`
({uses "Smith.dbl"}[]) and `s` represents ({uses "Smith.Represents"}[]) the
configuration with working string `true :: w` at phase `p` with budget `n + 1`,
then there are `k` and a bag element `x >= 1` below every bag element with
`k = x + 2`, and `System5.nSteps s k` ({uses "BiTM.System5.step"}[]) is some `s'`
that represents the configuration with working string `w ++ dbl a` at phase
`(p + 1) % C.appendants.length` with budget `n`, again with
`s'.rules.length + 2 = s.rules.length`.
:::

:::proof "Smith.represents_step_true_time"
Pops at `x` and `x + 2`, with a pure decrement in between. The two pops deposit
the second rule's integers shifted by `x` and by `x + 2`; no two integers of a
second rule are exactly 2 apart (`Smith.encodePaired_snd_no_gap_two`), so the two
blocks are disjoint under `xorMerge` ({uses "BiTM.xorMerge"}[]) and both survive,
and together they are the canonical pairs of the doubled appendant
({uses "Smith.perm_append_shuffle"}[], {uses "Smith.encodeAppendant_snd_bag_perm"}[]).
The new bag is the old one minus the consumed pair, shifted down by `x + 2`,
followed by the pairs of the appended appendant, exactly as `CTS.step` appends
it; the threshold `x + 3 <= i` is met with equality.
:::

:::lemma_ "Smith.perm_append_shuffle" (parent := "cts_to_system5") (lean := "Smith.perm_append_shuffle")
Four blocks regroup: `(A ++ X) ++ (B ++ Y)` is a permutation of
`(A ++ B) ++ (X ++ Y)`. What the two pops deposit interleaved is what the
canonical layout lists in one piece.
:::

:::proof "Smith.perm_append_shuffle"
Associativity of `++` and `List.perm_append_comm` for the middle two blocks.
:::

:::lemma_ "Smith.encodeAppendant_snd_bag_perm" (parent := "cts_to_system5") (lean := "Smith.encodeAppendant_snd_bag_perm")
The two shifted copies of the second rule of an appendant's encoding
(`BiTM.encodeAppendant a i`), shifted by `m` and by `m + 2`, are together a
permutation of the bag the working-string encoder of {uses "BiTM.ctsToSystem5"}[]
builds for the word `a` from the counter `i + m` (`BiTM.ctsConfigToSystem5BagAux`).
:::

:::proof "Smith.encodeAppendant_snd_bag_perm"
Induction on the word `a`, unfolding `BiTM.encodeAppendant` and `BiTM.ctsConfigToSystem5BagAux` one symbol at a time; the two shifted copies of each pair land where the working-string encoder puts them, up to the order of the list.
:::

Both lemmas pin the step count (`k = x + gap b`) and, since milestone M6, also
return that exactly two rules were consumed.

:::lemma_ "Smith.double_currentAppendant_dbl" (parent := "cts_to_system5") (lean := "Smith.double_currentAppendant_dbl")
Every appendant of a doubled system `double C` ({uses "Smith.double"}[]) is a
doubled word `dbl a` ({uses "Smith.dbl"}[]): the doubled appendant of `C` at an
even phase, the blank appendant at an odd phase.
:::

:::proof "Smith.double_currentAppendant_dbl"
By the definition of `double`: its appendant list alternates the doubled appendants of `C` with blank appendants, and both are doubled words (`dbl a` and `dbl []`).
:::

:::lemma_ "Smith.represents_step_double" (parent := "cts_to_system5") (lean := "Smith.represents_step_double")
Both cases at once, over a doubled system. If `c.data` is nonempty and `s`
represents ({uses "Smith.Represents"}[]) `c` in `double C0`
({uses "Smith.double"}[]) with budget `n + 1`, then for some `k >= 1` the run
`System5.nSteps s k` ({uses "BiTM.System5.step"}[]) is some `s'`, the step
`(double C0).step c` is some `c'`, `s'` represents `c'` with budget `n`, and
`s'.rules.length + 2 = s.rules.length`.
:::

:::proof "Smith.represents_step_double"
Case on the head bit: {uses "Smith.represents_step_false_time"}[] for a 0 and
{uses "Smith.represents_step_true_time"}[] for a 1, whose hypothesis that the
appendant appended is `dbl a` for some `a` is supplied by
{uses "Smith.double_currentAppendant_dbl"}[], the one place the doubling is used.
The step count is `x + gap b` ({uses "Smith.gap"}[]), at least 1 since `x >= 1`.
:::

# Formal statements

:::theorem "Smith.cts_system5_forwardSim" (parent := "cts_to_system5") (lean := "Smith.cts_system5_forwardSim")
For every cyclic tag system `C0`, the relation between a fuelled
({uses "Smith.fueled"}[]) cyclic tag state `(c, f)` and a System 5 configuration
`s` that says `s` represents ({uses "Smith.Represents"}[]) the doubled
configuration `dblCfg c` ({uses "Smith.dblCfg"}[]) in `double C0`
({uses "Smith.double"}[]) with budget `2 * f` is a forward simulation
({uses "Smith.ForwardSim"}[]) from the fuelled system of `C0` to System 5
({uses "BiTM.System5.step"}[]).
:::

:::proof "Smith.cts_system5_forwardSim"
{uses "Smith.ForwardSim_comp"}[] of the doubling link
{uses "Smith.double_forwardSim_fueled"}[] with the forward simulation from the
fuelled doubled system into System 5 that {uses "Smith.represents_step_double"}[]
gives (`Smith.represents_forwardSim`, one unit of fuel per appendant of budget);
the composite relation is read in its unpacked form by `Smith.ForwardSim_congr`.
:::

:::theorem "Smith.conjecture5_finite" (parent := "cts_to_system5") (lean := "Smith.conjecture5_finite") (tags := "T1")
T1, the finite form of Conjecture 5. For a cyclic tag system `C0`, a configuration
`cfg`, a budget `N` and a run `C0.nSteps cfg n = some c'` of `n` steps with
`n <= C0.appendants.length * N`, there is a schedule `times` with `times 0 = 0`
and `times j < times (j + 1)` for every `j < n`, such that for every `j <= n`
there are the `j`-th cyclic tag configuration `cj` and a System 5 configuration
`sj` reached from `ctsToSystem5 C0 cfg N` ({uses "BiTM.ctsToSystem5"}[]) in
`times j` steps ({uses "BiTM.System5.step"}[]) with `sj` representing
({uses "Smith.Represents"}[]) `dblCfg cj` ({uses "Smith.dblCfg"}[]) in
`double C0` ({uses "Smith.double"}[]) with budget
`2 * (C0.appendants.length * N - j)`.
:::

:::proof "Smith.conjecture5_finite"
{uses "Smith.ForwardSim_nSteps"}[] applied to
{uses "Smith.cts_system5_forwardSim"}[] from the initial pair
`(cfg, C0.appendants.length * N)` and `ctsToSystem5 C0 cfg N`, related by
{uses "Smith.ctsToSystem5_represents"}[]. The run of the fuelled system is the run
of `C0` with the fuel counting down, so the schedule
({uses "Smith.IsSimSchedule"}[]) unpacks to the three clauses.
:::

:::definition "Smith.RepresentsExact" (parent := "cts_to_system5") (lean := "Smith.RepresentsExact")
`RepresentsExact s C c b` is `Represents s C c b` ({uses "Smith.Represents"}[])
together with `s.rules.length = 2 * b`: the rule list is exactly two rules per
appendant of budget long.
:::

:::theorem "Smith.conjecture5_finite_exact" (parent := "cts_to_system5") (lean := "Smith.conjecture5_finite_exact") (tags := "T1")
T1 with the rule count. Under the hypotheses of {bpref "Smith.conjecture5_finite"}[],
a schedule with the same three clauses and, at every scheduled time, in addition
`sj.rules.length = 2 * (2 * (C0.appendants.length * N - j))`, that is
`RepresentsExact` ({uses "Smith.RepresentsExact"}[]) at the remaining budget.
At the end of the budget the rule list is empty.
:::

:::proof "Smith.conjecture5_finite_exact"
The same lifting ({uses "Smith.ForwardSim_nSteps"}[]) of the exact relation. The
per-step lemma ({uses "Smith.represents_step_double"}[]) pops exactly two rules
per appendant, so `RepresentsExact` is a forward simulation from the fuelled
doubled system (`Smith.represents_exact_forwardSim`), composed with
{uses "Smith.double_forwardSim_fueled"}[] into
`Smith.cts_system5_exact_forwardSim`; and the encoder output has two rules per
appendant of budget (`Smith.ctsToSystem5_representsExact`, from
{uses "Smith.ctsToSystem5_represents"}[]).
:::

The exact variant is what T4 needs: at the end of the budget the rule list is
empty, which is the terminal event of the System 4 emulation (the
{ref "system5-to-system4"}[chapter on System 5 to System 4]). `Represents` alone
leaves the rules beyond the budget unconstrained.

:::definition "Smith.decodeBag" (parent := "cts_to_system5") (lean := "Smith.decodeBag")
The decoder of this link: sort the bag, then read it two integers at a time from
the bound 0, a gap of 1 for a 0 bit and of 2 for a 1 bit ({uses "Smith.gap"}[]);
`none` on an odd-length bag, on a start not above the previous pair, or on a gap
that is neither 1 nor 2.
:::

:::notebook "Smith.decodeBag"
:::

:::lemma_ "Smith.Represents_decode" (parent := "cts_to_system5") (lean := "Smith.Represents_decode")
A represented bag decodes to the working string it represents: from
`Represents s C c b` ({uses "Smith.Represents"}[]) follows
`decodeBag s.bag = some c.data` ({uses "Smith.decodeBag"}[]).
:::

:::proof "Smith.Represents_decode"
The bag is a permutation of `pairsOf c.data a` ({uses "Smith.pairsOf"}[]) for
starts with `pairsAsc 0 c.data a` ({uses "Smith.pairsAsc"}[]), a sorted list, so
sorting the bag returns it, and the pair reader inverts `pairsOf` on ascending
starts (`Smith.decodeBag_of_perm`).
:::

:::corollary "Smith.conjecture5_decode" (parent := "cts_to_system5") (lean := "Smith.conjecture5_decode") (tags := "T1")
T1 in decoded form. Under the hypotheses of {bpref "Smith.conjecture5_finite"}[],
a schedule with the same two clock clauses such that at every scheduled time
`decodeBag sj.bag = some (dbl cj.data)` ({uses "Smith.decodeBag"}[],
{uses "Smith.dbl"}[]): the System 5 bag decodes to the doubled working string of
the `j`-th cyclic tag configuration, with no existential over the pair starts
left in the conclusion.
:::

:::proof "Smith.conjecture5_decode"
{uses "Smith.conjecture5_finite"}[] and {uses "Smith.Represents_decode"}[] at
each scheduled time.
:::

`Represents` is functional in the working string: one bag represents at most one
string, whatever the cyclic tag system, the phase and the budget
(`Smith.Represents_data_unique`).

# Notes and caveats

- The times are pinned by pop events in the step lemmas (the run lasts
  `x + gap b` steps), but `conjecture5_finite` exposes only the existential
  schedule. The schedule is at least as fast as the source clock,
  `n <= times n` (`Smith.conjecture5_times_ge`), so it is not the degenerate
  constant one.
- The rules clause of `Represents` pins the canonical `cy2s5.pl` spacing
  (consecutive rule pairs laid down contiguously, the counter advanced by 4 per
  doubled 0 and 6 per doubled 1), so the Lean relation is a strict sub-relation
  of Smith's p. 19 condition, which allows any spacing of at least 3. It is
  contained in Smith's, since the canonical layout meets each of his bounds with
  equality; the containment is strict, and the hand-built p. 19 program is the
  witness (`Smith.pdf19`, in the relation at budget 2 and out of it at budget 3).
  The restriction is adequate for T1 because the canonical layout is what the
  encoder emits and what one System 5 step re-establishes; relaxing it is not
  needed downstream.
- `System5.step` is `none` when the bag or the rule list is empty. The review ran
  Smith's `system5.pl` and found the Lean and Perl runs agree step for step on
  the p. 31 example (36 iterations); the difference from Smith's prose about the
  terminal step is routed around on the System 4 side ({bpref "Smith.repS4_terminal"}[`Smith.repS4_terminal`],
  the {ref "system5-to-system4"}[chapter on System 5 to System 4]).
- The p. 29 program (`cy2s5.pl 3 01 1 10`) is run through both step cases by
  `decide` in [`Smith/Conjecture5.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Smith/Conjecture5.lean) and [`Vectors/SmithVectors.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/Vectors/SmithVectors.lean) (D1 to D3).

# Depends on

The modules of this chapter are `Smith.Simulation`, `Smith.Doubling`,
{bpref "Smith.Represents"}[`Smith.Represents`], `Smith.System5Runs`, `Smith.Conjecture5`,
`Smith.ConjectureFive`, `BiTM.System5`, `BiTM.CTSToSystem5`, `BiTM.XorMerge` and
`TagSystem.Basic`. The cyclic tag systems themselves (`TagSystem.CTS`,
`TagSystem.CTSConfig`, `TagSystem.CTS.step`, `TagSystem.CTS.nSteps`) are those of
[`TagSystem/Basic.lean`](https://github.com/WolframInstitute/TuringMachine/blob/lean-proofs/Proofs/TagSystem/Basic.lean), the target of the {ref "tm-to-cts"}[chapter on the machine reduction].
Nothing in this chapter depends on a node of another chapter. Downstream,
{bpref "Smith.conjecture4_cts"}[`Smith.conjecture4_cts`] of the chapter on System 5 to System 4 consumes
{bpref "Smith.conjecture5_finite"}[`Smith.conjecture5_finite`], {bpref "Smith.system4_emulation"}[`Smith.system4_emulation`] and
{bpref "Smith.conjecture0_finite"}[`Smith.conjecture0_finite`] of the chapter on Conjecture 0 consume
{bpref "Smith.conjecture5_finite_exact"}[`Smith.conjecture5_finite_exact`], and the decoders of the chapters on Conjecture 0
and on the infinite form ({bpref "Smith.decodeW23"}[`Smith.decodeW23`], {bpref "Smith.decodeTM"}[`Smith.decodeTM`]) end in
{bpref "Smith.decodeBag"}[`Smith.decodeBag`].
