# Plan: finishing the Lean proof of Wolfram (2,3) universality

Date: 2026-09-15. Companion to REVIEW.md. Status: all decisions in section 8 resolved on
2026-09-15; M0 done 2026-09-15 (see "M0 notes" in section 5); M1 done 2026-09-15 (see "M1
notes" in section 5); M2 is next.

## 1. Where we are

- Everything builds (10 s), but the four sorries sit under false statements and the proved
  universality theorem is a tautology. See REVIEW.md sections 1 and 4.
- Faithful and reusable: `wolfram23` (System 0), Cook's tag -> CTS, `IsValidWolfram23Cfg` and
  non-halting, `System5.step`, the cy2s5 encoder `ctsToSystem5`, `System4.step`, `XorMerge`, the
  false-head 4-step lemma, small cores of the halting libraries.
- Broken definitions: `system5ToSystem4` (two stars missing per rule), `System1`/`GeneralizedTM`
  (cannot read the right neighbour), `ctsToSystem5` ignores the CTS phase.
- Missing entirely: Systems 1-3, System 4 -> 3 (Lemmas 0-1, parity scans), System 5 -> 4 emulation,
  loop-freeness, exit condition, the finite-form Conjecture 0, the infinite concatenation.
- Three obstructions any target must respect: (a) wolfram23 never halts from valid configs, so
  halting-based predicates are either vacuous or unsatisfiable; (b) wolfram23 has no periodic
  orbits, so a time-independent step-faithful `encode` function is impossible for CTSs with
  cycles; (c) the encoded System 5 run always terminates (finite rule budget), so no single finite
  initial condition mirrors an infinite CTS run step for step.

## 2. Target theorems

Formalize what Smith proves, in the order he proves it.

T1 (Conjecture 5, finite form). For every two-colour CTS `C`, nonempty working string `w0`, and
budget `N`, the System 5 program `P := ctsToSystem5 (double C) w0 N` (plus, if needed, the large
integers) emulates `C` for `N` steps: there are strictly increasing times `t_0 = 0 < t_1 < ... < t_N`
such that for every `k <= N` the System 5 configuration after `t_k` steps stands in the relation
`Represents` to the `k`-th CTS configuration, where

    Represents (s : System5Config) (c : CTSConfig) (budget : Nat) : Prop :=
      exists (a : List Int), a strictly increasing, a.length = 2 * c.data.length,
        s.bag ~ (pairs of a with gap 1 for bit 0 and gap 2 for bit 1, after doubling) /\
        s.rules = encoding of the appendants of C from phase c.phase onward, at least
                  `budget` groups long, every second rule >= max bag + 3, first rule = second + 2.

`~` is `List.Perm` (or equality of sorted lists, or `Multiset` equality if Mathlib is adopted).
This is the p.19 "acceptable initial condition" relation. It is not equality with the canonical
encoder output, which is why the current statements are false. Times are fixed by pop events
("immediately after the 4k-th rule pop"), not by an existential over arbitrary `m`.

T2 (Conjecture 5 implies 4). For every well-formed System 5 program `P` and every `f` with
`f >= 3` and `f >= 2 * finishTime P`, the System 4 tape `system5ToSystem4 P f` (with the two stars
restored) emulates the System 5 run of `P`: at each return of the head to the leftmost set in state
A after a star removal, the leftmost conglomerate decodes (x -> x/2 + 1 on even elements, ignoring
the band above f-3) to the current System 5 bag and the remaining sets encode the remaining rules
shifted by the running parameter `t`; and when `P` attempts to pop a nonexistent rule the head
leaves the defined tape in state C. Includes the finish-time bound `finishTime P <= 3^(n-1) * M`.

T3 (Conjecture 4 implies 3; Conjectures 3 = 2 = 1 = 0). System 4 -> System 3 via parity blocks of
width 2^w with `2^w >= 3f` (Lemma 0, Lemma 1, Corollary 1 methods), then the relabelings
System 3 -> 2 -> 1 -> 0 as simulations with a 1-or-3 step count. Requires a machine type that reads
the active cell and its right neighbour.

T4 (Conjecture 0, finite form, the headline). For every two-colour CTS `C`, working string `w0`
and budget `N` there is a finite tape segment `IC C w0 N : List (Fin 3)` such that the wolfram23
run started on its leftmost cell in state A (i) never visits a cell left of the segment, (ii) has a
computable decoding of the first `N` CTS configurations at explicit times, and (iii) eventually
has the head on the first cell right of the segment in state A, before which (i) and (ii) hold.
Vacuity guard: the decoding is a partial function from tape windows to CTS configurations that
returns `none` unless the window is a valid encoding, and the time sequence is strictly increasing.

T5 (loop-freeness). No wolfram23 configuration confined to a finite tape interval is periodic;
equivalently the head leaves every finite interval. Proof via System 1 and the zero-position sum
(PDF p.21-22). This is also the formal refutation of the current step-faithful predicates.

T6 (Conjecture 0, infinite form; optional). With an infinite tape type (`Int -> Fin 3` or the
zipper plus a background generator), the concatenation `IC C w0 1 ++ IC C w0 2 ++ ...` emulates
`C` forever in Smith's sense: for every `k` the run at some time has the head at the start of block
`k` in state A and then reproduces the first `k` CTS configurations. Follows from T4 and T5.

T7 (universality of cyclic tag systems, self-contained). For every well-formed Turing machine `M`
(states and symbols in range, transitions in range) and configuration `c`, there is a 2-tag system
and an initial tag word such that the tag run simulates `M`'s run step for step with a decoder
(genuine Cocke-Minsky construction: tape halves as unary blocks, doubling and halving productions;
Minsky 1967 Thm 14.6-1, or the smaller variant of Cook 2004 section 2.1), composed with the
already proved `tagToCTS_simulation` (one tag step = 2k CTS steps) to give a CTS that simulates `M`
with a decoder. Halting of `M` is read off the decoded configuration, so no halting convention
(HaltsEmpty, ctsHalted, state 0) has to be propagated.

T8 (headline). For every well-formed TM `M`, configuration `c`, and budget `N`, there is a finite
wolfram23 initial condition from which the first `N` configurations of `M` can be decoded at
explicit times, with the exit condition of T4. This is T4 composed with T7. It is universality in
the literal sense, with no informal appeal to the literature: `#print axioms` must show only
`propext`, `Classical.choice`, `Quot.sound`. T4 alone (CTS emulation) is exactly Smith's theorem
and remains an intermediate result; it must not be named "universal".

The current "faithful Cocke-Minsky" theorem (`cocke_minsky_reduces_faithful_universal`) is a
halting-oracle encoding and is not a step toward T7; it goes to the archive.

## 3. Proof architecture, link by link

Emulation predicate (one definition, reused for every link): for step functions `stepS`, `stepT`
and a relation `R`,

    ForwardSim R := forall s t, R s t -> forall s', stepS s = some s' ->
                    exists k >= 1, exists t', nStepsT t k = some t' /\ R s' t'

with composition `ForwardSim R -> ForwardSim R' -> ForwardSim (R ; R')` and a lifting lemma to
`n` source steps. Relations, not encoders: a relation may relate one source configuration to many
target configurations (different offsets, different remaining budgets), which dissolves obstruction
(b). Budgets live inside `R` (remaining rule groups, remaining f-t slack), which dissolves (c).

Link A: CTS -> doubled CTS. `Doubling.lean`: `double C`, `dbl w`; theorem
`(double C).nSteps {dbl w, 2*phase} (2n) = Option.map dbl-config (C.nSteps {w, phase} n)`.
Difficulty: easy. Reuse: `TagSystem/Basic.lean`.

Link B: doubled CTS -> System 5 (T1). `Represents` as above; per-step lemma in two cases.
0-head: pops at min, min+1 (first pair) and min+2, min+3 (second doubled pair); r2+2 cancels r1
exactly; bag returns to `aux rest` shifted; existing false-head engine covers the fresh-encoder
instance and needs generalising to the relation (rules already incremented by the elapsed time,
phase rotated). 1-head: pops at min, min+2, min+3, min+5; appended pairs (x, x+1) -> x..x+3 and
(x, x+3) -> x, x+2, x+3, x+5; the gap >= 3 keeps ascending order; the new pairs sit above the old
bag. Then `ForwardSim` lifting gives T1 by induction on `n <= N`. Termination variant: add the
large integers and prove the terminal event occurs (needed only for T2's exit clause).
Difficulty: medium; the bookkeeping is finite and the encoder facts (r1 = r2 + 2, Nodup, bounds)
exist. Reuse: `System5.lean` step characterisations, `XorMerge`, encoder lemmas, false-head engine.

Link C: System 5 -> System 4 (T2). Fix the encoder first. Define well-formedness of System 4 tapes
(sets Nodup, first element a set, no two adjacent stars) and the running parameter `t`. Prove the
conglomeration lemma (adjacent unstarred sets act as their symmetric difference), the two sweep
lemmas (no-zero step: two sweeps, one empty set merged, t += 2; zero step: two nested loops that
sweep the rule set and the all-integers set into the bag), the finish-time bound, and the exit in
state C. Difficulty: hard (long but concrete case analysis on `System4.step`).

Link D: System 4 -> System 3 (T3, first half). Define the lookahead machine type
`transition : State -> Sym -> Sym -> (State, Sym, Sym, Dir)` reading active cell and right
neighbour, Systems 1-3 from the p.45 Perl table, and the parity-block encoding of a System 4 tape
(sets -> 2^w-wide blocks of 1s and 2s, stars -> the separator pattern). Prove Lemma 0 (nine
sublemmas about scans over a block of 1s and 2s), Lemma 1 (parity of the scan sequence), and the
System 3 simulation of each System 4 rule, with `2^w >= 3f`. Difficulty: research-level within the
project; this is the deepest part of Smith's proof and has no Lean scaffolding today.

Link E: System 3 -> 2 -> 1 -> 0 (T3, second half). Three relabelings with 1-or-3 step
correspondences, each checkable by `decide` over the finite rule tables plus a short induction.
Difficulty: easy-medium once Link D's machine type exists.

Link F: exit condition and composition (T4). Thread "never visits left of the segment" and "first
exit to the right is in state A" through Links B-E; define `IC` as the composition of the encoders
and `decode` as the composition of the decoders. Difficulty: medium.

Link G: loop-freeness (T5). Measure `V(cfg) = sum of positions of 0-cells in the interval`; check
rule by rule (System 1 table, `decide`) that state changes decrease `V` and that any increase is
undone next step; conclude no confined periodic orbit. Difficulty: medium.

Link H: infinite form (T6). New tape type, concatenation, hand-off argument. Difficulty: medium,
after everything else.

Link I: TM -> 2-tag -> CTS (T7). Independent of Links A-H; shares only the `CTS` type and the
`ForwardSim` calculus. Steps: (1) a `WellFormed` predicate on `BiTM.Machine` (currently
`numStates`/`numSymbols` are never read and transitions are total on `Nat`); (2) optionally a
reduction of arbitrary well-formed machines to a 2-symbol alphabet, or a base-k Cocke-Minsky
encoding directly; (3) the tag alphabet (state markers, block markers), the encoder of a
configuration as a tag word, the productions, and the lemma "one TM step = a bounded number of tag
phases" as a `ForwardSim` with a decoder; (4) composition with `tagToCTS_simulation`. Difficulty:
medium-hard, no research risk (textbook construction), roughly 1,500-2,000 lines. If Mathlib is
adopted, consider stating T7/T8 over Mathlib's `Turing.TM0` (or proving a bridge to it) so the
result connects to Mathlib's computability library.

## 4. Engineering decisions

- Toolchain: stay on v4.29.0-rc6 for the cleanup milestone (it builds in 10 s); move to a current
  stable (v4.32.x or newer) together with Mathlib at the start of the new development. Replace
  `native_decide` by `decide` in `Wolfram23Valid.lean` now (it leaks 12 axioms downstream).
  Done in M1: the tree is on `leanprover/lean4:v4.32.2` with Mathlib pinned at tag `v4.32.2`.
- Mathlib: adopt it. `Multiset`, `Finset`, the `List.Perm` API, `Nat` and `Int` lemmas, `omega`,
  `decide`, `simp` sets, and `Function.iterate` remove most of the hand-rolled bag and parity
  reasoning that consumed the previous 1,800 iterations. First build is one `lake exe cache get`.
  Batteries alone lacks `Multiset`.
- Module layout: new `Smith/` directory (Doubling, System5, System5Encode, System5Emulates,
  System4, System4Encode, System4Emulates, Lookahead, Systems123, System3Encode, System3Emulates,
  LoopFree, Conjecture0, Infinite), each with `#eval`/`decide` regression tests against the PDF
  traces (cy2s5 outputs for `3 01 1 10` and `test1.cy`; the 36-line system5 trace; the 545-token
  s52s4 tape; the C-format string `110011110011110010`).
- Keep as is: `TM/Defs.lean` (drop `decodeRule`), `BiTM/Basic.lean`, `TagSystem/Basic.lean`,
  `TagSystem/TagToCTS.lean`, `BiTM/XorMerge.lean`, `BiTM/Wolfram23Valid.lean`.
- Salvage into `Smith/`: `System5.step` and its step characterisations, `System4.step`, the
  cy2s5 encoder definitions and structural lemmas, the false-head engine, the thin cores of
  HaltsEmpty/HaltInduction (about 800 lines total).
- Archive (move to `Archive/`, out of the lakefile roots, on this branch; delete once superseded):
  `BiTM/CTSToSystem5.lean`, `BiTM/SmithChain.lean`, `BiTM/CockeMinsky.lean`,
  `BiTM/CockeMinskyConstruction.lean`, `BiTM/Smith.lean`, `BiTM/System1.lean`,
  `BiTM/GeneralizedTM.lean`, `BiTM/Wolfram23Periodic.lean`, most of `TagSystem/HaltsEmpty.lean`,
  most of `BiTM/HaltInduction.lean`. About 30,000 lines.
- Tooling: lean-lsp-mcp for goals and diagnostics (registered in this config dir), `lake build`
  as the acceptance check, `#print axioms` on the headline theorem in CI.
- Style: plain ASCII in comments (GUIDE.md), no iteration-log comments in source; findings go in
  docs.

## 5. Milestones

| Id | Deliverable | Acceptance check | Effort |
| --- | --- | --- | --- |
| M0 | Cleanup: archive dead weight, fix both encoders (stars, phase), regression tests, `decide` instead of `native_decide`, Nodup and well-formedness invariants stated and preserved | `lake build` green, 0 sorry; all PDF test vectors pass by `#eval`/`decide`; `#print axioms not_halts_wolfram23_valid` shows no `native_decide` | 2-3 days |
| M1 | Mathlib + toolchain bump; `ForwardSim` calculus; `Represents`; doubling lemma | builds; `ForwardSim` composition and lifting proved | 2-3 days |
| M2 | T1: Conjecture 5, both head cases | `lake build` 0 sorry in `Smith/System5Emulates.lean`; `#print axioms` clean; `decide` example on `test1.cy` for 8 CTS steps | 1-3 weeks |
| M3 | T2: System 5 -> System 4 with fixed encoder; finish-time bound; exit in state C | 0 sorry; `decide` example reproducing the p.41 trace | 2-4 weeks |
| M4 | Lookahead machine type; Systems 1-3; relabelings 3 = 2 = 1 = 0; T5 loop-freeness | 0 sorry; `decide` checks of the 1-or-3 step correspondences on the rule tables | 1-2 weeks |
| M5 | T3 first half: System 4 -> System 3 (Lemmas 0, 1, parity blocks, w choice) | 0 sorry | 3-6 weeks (uncertain) |
| M6 | T4: finite-form Conjecture 0 with exit condition and decoder; vacuity theorem for the decoder | 0 sorry; `#print axioms` shows only propext, Classical.choice, Quot.sound | 1-2 weeks |
| M4b | T7: `WellFormed` machines; genuine Cocke-Minsky TM -> 2-tag with decoder; composition with `tagToCTS_simulation` | 0 sorry; `decide` example simulating a small TM for a few steps through tag and CTS; `#print axioms` clean | 2-4 weeks |
| M8 | T8: compose T4 and T7 into the headline universality theorem | 0 sorry; `#print axioms` shows only propext, Classical.choice, Quot.sound; the theorem statement mentions only `BiTM.Machine`, `wolfram23`, and the decoder | 2-3 days |
| M7 | T6: infinite form on an infinite tape type (optional) | 0 sorry | 1-2 weeks |

### M0 notes (done 2026-09-15)

Archived (stage 1): `BiTM/SmithChain.lean`, `BiTM/CockeMinsky.lean`,
`BiTM/CockeMinskyConstruction.lean`, `BiTM/Smith.lean`, `BiTM/System1.lean`,
`BiTM/GeneralizedTM.lean`, `BiTM/Wolfram23Periodic.lean` and the 19,305-line
`BiTM/CTSToSystem5.lean` moved under `Archive/` and out of the lakefile roots;
`CTSToSystem5.lean`, `TagSystem/HaltsEmpty.lean` and `BiTM/HaltInduction.lean`
rewritten from their surviving cores; `TM.decodeRule` dropped. About 23,000
lines left the roots.

Encoder fixes (stage 2), each checked against the Perl in the PDF:

- `encodeS5RuleToS4Elems` now emits the two stars `s52s4.pl` prints before the
  rule set and before the all-integers set (PDF p. 32-33), so a rule block has
  `8 * f` elements instead of `8f - 2`. `encodeS5RuleToS4Elems_length` is now
  stated for `f >= 1` as `8 * f`, with the unconditional form kept as
  `encodeS5RuleToS4Elems_length_raw`; `system5ToSystem4_length` is new. The
  `allInts` argument is spelled `f * 3 + 1` in both places.
- `encodeBag` is now the parity fold `xorInsert` rather than `List.map`, which
  is what the Perl hash does. It agrees with the old map up to list order on
  `Nodup` bags (`encodeBag_eq_reverse_map`); `encodeBag_length` now carries a
  `Nodup` hypothesis, and `encodeBag_nodup` is unconditional.
- `ctsRulesToSystem5Rules` rotates the appendant list by
  `cfg.phase % |appendants|` (`appendantsFromPhase`), so the rule stream starts
  at the appendant `CTS.currentAppendant` reads. At phase 0 it is exactly
  `cy2s5.pl` (`ctsRulesToSystem5Rules_phase_zero`). `ctsRulesToSystem5Rules_one`
  was restated over the rotated list; the length lemma is unchanged, via a new
  `length_rotateLeft`.

`native_decide` is gone from every module of the Smith chain: the two proofs in
`Wolfram23Valid.lean` use `decide`, and the sanity checks in `BiTM/Basic.lean`,
`BiTM/System4.lean`, `TagSystem/Basic.lean` and `TagSystem/TagToCTS.lean` were
converted as well. `#print axioms BiTM.not_halts_wolfram23_valid` now reports
only `propext, Quot.sound`. `wolfram23_step2`, `wolfram23_runs_10` and
`wolfram23_runs_20` were unreferenced and are gone (`not_halts_wolfram23_init`
subsumes them). The remaining `native_decide` sites are in `OneSidedTM/`, which
is unrelated to the Smith chain, and in the D5 System 4 runs of
`Tests/SmithVectors.lean`.

Invariants proved:

- `System5_step_bag_nodup` / `System5_nSteps_bag_nodup`: `System5.step` is
  faithful to `system5.pl` only on `Nodup` bags, and `Nodup` propagates.
- `System5_step_bag_ge_one`, `System5_step_rules_ge_one`,
  `System5_nSteps_bag_ge_one`: positivity of the bag propagates, given a `Nodup`
  bag and positive rules.
- `System4Config.WellFormed` (leftmost element a set, no two adjacent stars,
  every set `Nodup`) with `System4_step_wellFormed` and
  `System4_nSteps_wellFormed`. All three clauses are preserved, with no
  weakening: deleting a star (rules 2 and 4) brings two non-stars together, and
  rules 3 and 5 only rewrite sets.
- Encoder well-formedness: `ctsToSystem5_bag_nodup`, `ctsToSystem5_bag_ge_one`,
  `ctsToSystem5_rules_nodup`, `ctsToSystem5_rules_ge_three`; `encodeBag_nodup`,
  `allInts_nodup`, `encodeS5RuleToS4Set_nodup`.

`Tests/SmithVectors.lean` (a lakefile root) holds the PDF regression vectors:
the two `cy2s5.pl` outputs, the phase-1 rotation, the 36-step `system5.pl` run
of PDF p. 31 with its first three printed bags and its C-format line, the
545-element / 272-star `s52s4.pl` tape at `f = 16` with its sets and its
`WellFormed` proof, the 9,906-step `system4.pl` run with the C-format line
`110011110011110010` of PDF p. 41, and the System 0 transition table. It is the
only module allowed to use `native_decide`, and `native_decide` is used only for
the System 4 runs of D5 (about 10^4 steps over the 545-element tape); the D4
structural checks, the `WellFormed` proof of the s52s4 tape included, close by
plain `decide`. Nothing outside it depends on anything proved there.

Left undone in M0: the general theorem that `system5ToSystem4` always produces a
`WellFormed` tape (only the `f = 16` instance is checked, by `decide`);
the terminal event of System 5 (the step becomes total, decision 5 of section 8)
is still modelled as `step = none`; and Smith's "very large integers" are still
absent from `ctsToSystem5`, as they are from `cy2s5.pl`.

### M1 notes (done 2026-09-15)

Stage 1, toolchain. `lean-toolchain` is `leanprover/lean4:v4.32.2` and `lakefile.lean`
requires Mathlib at tag `v4.32.2` (rev 905b95818eb3), the tag pinned to that toolchain.
One Lean API break had to be repaired, in `System4_step_wellFormed` (a `simpa ... using`
that no longer closed a definitional gap under an unfolded `Decidable.rec`); no statement
changed. `#print axioms BiTM.not_halts_wolfram23_valid` still reports only
`propext, Quot.sound`.

Stage 2, the new development. Three modules under `Smith/`, all three added to the
lakefile roots: `Smith.Simulation`, `Smith.Doubling`, `Smith.Represents`. Zero `sorry`,
zero warnings from these three files, no `native_decide`. Clean rebuild of the project
library: 14.4 s wall, 552 jobs, 0 errors, 63 warnings (all pre-existing
`linter.unusedSimpArgs` in `OneSidedTM/` and one in `BiTM/System5.lean`).

`Smith/Simulation.lean`, the emulation calculus of section 3. `StepSys S` bundles a
partial step function (bundled, not a typeclass: several systems share one state type,
for instance every `CTS` on `CTSConfig`), with `StepSys.nSteps` and the equations
`nSteps_zero`, `nSteps_one`, `nSteps_succ_left`, `nSteps_succ`, `nSteps_add`,
`nSteps_some_of_le`, `step_some_of_nSteps`. Then

    ForwardSim MS MT R := forall s t, R s t -> forall s', MS.step s = some s' ->
      exists k, 1 <= k /\ exists t', MT.nSteps t k = some t' /\ R s' t'

with `ForwardSim_comp` along `Rcomp R R' := fun s u => exists t, R s t /\ R' t u`,
`ForwardSim_nSteps_weak` (n source steps give m >= n target steps), and the strong
lifting `ForwardSim_nSteps`: an explicit schedule `times : Nat -> Nat` with
`times 0 = 0`, `times j < times (j+1)` for `j < n`, and both runs defined and related
at every `j <= n` (`IsSimSchedule`; `IsSimSchedule_le` gives `j <= times j`). The strong
form was proved, so the weak `exists m, n <= m` fallback was not needed.
`ForwardSim_of_fun` covers functional encoders. The vacuity guard is explicit:
`ForwardSim_of_stuck` shows that a relation whose source states never step is a
`ForwardSim` for free, and `ForwardSim_nontrivial` is the antidote (a related source
state that steps forces `MT.step t = some t1`). `ForwardSimDecode MS MT decode :=
ForwardSim MS MT (fun s t => decode t = some s)` with `ForwardSimDecode_functional`.
`ForwardSim` is not decidable (the witness `k` is unbounded), so its two non-degeneracy
examples are explicit: `demo_forwardSim` (a two-target-steps-per-source-step simulation)
and `demo_not_forwardSim` (no relation with a stepping source is a `ForwardSim` into a
target that cannot move), the latter proved through `ForwardSim_nontrivial`.

`Smith/Doubling.lean`, link A. `ctsSys C : StepSys CTSConfig` with
`ctsSys_nSteps : (ctsSys C).nSteps c n = C.nSteps c n`; `dbl` (each bit twice),
`dblAppendants` (each appendant doubled, each followed by a blank), `double`, and
`dblCfg c = { data := dbl c.data, phase := 2 * c.phase }`. Proved: `dbl_length`,
`dbl_append`, `dbl_eq_nil_iff`, `dblAppendants_length`,
`double_currentAppendant_even : (double C).currentAppendant (2*p) = dbl (C.currentAppendant p)`,
`double_currentAppendant_odd : (double C).currentAppendant (2*p+1) = []`,
`double_nSteps_two : (double C).nSteps (dblCfg c) 2 = Option.map dblCfg (C.step c)`
(the halting case is covered: a doubled working string is empty exactly when the
original is, and a one-bit working string still affords two doubled steps), the
corollary `double_nSteps` at `2 * n`, and `double_forwardSim`, link A as a `ForwardSim`
with `k = 2`. PDF p. 18 vectors by `decide`: `pdf_double_appendants` and
`pdf_double_data` reproduce `111100 1111 "" 00 "" 0011 "" "" ""` from `110 11 0 01 ""`,
and `pdf_double_steps_agree` checks the even-step correspondence for the first four
original steps. Negative examples: `pdf_double_odd_step_differs` (after one doubled step
the two sides differ, so the factor 2 is real) and `dbl_ne_true_false` (`dblCfg` is not
surjective).

`Smith/Represents.lean`, the representation relation T1. The exact Lean definition:

    def Represents (s : System5Config) (C : CTS) (c : CTSConfig) (budget : Nat) : Prop :=
      (exists a : List Int, pairsAsc 0 c.data a = true /\ s.bag.Perm (pairsOf c.data a)) /\
      (exists (i : Int) (rest : List (List Int)),
          (forall x in s.bag, x + 3 <= i) /\
          s.rules = (ruleBlocks (appendantsFrom C c.phase budget) i).1 ++ rest)

(`forall x in` stands for the bounded-membership quantifier and `/\` for
conjunction). `C` is the DOUBLED system and `c` its
configuration, so `c.data` is a doubled working string and one pair of bag integers
belongs to each of its bits. Doubling is a precondition, not a side condition:
`encodePaired` reads an appendant two bits at a time and drops a trailing odd bit, so
the rules clause is meaningful only for `C = double C0`, and every statement about
`Represents` here and in M2 is stated over a doubled system. The supporting
definitions:

    gap b            : Int            -- 1 for a 0, 2 for a 1
    pairsOf w a      : List Int       -- x :: (x + gap b) :: ... , one pair per bit
    pairsAsc lo w a  : Bool           -- lo < a_0 and a_j + gap (w_j) < a_(j+1)
    encodePaired w i                  -- the rule pair of one doubled appendant,
                                      -- read two bits at a time
    ruleBlocks L i                    -- two rules per appendant, threading the counter
    appendantsFrom C p n              -- the appendants read at phases p, ..., p+n-1

`pairsAsc` is Bool-valued, hence decidable, which is what makes the examples
`decide`-checkable. The rules clause is existential in the counter `i` and in the tail
`rest`, and therefore survives (a) a uniform increment of the whole rule list and (b)
dropping consumed rule groups; it is not equality with the canonical encoder output.

Fidelity of the rules clause. Smith's p. 19 condition asks only that the lower integer
of each pair of a second rule sit at least 3 above every integer of the initial bag, of
every previous rule other than the first rule of a pair, and of the earlier bits of the
same appendant; any spacing meeting those bounds is acceptable. The Lean clause pins the
canonical `cy2s5.pl` layout instead: `encodePaired` advances the counter by exactly 4
per doubled `0` and 6 per doubled `1`, `ruleBlocks` lays consecutive rule pairs down
contiguously, and only the base counter `i` and the tail are quantified. The relation is
therefore a strict sub-relation of Smith's. It is contained in Smith's, because the
canonical layout meets each of those bounds with equality (a doubled `0` pair occupies
`x, x + 1` with the next pair at `x + 4`; a doubled `1` pair occupies `x, x + 3` with
the next pair at `x + 6`). The containment is strict: the hand-built program Smith
prints on p. 19 uses extra slack from its third rule pair on, so it is in the relation
at budget 2 and out of it at budget 3 (`pdf19`, `pdf19_represents_budget2`,
`pdf19_not_represents_budget3`, and `pdf19_ne_encoder`, which records that it is not the
encoder output either). The restriction is adequate for T1, since the canonical layout
is what the encoder emits and what one System 5 step re-establishes, with the threshold
met exactly; proving that is the M2 per-step lemma. Relaxing the clause to Smith's
"at least 3" condition is an optional later generalisation, listed under open points.

Proved about the relation: `Represents_bag_multiset` (the bag clause as a `Multiset`
equality, the one place Mathlib is load-bearing), `Represents_bag_nodup`,
`Represents_bag_ge_one`, `Represents_bag_length` (`s.bag.length = 2 * c.data.length`),
`Represents_bag_ne_nil_of_data_ne_nil` (the "no degenerate witness" theorem of section 6
for link B) and its converse `Represents_data_ne_nil_of_bag_ne_nil`,
`Represents_rules_pair` (first rule = second `.map (+2)`), `Represents_rules_ge` (every
integer of every leading rule sits at least 3 above every bag element),
`ruleBlocks_odd_phase_blank` and `Represents_blank_rules` (a doubled system at an odd
phase has two blank rules in front), and `Represents_shift` (a uniform increment of bag
and rules by any `m >= 0` preserves the relation), on top of `encodePaired_shift`,
`ruleBlocks_shift`, `pairsOf_map_add`, `pairsAsc_map_add`, `pairsAsc_mono`.

Base case:

    theorem ctsToSystem5_represents (C : CTS) (cfg : CTSConfig) (N : Nat) :
        Represents (ctsToSystem5 C cfg N) (double C) (dblCfg cfg)
          (2 * (C.appendants.length * N))

The budget is the number of appendants of the doubled system times the number of full
cycles the encoder emitted. The statement is stronger than the form quoted in section 2:
neither `1 <= N` nor `cfg.data <> []` is needed;
`ctsToSystem5_represents_nontrivial` adds, under those two hypotheses, that the bag, the
rule list and the budget are all nonempty. The proof identifies the 4 rules per appendant
of `cy2s5.pl` with 2 rules per appendant of the doubled system
(`encodePaired_dbl : encodePaired (dbl a) i = encodeAppendant a i`,
`ruleBlocks_flatMap`, `appendantsFrom_double`) and the phase-indexed traversal with the
rotated appendant list (`appendantsFrom_full`, via a new `rotateLeft_getElem?`), and on
the bag side writes the `cy2s5.pl` bag as the pairs of an explicit ascending list of
starts (`startsOf`, `pairsOf_dbl_startsOf`, `pairsAsc_dbl_startsOf`).

Non-degeneracy of `Represents` (section 6 discipline). Positive: `ex_represents`, the
TM23Proof.pdf p. 29 example (`cy2s5.pl 3 01 1 10`, bag `1,2,3,4,5,7,8,10`, rules
`15,18 / 13,16 / "" / "" / 21,24,27,28 / 19,22,25,26 / "" / ""`), with starts
`1, 3, 5, 8` for the doubled working string `0011` and rule counter 13; every clause is
closed by `decide`, and `ex_encoder` checks the encoder output itself by `decide`.
Negative: `ex_not_represents_wrong_bag` (the bag `1,2,3,5,6,8,15,18` does not represent
the doubled word `0011` for any rule list and any budget) and
`ex_not_represents_empty_bag` (the empty bag never represents a nonempty working
string). Caveat: these two are not literally `decide` proofs, because the bag clause
quantifies existentially over the unbounded list of starts. They are reduced to
`decide`-checkable facts by two inversion lemmas that are part of the development:
`eq_pairsOf_of_perm` (a strictly increasing bag that is a permutation of a family of
pairs is that family of pairs, via `pairsOf_pairwise`) and `Represents_bag_length`.
`pairsAsc` itself has a `decide`-checked positive and negative example
(`ex_pairsAsc_pos`, `ex_pairsAsc_neg`). Both of those negative examples fail on the bag
clause alone, so the rules clause has two of its own, at budget 1, where it is not
vacuous: `ex_not_represents_low_counter` (the rule pair has the right shape, which
forces the counter, and the forced counter breaks the threshold `x + 3 <= i`) and
`ex_not_represents_swapped_rules` (the pair is in the wrong order, so no counter fits).
At budget 0 the rules clause constrains nothing and `Represents` reduces to the bag
clause, which `ex_represents_budget_zero` records. `IsSimSchedule` has
`demo_isSimSchedule` (the schedule `j |-> 2 * j` for two steps of the worked example)
and `demo_not_isSimSchedule` (the constant schedule, the trivial witness the strict
monotonicity clause exists to exclude).

Nothing was left unproved in M1: every lemma listed for the milestone closed. Open
points carried into M2: the per-step lemma itself (0-head and 1-head cases) is untouched,
`Represents` says nothing about the "very large integers" of TM23Proof.pdf p. 19 (they
are absent from `cy2s5.pl` and only matter for the terminal event), and the budget
bookkeeping still counts full cycles rather than single appendant emissions, so budgets
quoted from the PDF must be rescaled by `|appendants|` as recorded in the M0 notes.
Relaxing the rules clause from the canonical `cy2s5.pl` spacing to Smith's "at least 3"
condition is an optional generalisation; nothing downstream needs it, since the encoder
emits the canonical layout. One statement-shape decision is due at the start of M2:
`ForwardSim` quantifies over every source step, so it cannot hold for the fixed relation
`fun c s => Represents s C c b` once the budget runs out (the cyclic tag system steps on,
the System 5 program cannot). Either give the source a fuel counter,
`StepSys (CTSConfig x Nat)` whose step decrements the fuel and is stuck at 0, and take
`R (c, n) s := Represents s C c n`, in which case `ForwardSim_nSteps` applies unchanged;
or state T1 directly in `IsSimSchedule` form with `n <= budget`, bypassing `ForwardSim`.

Critical path: M0 -> M1 -> M2 -> M3 -> M5 -> M6 -> M8. M4 and M4b run in parallel with M2/M3
(M4b is independent of the whole Smith side). M7 is optional. Total: roughly four months of
focused work; M5 carries most of the risk, M4b none beyond volume.

## 6. Risks and mitigations

- Statement drift back into vacuity. Mitigation: every emulation theorem uses `ForwardSim` with a
  relation that has a partial decoder and pop-event time indices; add a "no degenerate witness"
  theorem per link (e.g. `Represents s c b -> c.data <> [] -> s.bag <> []`).
- Obstruction (a) halting: never use `Halts wolfram23`; use the exit condition.
- Obstruction (b) periodicity: never use `encode : CTSConfig -> Config` functions; T5 proves the
  obstruction is real, which also documents why the old predicates were abandoned.
- Obstruction (c) termination of System 5: budgets are part of the relation; the infinite form is
  by concatenation, not by one finite initial condition.
- Link D size. Mitigation: formalize Lemma 0's nine sublemmas as `decide`-checked finite facts
  about one block plus one induction on block count; prototype with small w before generalising.
- Encoder fidelity regressions. Mitigation: PDF traces as `decide` tests in every encoder module.
- Toolchain and Mathlib churn. Mitigation: pin Mathlib to a tagged release matching the toolchain.

## 7. First three tasks

1. M0 fixes, no new theory: add the two stars in `encodeS5RuleToS4Elems` and the parity fold in
   `encodeBag`; rotate the appendant list by `phase` in `ctsRulesToSystem5Rules`; create
   `Proofs/Tests/SmithVectors.lean` with the PDF test vectors as `decide`/`#eval` checks; replace
   `native_decide` in `Wolfram23Valid.lean`; state `System5_step_bag_nodup` and a System 4
   well-formedness predicate with preservation lemmas. Build green, commit.
2. Archive: move the files listed in Section 4 to `Archive/`, trim the lakefile roots, salvage the
   listed cores into `Smith/`, keep the build green, commit. Update REVIEW.md pointers.
3. Define `ForwardSim`, `Represents`, `double` and prove the doubling lemma and the 0-head case of
   the per-step lemma against `Represents` (porting the false-head engine). This is the first
   theorem that could not have been proved under the old statements.

## 8. Decisions (all resolved 2026-09-15)

1. Target: resolved. Finite-budget statements first (T4, then the headline T8); the infinite form
   (T6) is optional and comes last, on a new tape type.
2. Scope: resolved 2026-09-15. The headline is the self-contained T8 (TM -> 2-tag -> CTS ->
   wolfram23), with a genuine Cocke-Minsky construction (M4b). No literature result is cited in
   place of a proof, and no theorem is named "universal" unless its statement quantifies over
   Turing machines. T4 (CTS emulation, Smith's own theorem) stays as an intermediate result.
   Sub-decision: state T7/T8 over `BiTM.Machine` with a `WellFormed` predicate, or over Mathlib's
   `Turing.TM0`. Recommendation: `BiTM.Machine` plus `WellFormed` first, bridge to `Turing.TM0`
   later if wanted.
3. Toolchain and library: resolved. Adopt Mathlib and bump the toolchain to the Lean version
   Mathlib's chosen release pins (v4.32.x or newer) at the start of M1; M0 stays on v4.29.0-rc6.
4. Old files: resolved. Archive the exploratory files under `Archive/`, outside the lakefile roots,
   on this branch; delete them once M2 lands.
5. System 5 semantics: resolved. The step becomes total when the rule list is empty and exposes
   the terminal event "a 0 surfaced with no rule left" explicitly (the event Conjecture 5 and the
   System 4 exit-in-state-C argument depend on).
