# Plan: finishing the Lean proof of Wolfram (2,3) universality

Date: 2026-09-15. Companion to REVIEW.md. Status: all decisions in section 8 resolved on
2026-09-15; M0 done 2026-09-15 (see "M0 notes" in section 5); M1 done 2026-09-15 (see "M1
notes" in section 5); M2 done 2026-09-15 (see "M2 notes" in section 5); M3 done 2026-09-21
(see "M3 notes" in section 5); M4 done 2026-09-21 (see "M4 notes" in section 5); M5 done
2026-09-21 (see "M5 notes" in section 5); M6 done 2026-09-21 (see "M6 notes" in section 5);
M4b done 2026-09-21 (see "M4b notes" in section 5); M8 is next.

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

### M2 notes (done 2026-09-15)

T1 is proved. Four modules carry it: `Smith/System5Runs.lean` (run lemmas, the
bag decoder, arithmetic helpers), `Smith/Conjecture5.lean` (the per-step lemma,
both head cases), `Smith/ConjectureFive.lean` (the assembly into `ForwardSim`
and T1 itself), plus the `fueled` section added to `Smith/Simulation.lean` and
`double_forwardSim_fueled` in `Smith/Doubling.lean`. All four are lakefile
roots. Zero `sorry`, no `native_decide`, no axioms beyond `propext`,
`Classical.choice`, `Quot.sound`; `lake build` 617 jobs, warm 0.9 s, clean
rebuild of the five Smith modules plus Tests 7.7 s wall.

The per-step lemma. `x` is the smallest bag integer, `b` the leading bit of the
doubled working string, `k = x + gap b` the number of System 5 steps of one
doubled cyclic tag step (`gap false = 1`, `gap true = 2`, so `k >= 2`):

    theorem represents_step_false (C : CTS) (w : List Bool) (p n : Nat)
        (s : System5Config)
        (h : Represents s C { data := false :: w, phase := p } (n + 1)) :
        exists k, 1 <= k /\ exists s', System5.nSteps s k = some s' /\
          Represents s' C { data := w, phase := (p + 1) % C.appendants.length } n

    theorem represents_step_true (C : CTS) (w : List Bool) (p n : Nat)
        (s : System5Config) (a : List Bool)
        (happ : C.currentAppendant p = dbl a)
        (h : Represents s C { data := true :: w, phase := p } (n + 1)) :
        exists k, 1 <= k /\ exists s', System5.nSteps s k = some s' /\
          Represents s' C { data := w ++ dbl a,
                            phase := (p + 1) % C.appendants.length } n

Both are corollaries of `_time` forms that pin the step count (`(k : Int) = x +
1`, resp. `x + 2`) and exhibit `x` as a bag element below every bag element;
those are what the schedule of T1 is built from. `represents_step_double` and
`represents_step_double_time` do both head bits at once over a doubled system,
where `double_currentAppendant_dbl` discharges the `dbl a` hypothesis at every
phase (even phases: a doubled appendant; odd phases: `dbl [] = []`).

The run, in Smith's words. Steps `1 .. x - 1` are pure decrements; step `x` pops
the first rule of the leading pair, which lands at least `i + 2 + x` while the
surviving bag is at most `i - 3 - x`, so the `xorMerge` is an append. In the
0-head case step `x + 1` pops the second rule, which by `r1 = r2.map (. + 2)`
has become exactly the block the first pop deposited, so `xorMerge` cancels it.
In the 1-head case step `x + 1` is a pure decrement and step `x + 2` pops the
second rule; the deposited block is `r2 + x` and the new one `r2 + (x + 2)`, and
no two integers of `r2` are exactly 2 apart, so both survive and together are
the canonical bag of the appended appendant laid out from `i + x`.

The assembly (`Smith/ConjectureFive.lean`):

    theorem represents_forwardSim (C0 : CTS) :
        ForwardSim (fueled (ctsSys (double C0))) system5Sys
          (fun p s => Represents s (double C0) p.1 p.2)

    theorem cts_system5_forwardSim (C0 : CTS) :
        ForwardSim (fueled (ctsSys C0)) system5Sys
          (fun p s => Represents s (double C0) (dblCfg p.1) (2 * p.2))

    theorem conjecture5_finite (C0 : CTS) (cfg : CTSConfig) (N n : Nat)
        (hn : n <= C0.appendants.length * N) (c' : CTSConfig)
        (hrun : C0.nSteps cfg n = some c') :
        exists times : Nat -> Nat, times 0 = 0 /\
          (forall j, j < n -> times j < times (j + 1)) /\
          forall j, j <= n -> exists cj sj, C0.nSteps cfg j = some cj /\
            System5.nSteps (ctsToSystem5 C0 cfg N) (times j) = some sj /\
            Represents sj (double C0) (dblCfg cj)
              (2 * (C0.appendants.length * N - j))

    theorem conjecture5_decode (same hypotheses) :
        exists times : Nat -> Nat, times 0 = 0 /\
          (forall j, j < n -> times j < times (j + 1)) /\
          forall j, j <= n -> exists cj sj, C0.nSteps cfg j = some cj /\
            System5.nSteps (ctsToSystem5 C0 cfg N) (times j) = some sj /\
            decodeBag sj.bag = some (dbl cj.data)

The budget lives in the source system, not in the relation: `fueled M` (new in
`Smith/Simulation.lean`) pairs a state with a step budget and is stuck at 0,
which is decision (i) of the two the M1 notes left open. One unit of original
fuel is one cyclic tag step, hence two appendants of the doubled system, hence
the `2 * p.2` of the composed relation; `ForwardSim_comp` with
`double_forwardSim_fueled` (k = 2) does the composition and the new
`ForwardSim_congr` removes the existential `ForwardSim_comp` leaves behind.
`conjecture5_isSimSchedule` is the same fact in `IsSimSchedule` form, from which
both theorems above are read off; `sim_schedule_le` (proved from
`IsSimSchedule_le`) and `conjecture5_times_ge` record `j <= times j` and
`n <= times n`, so the schedule cannot be the degenerate constant one.

Fidelity. The threshold clause of `Represents` is met with equality in the
1-head case: the appended appendant reaches `i' + x - 1` and the new counter is
`i' + (x + 2)`, so the threshold holds with no slack at all. In the 0-head case it
holds with slack at least `2x + 2`. This is the sense in which the canonical
`cy2s5.pl` spacing is exactly what one step re-establishes, as the M1 fidelity
note predicted.

Decoder. `decodeBag : List Int -> Option (List Bool)` (`Smith/System5Runs.lean`)
sorts the bag and reads it pair by pair, mirroring `pairsAsc` clause for clause;
`Represents_decode` turns every `Represents` into a decoding and
`Represents_data_unique` makes the decoded word unique. Positive and negative
`decide` examples: `decodeBag [1,2,3,4,5,7,8,10] = some [false,false,true,true]`
(the p. 29 bag), `decodeBag [2,4,3,1] = some [false,false]` (any permutation),
against `decodeBag [1,2,3] = none`, `decodeBag [1,2,3,6] = none`,
`decodeBag [0,1] = none`, `decodeBag [1,2,2,3] = none`.

Regression instances. On `cy2s5.pl 3 01 1 10` (p. 29, `exCTS`, `exCfg`, N = 1)
the schedule is 0, 4, 10 and the decoded words are `dbl 01`, `dbl 1`, `dbl 10`;
the intermediate doubled steps 2 and 7 are pinned too, and the per-step lemma is
applied as a term four times in a row. On `test1.cy` (p. 28, working string
`11011`, appendants `101 01 0 "" 010`, N = 10) the schedule of the first eight
cyclic tag steps is 0, 6, 12, 16, 22, 28, 40, 44, 50 and each time decodes to
`dbl` of the working string of that step, which is the eight-step `decide`
example the M2 row of the table asks for; `ex_c5_test1_conjecture5` applies
`conjecture5_decode` itself to those eight steps. Negative instances at unscheduled times: the p. 29 run does not
decode at times 1, 5 and 6, the `test1.cy` run does not decode at time 13, and
the word the p. 29 run decodes to at time 2 has odd length, so it is not `dbl`
of anything. All by `decide`; no `native_decide` was needed anywhere.

Left undone in M2. The relation is still the canonical-spacing sub-relation of
Smith's p. 19 condition (the optional generalisation of the M1 notes is
untouched); `Represents` still says nothing about the "very large integers" of
p. 19 and nothing about the terminal event, so T1 covers only runs within the
budget and does not yet say what happens when the rules run out (that is what
T2's exit-in-state-C clause will need); the budget still counts full cycles, so
a PDF budget must be divided by the number of appendants; and the schedule of
`conjecture5_finite` is existential rather than given by a closed formula
`times j = sum of (x_i + gap b_i)`, since the `_time` lemmas pin each increment
but no aggregate was stated.

### M3 notes (done 2026-09-21)

T2 is proved, in the finite form with the System 5 run length as the budget.
Two modules, both lakefile roots: `Smith/System4Runs.lean` (the run lemmas,
about 780 lines) and `Smith/Conjecture4.lean` (the relation, the per-step
lemma, T2, the decoder, the composition with T1, about 880 lines). Zero
`sorry`, no `native_decide`; `#print axioms` of `conjecture4_finite`,
`conjecture4_cts_exists_f`, `RepS4_decode` and `repS4_forwardSim` shows only
`propext, Classical.choice, Quot.sound` (`repS4_exit`: `propext, Quot.sound`).
`lake build` is 619 jobs; the two modules build in about 5 s together and
emit no warnings.

The run lemmas (`Smith/System4Runs.lean`). Each rule of `System4.step` is
stated at a focus `L ++ e :: R` with the head on `e` (`step_setA`,
`step_setA_zero`, `step_starA`, `step_setBC`, `step_starB`, `step_starC`),
so every run of the emulation is a composition of local moves with an
arbitrary context on both sides. On top of them: `sweep` (a B/C pass over a
block of adjacent sets `sets K` decrements every set and flips the state
once per set that contains `0`, so it ends in `flip (parMem 0 K) st`, where
`parMem x K` is parity membership, that is membership in the "one big merged
set" of PDF p. 16), `moveLeft`, `turn`, `turnFrom` (the state A walk back to
the left end and the turn into B), `cPhase` (in state C the `g` star/empty
pairs become `g` star/`{0}` pairs in `2g` steps), and the macros of p. 17-18:
`dStep` (turn, sweep, star, turn, sweep, star, walk back; `4|K| + 4` steps,
both sweeps quiet), `preLoop` (the 8 steps at the arrival at a block in state
C: toggle of `1`, two decrements, the two stars around the set deleted, one
empty set merged), `loopIter` (one iteration of Smith's loop, `2|K| + 1`
steps, on the block `loopK i R = {0} :: {}^i ++ [R] ++ {}^(i+2)`), `loopRun`
(`n` iterations), `finalPass` (the last pass, which merges the block into the
leftmost block and returns the head to the left end), and `popPhase`, which
chains turn, sweep, `cPhase`, `preLoop`, `loopRun` and `finalPass` from a
left-end configuration with a `0` in the merged leftmost block. `popPhase` is
applied twice per System 5 pop, once at the rule set and once at the
all-integers set; the loop counts are `g - 1` and `f + t - 3`, as on
p. 17-18. The step counts of the composite runs are existential (the schedule
of T2 is existential anyway).

The relation `RepS4 c s f j h` (`Smith/Conjecture4.lean`) is the "condition
during execution" of p. 17 after `j` System 5 steps with `h` steps of budget
left: there is a nonempty block `K` of sets, each `Nodup` and nonnegative,
with

    c = ⟨sets K ++ starredEmptyPairs (f - 2j) ++ encBlocks s.rules f (2j), 0, A⟩

where `encBlocks` lays down one block per remaining rule whose rule set is
`0..3f` toggled at `rulePos f t k = 2k + f + 3 - t` with `t = 2j` (the tape
integer of a rule entry is fixed while the entry grows by 1 per step,
`encBlocks_shift`); `2j + 2h < f`; for every `0 <= x` with
`x + 2j + 2 < 2f`, `parMem x K = decide (exists e in s.bag, x = 2e - 2)`;
`s.bag` is `Nodup` with `1 <= e` and `e + j < f` for every element; every
rule is `Nodup` with `0 <= k` and `k + j + 2h < f` for every entry. The band:
the symmetric difference of `K` agrees with the encoded bag only below
`2f - 2j - 2`; above it the all-integers sets leave debris (`{0..2f+t-3}`
xor `{0..2f-t}` after a pop, then decremented by 2 per step), which is what
Smith's "f sufficiently large" is for. The budget clause on the rules keeps
every popped integer below the band; it is invariant because a rule entry
grows by 1 per step while its threshold shrinks by 1.

The per-step lemma. `repS4_dStep` (`1` not in the bag) is `dStep` plus the
shift of the blocks. `repS4_pStep` (`1` in the bag, rules `r :: rest`) is
`popPhase` at `encRuleSet r f (2j)` followed by `popPhase` at
`allInts (3f + 1)`; the zero facts it needs (`0 in decrN i (xorInsert 1 S)`
at the loop indices) come from `encRuleSet_mem_low` (every integer below the
first rule position `f + 3 - t` is in the rule set) and `allInts_mem`. The
parity clause after the pop is the identity

    parMem x K2 = parMem (x + 2) K xor decide (exists k in r, x = 2k)

for `x` below the new band: the rule set contributes `x + g + 3 in Rs`, which
there is `not (exists k in r, x = 2k)`, and the all-integers set contributes
`true`; on the System 5 side `xorMerge_mem_iff` and `exists_xor_encode` read
the new bag `xorMerge ((bag - 1).erase 0) (r + 1)` the same way.
`system5ToSystem4_repS4` is the initial condition (`t = 0`,
`K = [encodeBag bag]`; `system5ToSystem4_eq` identifies the M0 encoder with
`encBlocks _ f 0`).

Assembly. `repS4_forwardSim f h0 : ForwardSim (fueled system5Sys) system4Sys
(fun p c => p.2 <= h0 /\ RepS4 c p.1 f (h0 - p.2) p.2)` (the step count is
the fuel spent), and

    theorem conjecture4_finite (s : System5Config) (f h n : Nat)
        (hbag : s.bag.Nodup) (hbag1 : forall e in s.bag, 1 <= e /\ e < f)
        (hrules : forall r in s.rules, r.Nodup /\ forall k in r, 0 <= k /\ k + 2 * h < f)
        (hf : 2 * h < f) (hn : n <= h) (s' : System5Config)
        (hrun : System5.nSteps s n = some s') :
        exists times : Nat -> Nat, times 0 = 0 /\
          (forall i, i < n -> times i < times (i + 1)) /\
          forall i, i <= n -> exists si ci, System5.nSteps s i = some si /\
            System4.nSteps (system5ToSystem4 s f) (times i) = some ci /\
            RepS4 ci si f i (h - i)

Exit: `repS4_exit`, from a related configuration with an empty rule list and
`1` in the bag (the pop attempt that is Conjecture 5's terminal event) the run
reaches a configuration in state C with the head just past the right end,
where `System4.step` is `none`. Decoder: `decodeS4 c b` reads the parity set
of the leftmost block below `b`; `RepS4_decode` shows that at
`b = 2f - 2j - 2` it returns a permutation of the System 5 bag. Composition:
`conjecture4_cts` and `conjecture4_cts_exists_f` compose T1 and T2
(schedules composed through `strictMono_of_succ`): for every cyclic tag
system, configuration, budget `N` and `n` within the budget there are `L`
(the System 5 run length) and `f0` such that for every `f >= f0` the System 4
tape `system5ToSystem4 (ctsToSystem5 C0 cfg N) f` has a strictly increasing
schedule at which it stands in `RepS4` to a System 5 configuration that
`Represents` the `i`-th cyclic tag configuration.

Regression (`Tests/SmithVectors.lean`, D7): on the p. 33 program
`2 1,4 1,6 "" ""` at `f = 16` the bounds allow a budget of 4; the D5 run is
back at the left end in state A at times 8, 1336, 1616, 1904 and `decodeS4`
there reads `1`, `3,6`, `2,5`, `1,4`, the System 5 bags; at 570 (the end of
the first pop phase) and 1475 (the middle of a D-step) it reads `none`. By
`native_decide` (runs of 10^3 steps); the D-step itself, time 8, is checked
against the tape `sets [{0}, {}, {}] ++ 14 pairs ++ blocks` by plain
`decide`.

Left undone in M3. The finish-time bound `finishTime P <= 3^(n-1) M` of
p. 20-21 is not formalised: T2 takes the System 5 run length as its budget
and `conjecture4_cts_exists_f` chooses `f` from it, so no closed form for `f`
is stated. `System5.step` is still `none` on an empty rule list (decision 5
of section 8 remains to be implemented); `repS4_exit` states the terminal
event as "rules empty and `1` in the bag". The relation fixes the tape layout
of `s52s4.pl` exactly (block widths `2f` and `2f - 2`), not Smith's looser
"possibly containing other integers higher than 3f". `RepS4` says nothing
about the tape off the schedule; the head is also back at the left end in
state A at unscheduled times (the end of the first pop phase, the middle of a
D-step), which the D7 negative instances record.

### M4 notes (done 2026-09-21)

Four modules, all lakefile roots, about 950 lines together: `Smith/Lookahead.lean`
(the machine type and the four rule tables), `Smith/Systems123.lean` (the
relabelings), `Smith/LoopFree.lean` (T5), `Smith/Wolfram23Bridge.lean` (T5 for
`BiTM.wolfram23`). Zero `sorry`, no `native_decide`; `#print axioms` of
`sys3_sys0_forwardSim`, `sys1_leaves`, `sys0_leaves`, `sys0_not_periodic`,
`wolfram23_leaves` and `wolfram23_not_periodic` shows only `propext,
Classical.choice, Quot.sound`. `lake build` is 676 jobs.

The machine type (`Smith/Lookahead.lean`). `LMachine.trans : LState -> Fin 3 ->
Fin 3 -> LRule` reads the state, the active cell and its right neighbour (`0`
when there is none) and returns `one st' a' d` (rewrite the active cell) or
`two st' a' b' d` (rewrite both cells), the two rule shapes of `sys0-3.pl`
(p. 45, `%rules` keyed by one or two cells). Configurations are finite zippers
`(left, head, right, state)` like `BiTM.Config`, left cells nearest first;
`lstep` is `none` on a move off either end and on a two-cell rule with no
neighbour; `exitRight` records the state and the final tape when a one-cell
rule moves the head off the right end, the exit event of Conjectures 0 to 3.
A list-plus-index representation was tried first and abandoned: its focus
lemmas are keyed on `L.length` and stop matching once `simp` re-associates
`(L ++ [x]) ++ a :: R`; on the zipper every move is structural and the case
analyses close by `simp`. The four tables are transcribed from p. 45 (`sys0`
is Wolfram's table, D6 of the tests); `OneIgnoresNeighbour` holds for each by
`decide`; the `sys0-3.pl 0 N 00A00000` trace of p. 47 is reproduced tape for
tape over its 27 steps, and its exit (`1122112` in state B) by `exitRight`.

The relabelings (`Smith/Systems123.lean`), each a `ForwardSim` from the higher
system to the lower one, the direction the chain needs. `sys1_sys0_forwardSim`
on the identity relation: one System 1 step is one System 0 step, or three
for `B21` and `B22` (`sys0_B2_three`: `B2 -> A0>`, then `A1 -> A2<` or
`A2 -> A1<`, then `A0 -> B1>`). `sys2_sys1_forwardSim` along `phi2` (state C
is state B with the active cell swapped `1 <-> 2`), one step to one step
(`phi2_step : lstep sys1 (phi2 c) = (lstep sys2 c).map phi2`).
`sys3_sys2_forwardSim` along `phi3` (every cell left of the head swapped, and
the head itself in state A), `phi3_step`. The composite

    sys3_sys0_forwardSim : ForwardSim (lsys sys3) (lsys sys0) (fun c c' => c' = phi2 (phi3 c))

is what link F composes with the System 4 -> System 3 emulation of M5. The
correspondences are also checked by `decide` on every three-cell tape, with
negative instances showing that neither relabeling is the identity. `phi2` is
many-to-one (System 1 has no state C), so these are simulations, not
bisimulations; the other direction is not needed by the chain.

T5 (`Smith/LoopFree.lean`), Smith's p. 22 argument, made in System 1. `V c`
is the sum of the positions, counted from 1, of the 0s of the tape; `W c` is
`V c` without the head cell in state A (the `A0 -> B1>` step that must follow
spends it); `phase c` is the head position plus the tape length in state A,
and the number of cells to the right in state B. `sys1_measure`: every
System 1 step from a configuration in state A or B decreases `(W, phase)`
lexicographically and stays in A or B; it is checked rule by rule by `simp`
and `omega` after splitting on both neighbours (`B20` raises `V` by the head
position and lowers `W` by 1, which is Smith's "decreases to a lower value
than the value it increased from"). `run_ends_of_measure` turns such a
measure into the end of the run (a double induction on the two bounds), so
`sys1_leaves : c.state <> C -> exists n, lnSteps sys1 c n = none`;
`sys1_none_sys0` (System 0 is stuck wherever System 1 is: `B2` at the last
cell moves System 0 off the tape) and `run_ends_of_sim` transfer it along the
1-or-3 correspondence to `sys0_leaves`, and `sys0_not_periodic` follows. On
the p. 47 tape `V` is not monotone along the System 0 run while `W` is
monotone along the System 1 run, both by `decide`.

The bridge (`Smith/Wolfram23Bridge.lean`). `toBi` reads a System 0
configuration as a `BiTM.Config` (A is 1, B is 2, symbols by `Fin.val`);
`toBi_step`: a System 0 step is a `wolfram23` step; `toBi_exit`: where
System 0 leaves its tape, `wolfram23` steps onto an implicit blank and its
explicit tape grows by one cell (`biSize`); `toBi_ofBi`: every valid
configuration (`IsValidWolfram23Cfg`) is `toBi` of one. Hence
`wolfram23_leaves`: from every valid configuration the run reaches a
configuration with one more explicit cell, that is, the head has left the
initial finite tape; and `wolfram23_not_periodic`, because `biSize` never
decreases along a `BiTM` run (`biSize_step`). This is the formal counterpart
of the refutations of REVIEW.md section 4.1 (the step-faithful predicates
needed a periodic configuration) and settles, in Smith's direction, what the
old code base treated as open.

Left undone in M4: the exit time is existential (the proof bounds it by the
measure, but no closed form is stated); `exitRight` is defined but nothing yet
relates the exit state of System 3 to that of System 0 through the
relabelings, which link F's "exit in state A" will need; the relabelings are
proved only in the direction the chain uses.

### M5 notes (done 2026-09-21)

Three modules, all lakefile roots, about 1900 lines together:
`Smith/ParityBlocks.lean` (the parity theory of a block), `Smith/System3Runs.lean`
(the runs of System 3 over a block), `Smith/Conjecture3.lean` (the relation, the
per-rule lemmas, the initial tape, T3). Zero `sorry`, no `native_decide`;
`#print axioms` of `sys4_sys3_forwardSim`, `sys4_sys0_forwardSim`,
`conjecture3_finite` and `rep3_init` shows only `propext, Classical.choice,
Quot.sound`. `lake build` is 679 jobs. The D8 vectors of `Tests/SmithVectors.lean`
run a six-step System 4 program through System 3 by `decide`.

Parity blocks (`Smith/ParityBlocks.lean`). A block of 1s and 2s is `Bits` (`2`
is `true`). A System 3 scan in state B or C is the prefix-XOR transducer
`scanFrom s`; `T = scanFrom false` is Smith's operator, and the C-scan is the
B-scan of the block with its first bit toggled (`scanC_eq_T_toggle`, Lemma
0.5-0.8 in one line). `parAt x k` is the parity of the block after `k` scans,
and `parAt_xor` says it is linear. Smith's strings for the one-element sets
(p. 8) are the rows `row n i` of the rule-60 automaton, `row n (i + 1) = stepR
(row n i)` with `T (row n (i + 1)) = row n i`; at width `2^w` the rows have
period `2^w` by the Frobenius identity `stepR^[2^w] x = shiftR^[2^w] x xor x`
(`stepR_iterate_two_pow`, an induction on `w` with `shiftR^[2^w]` killing the
block), which gives Lemma 1 as `parAt_row : parAt (row (2^w) i) k = decide (k =
i)` for `i, k < 2^w`. So the block of a set is the XOR of the rows of its
elements, and it decodes to the set on the next `2^w` scans; this is the whole
of Smith's "Lemma 1" and of the choice of `w`.

The runs (`Smith/System3Runs.lean`): `walkLeft` (state A walks left over 1s and
2s onto the first other cell, Lemma 0.1), `turnA` (`A0 -> B2>`), `starB` (`B0 ->
A2<`), `scanBlock` (a scan over a block followed by a non-zero cell leaves
`scanFrom s` behind and exits in the state given by the parity), `scanBlock0B`
and `scanBlock0C` (a scan followed by a 0: an exit in B lands on the 0 in B; an
exit that would be in C turns the last cell, a 2, into a 0 and lands on the 0 in
state A, the two 0s of Smith's star active in state C, p. 11 and 13).

The relation (`Smith/Conjecture3.lean`). Rather than a predicate on pairs of
tapes, an abstract configuration `AC` (items left of the head nearest first,
items right of it, the left end `0^m 2 2 1^t`, the System 4 state, and a
`Focus`) from which both `AC.to4` and `AC.toL` are computed; `Rep3 c3 c4 w h`
is "some `AC` satisfying `AC.OK w h` maps to both". `AC.OK`: every block has
width `2^w` and decodes to its set on the next `h + 1` scans (`Decodes`), `h`
being the System 4 fuel; `h + 3 <= 2^w`; `h <= m`; the star-side rule (a star
left of the head, or at the head in state A or C, stands in the place of the
last cell of the set before it, which is a 2; a star right of the head, or at
the head in state B or C, in the place of the first cell of the set after it,
which is a 2: `LeftOK`, `RightOK`, `HeadLastTrue`, `HeadFirstTrue`); and the
head shapes: `setA` (state A, anywhere in the block, held as a zipper), `setB`
(state B or C, first cell), `setT` (System 4 in state C right after rule 5,
System 3 in state B on the second cell, the block decoding to the set with 1
toggled), `star`, `off` (head on the closing 1 after System 4's head left the
tape). The star-side rule and the `setT` shape were found and validated by a
Python checker of the relation along `system4.pl` runs before anything was
proved; the checker's first version had the active set on the wrong side of
the rule, which is the kind of error the formalization is for.

The per-rule lemmas, each a `Matches` witness (a System 3 run of at least one
step to the `AC.toL` of an `AC` whose `AC.to4` is the System 4 result): rule 1
is `walkLeft` over `p + 1` steps onto the previous block's last cell or a
star's 0, or, at the left end, `turnRun` (`p + 2t + 6` steps: walk, `turnA`,
scan back over `2 2 1^t` which becomes `2 1 1^t`, so `t` grows by one and `m`
drops by one); rule 2 is one `turnA`; rule 4 one `starB`; rule 5 one `turnA`
onto the second cell of the next block; rule 3 is `scanRun`, a scan of `2^w`
cells (or `2^w - 1` from `setT`) landing as `landing` says on the closing 1,
the next block's first cell, or a star (`afterScan_toL`, `afterScan_to4`,
`afterScan_OK` repack the result once for all three starts). The parity side:
`Decodes_T` (B-scan decodes the decremented set), `Decodes_scanC` (the C-scan
too, because the first-bit toggle is `xorB` with `unit`, whose parity is at
scan 0 only), `Decodes_transient` (the skipped-cell scan after rule 5: the
block's first bit is kept, so the result is `true :: T tail`, and toggling 1
before the decrement is toggling 0 after it), and `Decodes_parity` (the first
scan decides `0 in S`, which is what makes System 3's exit state agree with
System 4's toggle). `ac_step` dispatches on the focus and the state, and

    sys4_sys3_forwardSim (w) : ForwardSim (fueled system4Sys) (lsys sys3) (fun p c => Rep3 c p.1 w p.2)

The initial tape: `encSet` is Smith's block (`s42s0-3.pl`): the XOR of the
rows of the elements and of the last row (all 2s), plus the row `2^w - 2` when
the first cell would be a 1; the two extra rows have their parity at scans
`2^w - 1` and `2^w - 2`, outside the window, and make the first cell a 2 so
that a star may stand in its place (`firstTrue_encSet`, `Decodes_encSet`).
`initAC w h S0 rest` is the abstract configuration of a well-formed tape with
the head on its leftmost element in state A, left end `0^h 2 2 1`;
`rep3_init` is the initial condition, under `h + 3 <= 2^w`, no star last, and
every set element in `[0, 2^w)`. Composed with M4's `sys3_sys0_forwardSim`,

    sys4_sys0_forwardSim (w) : ForwardSim (fueled system4Sys) (lsys sys0)
      (fun p c0 => exists c3, Rep3 c3 p.1 w p.2 /\ c0 = phi2 (phi3 c3))

and `conjecture3_finite` is T3 in the finite form of `conjecture4_finite`: a
System 4 run of `n <= h` steps is tracked by the System 0 run from
`phi2 (phi3 (initAC w h S0 rest).toL)` at strictly increasing times, the
configurations standing in `Rep3` with the budget counting down.

Design notes. The relation is stated on the System 3 tape directly and the
swap of the cells left of the head is left to `phi3`, so Smith's `s42s0-3.pl 3`
output is `phi3` of `initAC`'s tape, not the tape itself. Blocks are kept as
plain `Bits` inside items and decomposed only at the focus; left items are
rendered by `ofBits x.reverse`, so a set is split at its last bit by `x.reverse
= b :: xl` and never by `getLast`. `Item.set` carries both the block and the
System 4 set, which removes the `Forall2` between item lists and element lists
that a first version had. The width condition is `h + 3 <= 2^w`, weaker than
Smith's `2^w >= 3f` because the fuel, not `f`, bounds the scans; the link to
`f` is made when T2 and T3 are composed (M6), where `2^w` must also exceed
every set element, which `conjecture4_finite`'s bounds give in terms of `f`.

Left undone in M5: the exit event (the head leaving the tape in state C at
the end of the System 4 run, T4's "first exit to the right") is present as the
`off` focus of `Rep3` but not yet turned into an `exitRight` statement for
System 3 or System 0; the System 4 side of the composition (T2's `RepS4` and
`decodeS4`) is not yet threaded through `Rep3` to a decoder on the System 0
tape; both are M6.

### M6 notes (done 2026-09-21)

One module, `Smith/Conjecture0.lean` (about 950 lines), plus a rule-count clause
added to the M2 step lemmas. Zero `sorry`, no `native_decide`; `#print axioms
conjecture0_finite` shows only `propext, Classical.choice, Quot.sound`. `lake
build` is 680 jobs. The D9 vectors of `Tests/SmithVectors.lean` exercise the
decoder by `decide`, with negative instances.

The statement, `conjecture0_finite`: for a two-colour cyclic tag system `C0`, an
initial configuration `cfg` and a budget `N` such that the run lasts the
`appendants.length * N` steps of the budget and leaves a nonempty word, there
are a wolfram23 configuration `start`, a width `2^w`, a band `b`, strictly
increasing times `times i` and an exit time `T` with: `start` valid and in state
A; at time `times i` the tape decodes by `decodeW23 (2^w) b` to `dbl` of the
`i`-th working string; up to time `T` the explicit tape keeps its size, so no
cell outside the initial tape is visited; and at time `T + 1` the head is on the
cell right of the tape, a 0, in state A. That last clause is Smith's exit
condition (p. 4: "the first cell to become active after the emulation has
finished is the cell to the right of the initial condition, and if that cell is
a 0 it becomes active in state A"), and it holds for the composed encoders
because System 3's exit `C1 -> A00>` reads the implicit 0 as its right
neighbour, which is `B2 -> A0>` of wolfram23 after the relabelings.

Two corrections to the T4 statement of section 2. The head does not start on
the leftmost cell of the tape but on the first cell of the first block, as in
Smith's `s42s0-3.pl` output (the marker `A` sits after the left end `0^m 2 2 1`;
the leftmost cell is a 0, as the conjecture says, and it is never visited: the
turns consume at most `h` of the `m >= h` zeros). And the run must be assumed
to last the budget without emptying the word: an emptied word empties the
System 5 bag, System 4 then sweeps forever and never exits.

The pieces. `Bound5`: the integers of a System 5 configuration grow by at most
one per step (`xorMerge_mem_or` for the pop), which bounds the terminal
decrements and the band. `RepresentsExact` (in `Smith/ConjectureFive.lean`):
`Represents` plus "the rule list is exactly two rules per appendant of budget";
the M2 step lemmas now also return `s'.rules.length + 2 = s.rules.length` (the
witness they construct pops exactly the leading pair), so
`conjecture5_finite_exact` gives an empty rule list at the end of the budget,
which is the terminal event T2's exit needs; `Represents` alone leaves the
rules beyond the budget unconstrained. `repS4_terminal`: with the rules
exhausted, `repS4_dStep` until 1 is in the bag, then `repS4_exit`, by
induction on a bound of a bag element. `RepS4_decode_band`: the decoder of
link C below a fixed band, which lies under the debris (`b + 2j + 2 <= 2f`) and
holds every bag position (`2e - 2 < b`); the band is `2f - 2L - 2` for the
System 5 run length `L`, and `f` is chosen above `B0 + 2L` so that the bag,
bounded by `B0 + L`, fits under it. `system5ToSystem4_wellFormed`,
`system5ToSystem4_last_set`, `system5ToSystem4_elem_lt`: what `rep3_init`
needs of the encoder tape (no adjacent stars by an append lemma over the
block structure; every set integer below `3f + 3`).

The decoder `decodeW23 N b cfg`: the head cell and the cells right of it up
to the first 0 are the blocks of the leading conglomerate (the star after the
leading sets is a 0 standing in for the first cell of the next set, so the run
of nonzero cells is exactly `|K| * N` long); `decodeBlocks` checks that they
are 1s and 2s making whole blocks, XORs the blocks (`xorBlocks`), takes the
parity set of the XOR below `b` (`parAt`), and reads it as link C does
(`x / 2 + 1` on an even set, `none` otherwise); `decodeBag` of link B then
reads the working string. `rep3_decode`: at a System 4 configuration
`<sets K ++ star :: R, 0, B>`, the configuration one step after every
scheduled time of T2 (the head has turned and is on the first cell of the
first block in System 3's state B, where `phi3` leaves the head and the cells
to its right alone), `decodeW23` agrees with `decodeS4`; the decoding times
are therefore the T2 times plus one System 4 step, carried to System 0 by the
T3 schedule. `rep3_exit`: at System 4's exit configuration `Rep3` forces the
`off` focus, so the System 3 head is on the closing 1 in state C.

The assembly composes the finite forms (T1 exact, `conjecture4_finite` with
budget `H = L + M + 1`, `repS4_terminal`, `conjecture3_finite` with fuel
`h4 = T4 + b`, `toBi_run`) by their schedules rather than by `ForwardSim_comp`,
because the fuel lives in a different source system at each link. The
parameters are picked in order: `M = (B0 + L).toNat`, `H`, `f = B0.toNat + 2H
+ 2L + 5`, `b`, then the System 4 exit time `T4`, `h4`, and `w = h4 + 3f + 6`
(so `2^w > w` covers both `h4 + 3` and `3f + 3`). "Never visits a cell outside
the tape" is `biSize` constant, since a wolfram23 step onto an implicit blank
grows the explicit tape (`toBi_exit`), and the zipper run is defined.

Left undone in M6: the decoder returns the doubled word `dbl w`; undoubling
is a one-line inverse not yet written. The phase of the cyclic tag
configuration is not decoded (it is `(cfg.phase + i) % appendants.length`).
The times are existential (`times`, `T`) with no closed form. T6, the infinite
form, is not attempted (optional M7).

### M4b notes (done 2026-09-21)

Three modules, all lakefile roots, about 1200 lines together:
`TagSystem/TagRounds.lean` (2-tag systems over any alphabet, runs by rounds),
`TagSystem/CockeMinsky.lean` (the simulation of a binary machine by a 2-tag
system), `TagSystem/TMToCTS.lean` (the finite alphabet, the cyclic tag system,
the decoder, T7). Zero `sorry`, no `native_decide` outside the tests;
`#print axioms t7_finite` shows only `propext, Classical.choice, Quot.sound`.
`lake build` is 851 jobs. `Tests/TMToCTSVectors.lean` runs a three-state
machine through the tag system by `decide` and through the cyclic tag system
by `native_decide`, and reads it back with the decoder.

Rounds (`TagSystem/TagRounds.lean`). `stepP P` is the 2-tag step with
productions `P` on `List sigma` (`Tag.step` is `stepP ts.productions`, so
nothing about `Fin k` enters the construction). A round processes the whole
current word: `passOut P u` is the concatenation of the productions of every
other symbol of `u`, starting with the first; `nStepsP_even` says a word of
even length `2n` is replaced by `passOut` of it in `n` steps; `nStepsP_odd`
says a word of odd length `2n + 1` is replaced in `n + 1` steps by `passOut`
of it without its first symbol, because the last symbol read takes the first
appended symbol as its deleted partner. That one dropped symbol is the whole
mechanism: the next round then reads the second of each pair. The
computation lemmas give `passOut` on pairs read aligned (`passOut_pairs2`),
on pairs read shifted (`passOut_cons_pairs2`: after a leading symbol, the
second of each pair), and on runs (`passOut_cons_replicate_append`: a symbol,
then half of a run rounded down, then the rest read from its first or second
symbol according to the run's parity).

The construction (`TagSystem/CockeMinsky.lean`), Cocke and Minsky's in the
phase design of the module header, validated by a Python simulation of random
machines before it was proved. The configuration `(q, left, head, right)` is
the word `A_q x (al_q x)^m B_q x (be_q x)^N` with `m = val left` (nearest
cell least significant) and `N = head + 2 val right`: the scanned cell is the
lowest bit of the right number. Round 1 doubles nothing and halves nothing;
it sets up the parity read: `A -> P1 P0`, `al -> p p`, `B -> Q`, `be -> r`,
after which the word `P1 P0 (p p)^m Q r^N` has the parity of `N + 1`. Round 2
reads `N / 2` of the `r` (the run starts after the odd prefix `Q`) and
produces the pairs `E1 E0 (e1 e0)^m F1 F0 (f1 f0)^(N/2)`; round 3 reads the
first of each pair when `N` is odd and the second when `N` is even, so every
symbol read in round 3 knows the scanned bit. Round 3 executes the
transition: for a move to the right it writes the next configuration word
directly (`w + 2m` and `N / 2`); for a move to the left it writes `G g^m H H
k^(4 (N/2))`, whose round 4 halves `m` and reads its parity into the frame
of round 5, which writes `A x (al x)^(m/2) B x (be x)^(2w + (m mod 2) + 4
(N/2))`. Whenever a round reads the second of each pair, the production of
the first symbol read carries a leading pad `x`, which the odd round before
it consumes, so the current tag word at the start of every machine step is
exactly the configuration word (`tm_step_tag`: three rounds for a move to
the right, five for a move to the left, step counts explicit).

The finite alphabet and the cyclic tag system (`TagSystem/TMToCTS.lean`).
Symbols carry a kind, a state and two bits; `enc` sends the symbols with
states below `S` injectively into `Fin (1 + 84 S)` and `dec` inverts it
(`dec_enc`), `WordOK` says all states of a word are below `S`, which the
productions preserve under `WF` (`prod_OK`, 21 kinds by one `simp` call),
and `nStepsP_enc` carries the runs over. `tagK tm S` is the resulting
`Tag (1 + 84 S)`; `cts_of_tag` iterates `tagToCTS_simulation` of the old
`TagSystem/TagToCTS.lean` (unchanged, its `2k` steps per tag step confirmed):
`k` tag steps are `2 (1 + 84 S) k` cyclic tag steps. `WF tm` (decidable):
from a state below `numStates` reading a bit the machine writes a bit and
moves to a state below `numStates`; `ValidCfg`: the tape holds bits. Then

    tm_cts_forwardSim : ForwardSim (tmSys tm) (ctsSys (tagToCTS (tagK tm S) _))
      (fun c d => ValidCfg c /\ c.state < S /\ d = ctsOfCfg S c)

and `tm_tag_forwardSim` at the tag level (used by M8, where the number of
cyclic tag cycles must be the number of tag steps). The decoder `decodeCTS`
reads the one-hot blocks back as tag symbols (`tagWordDecode`, an inverse of
`tagWordEncode`, from `range_map_beq`: the block of `i` is `i` falses, a
true, and falses), the symbols as a configuration word (`parseWord`, counting
the pairs), and the two numbers as tape halves (`natBits`); it returns the
configuration without trailing blanks (`canon`), because the numbers do not
see them, and `decodeCTS_word` is its correctness. `t7_finite` is T7 in the
finite form of the other links.

Design notes. States are `Nat` in the symbols, not `Fin S`, so that the
productions need no bound; the bound is an invariant (`WordOK`) rather than a
type. `WF` restricts the machines to two symbols, as PLAN.md section 3 allows
(link I, step 2); a base-`k` variant of the rounds is possible but not done,
and neither is the classical reduction of `k`-symbol machines to two symbols.
The halting state 0 of `BiTM` is not treated specially by the tag system: the
simulation is stated for machine steps, and a halted machine makes none.

Left undone in M4b: the reduction to two symbols; a decidable `WF` for
`numSymbols`; the tag system's own halting is not related to the machine's.

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
