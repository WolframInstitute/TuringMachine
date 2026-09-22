# Review: state of the Lean formalization of Wolfram (2,3) universality

Date: 2026-09-15. Branch `lean-proofs`, commit 6f002bc. Reviewer: Claude (Fable 5.1), from
24 parallel file/PDF/fidelity audits plus direct `lake env lean` probes (see "Method").

Status note (after milestone M0, same day): this is a dated snapshot of the tree at commit
6f002bc. The file paths and line numbers in sections 2, 4 and 6 refer to that layout. M0 moved
`BiTM/SmithChain.lean`, `BiTM/CockeMinsky.lean`, `BiTM/CockeMinskyConstruction.lean`,
`BiTM/Smith.lean`, `BiTM/System1.lean`, `BiTM/GeneralizedTM.lean`, `BiTM/Wolfram23Periodic.lean`
and the 19,305-line `BiTM/CTSToSystem5.lean` unchanged to `Archive/BiTM/` (line numbers still
valid there), replaced `BiTM/CTSToSystem5.lean` by a slim encoder module, trimmed
`TagSystem/HaltsEmpty.lean` and `BiTM/HaltInduction.lean`, fixed the two encoder bugs of section
4.3 (stars, phase), removed `native_decide` from the theorem chain, stated the Nodup and
well-formedness invariants, and added `Vectors/SmithVectors.lean`. See PLAN.md, "M0 notes".

Status note (after milestone M1, same day): the tree is now on `leanprover/lean4:v4.32.2`
with Mathlib pinned at tag `v4.32.2`, and `Smith/Simulation.lean`, `Smith/Doubling.lean` and
`Smith/Represents.lean` (the `ForwardSim` calculus, the doubling lemma and the representation
relation) are lakefile roots. Sections 1 and 7 below describe the pre-M1 toolchain, module
count and build time and are stale in those respects; PLAN.md, "M1 notes", is the current
record. The `native_decide` sites still in `OneSidedTM/` predate M0, are outside the Smith
chain and are not depended on by it, as the M0 notes record.

Status note (after milestone M3, 2026-09-21): `Smith/System4Runs.lean` and
`Smith/Conjecture4.lean` prove T2, the System 5 -> System 4 link, with the fixed
`s52s4.pl` encoder (section 4.3's two missing stars) and the exit in state C; the
line "System 5 -> System 4: no emulation theorem attempted" in section 2 is
therefore stale. PLAN.md, "M3 notes", is the current record.

Status note (after milestone M4, 2026-09-21): Systems 1, 2 and 3 exist
(`Smith/Lookahead.lean`, on the lookahead machine type section 4.3 asks for) and
the equivalences 0 = 1 = 2 = 3 are proved as forward simulations
(`Smith/Systems123.lean`), so the "missing" entries for them in the table of
section 5 are stale. T5, loop-freeness, is proved (`Smith/LoopFree.lean`,
`Smith/Wolfram23Bridge.lean`: `wolfram23_not_periodic`), which closes in Smith's
direction the periodicity question that section 4.1 says the old code treated as
open, and confirms the refutation of the step-faithful predicates recorded there.

Status note (after milestone M5, 2026-09-21): the System 4 -> System 3 link, the
part of the chain section 2 calls the hardest and section 5 marks as missing, is
proved (`Smith/ParityBlocks.lean`, `Smith/System3Runs.lean`,
`Smith/Conjecture3.lean`: `sys4_sys3_forwardSim`, and with M4
`sys4_sys0_forwardSim`, `conjecture3_finite`). PLAN.md, "M5 notes", is the
current record; the table of section 5 is stale for Systems 3 and 4.

Status note (after milestone M6, 2026-09-21): T4, the finite form of
Conjecture 0 with Smith's exit condition and a decoder, is proved
(`Smith/Conjecture0.lean`: `conjecture0_finite`, axioms `propext,
Classical.choice, Quot.sound`). This is the theorem section 1 says the code
base did not have (its `not_halts_wolfram23_valid` was a tautology); it is
Smith's theorem, cyclic tag emulation, and is not named universality (T8
composes it with T7, which is M4b/M8). PLAN.md, "M6 notes", is the current
record.

Status note (after milestone M4b, 2026-09-21): T7, the simulation of a
well-formed binary Turing machine by a cyclic tag system with a decoder, is
proved by a genuine Cocke-Minsky construction (`TagSystem/TagRounds.lean`,
`TagSystem/CockeMinsky.lean`, `TagSystem/TMToCTS.lean`: `t7_finite`). This
replaces the halting-oracle "faithful Cocke-Minsky" theorem section 4.1
rejects. PLAN.md, "M4b notes", is the current record.

Status note (after milestone M8, 2026-09-21): the headline theorem of PLAN.md
section 2, T8, is proved: `Smith.wolfram23_universal` in
`Smith/Universality.lean`, with axioms `propext, Classical.choice, Quot.sound`
and no `sorry` or `native_decide` in its dependency cone. This supersedes the
bottom line of section 1 (the tautological `not_halts_wolfram23_valid`, the
four uncloseable sorries, the archived halting-oracle encoding). Section 1 to
8 below are kept as the record of the state on 2026-09-14 and of the reasons
for the plan; PLAN.md, "M0 notes" to "M8 notes", is the record of what was
built.

Status note (after milestone M7, 2026-09-22): T6, the infinite form, is
proved: `Smith.wolfram23_infinite` in `Smith/Infinite.lean` (with
`Smith/Guards.lean`), axioms `propext, Classical.choice, Quot.sound`. One
right-infinite tape per machine and input, no budget and no hypothesis on
halting; the blocks are guarded System 4 tapes chained through rule 5, not
T4's finite initial conditions, which do not chain. What it does not give:
a closed-form size for block `k` (the parameters come from the emulation's
own run lengths, as in T4), a single schedule of times across blocks, and,
like T8, any bound on the encoder, so its statement alone does not exclude
a tape holding the run in advance (the blueprint's chapter on the infinite form). The
independent review of 2026-09-21 (the blueprint's open-items chapter, `Blueprint/Chapters/OpenItems.lean`) found no
soundness problem in M0-M8; its documentation corrections are applied in
PLAN.md sections 1, 2, 5 and 8 and in the module headers it names. PLAN.md,
"M7 notes", is the current record.

Status note (after milestone M9, 2026-09-23): open item 1 is done. The
initial conditions are definitions that run no system: `Smith.IC tm c n`
for T8 (`Smith.wolfram23_universal_ic`), `Smith.icStart s` for T4
(`Smith.conjecture0_closed`), `Smith.ITape tm c` for T6
(`Smith.wolfram23_infinite_ic`), built from closed-form bounds on the runs
of System 5 (`Smith.System5.run_bound`), System 4
(`Smith.System4.run_bound`) and the tag system (`TagSystem.tagTime_le`).
The existential statements are corollaries. Axioms unchanged. Not stated as
a theorem: a closed-form bound on the size of the tapes. PLAN.md, "M9
notes", is the current record.

## 1. Bottom line

- The project builds. All 37 modules compile on the pinned toolchain `leanprover/lean4:v4.29.0-rc6`
  in about 10 s from the cached oleans (0 errors, 73 lint warnings). Three declarations use `sorry`
  (four sorry sites): `cmStep_sim` (CockeMinskyConstruction.lean:1029), `smith_reduces_faithful`
  (SmithChain.lean:214) and both branches of `smith_per_step_extension` (SmithChain.lean:1133, 1180).
- None of the four sorries can be closed. Each sits under a statement that is false or unsatisfiable
  (Section 4). The work needed is restatement, not more proof search.
- No theorem in the development currently states a true and meaningful universality property of
  `wolfram23`. The headline `wolfram23_universal : IsUniversal wolfram23` is axiom-clean but
  `IsUniversal` is provably equivalent to `True` (CockeMinsky.lean:205, 372) and both endpoint
  reductions are constant encoders. Every stronger predicate the loop introduced
  (`IsSubstantiallyUniversal`, `SmithReducesFaithful`, `SmithReducesStepFaithful`,
  `SmithChainEmulators`) is refutable for `wolfram23`.
- What is genuinely correct and reusable: the machine model and the `wolfram23` table, Cook's
  tag -> CTS reduction, the validity invariant and non-halting of `wolfram23`, the System 5
  interpreter, the CTS -> System 5 encoder (bit-exact against Smith's `cy2s5.pl`), the System 4
  interpreter, the symmetric-difference library, and the false-head 4-step lemma. Roughly 3,000 of
  the 35,000 lines.
- Two definitions are wrong relative to Smith: the System 5 -> System 4 encoder drops two stars
  per rule block (its emulation is observably different), and "System 1" is `wolfram23` relabelled
  (Smith's Systems 1-3 need a machine that reads the right neighbour, which the current type cannot
  express).
- The formalization is off in kind, not just in detail: it treats universality as halting
  preservation via a time-independent encoder, while Smith proves finite-budget emulation of
  cyclic tag systems by a budget-dependent initial condition, for a machine that never halts.

## 2. What exists

Files and sizes (lines): TM/Defs 52, BiTM/Basic 148, TagSystem/Basic 216, TagSystem/TagToCTS 578,
TagSystem/HaltsEmpty 2993, BiTM/HaltInduction 1980, BiTM/Wolfram23Valid 333, BiTM/Wolfram23Periodic
580, BiTM/Smith 98, BiTM/XorMerge 317, BiTM/System5 1489, BiTM/System4 805, BiTM/System5ToSystem4
294, BiTM/CTSToSystem5 19305, BiTM/GeneralizedTM 298, BiTM/System1 452, BiTM/CockeMinsky 642,
BiTM/CockeMinskyConstruction 1957, BiTM/SmithChain 2439.

Import graph (leaf to root): TM.Defs -> BiTM.Basic; TagSystem.Basic -> TagToCTS -> HaltsEmpty;
HaltInduction (Basic, HaltsEmpty); Wolfram23Valid -> Wolfram23Periodic; Smith; XorMerge -> System5,
System4 -> System5ToSystem4; CTSToSystem5 (TagSystem.Basic, System5); GeneralizedTM -> System1;
CockeMinsky -> CockeMinskyConstruction -> SmithChain (imports everything).

Intended chain: TM -> 2-tag (Cocke-Minsky) -> CTS (Cook) -> System 5 -> System 4 -> System 3 ->
System 2 -> System 1 -> System 0 = wolfram23 (Smith 2007).

Link status:
- TM -> 2-tag: definitions exist; `cocke_minsky_reduces` is the constant `fun _ => []` encoder;
  the "faithful" variant is a halting-oracle trick (Section 4.4); the concrete Minsky-style encoder
  is sorry'd and false as defined.
- 2-tag -> CTS: fully proved (forward halting direction only, which is what the chain uses).
- CTS -> System 5: encoder faithful; emulation theorems false as stated (Section 4.2).
- System 5 -> System 4: encoder wrong by two stars per rule; no emulation theorem attempted beyond
  hypothesis-parametric lifting lemmas whose hypotheses the encoder cannot satisfy.
- System 4 -> 3 -> 2 -> 1: nothing (Systems 2, 3 absent; System 1 is a relabelled wolfram23).
- System 1 -> System 0: lock-step "equivalence" that holds only because both sides are wolfram23.
- Universality: `IsUniversal wolfram23` proved via constant encoders; `isUniversal_wolfram23_via_chain`
  is conditional on the unsatisfiable `SmithChainEmulators`.

## 3. What is genuinely proven and reusable

- `TM/Defs.lean`, `BiTM/Basic.lean`: zipper tape model, `step`, `nSteps`, `eval`, `Halts`. The
  `wolfram23` table matches Smith's System 0 (PDF p.3) entry for entry and Wolfram rule 596440
  (base-12 digits 2,4,9,1,11,4). Keep. Caveats in Section 5.
- `TagSystem/Basic.lean`, `TagSystem/TagToCTS.lean`: Cook 2004's one-hot, 2k-appendant construction.
  `tagToCTS_simulation` (TagToCTS.lean:303) is an exact lock-step theorem (one tag step = 2k CTS
  steps). Halting is a strict sandwich `Tag.HaltsEmpty -> CTS.Halts -> Tag.Halts` (both converses
  have concrete counterexamples). Header line 9 still describes an abandoned k-appendant version.
- `BiTM/Wolfram23Valid.lean`: `IsValidWolfram23Cfg`, preservation, `not_halts_wolfram23_valid`
  (wolfram23 never enters state 0 from an in-alphabet config), `wolfram23_at_n`. Solid. Two
  `native_decide` proofs (`wolfram23_nextState_in_range`, `wolfram23_write_in_range`) leak 12
  `native_decide` axioms into everything downstream; `decide` suffices.
- `BiTM/XorMerge.lean`: correct symmetric-difference library; `xorInsert` is also the primitive in
  `System4.step` and in the s52s4 rule encoder.
- `BiTM/System5.lean` `System5.step`: faithful to `system5.pl` (PDF p.30-31) on Nodup bags. Verified
  line by line against the 36-line printed trace for `cy2s5.pl 3 01 1 10` and the C-format string.
  One Lean step = Perl steps 1-3 fused (pair cancellation happens lazily inside `xorMerge` at pop
  time). Faithful only under a `bag.Nodup` invariant that is nowhere stated in the file.
- `BiTM/CTSToSystem5.lean` lines 56-216: the encoder `ctsConfigToSystem5Bag`, `encodeAppendant`,
  `processCycle`, `nCycles`, `ctsRulesToSystem5Rules`, `ctsToSystem5`. Bit-exact against `cy2s5.pl`
  on both PDF examples (verified by `#eval` in this session and by Python on 2000 random CTSs):
  working string 11011 -> bag 1,3,4,6,7,9,10,12,13,14,15,16,17,19,20,22,23,25,26,28 and rules
  33,36,39,40,43,46 / 31,34,37,38,41,44 / "" / "" / 49,50,53,56 / ...; "01" with rules 1, 10 ->
  bag 1,2,3,4,5,7,8,10, rules 15,18 / 13,16 / "" / "" / 21,24,27,28 / 19,22,25,26 / ...
  Structural lemmas worth keeping: r1 = r2.map (+2), Nodup, 4 rules per appendant, length and
  lower-bound facts (about 200 lines).
- False-head engine: from a bag Perm-equivalent to the encoder bag with head bit 0, four
  consecutive pops consume r1, r2, "", "" with r2+2 cancelling r1 and leave `aux rest 1` up to
  permutation (CTSToSystem5.lean:16462, 17597; SmithChain.lean:1230, 1526). Correct and reusable.
- Empirical discoveries recorded in comments and confirmed by the audits: a 0-head CTS step costs 4
  System 5 steps (PPPP), a 1-head step costs 6 (PDPPDP); after a 1-head step the bag is
  `aux rest 1 ++ aux appendant (counter rest + 6)`, a valid but non-canonical encoding.
- `BiTM/System4.lean` `System4.step`: faithful to `system4.pl` and to the five rules of
  Conjecture 4 (PDF p.10) on all well-formed tapes (two unreachable branches differ; see the
  comments in BiTM/System4.lean); matched configuration for configuration over 7 + 1337 + 9906 Perl
  steps, including the p.41 C-format output `110011110011110010` on the Perl-encoded tape.
- Thin cores of `TagSystem/HaltsEmpty.lean` (about 400 lines: `tagNSteps`, eval/nSteps bridges,
  `CTS_nSteps_succ_decompose`, `find_min_or_none`, `CTS_Halts_induction`) and `BiTM/HaltInduction.lean`
  (about 30 declarations: step/halted dichotomy, `nSteps_one/add`, `BiTM_nSteps_some_compose`,
  `BiTM_Halts_nSteps_pred`, tape-length monovariants).

## 4. What is false, vacuous, or misdirected

### 4.1 Universality predicates

- `IsUniversal utm` (CockeMinsky.lean:130) is `True` for every machine: `IsUniversal_trivial` (205)
  and `IsUniversal_iff_exists_halting_cfg` (372) are in the same file. `wolfram23_universal` (144)
  composes `encode := fun _ => []` (1-symbol tag system) with `encode := fun _ _ => state-0 config`.
  Cook's theorem is invoked on the constant empty word and discarded.
- `Halts wolfram23 cfg` is unreachable from valid configs (Wolfram23Valid.lean:179). It is
  satisfiable only from state 0 or via the out-of-alphabet fallback at Basic.lean:116 (state >= 3 or
  head >= 3 halts in one step). Wolfram's machine has no halt state; every `Halts wolfram23`
  conclusion is about a formalization artifact.
- `IsSubstantiallyUniversal wolfram23` (233) is false. `Machine.transition` is total on Nat, so the
  source ranges over infinite-state "machines" whose halting trajectories have unbounded backward
  depth into one configuration; exact per-step emulation into a finite machine forces a repeat.
  Independently, a self-looping source forces a periodic point of wolfram23 (next item).
- `SmithReducesStepFaithful` (Smith.lean:35) is false: `selfLoopCTS` has a self-step, so
  `smithReducesStepFaithful_implies_wolfram23_periodic` (Smith.lean:91) yields a periodic wolfram23
  configuration, and wolfram23 has none. Smith proves this on PDF p.21-22 ("a finite region of
  system 0 cannot get into a loop", via a zero-position-sum measure in System 1); the audits
  re-derived it by a rightmost-cell case analysis and by exhaustive search over all valid configs
  with total tape length <= 9. The docstrings (Smith.lean:69-70, SmithChain.lean:2379-2386) treat
  periodicity as an open question; the sign of Smith's key lemma is backwards in the codebase.
- `SmithReducesFaithful` and `SmithReducesFaithfulHalting` (SmithChain.lean:86, 108) are
  unsatisfiable: clause 1 fixes a single halted target H; clause 2 gives, for the CTS with the one
  empty appendant, halting chains of every length L into the single halted CTS config, hence L
  distinct wolfram23 ancestors of H on one trajectory; but tape length is monotone under `step` and
  the alphabet along a trajectory into H is finite, so H has finitely many ancestors. Therefore
  `smith_reduces_faithful` (214) is a false sorry.
- `SmithChainEmulators` (SmithChain.lean:2118) is unsatisfiable: clause 1 fails for `ctsToSystem5`
  (iter 873), clause 5 fails for `system5ToSystem4` (iter 787: a halted System 5 config encodes to a
  set in state A, which steps), clauses 3 and 6 need wolfram23 to reach state 0, and the bundle
  forces a periodic point. All 8 theorems conditioned on it are vacuous at wolfram23.
- `CockeMinskyReducesFaithful` (CockeMinskyConstruction.lean:1097) is satisfied for every TM by a
  halting oracle: `cocke_minsky_reduces_faithful_universal` (1802) branches on `Halts tm cfg` with
  `classical`, extracts the halting time with `Classical.choose`, and encodes halting configs as
  a^(2*remaining time) into the fixed tag system {a -> [], b -> [b,b]}, non-halting ones as [b,b].
  The tag system has decidable halting; the encoder does all the work. Its consumer
  `TM_to_CTS_reduction_via_cocke_minsky` (SmithChain.lean:2176) inherits the emptiness.

### 4.2 Conjecture 5 statements (CTS -> System 5)

- `ctsToSystem5_emulates_with_budget` (SmithChain.lean:1623) and `ctsToSystem5_emulates` (1708)
  are false as stated. Counterexample: cts {appendants := [[false]]}, cfg {data := [true,false]},
  N = 1, n = 1: the System 5 run halts after 6 steps and its bag never equals
  `ctsConfigToSystem5Bag {data := [false,false]}`. They type-check only because
  `smith_per_step_extension` (1060) is sorry'd. Its two sorries (1133 false-head, 1180 true-head)
  cannot be closed: (a) there is no budget hypothesis (N = 0 gives no steps), (b) after any 1-head
  step the bag is a valid encoding with a permanent gap (the appended block lands at counter + 6),
  never the canonical contiguous encoding, so rigid equality is unreachable for every m.
- `SmithPerStepExtensionPerm` (1204) is false too (N = 0; and for every 1-head step at N >= 1), so
  `ctsToSystem5_emulates_with_budget_perm` (1672) is an implication from False.
- The Perm-chain lemmas in CTSToSystem5.lean (iters 1000-1185) re-encode the rule queue fresh from
  the current CTS config at every chain point and ignore `cfg.phase`. They prove "a freshly restarted
  encoder tracks one 0-head step up to permutation", not that the single System 5 run from the
  `cy2s5.pl` output tracks the CTS.
- Root cause (confirmed by the p.19-20 text and by simulation): the correct invariant is a relation,
  not equality with one canonical encoder output. Smith's initial condition allows any strictly
  increasing arrangement of pairs (gap 1 for a 0, gap 2 for a 1) and requires second rules to sit
  at least 3 above everything earlier; after a step "the resulting string is an acceptable initial
  condition". The comparison points are rule-pop events, not a fixed step count.
- `ctsToSystem5_halt_preservation` (CTSToSystem5.lean:19082) is closed with N := 0 (empty rules),
  as the file itself notes.
- The AllEmptyAppendants family (about 45 theorems) is honestly proved but for CTSs whose appendants
  are all empty, i.e. systems that never append anything.

### 4.3 Definition bugs relative to Smith

- `system5ToSystem4` (System5ToSystem4.lean:62-73): `s52s4.pl` prints a star before each rule set
  and before each all-integers set; the Lean encoder omits both, giving 8f-2 elements per rule block
  instead of 8f, adjacent sets, and star runs f/2f/2f-2 instead of f+1/2f+1/2f-1. Running the
  Lean-faithful System 4 interpreter on the Lean-encoded tape for the PDF example
  (`s52s4.pl 16 2 1,4 1,6 "" ""`) prints `11001111100111100` where Smith prints
  `110011110011110010`; with the two stars restored the outputs agree token for token (f = 16, 24).
  `encodeBag` also skips the parity cancellation the Perl performs (matters only for non-Nodup bags).
- `ctsRulesToSystem5Rules` ignores `cfg.phase`: rules always start from appendant 0. Faithful to
  `cy2s5.pl` (which has no phase) only at phase 0; the emulation theorems quantify over all configs.
  Also Lean's `n` counts full cycles (4*|appendants|*n rules) where the Perl's n counts appendant
  emissions (4n rules); harmless superset, but PDF budgets must be rescaled. The proof's "very large
  integers" (PDF p.19, 21) are absent, exactly as in `cy2s5.pl`; they matter only for Conjecture 5's
  terminal event (attempt to pop a nonexistent rule), which drives the System 4 exit in state C.
- `System5.step` halts when the rule list is empty; Smith's system keeps decrementing until a 0
  surfaces and that attempt is the distinguished terminal event. The halt check is also placed at the
  start of a step (Perl: end), so step counts can differ by one on degenerate configs.
- `GeneralizedTM` reads one cell. Smith's Systems 1-3 read the active cell and its right neighbour
  ("B20" = state B, active 2, neighbour 0; PDF p.4 table and the Perl `%rules` on p.45:
  B20 -> A00>, B21 -> B12>, B22 -> B11>). `System1.lean` models 20/21/22 as extra tape symbols and
  leaves their transitions as halting placeholders, so `system1` is wolfram23 relabelled. The
  lock-step theorems (System1.lean:163, 248) are true of the relabelling and false of the real System
  1 (one System 1 step = 3 System 0 steps for B21/B22). Systems 2 and 3 do not exist in Lean.
- `Machine.numStates`/`numSymbols` are never read by `step`; `wolfram23.numStates := 3`.
  `TM.decodeRule` decodes Wolfram rule numbers incorrectly (unused).

### 4.4 Model limitations that shape any target statement

- `Config` is a finite zipper with implicit blank 0 on both sides, and equality is representation
  equality (`left = []` and `left = [0]` differ; rule (B,2) writes explicit zeros). Periodicity as
  used in the obstruction theorems is representation-level; semantically the notions coincide here.
- Smith's infinite emulation (PDF p.22, "From arbitrary to infinite") concatenates the finite
  initial conditions IC(C,1), IC(C,2), ... into an infinite, non-periodic tape. The current `Config`
  cannot express it; the finite-budget statement (Conjecture 0 as stated on p.3 and p.21) can.
- Halting: wolfram23 never halts; Smith's "emulation finished" is a tape/head event (the head first
  becomes active on the cell right of the initial condition, in state A). Any Halts-based predicate
  for wolfram23 is modelling a state the machine does not have.

## 5. Smith's argument and its Lean counterparts

| PDF claim | Pages | Lean counterpart |
| --- | --- | --- |
| System 0 table (Conjecture 0) | 3 | `wolfram23` (faithful) |
| Systems 1, 2, 3 tables; equivalences 0=1=2=3 (relabelings, 1-or-3 steps) | 3-5, 44-48 | missing; `system1` is not System 1 |
| Lemma 0, Lemma 1 (parity scans over 2^w blocks), Corollaries, Methods 1-2 (XOR CA) | 5-9 | missing |
| Conjecture 4 (System 4 rules) | 10 | `System4.step` (faithful) |
| Conjecture 4 implies 3: System 4 -> System 3 initial condition, w choice | 10-15, 21 | missing |
| Conjecture 5 (System 5) | 15 | `System5.step` (faithful under Nodup; terminal event not modelled) |
| Conjecture 5 implies 4: s52s4 initial condition, f and t, two-case sweep | 16-18, 32-33 | `system5ToSystem4` (two stars missing); no emulation theorem |
| Doubling trick D(C) | 18 | implicit in the encoder; no lemma |
| CTS -> System 5 initial condition (cy2s5) | 19, 28-29 | `ctsToSystem5` (faithful at phase 0) |
| Proof of Conjecture 5: 0-head and 1-head cases, termination via large integers | 19-20 | false-head fragment only; statements false |
| Finish-time bound 3^(n-1) M; f = 2*3^(n-1)*M; large integers >= 3^(n-1)M+1 | 20-21 | missing |
| Loop-freeness of System 0 (finite region cannot trap the head) | 21-22 | missing; codebase assumes the opposite is open |
| Exit condition and infinite emulation by concatenation | 21-22 | missing; not expressible on `Config` |
| Lemma 2 (parity sets), one-cycle and 2n-cycle conditions (non-universality of the encoder) | 22-26 | missing |
| Interpreters cytag/cy2s5/system5/s52s4/system4 with printed traces | 27-43 | usable as regression test vectors |

## 6. Dead weight (estimates)

- `BiTM/CTSToSystem5.lean`: 19,305 lines, about 1,141 declarations, 48 `native_decide` sites. About
  10 declarations are referenced from other files. Iterations 1185-1866 are a corollary treadmill
  ("N-lemma milestone" banners), including about 60 theorems under the unsatisfiable hypothesis
  `not (System5.Halts (ctsToSystem5 ...))` (every encoded System 5 run halts). Keep about 400 lines.
- `BiTM/SmithChain.lean`: 2,439 lines; keep the false-head lemmas (about 100 lines); the 700-line
  Cocke-Minsky smoke-test block and the hypothesis-parametric universality scaffold go.
- `TagSystem/HaltsEmpty.lean`: 173 declarations, 41 used elsewhere; keep about 400 lines.
- `BiTM/HaltInduction.lean`: about 110 declarations, about 30 load-bearing; the induction principles
  it is named for have zero external uses.
- `BiTM/System5.lean` about 85 of 120 declarations unused; `BiTM/System4.lean` Halts algebra is about
  an always-true predicate (every finite System 4 tape halts); `BiTM/Wolfram23Periodic.lean` has no
  downstream importers; `BiTM/CockeMinskyConstruction.lean`, `BiTM/CockeMinsky.lean`,
  `BiTM/GeneralizedTM.lean`, `BiTM/System1.lean`, `BiTM/Smith.lean` are misdirected wholesale.
- Iteration history (from comments; no transcripts survive): iters ~90-135 Cocke-Minsky ladder;
  397-483 universality predicates; 526-588 halting infrastructure; 637-746 periodicity; 645-665
  encoder lemmas; 792-875 the Conjecture 0 saga (3 -> 4 rules per appendant fix at 818, 0-head
  success at m=4, 1-head refutation, schematic-bag discovery, termination insight); 888-913
  cancellation algebra; 956-1029 counter shift (abandoned); 1000-1185 Perm chain; 1185-1866
  lemma farming. Stray references to "iter 6979/7341/8409" are typos.

## 7. Engineering facts

- Toolchain `v4.29.0-rc6` was not installed when this review started; the VS Code Lean extension
  auto-installed it (done 01:14). Elan proxies block silently on the install lock meanwhile.
  Other installed toolchains: v4.15.0, v4.30.0, v4.32.0, v4.32.2.
- No Mathlib, no Batteries (`lake-manifest.json` packages: []). Bags are `List Int`; sets in System 4
  are `List Int`; all multiset reasoning is hand-rolled.
- `#print axioms`: `wolfram23_universal`, `isUniversal_wolfram23_via_chain`,
  `cocke_minsky_reduces_faithful_universal`, `tagToCTS_halting_forward` use only propext,
  Classical.choice, Quot.sound. `smith_reduces_faithful`, `ctsToSystem5_emulates_with_budget`,
  `smith_per_step_extension` use sorryAx. `not_halts_wolfram23_valid`, `wolfram23_halts_iff_system1_halts`
  carry 12 `native_decide` axioms from Wolfram23Valid.lean.
- Full `lake build` takes about 10 s with a warm cache; CTSToSystem5 rebuilds in 4 s.
- Lean MCP (`uvx lean-lsp-mcp` 0.30.0) is registered in this config dir as of today.

## 8. Method

Parallel audits: 11 module readers, 5 chunk readers over CTSToSystem5.lean, 1 PDF reader (pages
15-26; the readers for pages 3-14, 27-43, 44-55 and the dependency analyst were cut off by the
account spend limit and their content was covered by the fidelity checkers instead), and 6 fidelity
checkers that re-implemented both the Perl programs and the Lean definitions in Python and compared
them on the PDF's printed traces and on thousands of random inputs. Ground truth from Lean itself:
`lake build`, `#print axioms`, and `#eval` of the encoder and System 5 trajectory on the two PDF
examples (scratch file, not committed). Claims of falsity above were checked against concrete
counterexamples by at least one checker and, where cheap, by the reviewer.
