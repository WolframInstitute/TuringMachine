# 11. Open items

The list below comes from the independent adversarial review of 2026-09-21 (eight
reviewers, three verifiers per finding, synthesis), reconciled with the code as of
commit `bb4f95b`. None is a soundness problem: the review found no blocker and confirmed
the axiom check. They are gaps between the statement and the word "universal", and
debts in the documentation. Items are ordered by weight. Status 2026-09-22: items
marked "done" were applied after T6 landed; the rest are open.

## A. Mathematics

1. Closed-form initial condition and finish-time bounds (major). The tape of
   `[[Smith.conjecture0_finite]]` and `[[Smith.wolfram23_universal]]` is existential and
   sized in the proof from the emulation's own run lengths (chapter 08). To answer the
   "the encoder does the computation" objection the way Smith does (p. 20-26), the
   development needs: (i) Smith's System 5 finish-time bound `finishTime P <= 3^(n-1) M`
   (T2 of `docs/PLAN.md` section 2 promises it; the M3 notes say it is undone; no
   declaration named `finishTime` exists); (ii) a System 4 exit-time bound from the
   explicit step counts of `[[Smith.dStep]]`, `[[Smith.popPhase]]`, `[[Smith.repS4_terminal]]`;
   (iii) a bound on the tag steps of chapter 03 in terms of `|c| + n` (the round lengths
   are explicit in `[[TagSystem.tm_step_tag]]`); (iv) a lemma that T7's cyclic tag run
   continues for any budget at or above the needed one, including after `tm` halts
   (`[[BiTM.step]]` is `none` in state 0 and the Cocke-Minsky step lemmas need `q != 0`);
   (v) a definition `IC tm c n` from those bounds and the theorem restated with
   `start = IC tm c n`, or at least `biSize start <= F tm c n` for a closed form `F`. A
   merely computable `IC` that runs the systems would not answer the objection.
2. The infinite form T6 (chapter 10): done 2026-09-22, `[[Smith.wolfram23_infinite]]`.
   One right-infinite tape per machine and input, no budget and no hypothesis on
   halting. It does not by itself give a closed form for the size of block `k`.
3. Binary machines (minor). `[[TagSystem.WF]]` covers two-symbol machines; the reduction
   of k-symbol machines, or a bridge to Mathlib's `Turing.TM0`, is not formalized.
   Wording of `docs/PLAN.md` section 2 T7/T8 ("well-formed binary TM"): done.
4. Event-based decoding times (minor). The schedule is existential and nothing is said
   about `decodeTM` at other times; on the D9 tape `decodeW23` returns `some` at
   unscheduled times. The proof has a syntactic marker (System 4 pop event, head at the
   left end in state A) that could be surfaced, and a clause "at every time up to `T`
   the decoder returns `none` or the latest scheduled configuration" would close it.
5. The halt row (minor). `WF` constrains the never-executed row of state 0 because the
   tag productions keep applying `tm.transition 0 _` after halting. A wrapper under
   `forall q < numStates, 0 < q -> ...` via a `patch0` lemma (`nSteps (patch0 tm) =
   nSteps tm`) would remove the wart. Documented in the `WF` docstring (done
   2026-09-22); the wrapper is open.
6. `decodeCTS` soundness (minor). Done 2026-09-22: `symbolDecode` requires the block
   length `k`, `tagWordDecode` requires whole blocks, with the soundness lemmas
   `[[TagSystem.symbolDecode_sound]]` and `[[TagSystem.tagWordDecode_sound]]` and negative
   vectors in `Tests/TMToCTSVectors.lean` (a short last block, a stray bit).
7. `ForwardSim` documentation (minor). Done: the docstring of `Smith/Simulation.lean`
   says the content is in the relation being a decoder graph.
8. Two unreachable branches of `[[BiTM.System4.step]]` differ from `system4.pl` (rule 5
   with the star last, rule 4 at index 0). Done: comments in `BiTM/System4.lean`,
   `docs/REVIEW.md` softened to "faithful on all well-formed tapes".

## B. Tests

9. No vector runs `[[Smith.decodeTM]]` or `[[Smith.undbl]]`; on the D9 positive tape
   `decodeTM` returns `none`. Done in part 2026-09-22: `undbl` vectors and the last two
   stages of `decodeTM` on the doubled encoding of a configuration
   (`Tests/TMToCTSVectors.lean`), `decodeTM` rejecting the D9 and D10 words
   (`Tests/SmithVectors.lean` D10). A positive `decodeTM` vector on a rendered tape is
   out of reach: it needs a block of width at least `2^13`, whose rendering builds its
   parity rows by iteration.
10. No vector runs a machine into the halt state. Done: `tmH` in
    `Tests/TMToCTSVectors.lean`, through the tag system, the cyclic tag system and the
    decoder.
11. `Tests/SmithVectors.lean` header and `docs/PLAN.md` lines 273-277 say `native_decide`
    is used only for D5; D7 used it seven times and `Tests/TMToCTSVectors.lean` four
    times. Done: D7 and `Tests/TMToCTSVectors.lean` now close by `decide +kernel`, so
    `native_decide` is used only for the three D5 runs, and the headers say so.

## C. Documentation corrections (docs/PLAN.md unless stated)

12. Section 2 T4 (lines 63-67): "started on its leftmost cell in state A" is false for
    the witness; the head starts on the first cell of the first block, the left end is
    `0^m 1 1 2` after relabeling, the run must last the budget with a nonempty word
    (`hne`), the schedule is existential. Line 93 "T4 alone ... is exactly Smith's
    theorem": qualify. Done 2026-09-22.
13. Section 2 T6 (lines 75-78): "Follows from T4 and T5" is unsupported by the formal T4
    (chapter 10); T5 is not used by the chain (chapter 07). Done (T6 rewritten).
14. Section 2 T1 (lines 46-48) and T4 (line 66), T8 (lines 90-91): "explicit times" and
    "times are fixed by pop events" describe the step lemmas, not the theorems; say "at
    a strictly increasing schedule of times". Done.
15. Section 2 T2 (lines 50-56): drop or mark as open the `finishTime` clauses; the M3
    table row lists the finish-time bound as delivered. Done (marked open in T2; the M3
    row is left as the original plan, the M3 notes say it is undone).
16. Section 8 decision 5 (line 1174): marked resolved but `System5.step` is still `none`
    on an empty rule list; change to "deferred, superseded by `repS4_terminal`; see M3
    notes", and fix line 3. Done.
17. M8 notes (lines 1111-1125): "universality in the literal sense" and "a closed-form
    `IC` would be a corollary of unfolding those choices" are wrong (unfolding yields
    `tt n`, `t5 n`, `k`); add to the caveats the `n`-dependence of the tape, the absence
    of any encoder bound, and the missing Lemma 2. "The regression vectors ... exercise
    it" (lines 1120-1123): they exercise the components, not `decodeTM`. Done.
18. M8 row (line 210) and M8 notes (line 1094): `BiTM.Machine` does not exist; the type
    is `TM.Machine`. The statement also mentions `TagSystem.WF`, `TagSystem.ValidCfg`,
    `BiTM.IsValidWolfram23Cfg`, `TagSystem.canon`, `Smith.biSize`; list them. Done (the
    row; the M8 notes' sentence now reads "as the milestone table asks" against the
    corrected row).
19. M6 notes (lines 930-936): "the leftmost cell ... is never visited" is not a theorem
    (only `biSize` constancy is). Done.
20. Section 1 describes the 2026-09-14 tree with no stale marker; add a status line
    pointing to the M0-M8 notes. Done.
21. `Smith/Universality.lean` header lines 4-6 ("Every run ... from a finite initial
    tape"): loose; the docstring at lines 48-56 is correct. Header reworded (done); the
    name is kept, item 2 being done.
22. `Smith/Lookahead.lean` header: `exitRight` is not the observable exit of Conjecture 3
    in the chain (two-cell rule at the right end); reword (chapter 02). Done.
23. `TagSystem/TagToCTS.lean` line 9: "The CTS has k appendants" should read "2k
    appendants: k production encodings followed by k empty appendants". Done.
24. `Smith/Conjecture3.lean` imports `Smith/LoopFree.lean` only for `lnSteps_add`; move
    the lemma to `Smith/Lookahead.lean` so that the import graph does not suggest T3 uses
    T5. Done.
25. `docs/REVIEW.md` line 161 (item 8 above) and the status notes: add one after T6.
    Done.
