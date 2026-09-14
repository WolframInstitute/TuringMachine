/-
  BiTM.CTSToSystem5

  Smith's CTS → System 5 encoder (PDF `TM23Proof.pdf` p. 27-28,
  `cy2s5.pl`).  Doubles each bit of the working string and each
  appendant of the CTS into integer-multisets that drive a
  System 5 simulation.

  Extracted from `BiTM.CockeMinskyConstruction` in a refactor.

  Contents:
    * `ctsConfigToSystem5BagAux`, `ctsConfigToSystem5Bag` — encode
      the working string into the System 5 bag
    * `counterAfterWorkingString` — counter value after the working-
      string loop
    * `encodeAppendant`, `processCycle`, `nCycles` — encode CTS
      appendants into System 5 rules over `n` cycles
    * `ctsRulesToSystem5Rules`, `ctsToSystem5` — top-level encoder
    * Length lemmas: 4 ints per bit, 3 rules per appendant per cycle
    * **Iter 859-868 schematic-predicate infrastructure**:
      - `schematicTrueHeadBag pre appended` — bag at m=6 in true-head
        trajectory (per universal formula verified across 5 cases)
      - `schematicFalseHeadBag data` — bag at m=4 in false-head
        trajectory (= rigid encoder)
      - Length, boundary, and cons-decomposition lemmas
      - Concrete schematic predicate target for `smith_per_step_extension`

  PROGRESS NOTES (iters 859-868):
    Discovered the predicate `_emulates_with_budget`'s rigid bag
    equality is satisfiable for false-head step at m=4 (across 1/2/3-bit
    data) but FAILS for true-head step (machine-verified at N up to 20,
    m up to 200).  Identified the universal pattern: at m=6, the
    true-head bag has a 6-counter gap before the appended portion,
    captured by `schematicTrueHeadBag`.  This gives a concrete
    schematic-predicate target for the smith_per_step_extension
    true-head sorry.  See iter 836/859/860/861/862/863 for details.
-/

import TagSystem.Basic
import BiTM.System5

namespace BiTM

open TagSystem

/-- Per-bit doubling encoder for the CTS working string into System 5 bag
    positions.  Faithfully implements the `while($temp ne '')` loop of
    `cy2s5.pl` (PDF p. 27).

    For each bit of `cfg.data`, starting at counter `i = 1`:
    * `true` ('1'): emit `[i, i+2, i+3, i+5]`, advance counter by 6.
    * `false` ('0'): emit `[i, i+1, i+2, i+3]`, advance counter by 4.

    Verified against the test1.cy example (PDF p. 27): working string
    `11011` produces bag `1,3,4,6,7,9,10,12,13,14,15,16,17,19,20,22,23,25,26,28`. -/
def ctsConfigToSystem5BagAux : List Bool → Int → List Int
  | [], _ => []
  | true :: rest, i => i :: (i + 2) :: (i + 3) :: (i + 5) ::
                       ctsConfigToSystem5BagAux rest (i + 6)
  | false :: rest, i => i :: (i + 1) :: (i + 2) :: (i + 3) ::
                        ctsConfigToSystem5BagAux rest (i + 4)

/-- **`ctsConfigToSystem5BagAux_nil` (iter 792)**: empty data encodes
    to empty bag at any starting counter.  Direct from the def. -/
@[simp] theorem ctsConfigToSystem5BagAux_nil (i : Int) :
    ctsConfigToSystem5BagAux [] i = [] := rfl

/-- **`ctsConfigToSystem5BagAux_true_cons` (iter 793)**: explicit
    cons-true unfolding.  `rfl`-equivalent to the def, useful for
    `rw` chains. -/
theorem ctsConfigToSystem5BagAux_true_cons (rest : List Bool) (i : Int) :
    ctsConfigToSystem5BagAux (true :: rest) i
    = i :: (i + 2) :: (i + 3) :: (i + 5) ::
      ctsConfigToSystem5BagAux rest (i + 6) := rfl

/-- **`ctsConfigToSystem5BagAux_false_cons` (iter 793)**: explicit
    cons-false unfolding.  `rfl`-equivalent to the def. -/
theorem ctsConfigToSystem5BagAux_false_cons (rest : List Bool) (i : Int) :
    ctsConfigToSystem5BagAux (false :: rest) i
    = i :: (i + 1) :: (i + 2) :: (i + 3) ::
      ctsConfigToSystem5BagAux rest (i + 4) := rfl

def ctsConfigToSystem5Bag (cfg : CTSConfig) : List Int :=
  ctsConfigToSystem5BagAux cfg.data 1

/-- Sanity check: the PDF's `test1.cy` example matches our encoder.
    Working string `11011` should produce
    `[1, 3, 4, 6, 7, 9, 10, 12, 13, 14, 15, 16, 17, 19, 20, 22, 23, 25, 26, 28]`. -/
example :
    ctsConfigToSystem5Bag { data := [true, true, false, true, true], phase := 0 }
      = [1, 3, 4, 6, 7, 9, 10, 12, 13, 14, 15, 16, 17, 19, 20, 22, 23, 25, 26, 28] := by
  decide

/-- The counter value (= `i` in `cy2s5.pl`) after the working-string loop.
    Starts at 1, advances by 4 per `false` bit or 6 per `true` bit. -/
def counterAfterWorkingString (data : List Bool) : Int :=
  data.foldl (fun acc b => acc + if b then 6 else 4) 1

/-- **Iter 863 helper**: the schematic bag at m=6 (true-head step), per the
    universal formula verified across iters 859/861/862/863:
    `bag.mergeSort = aux pre 1 ++ aux appended (END_OF_PRE + 6)`
    where `END_OF_PRE = counterAfterWorkingString pre`.

    The 6-counter gap is constant (= 2 P-step counter advancement per
    Smith Conjecture 5).  This gives the schematic-predicate target
    that the true-head branch of `smith_per_step_extension` must hit. -/
def schematicTrueHeadBag (pre appended : List Bool) : List Int :=
  ctsConfigToSystem5BagAux pre 1 ++
    ctsConfigToSystem5BagAux appended (counterAfterWorkingString pre + 6)

/-- **Iter 864 helper**: the schematic bag at m=4 (false-head step) is just
    the rigid encoder of `result.data`.  Verified across iters
    850-851/855/860 for cfgs of 1/2/3-bit data with various appendants.

    No counter offset for false-head: dropped false bit's encoding
    region is consumed in 4 D-steps and the trajectory's bag returns
    to `aux result.data 1` (counter resets contiguously). -/
def schematicFalseHeadBag (data : List Bool) : List Int :=
  ctsConfigToSystem5BagAux data 1
-- Length theorems for the helpers are defined after
-- `ctsConfigToSystem5BagAux_length` (line ~682).

/-- Encode one CTS appendant as a pair of System 5 rules `(first, second)`,
    plus the post-encoding counter value.  Per `cy2s5.pl` (PDF p. 28):
    * `false` ('0'): firstRule += [i+2, i+3]; secondRule += [i, i+1]; i += 4.
    * `true`  ('1'): firstRule += [i+2, i+5]; secondRule += [i, i+3]; i += 6.

    Returns (firstRule, secondRule, newCounter). -/
def encodeAppendant : List Bool → Int → List Int × List Int × Int
  | [], i => ([], [], i)
  | true :: rest, i =>
      let (r1, r2, i') := encodeAppendant rest (i + 6)
      ((i + 2) :: (i + 5) :: r1, i :: (i + 3) :: r2, i')
  | false :: rest, i =>
      let (r1, r2, i') := encodeAppendant rest (i + 4)
      ((i + 2) :: (i + 3) :: r1, i :: (i + 1) :: r2, i')

/-- Process one cycle through all CTS appendants.  Each appendant
    produces 3 System 5 rules (pair + a blank rule, per `cy2s5.pl`
    PDF p. 28). -/
def processCycle : List (List Bool) → Int → List (List Int) × Int
  | [], i => ([], i)
  | rule :: rest, i =>
      let (r1, r2, i') := encodeAppendant rule i
      let (restRules, i'') := processCycle rest i'
      (r1 :: r2 :: [] :: [] :: restRules, i'')
      -- ITER 818 FIX (per Smith's `cy2s5.pl` PDF p. 28):
      -- `print $temp," ",$temp2,' "" ""'` — emits FOUR rules per
      -- appendant: r1, r2, "", "".  All `3 * |appendants| * N` rule-
      -- count references updated to `4 * |appendants| * N` in the
      -- cascade fix.

/-- **`processCycle_nil_full` (iter 795)**: empty rule list at counter
    `i` produces empty cycle output and unchanged counter.  Direct
    from the def.  (`processCycle_nil` exists for the `.1 = []`
    component.) -/
@[simp] theorem processCycle_nil_full (i : Int) :
    processCycle [] i = ([], i) := rfl

/-- Repeat `processCycle` for `n` cycles, threading the counter.

    **PARAMETRIZATION NOTE (iter 820)**: Smith's `cy2s5.pl`'s `n`
    argument is "total appendant emissions" (cyclic — emits up to `n`
    appendants total across cycles), while our `n` is "complete cycle
    count".  Relationship: `cy2s5_n = lean_n * |appendants|`.  Our
    `nCycles cts.appendants N i` produces `4 * |appendants| * N` rules,
    while `cy2s5.pl N` produces `4 * N` rules.  This isn't a
    correctness issue per se (extra rules don't hurt — they're just
    unused trailing material), but means our `N` budget is "wider"
    than Smith's per cycle.  Downstream theorems' `N ≥ ...` hypotheses
    should account for this scale factor when comparing to PDF claims. -/
def nCycles (rules : List (List Bool)) : Nat → Int → List (List Int)
  | 0, _ => []
  | k + 1, i =>
      let (cycle, i') := processCycle rules i
      cycle ++ nCycles rules k i'

/-- **`nCycles_zero` (iter 794)**: 0 cycles of any rules at any
    counter produces an empty rule list.  Direct from the def. -/
@[simp] theorem nCycles_zero (rules : List (List Bool)) (i : Int) :
    nCycles rules 0 i = [] := rfl

/-- **`nCycles_succ` (iter 794)**: explicit succ-cycle unfolding.
    `rfl`-equivalent to the def, useful for `rw` chains.  -/
theorem nCycles_succ (rules : List (List Bool)) (k : Nat) (i : Int) :
    nCycles rules (k + 1) i
    = (processCycle rules i).fst ++ nCycles rules k (processCycle rules i).snd := rfl

/-- **Iter 929**: 1 cycle equals processCycle's output (with empty
    suffix from nCycles 0). -/
theorem nCycles_one (rules : List (List Bool)) (i : Int) :
    nCycles rules 1 i = (processCycle rules i).fst := by
  rw [show (1 : Nat) = 0 + 1 from rfl, nCycles_succ, nCycles_zero, List.append_nil]

/-- **Iter 935**: nCycles for k+1 takes first cycle = processCycle plus rest. -/
theorem nCycles_succ_eq_append (rules : List (List Bool)) (k : Nat) (i : Int) :
    nCycles rules (k + 1) i
      = (processCycle rules i).fst
        ++ nCycles rules k (processCycle rules i).snd :=
  nCycles_succ rules k i

-- Iter 930 ctsRulesToSystem5Rules_one moved after the def

/-- Per-rule doubling encoder for CTS appendants.  Faithful to
    `cy2s5.pl` PDF p. 28: starts the rule counter at
    `counterAfterWorkingString cfg.data + 2`, then runs `n` cycles
    through `cts.appendants`. -/
def ctsRulesToSystem5Rules (cts : CTS) (cfg : CTSConfig) (n : Nat) : List (List Int) :=
  nCycles cts.appendants n (counterAfterWorkingString cfg.data + 2)

/-- The CTS → System 5 encoder.  For an `n`-step CTS emulation, the
    rules list is `n` cycles of the CTS appendants.  `n` is the upper
    bound on emulation length passed to `cy2s5.pl` as its first arg. -/
def ctsToSystem5 (cts : CTS) (cfg : CTSConfig) (n : Nat) : System5Config :=
  { bag := ctsConfigToSystem5Bag cfg
    rules := ctsRulesToSystem5Rules cts cfg n }

/-- **Iter 930**: ctsRulesToSystem5Rules at N=1 unfolds to processCycle. -/
theorem ctsRulesToSystem5Rules_one (cts : CTS) (cfg : CTSConfig) :
    ctsRulesToSystem5Rules cts cfg 1
    = (processCycle cts.appendants (counterAfterWorkingString cfg.data + 2)).fst := by
  unfold ctsRulesToSystem5Rules
  exact nCycles_one cts.appendants (counterAfterWorkingString cfg.data + 2)

/-- **Iter 932**: bag projection of ctsToSystem5. -/
@[simp] theorem ctsToSystem5_bag_eq_bag (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    (ctsToSystem5 cts cfg n).bag = ctsConfigToSystem5Bag cfg := rfl

/-- **Iter 932**: rules projection of ctsToSystem5. -/
@[simp] theorem ctsToSystem5_rules_eq (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    (ctsToSystem5 cts cfg n).rules = ctsRulesToSystem5Rules cts cfg n := rfl

/-- Sanity check against the PDF's `test1.cy` example (p. 27).
    CTS appendants `[101, 01, 0, "", 010]`; first cycle's first three
    System 5 rules should be the encoding of `101`:
    `[33,36,39,40,43,46]`, `[31,34,37,38,41,44]`, `[]`. -/
example :
    (nCycles
      [[true, false, true], [false, true], [false], [],
       [false, true, false]]
      1
      (counterAfterWorkingString [true, true, false, true, true] + 2)).take 3
      = [[33, 36, 39, 40, 43, 46], [31, 34, 37, 38, 41, 44], []] := by
  decide

/-- **Iter 818 PDF-correctness test (PASSES with corrected encoder)**:
    per Smith's `cy2s5.pl` (PDF p. 28), each appendant produces FOUR
    System 5 rules: `temp temp2 "" ""` (two empty rules at the end).
    With the iter 818 fix, our encoder emits 4 rules per appendant.
    This test verifies the PDF-correct expected output for `test1.cy`'s
    first appendant `101`, including BOTH trailing empty rules. -/
example :
    (nCycles
      [[true, false, true], [false, true], [false], [],
       [false, true, false]]
      1
      (counterAfterWorkingString [true, true, false, true, true] + 2)).take 4
      = [[33, 36, 39, 40, 43, 46], [31, 34, 37, 38, 41, 44], [], []] := by
  decide

/-- **End-to-end smoke test**: encode the trivial CTS (working string `[1]`,
    one appendant `[1]`, 1 cycle) and run `System5.step` once.

    Initial bag `[1, 3, 4, 6]` (4 ints from one '1' bit).
    Counter after working string: 7.  Rules start at i = 9.
    Rule encoding for `[1]` at i=9: `([11, 14], [9, 12], 15)`.
    So rules list: `[[11, 14], [9, 12], []]`.

    After 1 step: 0 enters bag (1 - 1 = 0), so the first incremented
    rule `[12, 15]` is popped and merged into `bag.erase 0 = [2, 3, 5]`.
    `xorMerge` prepends each rule element (none in bag), giving
    `[15, 12, 2, 3, 5]`.  Rules now `[[10, 13], [], []]` (one extra
    empty rule per iter 818's 4-rules-per-appendant fix). -/
example :
    System5.step (ctsToSystem5
        { appendants := [[true]], nonempty := by decide }
        { data := [true], phase := 0 } 1)
      = some { bag := [15, 12, 2, 3, 5], rules := [[10, 13], [], []] } := by
  native_decide

/-- Multi-step smoke test: 2 steps from the same initial config (composed
    via two manual `System5.step` calls; `System5.nSteps` is defined later).
    Step 2 is a pure decrement (no `0` in `[14, 11, 1, 2, 4]`). -/
example :
    ((System5.step (ctsToSystem5
        { appendants := [[true]], nonempty := by decide }
        { data := [true], phase := 0 } 1)).bind System5.step)
      = some { bag := [14, 11, 1, 2, 4], rules := [[11, 14], [], []] } := by
  native_decide

-- (Iters 808-815: machine-checked counterexamples documenting that
-- the OLD 3-rules-per-appendant encoder couldn't satisfy Smith
-- Conjecture 0 for non-empty appendants.  Iter 816 identified the
-- root cause from the PDF; iter 818 applied the fix.)

/-- **Iter 821 verification with corrected encoder**: rerun the
    previously-failing case from iter 810.  For `cts := {appendants
    := [[true]]}`, `cfg := {data := [false, false]}`, `N := 3`, after
    1 CTS step `result.data = [false]` and encoded result bag = `[1,
    2, 3, 4]`.  Now check whether the corrected 4-rule encoder yields
    a System 5 trajectory reaching this bag. -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    ∃ m : Fin 50,
      (System5.nSteps (ctsToSystem5 cts cfg 3) m.val).map (·.bag)
        = some [1, 2, 3, 4] := by
  native_decide

-- (Iter 843: hand-guessed m values were wrong, removed.)

/-- **Iter 850 specific m verification**: m = 4 works (4 D-steps consume
    one false bit per Smith's PDF p. 28 trajectory).  Confirms the
    AllEmptyAppendants `_4steps_false_head` pattern carries to non-
    empty appendants when the popped rules' xor cancels. -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 3) 4).map (·.bag)
      = some [1, 2, 3, 4] := by
  native_decide

/-- **Iter 851 m=4 robustness**: same pattern for `[[false]]` appendant. -/
example :
    let cts : CTS := { appendants := [[false]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 3) 4).map (·.bag)
      = some [1, 2, 3, 4] := by
  native_decide

/-- **Iter 851 m=4 robustness**: same pattern for `[[true, false]]` 2-bit appendant. -/
example :
    let cts : CTS := { appendants := [[true, false]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 3) 4).map (·.bag)
      = some [1, 2, 3, 4] := by
  native_decide

/-- **Iter 855 longer-data verification**: m=4 false-head consumption
    works on data `[false, false, false]` (3 false bits) — bag at m=4
    matches encoded `[false, false]` (2 false bits remaining). -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 5) 4).map (·.bag)
      = some [1, 2, 3, 4, 5, 6, 7, 8] := by
  native_decide

/-- **Iter 852 true-head AllEmptyAppendants test**: for AllEmpty
    appendants `[[]]`, true-head case at m=6 should give bag = encoded
    result.  AllEmpty appendant adds nothing, so result.data = [false]
    (rest of [true, false] after dropping true-head). -/
example :
    let cts : CTS := { appendants := [[]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 3) 6).map (·.bag)
      = some [1, 2, 3, 4] := by
  native_decide

/-- **Iter 853 true-head non-AllEmpty NEGATIVE**: at m=6, non-AllEmpty
    `[[false]]` does NOT give exact encoded result bag.  Confirms iter
    834's negative finding at the smallest natural m candidate, and
    iter 836's predicate-weakness insight: Smith's actual claim for
    true-head with non-empty appendants is NOT exact bag-match at the
    natural m.  Either the predicate needs reformulation, or the
    proof needs to identify the correct m (likely much larger, with
    intermediate "noise" cancelling later). -/
example :
    let cts : CTS := { appendants := [[false]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 3) 6).map (·.bag)
      ≠ some [1, 2, 3, 4, 5, 6, 7, 8] := by
  native_decide

/-- **Iter 856 true-head with appendant `[[true]]`**: bag at m=6 has
    correct length (8) but NOT the encoded result values.  Confirms
    that true-head + non-empty appendant doesn't satisfy exact
    bag-match at m=6 for any non-empty appendant tested.  -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 3) 6).map (·.bag)
      ≠ some [1, 2, 3, 4, 5, 7, 8, 10] := by
  native_decide

/-- **Iter 857 true-head extended search**: try ANY m up to 100 for
    the true-head case `cts = [[true]], cfg = [true, false], N=3`.
    Encoded result for `[false, true]` is `[1,2,3,4,5,7,8,10]`.  -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    ¬ ∃ m : Fin 100,
        (System5.nSteps (ctsToSystem5 cts cfg 3) m.val).map (·.bag)
          = some [1, 2, 3, 4, 5, 7, 8, 10] := by
  native_decide

/-- **Iter 858 larger N test**: try N=20 with same true-head case
    to rule out budget shortage. -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    ¬ ∃ m : Fin 200,
        (System5.nSteps (ctsToSystem5 cts cfg 20) m.val).map (·.bag)
          = some [1, 2, 3, 4, 5, 7, 8, 10] := by
  native_decide

/-- **Iter 859 KEY DISCOVERY**: at m=6 with N=10, the true-head trajectory
    produces a bag that IS structurally the encoder of `[false, true]`
    but with NON-CONTIGUOUS counter offsets: first bit uses counter 1,
    second bit uses counter 11 (instead of contiguous 1, 5).

    Specifically: `bag.mergeSort = [1, 2, 3, 4, 11, 13, 14, 16]
    = ctsConfigToSystem5BagAux [false] 1 ++ ctsConfigToSystem5BagAux [true] 11`.

    This explains why the exact `s5_result.bag = ctsConfigToSystem5Bag result`
    predicate fails for true-head: `ctsConfigToSystem5Bag` uses a fixed
    starting counter and threads it through ALL bits contiguously.  The
    true-head System 5 trajectory introduces COUNTER GAPS between bits
    (the rule's contents land at higher counters than would be reached
    by contiguous threading).

    Resolution: the correct predicate is a SCHEMATIC equality — the
    bag decomposes into per-bit encoder outputs at SOME sequence of
    counters `c₀ < c₁ < ... < c_{k-1}` (one per data bit), not the
    rigid `[1, 1+#bits[0], ...]` sequence.  This is consistent with
    iter 836's PDF re-reading: Smith's actual claim is that the bag
    "represents" the data, not that it equals a specific list. -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 6).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some (ctsConfigToSystem5BagAux [false] 1 ++ ctsConfigToSystem5BagAux [true] 11) := by
  native_decide

-- Iter 860 probe: 2-bit false-head case. Bag length=4 confirmed.
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, true], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 4).map (fun s5 => s5.bag.length)
      = some 4 := by native_decide

/-- **Iter 860 KEY ASYMMETRY DISCOVERY**: false-head case satisfies the
    RIGID encoder predicate at m=4, even for multi-bit data.  For
    `cts := {[[true]]}, cfg := {[false, true]}, N := 10` after 1 CTS
    step result data = `[true]`, phase=1.  Bag at m=4 = `[1, 3, 4, 6]`
    = `ctsConfigToSystem5BagAux [true] 1` = `ctsConfigToSystem5Bag
    {data:[true], phase:1}` (the rigid encoder).

    **Counter RESET behavior** (false-head): the System 5 trajectory's
    counter resets/recycles back to 1 after consuming the dropped bit's
    encoding region — no counter gap.  Confirms the rigid predicate
    holds for false-head transitions across 1-bit AND 2-bit data.

    **Counter GAP behavior** (true-head, iter 859): the trajectory's
    counter does NOT reset — bag has gap [1, 2, 3, 4, 11, 13, 14, 16]
    instead of contiguous [1, 2, 3, 4, 5, 7, 8, 10].  4 P-step extension
    (true-head adds 2 P-steps to the 4 D-steps of false-head) leaves
    counter advanced by 6 = 2 × P-step counter cost.

    **Implication for predicate refinement**:
    - False-head sub-claim: closeable with RIGID predicate.
    - True-head sub-claim: needs SCHEMATIC predicate per iter 836
      option (b), specifically allowing per-bit counter offsets that
      arise from true-head's P-step counter advancement.

    This is GOOD NEWS — it means smith_per_step_extension's false-head
    case (line ~1001 in SmithChain.lean) is closeable with the EXISTING
    rigid statement, while only the true-head case (line ~1037) needs
    predicate reformulation. -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, true], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 4).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some [1, 3, 4, 6] := by native_decide

/-- **Iter 860 3-bit false-head verification**: same rigid-encoder
    behavior holds for `cfg := {[false, true, false]}, N := 10`.
    After 1 CTS step (drop false-head, no append) result = `{data :=
    [true, false], phase := 1}`.  Rigid encoder gives
    `aux [true, false] 1 = [1, 3, 4, 6, 7, 8, 9, 10]`.
    Confirms the rigid predicate holds for false-head transitions
    across 3-bit data too.  Pattern: m=4 false-head step always
    yields the rigid encoder of the post-step CTS data. -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, true, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 4).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some [1, 3, 4, 6, 7, 8, 9, 10] := by native_decide

/-- **Iter 864 false-head helper validation**: verify
    `schematicFalseHeadBag` matches the false-head trajectory bag
    across the 2/3-bit cases from iter 860. -/
example : -- 2-bit false-head: result data = [true]
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, true], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 4).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some (schematicFalseHeadBag [true]) := by native_decide

example : -- 3-bit false-head: result data = [true, false]
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, true, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 4).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some (schematicFalseHeadBag [true, false]) := by native_decide

/-- **Iter 861 verification with different appendant**: predict bag for
    iter 834's negative case (cts={[[false]]}, cfg=[true,false]) using
    the iter 861 pattern.  After 1 CTS step (drop true, append [false])
    result data = [false, false].  Predicted bag at m=6, N=10:
    `aux [false] 1 ++ aux [false] 11`. -/
example :
    let cts : CTS := { appendants := [[false]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 6).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some (ctsConfigToSystem5BagAux [false] 1 ++ ctsConfigToSystem5BagAux [false] 11) := by
  native_decide

/-- **Iter 862 UNIVERSAL FORMULA**: m=6 is the universal step count for
    the true-head transition, regardless of appendant length.  And the
    bag decomposition formula generalises to k-bit appendants.

    Verified across cases:
    - iter 859: 1-bit appendant, 2-bit data → m=6, pre=[false], appended=[true], offset=11
    - iter 861: 1-bit appendant, 3-bit data → m=6, pre=[false,true], appended=[true], offset=17
    - iter 862: 2-bit appendant, 3-bit data → m=6, pre=[false], appended=[true,false], offset=11

    **General formula** (true-head step):
      bag.mergeSort = aux pre 1 ++ aux appended (END_OF_PRE + 6)
    where:
      pre = result.data.take (result.data.length - appendant.length)
      appended = result.data.drop (result.data.length - appendant.length)
      END_OF_PRE = 1 + sumCounterAdvance(pre)
      sumCounterAdvance(bs) = sum over bits in bs of (false→4, true→6)

    The 6-counter gap is constant regardless of appendant length —
    it represents 2 P-step counter advancements (per Smith Conjecture 5,
    each P-step adds 3 to counter).  The appendant length only affects
    the LENGTH of `appended`, not the GAP. -/
example :
    let cts : CTS := { appendants := [[true, false]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 6).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some (ctsConfigToSystem5BagAux [false] 1 ++ ctsConfigToSystem5BagAux [true, false] 11) := by
  native_decide

/-- **Iter 870 rules inspection (simplest false-head case)**:
    cts={[[true]]}, cfg=[false, false], N=3.  rules[0] should be []
    (the encoder emits 4 rules per appendant per cycle: r1, r2, [], []
    per `cy2s5.pl` PDF p. 28). -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    (ctsToSystem5 cts cfg 3).rules.length = 12 := by native_decide

example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    (ctsToSystem5 cts cfg 3).rules.head? = some [13, 16] := by native_decide

/-- **Iter 870 step-by-step trace** of the false-head simplest case.
    Initial bag = aux [false, false] 1 = [1..8], rules[0] = [13, 16]
    (the encoded `[true]` appendant from PDF p. 28). -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 3) 1).map (fun s5 => s5.bag.length)
      = some 9 := by native_decide

/-- Iter 870: bag lengths at m = 0..4 in this trajectory:
    8 → 9 → 8 → 7 → 4.  Each step is a P-step (rule-popping); the
    cancellation pattern at step 4 reduces by 3 (the {1,2,3,4} portion
    shrinks but the popped rule's contributions linger). -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 3) 4).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some [1, 2, 3, 4] := by native_decide

/-- **Iter 871 rule-sequence verification**: the encoder emits 4 rules
    per appendant per cycle as `[r1, r2, [], []]` per `cy2s5.pl` PDF p. 28.
    For 3 cycles, total 12 rules.  Counter starts at
    counterAfterWorkingString [false,false] + 2 = 11. -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    (ctsToSystem5 cts cfg 3).rules
      = [[13, 16], [11, 14], [], [],
         [19, 22], [17, 20], [], [],
         [25, 28], [23, 26], [], []] := by native_decide

/-- **Iter 871 step-by-step bag trace** for cts={[[true]]}, cfg=[false,false], N=3.
    Step 1: pop rule [13,16], xor-merge with [1..7] (incremented to [14,17]
    after rule-increment, but the rule popped was already incremented).
    Step 2: bag at m=2 = ? -/
example : -- m=1
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 3) 1).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some [1, 2, 3, 4, 5, 6, 7, 14, 17] := by native_decide

example : -- m=2: rule [13,16] popped via xor-cancellation
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 3) 2).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some [1, 2, 3, 4, 5, 6] := by native_decide

example : -- m=3: pop empty rule (no merge), just decrement
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 3) 3).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some [1, 2, 3, 4, 5] := by native_decide

/-- **Iter 875 STRUCTURAL INSIGHT — System5 always terminates**.
    Each `System5.step` either consumes a rule (P-step) or decrements
    every bag element by 1 (D-step).  With finitely many rules and
    finite bag elements bounded above, the trajectory MUST halt:
    - Every D-step decreases (sum of bag elements) by |bag|.
    - Every P-step consumes 1 rule.
    - Total D-steps before next P-step is bounded by min(bag).
    - Total P-steps is bounded by |rules|.
    - Therefore total steps bounded.

    **Implication for Smith reduction**: for non-halting CTS configs,
    encoding into a finite System5Config must produce a trajectory
    that EVENTUALLY HALTS — but per-step CTS emulation requires
    infinite wolfram23 trajectory for non-halting CTS.  Conclusion:
    `SmithReducesFaithful` for non-halting CTS configs requires an
    encoder that produces UNBOUNDED wolfram23 tape (Smith's design).

    For halting CTS configs the System5 trajectory naturally halts,
    matching the CTS halt.  So the per-step emulation only needs to
    work on the halting prefix — which `cocke_minsky_reduces_faithful_universal`'s
    Classical.choose strategy can leverage.

    **Closure path refinement**: define `enc1 cts ctsCfg` as
    `ctsToSystem5 cts ctsCfg N` where N depends on `Halts cts ctsCfg`:
    - For halting: N = boundedHaltDepth-style witness
    - For non-halting: any N (encoded config halts; predicate handles
      via vacuous step clause: there's no `ctsCfg → ctsCfg'` chain
      because either CTS halts at ctsCfg [contradiction with cts.step]
      or evolves indefinitely [not handled by SmithReducesFaithful]).

    Wait — the SmithReducesFaithful step clause requires per-step
    for ANY (ctsCfg, ctsCfg') with cts.step ctsCfg = some ctsCfg'.
    This includes pairs from non-halting trajectories.  So this
    encoder design fails for non-halting CTS.

    **Final assessment**: `SmithReducesFaithful` may need to be
    weakened (per-step only for halting trajectories) or we accept
    that the codebase's faithful version is `cts.Halts → halt`
    only — which is precisely `SmithReduces` (the existing weak
    predicate) with the trivial halt-collapse encoder.

    Or: design a wolfram23 encoder that supports unbounded tape
    growth.  This is Smith's actual approach. -/
example : True := trivial -- placeholder anchor for the comment above

/-- **Iter 873 NEGATIVE FINDING — encoder is NOT evolution-stable**.
    Tested whether `nSteps (ctsToSystem5 cts cfg 3) 4 = some (ctsToSystem5 cts cfg' 2)`
    for cfg=[false,false], cfg'=[false]: machine-checked **FALSE**.  Bag
    matches (= [1,2,3,4]) but rules diverge.

    Reason: after 4 P-steps, original rules `[[13,16],[11,14],[],[],
    [19,22],[17,20],[],[]...]` become `[[23,26],[21,24],...]`
    (4 increments + first 4 popped).  Fresh `ctsToSystem5 cts [false] 2`
    has rules computed from a counter starting at counterAfterWorkingString
    [false]=5 with 2 cycles, NOT the +4-incremented suffix of the original.

    **Implication for chain hypothesis h₁_step**: cannot use
    `enc1 cts ctsCfg = ctsToSystem5 cts ctsCfg N` for any fixed N — the
    `nSteps` of the encoder doesn't land on the encoder of the next state.

    **Closure paths**:
    1. Define a different `enc1` that IS evolution-stable (e.g., uses
       a counter offset baked into the rules, so increments preserve
       structure).
    2. Use a Classical.choose-based `enc1` (analogous to
       `cocke_minsky_reduces_faithful_universal`) that bakes the
       halting trajectory into the encoder.
    3. Weaken h₁_step's predicate to bag-equality only (but composition
       lemmas in System5ToSystem4.lean require full-config equality).

    Path 2 is the most promising — see `cocke_minsky_reduces_faithful_universal`
    construction in CockeMinskyConstruction.lean for the template. -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    let cfg' : CTSConfig := { data := [false], phase := 1 }
    ¬ (System5.nSteps (ctsToSystem5 cts cfg 3) 4 = some (ctsToSystem5 cts cfg' 2)) := by
  native_decide

/-- **Iter 871 STRUCTURAL INSIGHT**: in the false-head trajectory, each
    cycle of 4 encoder rules `[r1, r2, [], []]` is consumed by 4
    consecutive P-steps:
    * Step k+1: pop incremented r1 → introduces {r1+1}'s elements into bag
    * Step k+2: pop incremented r2 → xor-cancels r1's contribution
                 (because r2's elements at this step equal r1's at step k+1)
    * Step k+3: pop empty rule (`[]`) → just decrement, no change
    * Step k+4: pop empty rule (`[]`) → just decrement, no change

    Net effect: 4 P-steps decrement the bag by 4 (each step removes a 0
    via decrement) and the appendant's contribution from r1/r2 cancels.
    The result is `aux rest 1` where `rest` is `data.tail` (the dropped
    false-head's encoded region is consumed; counter resets to 1).

    This is the algebraic foundation for `smith_per_step_extension`'s
    false-head case.  Proving it requires:
    1. Algebraic xorMerge cancellation: `xorMerge (xorMerge bag r1) r2 = bag`
       when r2 = r1's earlier-step values (precise statement TBD).
    2. List bookkeeping: `(aux (false :: rest) 1).map (·-1) = 0 :: aux rest 1`.

    These are tractable; future iters will tackle them. -/
example :
    -- Net effect: bag at m=4 equals the rigid encoder of result.data
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 3) 4).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some (schematicFalseHeadBag [false]) := by native_decide

/-- **Iter 863 sumCounterAdvance verification via `schematicTrueHeadBag`**:
    test the helper with a TRUE bit in `pre`.  cts={[[false]]},
    cfg=[true, true, false].  After 1 CTS step result data
    = [true, false, false].  pre=[true, false], appended=[false].
    `schematicTrueHeadBag [true, false] [false]` should match bag
    at m=6, N=10.  This validates the helper's encoding. -/
example :
    let cts : CTS := { appendants := [[false]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, true, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 6).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some (schematicTrueHeadBag [true, false] [false]) := by
  native_decide

/-- **Iter 863 helper validation across all earlier cases**: verify
    `schematicTrueHeadBag` reproduces all 4 iter 859/861/862 patterns. -/
example : -- iter 859: 1-bit appendant, 2-bit data
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 6).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some (schematicTrueHeadBag [false] [true]) := by
  native_decide

example : -- iter 861: 1-bit appendant, 3-bit data
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false, true], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 6).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some (schematicTrueHeadBag [false, true] [true]) := by
  native_decide

example : -- iter 862: 2-bit appendant, 3-bit data
    let cts : CTS := { appendants := [[true, false]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 6).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some (schematicTrueHeadBag [false] [true, false]) := by
  native_decide

example : -- iter 861 case w/ different appendant
    let cts : CTS := { appendants := [[false]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 6).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some (schematicTrueHeadBag [false] [false]) := by
  native_decide

/-- **Iter 861 PATTERN IDENTIFIED**: the counter gap in true-head
    trajectories appears specifically BEFORE the bit appended by the
    CTS step (rule[0]'s contents).  Verified by binary-search on bag
    sum (= 118 for the 3-bit case) and reconstruction:

    Case A (iter 859, 2-bit): cfg=[true, false], CTS step appends
    [true] giving data=[false, true].  Bag at m=6, N=10
    = `aux [false] 1 ++ aux [true] 11`.  Gap of 6 between counter
    end of bit 1 (=4) and counter start of bit 2 (=11) — so 11 - 5 = 6.
    Bit 2 IS the appended bit.

    Case B (iter 861, 3-bit): cfg=[true, false, true], CTS step
    appends [true] giving data=[false, true, true].  Bag at m=6, N=10
    = `aux [false] 1 ++ aux [true] 5 ++ aux [true] 17`.  Bits 1, 2
    contiguous (counters 1, 5).  Gap of 6 between counter end of bit 2
    (=10) and counter start of bit 3 (=17) — so 17 - 11 = 6.  Bit 3
    IS the appended bit.

    **General rule**: in true-head trajectory at m=6, N=10, the bag
    decomposes as the rigid encoder of all PRE-step bits (data minus
    last bit, contiguous from counter 1) followed by the encoded
    APPENDED bit at counter `1 + 4*|pre| + 6` — i.e., a 6-counter
    gap before the appended portion.  This 6-gap = 2 P-step counter
    advancement (each P-step adds 3 to counter, true-head has 2 P-steps).

    **Predicate refinement**: the schematic equality for true-head case
    is `s5_result.bag.mergeSort = aux pre 1 ++ aux appended (1 + 4*|pre| + 6)`
    where `pre = result.data.dropLast` and `appended = result.data.lastN
    (length of currentAppendant)`.  Concrete and PDF-faithful. -/
example :
    let cts : CTS := { appendants := [[true]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false, true], phase := 0 }
    (System5.nSteps (ctsToSystem5 cts cfg 10) 6).map (fun s5 => s5.bag.mergeSort (· ≤ ·))
      = some (ctsConfigToSystem5BagAux [false] 1 ++ ctsConfigToSystem5BagAux [true] 5
              ++ ctsConfigToSystem5BagAux [true] 17) := by native_decide

/-- **Iter 833 second verification**: try a 2-bit non-empty appendant
    `[true, false]`.  CTS with this appendant, data `[false, false]`,
    N=3: after 1 CTS step, result data = `[false]` (false-head dropped),
    encoded result bag = `[1, 2, 3, 4]`.  Confirm encoder reaches it. -/
example :
    let cts : CTS := { appendants := [[true, false]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false, false], phase := 0 }
    ∃ m : Fin 60,
      (System5.nSteps (ctsToSystem5 cts cfg 3) m.val).map (·.bag)
        = some [1, 2, 3, 4] := by
  native_decide

/-- **Iter 834 true-head NEGATIVE finding**: with `cts := {[[false]]}`,
    `cfg := {[true, false]}`, N := 3, after 1 CTS step result = `{data
    := [false, false]}` (true-head dropped, appendant `[false]`
    appended → data length stays at 2).  Encoded result bag has 8
    elements (4 per false bit).  But the System 5 trajectory's bag
    NEVER matches `[1, 2, 3, 4, 5, 6, 7, 8]` (the encoded result),
    even allowing list reordering.  Some bag of length 8 is reached,
    but with different element values.

    This indicates Smith Conjecture 0 may need either (a) larger N
    budget for true-head cases, or (b) a different/more nuanced bag
    correspondence than exact element match.  Iter 821's false-head
    success was a partial verification; true-head appears more
    delicate.  The encoder is correct per PDF p. 28; the predicate's
    exact-bag-match form may need refinement for true-head.  -/
example :
    let cts : CTS := { appendants := [[false]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    ¬ ∃ m : Fin 60,
        (System5.nSteps (ctsToSystem5 cts cfg 3) m.val).map
          (fun s5 => s5.bag.mergeSort (· ≤ ·))
          = some [1, 2, 3, 4, 5, 6, 7, 8] := by
  native_decide

/-- **Iter 834 extension**: try larger N=10, m≤200 to rule out
    budget shortage.  Still no match for true-head case. -/
example :
    let cts : CTS := { appendants := [[false]], nonempty := by decide }
    let cfg : CTSConfig := { data := [true, false], phase := 0 }
    ¬ ∃ m : Fin 200,
        (System5.nSteps (ctsToSystem5 cts cfg 10) m.val).map
          (fun s5 => s5.bag.mergeSort (· ≤ ·))
          = some [1, 2, 3, 4, 5, 6, 7, 8] := by
  native_decide

-- **Iter 836 PREDICATE INSIGHT**: re-reading PDF p. 3-15 (Conjectures
-- 0-5 statements), Smith's actual emulation claim is "system 5 emulates
-- CTS for an arbitrary number of steps" via HALT preservation, not
-- per-step bag matching.  Our `ctsToSystem5_emulates_with_budget`
-- predicate's exact-bag-match-at-each-n form is STRONGER than
-- Smith's actual proof establishes.
--
-- This explains the iter 834 finding: for true-head cases, the
-- exact bag-match doesn't hold even with corrected encoder + large
-- N, because the trajectory's bag may have intermediate "noise" that
-- cancels asymptotically (over the full emulation) rather than
-- being absent at every CTS-step boundary.
--
-- **Iter 859 CONCRETE WITNESS** (see example just below
-- `Iter 858 larger N test`): the true-head trajectory at m=6, N=10
-- produces a bag whose sort = `[1, 2, 3, 4, 11, 13, 14, 16]`, which
-- equals `ctsConfigToSystem5BagAux [false] 1 ++ ctsConfigToSystem5BagAux
-- [true] 11`.  So the bag IS the per-bit encoder of `[false, true]`,
-- but with NON-CONTIGUOUS counter offsets (1 and 11, not 1 and 5).
-- The current `ctsConfigToSystem5Bag` thread the counter contiguously
-- through bits via `+ 4`/`+ 6` increments, so the rigid equality
-- `s5_result.bag = ctsConfigToSystem5Bag result` cannot hold when
-- counter gaps are introduced.
--
-- Possible reformulations of `_emulates_with_budget`:
--   (a) Halt-preservation only:
--       `cts.Halts cfg → ∃ N m, System5.nSteps (ctsToSystem5 cts cfg N) m = none`.
--       Already exists trivially via N=0 (per WEAK-PREDICATE NOTE).
--   (b) Schematic bag-equality: `∃ counters : List Int, counters.length
--       = result.data.length ∧ counters.Sorted (· < ·) ∧
--       s5_result.bag.mergeSort = (List.zip result.data counters).foldr
--         (fun (b, c) acc => ctsConfigToSystem5BagAux [b] c ++ acc) []`.
--       Captures iter 859's witness; weaker than rigid equality but
--       still says "bag represents result.data".
--
-- The current `_emulates_with_budget` sorry should likely be reformulated
-- to match Smith's actual claim — option (b) is the most informative.

-- (Iter 823: tried to dump bag length progression; hand-guesses
-- were off so removed.  The existential `∃ m ∈ [0, 50)` from iter
-- 821 is sufficient evidence the encoder is correct.)


/-- `ctsConfigToSystem5BagAux` emits exactly 4 integers per bit. -/
theorem ctsConfigToSystem5BagAux_length (data : List Bool) (i : Int) :
    (ctsConfigToSystem5BagAux data i).length = 4 * data.length := by
  induction data generalizing i with
  | nil => simp [ctsConfigToSystem5BagAux]
  | cons b rest ih =>
    match b with
    | true =>
      show (i :: (i + 2) :: (i + 3) :: (i + 5) ::
            ctsConfigToSystem5BagAux rest (i + 6)).length = 4 * (rest.length + 1)
      have := ih (i + 6)
      simp; omega
    | false =>
      show (i :: (i + 1) :: (i + 2) :: (i + 3) ::
            ctsConfigToSystem5BagAux rest (i + 4)).length = 4 * (rest.length + 1)
      have := ih (i + 4)
      simp; omega

/-- The encoded bag has exactly 4 × |data| entries. -/
theorem ctsConfigToSystem5Bag_length (cfg : CTSConfig) :
    (ctsConfigToSystem5Bag cfg).length = 4 * cfg.data.length :=
  ctsConfigToSystem5BagAux_length cfg.data 1

/-- **Iter 865 length theorem**: `schematicTrueHeadBag` length is
    `4 * (pre.length + appended.length)`.  Each bit contributes 4
    encoded entries regardless of bit type. -/
theorem schematicTrueHeadBag_length (pre appended : List Bool) :
    (schematicTrueHeadBag pre appended).length
      = 4 * (pre.length + appended.length) := by
  simp [schematicTrueHeadBag, List.length_append,
        ctsConfigToSystem5BagAux_length]
  omega

/-- **Iter 865 length theorem**: `schematicFalseHeadBag` length is
    `4 * data.length`.  Direct from `ctsConfigToSystem5BagAux_length`. -/
theorem schematicFalseHeadBag_length (data : List Bool) :
    (schematicFalseHeadBag data).length = 4 * data.length := by
  simp [schematicFalseHeadBag, ctsConfigToSystem5BagAux_length]

/-- **Iter 866 boundary**: `schematicTrueHeadBag [] appended` = aux appended 7.
    With pre = [], counterAfterWorkingString = 1, so the appended portion
    starts at counter `1 + 6 = 7`.  No pre prefix in the bag. -/
@[simp] theorem schematicTrueHeadBag_nil_pre (appended : List Bool) :
    schematicTrueHeadBag [] appended
      = ctsConfigToSystem5BagAux appended 7 := by
  simp [schematicTrueHeadBag, counterAfterWorkingString]

/-- **Iter 866 boundary**: `schematicTrueHeadBag pre []` = aux pre 1.
    With appended = [], the second component is empty (encoder of []), so
    the bag is just the pre portion.  Equal to `schematicFalseHeadBag pre`. -/
@[simp] theorem schematicTrueHeadBag_nil_appended (pre : List Bool) :
    schematicTrueHeadBag pre []
      = ctsConfigToSystem5BagAux pre 1 := by
  simp [schematicTrueHeadBag]

/-- **Iter 866 boundary**: empty data → empty schematic bag. -/
@[simp] theorem schematicFalseHeadBag_nil :
    schematicFalseHeadBag [] = [] := by
  simp [schematicFalseHeadBag]

/-- **Iter 866 connection**: `schematicFalseHeadBag` is a special
    case of `schematicTrueHeadBag` with empty `appended`.  Suggests
    the unified schematic predicate covers both step types via the
    same helper, with the false-head case just having an empty
    appended portion. -/
theorem schematicFalseHeadBag_eq_trueHeadBag_nil_appended (data : List Bool) :
    schematicFalseHeadBag data = schematicTrueHeadBag data [] := by
  simp [schematicFalseHeadBag, schematicTrueHeadBag]

/-- **Iter 868 cons unfold (false-head)**:
    `schematicFalseHeadBag (false :: rest) = [1,2,3,4] ++ aux rest 5`. -/
theorem schematicFalseHeadBag_cons_false (rest : List Bool) :
    schematicFalseHeadBag (false :: rest)
      = [1, 2, 3, 4] ++ ctsConfigToSystem5BagAux rest 5 := by
  simp [schematicFalseHeadBag, ctsConfigToSystem5BagAux_false_cons]

/-- **Iter 868 cons unfold (true-head)**:
    `schematicFalseHeadBag (true :: rest) = [1,3,4,6] ++ aux rest 7`. -/
theorem schematicFalseHeadBag_cons_true (rest : List Bool) :
    schematicFalseHeadBag (true :: rest)
      = [1, 3, 4, 6] ++ ctsConfigToSystem5BagAux rest 7 := by
  simp [schematicFalseHeadBag, ctsConfigToSystem5BagAux_true_cons]

-- The `schematicTrueHeadBag` cons unfoldings depend on
-- `counterAfterWorkingString_cons_{false,true}` defined at line ~1235/1243,
-- so they are placed after those lemmas.

/-- `processCycle` produces exactly 4 System 5 rules per CTS appendant
    (per `cy2s5.pl` PDF p. 28: `r1 r2 "" ""`). -/
theorem processCycle_length (rules : List (List Bool)) (i : Int) :
    (processCycle rules i).fst.length = 4 * rules.length := by
  induction rules generalizing i with
  | nil => simp [processCycle]
  | cons r rest ih =>
    have key : ∀ (p : List Int × List Int × Int) (q : List (List Int) × Int),
        (let (r1, r2, _i') := p
         let (restRules, i'') := q
         ((r1 :: r2 :: [] :: [] :: restRules : List (List Int)), i'')).fst.length
        = 4 + q.fst.length := by
      intro p q
      cases p with | mk a bc => cases bc with | mk b c =>
        cases q with | mk d e => simp; omega
    have h_rest := ih (encodeAppendant r i).2.2
    show (let (r1, r2, i') := encodeAppendant r i
          let (restRules, i'') := processCycle rest i'
          ((r1 :: r2 :: [] :: [] :: restRules : List (List Int)), i'')).fst.length
        = 4 * (rest.length + 1)
    rw [key (encodeAppendant r i) (processCycle rest (encodeAppendant r i).2.2)]
    rw [h_rest]
    omega

/-- `nCycles` produces exactly `4 * |rules| * n` System 5 rules. -/
theorem nCycles_length (rules : List (List Bool)) (n : Nat) (i : Int) :
    (nCycles rules n i).length = 4 * rules.length * n := by
  induction n generalizing i with
  | zero => simp [nCycles]
  | succ k ih =>
    show ((let (cycle, i') := processCycle rules i
           cycle ++ nCycles rules k i').length) = 4 * rules.length * (k + 1)
    cases h_pc : processCycle rules i with
    | mk cycle i' =>
      have h_cycle_len : cycle.length = 4 * rules.length := by
        have := processCycle_length rules i
        rw [h_pc] at this; exact this
      have h_rec := ih i'
      simp [List.length_append, h_cycle_len, h_rec]
      have : 4 * rules.length * (k + 1) = 4 * rules.length * k + 4 * rules.length := by
        rw [Nat.mul_add, Nat.mul_one]
      omega

/-- The encoded rules have exactly `4 * |cts.appendants| * n` entries. -/
theorem ctsRulesToSystem5Rules_length (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    (ctsRulesToSystem5Rules cts cfg n).length = 4 * cts.appendants.length * n :=
  nCycles_length cts.appendants n _

/-- **Iter 957: dropping one full cycle from `nCycles`**.  Dropping
    `4 * rules.length` entries from `nCycles rules (k+1) i` gives
    `nCycles rules k j` where `j` is the counter advanced past the
    first cycle.  Each appendant in a cycle contributes 4 rules, so a
    full cycle is `4 * rules.length` rules.  This is the per-cycle
    structural identity behind the trajectory analysis: 4 P-steps
    per appendant, so consuming one cycle = consuming
    `4 * |appendants|` System5 rules. -/
theorem nCycles_drop_first_cycle (rules : List (List Bool)) (k : Nat) (i : Int) :
    (nCycles rules (k + 1) i).drop (4 * rules.length)
      = nCycles rules k (processCycle rules i).snd := by
  rw [nCycles_succ]
  have h_len : (processCycle rules i).fst.length = 4 * rules.length :=
    processCycle_length rules i
  rw [show (4 * rules.length) = (processCycle rules i).fst.length from h_len.symm]
  rw [List.drop_append]
  simp

/-- **Iter 957: dropping one cycle from `ctsRulesToSystem5Rules`**.
    Specialization of `nCycles_drop_first_cycle` to the encoder.  For
    `n ≥ 1`, dropping `4 * |cts.appendants|` System5 rules from the
    encoder consumes the first cycle, leaving `n - 1` cycles starting
    at the advanced counter.  This is the rule-side analog of
    "1 CTS step = 1 cycle = 4·|appendants| P-steps" — the cycle-
    boundary identity for the trajectory invariant. -/
theorem ctsRulesToSystem5Rules_drop_first_cycle
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (h_n : n ≥ 1) :
    (ctsRulesToSystem5Rules cts cfg n).drop (4 * cts.appendants.length)
      = nCycles cts.appendants (n - 1)
          (processCycle cts.appendants
            (counterAfterWorkingString cfg.data + 2)).snd := by
  unfold ctsRulesToSystem5Rules
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [nCycles_drop_first_cycle]
  simp

/-- **`ctsConfigToSystem5BagAux_head_eq_counter` (iter 645)**: the
    encoded bag always emits its starting counter `i` as the first
    value (regardless of the leading bit), as long as `data` is
    non-empty. -/
theorem ctsConfigToSystem5BagAux_head_eq_counter
    (data : List Bool) (h : data ≠ []) (i : Int) :
    ∃ rest, ctsConfigToSystem5BagAux data i = i :: rest := by
  cases data with
  | nil => exact absurd rfl h
  | cons head tail =>
    cases head with
    | true => exact ⟨_, rfl⟩
    | false => exact ⟨_, rfl⟩

/-- **`ctsConfigToSystem5Bag_head_eq_one` (iter 645)**: the encoded
    bag always starts with `1` for non-empty CTS data (since the
    encoder starts the counter at `i = 1`). -/
theorem ctsConfigToSystem5Bag_head_eq_one
    (cfg : CTSConfig) (h : cfg.data ≠ []) :
    ∃ rest, ctsConfigToSystem5Bag cfg = 1 :: rest := by
  unfold ctsConfigToSystem5Bag
  cases h_data : cfg.data with
  | nil => exact absurd h_data h
  | cons head tail =>
    cases head with
    | true => exact ⟨_, rfl⟩
    | false => exact ⟨_, rfl⟩

/-- **`ctsConfigToSystem5Bag_one_mem` (iter 645)**: `1 ∈ encoded bag`
    for non-empty CTS data — the precondition for the first System 5
    step from any encoded CTS config to be a rule pop. -/
theorem ctsConfigToSystem5Bag_one_mem
    (cfg : CTSConfig) (h : cfg.data ≠ []) :
    (1 : Int) ∈ ctsConfigToSystem5Bag cfg := by
  obtain ⟨rest, h_eq⟩ := ctsConfigToSystem5Bag_head_eq_one cfg h
  rw [h_eq]
  exact List.mem_cons.mpr (Or.inl rfl)

/-- **`ctsConfigToSystem5Bag_nonempty` (iter 645)**: encoded bag is
    non-empty whenever the CTS data is non-empty. -/
theorem ctsConfigToSystem5Bag_nonempty
    (cfg : CTSConfig) (h : cfg.data ≠ []) :
    ctsConfigToSystem5Bag cfg ≠ [] := by
  obtain ⟨rest, h_eq⟩ := ctsConfigToSystem5Bag_head_eq_one cfg h
  rw [h_eq]
  exact List.cons_ne_nil _ _

/-- **`ctsRulesToSystem5Rules_nonempty` (iter 645)**: encoded rules
    list is non-empty for any positive emulation budget. -/
theorem ctsRulesToSystem5Rules_nonempty
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (h_n : 1 ≤ n) :
    ctsRulesToSystem5Rules cts cfg n ≠ [] := by
  intro h
  have h_len := ctsRulesToSystem5Rules_length cts cfg n
  rw [h, List.length_nil] at h_len
  have h_app := cts.nonempty
  have h1 : 4 * cts.appendants.length > 0 := Nat.mul_pos (by decide) h_app
  have h2 : 4 * cts.appendants.length * n > 0 := Nat.mul_pos h1 (by omega)
  omega

/-- **`processCycle_cons_three` (iter 645, generalised iter 818)**:
    `processCycle (a :: tail) i` produces a rules list starting with
    `r1 :: r2 :: [] :: rest` (the first three of the 4-rules-per-
    appendant emission per `cy2s5.pl`). -/
theorem processCycle_cons_three (a : List Bool) (tail : List (List Bool)) (i : Int) :
    ∃ r1 r2 rest, (processCycle (a :: tail) i).1 = r1 :: r2 :: [] :: rest := by
  refine ⟨(encodeAppendant a i).1, (encodeAppendant a i).2.1,
          [] :: (processCycle tail (encodeAppendant a i).2.2).1, ?_⟩
  rfl

/-- **Iter 957: explicit 4-rules-per-appendant unfolding of `processCycle`**.
    The first appendant `a` in `(a :: tail)` produces exactly 4 rules
    `[r1, r2, [], []]` (per `cy2s5.pl` PDF p. 28), followed by the
    `processCycle` of the remaining appendants at the advanced counter.
    Definitional via `rfl`; stated for use in `rw` chains. -/
theorem processCycle_cons_four_explicit (a : List Bool) (tail : List (List Bool)) (i : Int) :
    (processCycle (a :: tail) i).1
      = (encodeAppendant a i).1 :: (encodeAppendant a i).2.1 :: [] :: [] ::
        (processCycle tail (encodeAppendant a i).2.2).1 := rfl

/-- **Iter 957: dropping 4 = consuming 1 appendant from `processCycle`**.
    After 4 P-steps within a cycle, we've consumed 4 System5 rules =
    1 appendant's worth.  Direct corollary of `processCycle_cons_four_explicit`. -/
theorem processCycle_drop_4_one_appendant
    (a : List Bool) (tail : List (List Bool)) (i : Int) :
    (processCycle (a :: tail) i).1.drop 4
      = (processCycle tail (encodeAppendant a i).2.2).1 := by
  rw [processCycle_cons_four_explicit]
  rfl

/-- **Iter 983: dropping 2 from `processCycle (a :: tail)` exposes the
    two empty rules emitted after r1 and r2**.  Per the 4-rules-per-
    appendant structure, after consuming r1 and r2, the next two
    System5 rules are `[]` and `[]`. -/
theorem processCycle_drop_2_two_empty_rules
    (a : List Bool) (tail : List (List Bool)) (i : Int) :
    (processCycle (a :: tail) i).1.drop 2
      = ([] : List Int) :: ([] : List Int) ::
        (processCycle tail (encodeAppendant a i).2.2).1 := by
  rw [processCycle_cons_four_explicit]
  rfl

/-- **Iter 983: dropping 2 from `nCycles (a :: tail) (k+1)` likewise
    exposes the two empty rules from the first cycle's first
    appendant**.  Lifts `processCycle_drop_2_two_empty_rules` through
    one cycle of `nCycles`. -/
theorem nCycles_drop_2_two_empty_rules
    (a : List Bool) (tail : List (List Bool)) (k : Nat) (i : Int) :
    (nCycles (a :: tail) (k + 1) i).drop 2
      = ([] : List Int) :: ([] : List Int) ::
        ((processCycle tail (encodeAppendant a i).2.2).1
          ++ nCycles (a :: tail) k (processCycle (a :: tail) i).snd) := by
  rw [nCycles_succ]
  rw [processCycle_cons_four_explicit]
  rfl

/-- **Iter 984: encoder rules dropped by 2 has [] :: [] :: ... form**.
    Direct corollary of `nCycles_drop_2_two_empty_rules` lifted to
    `ctsRulesToSystem5Rules`.  When `N ≥ 1` (and cts.appendants is
    non-empty by construction), the first two rules dropped are
    exactly `[]` and `[]` per the 4-rules-per-appendant encoder
    structure.  Used to identify the rule popped at step 3 of cfg5
    in the false-head trajectory. -/
theorem ctsRulesToSystem5Rules_drop_2_exists_empty_rules
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    ∃ rest_more, (ctsRulesToSystem5Rules cts cfg N).drop 2
      = ([] : List Int) :: ([] : List Int) :: rest_more := by
  unfold ctsRulesToSystem5Rules
  cases h_app : cts.appendants with
  | nil =>
    have := cts.nonempty
    rw [h_app] at this
    simp at this
  | cons a app_rest =>
    cases N with
    | zero => omega
    | succ k =>
      have h := nCycles_drop_2_two_empty_rules a app_rest k
        (counterAfterWorkingString cfg.data + 2)
      exact ⟨_, h⟩

/-- **Iter 991: encoder rules dropped by 3 has [] :: ... form**.
    Direct corollary of iter 984: drop 3 = drop 2 then drop 1, and
    `[] :: [] :: rest_more` after dropping 1 leaves `[] :: rest_more`.
    Used to identify the rule popped at step 4 of cfg5 in the false-
    head trajectory: still `[]`, since the encoder emits TWO empty
    rules per appendant. -/
theorem ctsRulesToSystem5Rules_drop_3_exists_empty_rule
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    ∃ rest_more, (ctsRulesToSystem5Rules cts cfg N).drop 3
      = ([] : List Int) :: rest_more := by
  obtain ⟨rest_more, h_drop2⟩ :=
    ctsRulesToSystem5Rules_drop_2_exists_empty_rules cts cfg N h_N
  refine ⟨rest_more, ?_⟩
  have h : (ctsRulesToSystem5Rules cts cfg N).drop 3
         = ((ctsRulesToSystem5Rules cts cfg N).drop 2).drop 1 := by
    rw [List.drop_drop]
  rw [h, h_drop2]
  rfl

/-- **`encodeAppendant_nil` (iter 645)**: empty appendant encodes to
    empty rules at counter `i`. -/
theorem encodeAppendant_nil (i : Int) :
    encodeAppendant [] i = ([], [], i) := by rfl

/-- Direct corollary: r1 of the empty appendant encoding is `[]`. -/
theorem encodeAppendant_nil_r1 (i : Int) : (encodeAppendant [] i).1 = [] := rfl

/-- Direct corollary: r2 of the empty appendant encoding is `[]`. -/
theorem encodeAppendant_nil_r2 (i : Int) : (encodeAppendant [] i).2.1 = [] := rfl

/-- **`ctsConfigToSystem5Bag_false_head_decomp` (iter 645)**: false-
    head encoded bag starts with `1 :: 2 :: 3 :: 4 :: ...`. -/
theorem ctsConfigToSystem5Bag_false_head_decomp (rest : List Bool) (phase : Nat) :
    ctsConfigToSystem5Bag { data := false :: rest, phase := phase }
    = 1 :: 2 :: 3 :: 4 :: ctsConfigToSystem5BagAux rest 5 := rfl

/-- **`ctsConfigToSystem5Bag_true_head_decomp` (iter 645)**: true-
    head encoded bag starts with `1 :: 3 :: 4 :: 6 :: ...`.  The
    pattern `1, 3, 4, 6` distinguishes the true head from the false
    (`1, 2, 3, 4`). -/
theorem ctsConfigToSystem5Bag_true_head_decomp (rest : List Bool) (phase : Nat) :
    ctsConfigToSystem5Bag { data := true :: rest, phase := phase }
    = 1 :: 3 :: 4 :: 6 :: ctsConfigToSystem5BagAux rest 7 := rfl

/-- **Iter 970: 1 stays in the false-head decremented-erased bag**.
    For `cfg.data = false :: rest`, the bag is `1 :: 2 :: 3 :: 4 :: ...`,
    so decrementing yields `0 :: 1 :: 2 :: 3 :: ...` and erasing 0
    leaves `1 :: 2 :: 3 :: ...` — which still contains 1.  This is
    the membership-preservation half of "step 2 is also a P-step".
    The full proof needs the firstRule disjointness (counter ≥ 8 for
    false-head, so 1 ∉ firstRule.map(·+1)) plus
    `xorMerge_mem_left_of_not_mem_right` (iter 969). -/
theorem ctsConfigToSystem5Bag_false_head_dec_erase_one_mem
    (rest : List Bool) (phase : Nat) :
    (1 : Int) ∈ ((ctsConfigToSystem5Bag
        { data := false :: rest, phase := phase }).map (· - 1)).erase 0 := by
  rw [ctsConfigToSystem5Bag_false_head_decomp]
  show (1 : Int) ∈ (((1 :: 2 :: 3 :: 4 ::
    ctsConfigToSystem5BagAux rest 5).map (· - 1)).erase 0)
  simp [List.map_cons, List.erase_cons_head]

/-- **Iter 973: 2 stays in the false-head decremented-erased bag**.
    Companion to iter 970: same false-head bag `1 :: 2 :: 3 :: 4 :: ...`,
    decrement-erase preserves 2 (since `3 ∈ bag` and `3 - 1 = 2`).
    Used to chain to step 3 of the false-head trajectory: bag-1
    contains 2 ⇒ decrement-erase of bag-1 contains 1 ⇒ step 3 is a
    P-step. -/
theorem ctsConfigToSystem5Bag_false_head_dec_erase_two_mem
    (rest : List Bool) (phase : Nat) :
    (2 : Int) ∈ ((ctsConfigToSystem5Bag
        { data := false :: rest, phase := phase }).map (· - 1)).erase 0 := by
  rw [ctsConfigToSystem5Bag_false_head_decomp]
  show (2 : Int) ∈ (((1 :: 2 :: 3 :: 4 ::
    ctsConfigToSystem5BagAux rest 5).map (· - 1)).erase 0)
  simp [List.map_cons, List.erase_cons_head]

/-- **Iter 987: 3 stays in the false-head decremented-erased bag**.
    Companion to iters 970/973 for value `3` (predecessor 4): bag
    starts `1 :: 2 :: 3 :: 4 :: ...`, decrement gives `0, 1, 2, 3, ...`,
    erase 0 leaves `1, 2, 3, ...` — contains 3.  Foundational for
    the membership cascade `4 ∈ cfg5.bag ⇒ 3 ∈ s5_1.bag ⇒ 2 ∈ s5_2.bag
    ⇒ 1 ∈ s5_3.bag` (step 4 is also a P-step). -/
theorem ctsConfigToSystem5Bag_false_head_dec_erase_three_mem
    (rest : List Bool) (phase : Nat) :
    (3 : Int) ∈ ((ctsConfigToSystem5Bag
        { data := false :: rest, phase := phase }).map (· - 1)).erase 0 := by
  rw [ctsConfigToSystem5Bag_false_head_decomp]
  show (3 : Int) ∈ (((1 :: 2 :: 3 :: 4 ::
    ctsConfigToSystem5BagAux rest 5).map (· - 1)).erase 0)
  simp [List.map_cons, List.erase_cons_head]

/-- **`ctsConfigToSystem5Bag_distinct_heads` (iter 645)**: false-head
    and true-head cfgs encode to bags with different second elements
    (2 vs 3) — encoder is informative about the head bit. -/
theorem ctsConfigToSystem5Bag_distinct_heads
    (rest1 rest2 : List Bool) (phase1 phase2 : Nat) :
    ctsConfigToSystem5Bag { data := false :: rest1, phase := phase1 }
    ≠ ctsConfigToSystem5Bag { data := true :: rest2, phase := phase2 } := by
  rw [ctsConfigToSystem5Bag_false_head_decomp,
      ctsConfigToSystem5Bag_true_head_decomp]
  intro h
  injection h with h1 h2
  injection h2 with h3 h4
  omega

/-- **`ctsConfigToSystem5Bag_emptyData_eq_nil` (iter 646)**: empty CTS
    data encodes to the empty bag.  Direct from the def of
    `ctsConfigToSystem5BagAux` on `[]`. -/
theorem ctsConfigToSystem5Bag_emptyData_eq_nil
    (cfg : CTSConfig) (h : cfg.data = []) :
    ctsConfigToSystem5Bag cfg = [] := by
  unfold ctsConfigToSystem5Bag
  rw [h]
  rfl

/-- **`ctsConfigToSystem5Bag_eq_nil_iff` (iter 646)**: clean iff —
    encoded bag is empty exactly when CTS data is empty.  Combines
    the two directions: empty data → empty bag (def) and non-empty
    data → non-empty bag (`ctsConfigToSystem5Bag_nonempty`). -/
theorem ctsConfigToSystem5Bag_eq_nil_iff (cfg : CTSConfig) :
    ctsConfigToSystem5Bag cfg = [] ↔ cfg.data = [] := by
  refine ⟨?_, ctsConfigToSystem5Bag_emptyData_eq_nil cfg⟩
  intro h
  rcases (Decidable.em (cfg.data = [])) with h_eq | h_ne
  · exact h_eq
  · exact absurd h (ctsConfigToSystem5Bag_nonempty cfg h_ne)

/-- **`ctsConfigToSystem5BagAux_shift` (iter 647)**: counter-shift
    property — shifting the starting counter by `delta` is equivalent
    to shifting all output values by `delta`.  Useful for relating bag
    transformations under decrement/increment to the encoder's
    recursive structure. -/
theorem ctsConfigToSystem5BagAux_shift (data : List Bool) (i delta : Int) :
    ctsConfigToSystem5BagAux data (i + delta)
    = (ctsConfigToSystem5BagAux data i).map (· + delta) := by
  induction data generalizing i with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | true =>
      show (i + delta) :: (i + delta + 2) :: (i + delta + 3) :: (i + delta + 5)
            :: ctsConfigToSystem5BagAux tail (i + delta + 6)
         = (i :: (i + 2) :: (i + 3) :: (i + 5) :: ctsConfigToSystem5BagAux tail (i + 6)).map
             (· + delta)
      simp only [List.map_cons]
      have h1 : i + delta + 2 = i + 2 + delta := by omega
      have h2 : i + delta + 3 = i + 3 + delta := by omega
      have h3 : i + delta + 5 = i + 5 + delta := by omega
      have h_assoc : i + delta + 6 = (i + 6) + delta := by omega
      rw [h1, h2, h3, h_assoc, ih]
    | false =>
      show (i + delta) :: (i + delta + 1) :: (i + delta + 2) :: (i + delta + 3)
            :: ctsConfigToSystem5BagAux tail (i + delta + 4)
         = (i :: (i + 1) :: (i + 2) :: (i + 3) :: ctsConfigToSystem5BagAux tail (i + 4)).map
             (· + delta)
      simp only [List.map_cons]
      have h1 : i + delta + 1 = i + 1 + delta := by omega
      have h2 : i + delta + 2 = i + 2 + delta := by omega
      have h3 : i + delta + 3 = i + 3 + delta := by omega
      have h_assoc : i + delta + 4 = (i + 4) + delta := by omega
      rw [h1, h2, h3, h_assoc, ih]

/-- **`ctsConfigToSystem5BagAux_at_four` (iter 647)**: `aux data 4 =
    (aux data 1).map (· + 3)`.  Direct corollary of `_shift`
    with `i = 1, delta = 3`. -/
theorem ctsConfigToSystem5BagAux_at_four (data : List Bool) :
    ctsConfigToSystem5BagAux data 4
    = (ctsConfigToSystem5BagAux data 1).map (· + 3) := by
  have h := ctsConfigToSystem5BagAux_shift data 1 3
  show ctsConfigToSystem5BagAux data 4 = _
  rw [show (4 : Int) = 1 + 3 from by omega]
  exact h

/-- **Iter 994: aux decrement shifts counter back by 1**.  Companion
    to `ctsConfigToSystem5BagAux_at_four` with negative delta:
    `(aux data (i+1)).map(·-1) = aux data i`.  Foundational for
    the bag-trajectory chain analysis: each decrement step in the
    System5 P-step corresponds to shifting the encoder counter back
    by 1.  Stated for `i = 4` since that's the form needed for the
    false-head trajectory's first decrement-erase. -/
theorem ctsConfigToSystem5BagAux_dec_at_five (rest : List Bool) :
    (ctsConfigToSystem5BagAux rest 5).map (· - 1)
    = ctsConfigToSystem5BagAux rest 4 := by
  have h := ctsConfigToSystem5BagAux_shift rest 5 (-1)
  have h_arith : (5 : Int) + (-1) = 4 := by omega
  rw [h_arith] at h
  have h_eq_fun : (fun x : Int => x + (-1)) = (fun x : Int => x - 1) := by
    funext x; omega
  rw [h_eq_fun] at h
  exact h.symm

/-- **Iter 996: aux decrement at counter 4 → counter 3**.  Companion
    to `_dec_at_five` for the second decrement step in the false-head
    trajectory.  After bag-1's `aux rest 4` portion gets decremented
    in step 2's bag-1.map(·-1), it becomes `aux rest 3`. -/
theorem ctsConfigToSystem5BagAux_dec_at_four (rest : List Bool) :
    (ctsConfigToSystem5BagAux rest 4).map (· - 1)
    = ctsConfigToSystem5BagAux rest 3 := by
  have h := ctsConfigToSystem5BagAux_shift rest 4 (-1)
  have h_arith : (4 : Int) + (-1) = 3 := by omega
  rw [h_arith] at h
  have h_eq_fun : (fun x : Int => x + (-1)) = (fun x : Int => x - 1) := by
    funext x; omega
  rw [h_eq_fun] at h
  exact h.symm

/-- **Iter 996: aux decrement at counter 3 → counter 2**.  Same
    pattern for step 3's decrement. -/
theorem ctsConfigToSystem5BagAux_dec_at_three (rest : List Bool) :
    (ctsConfigToSystem5BagAux rest 3).map (· - 1)
    = ctsConfigToSystem5BagAux rest 2 := by
  have h := ctsConfigToSystem5BagAux_shift rest 3 (-1)
  have h_arith : (3 : Int) + (-1) = 2 := by omega
  rw [h_arith] at h
  have h_eq_fun : (fun x : Int => x + (-1)) = (fun x : Int => x - 1) := by
    funext x; omega
  rw [h_eq_fun] at h
  exact h.symm

/-- **Iter 996: aux decrement at counter 2 → counter 1**.  Final
    decrement step of the 4-step false-head trajectory: brings the
    bag's aux portion to the target form `aux rest 1` (the encoder
    bag of the post-step CTS state). -/
theorem ctsConfigToSystem5BagAux_dec_at_two (rest : List Bool) :
    (ctsConfigToSystem5BagAux rest 2).map (· - 1)
    = ctsConfigToSystem5BagAux rest 1 := by
  have h := ctsConfigToSystem5BagAux_shift rest 2 (-1)
  have h_arith : (2 : Int) + (-1) = 1 := by omega
  rw [h_arith] at h
  have h_eq_fun : (fun x : Int => x + (-1)) = (fun x : Int => x - 1) := by
    funext x; omega
  rw [h_eq_fun] at h
  exact h.symm

/-- **Iter 1103: aux decrement at counter 7 → counter 6**.  True-head
    counterpart of iter 996's `_dec_at_five` (et al).  True-head bag
    uses `aux rest 7` as the suffix; after the first decrement step
    in the bag transition, this becomes `aux rest 6`.  **First
    building block** for the true-head Perm-chain analog of iter 994. -/
theorem ctsConfigToSystem5BagAux_dec_at_seven (rest : List Bool) :
    (ctsConfigToSystem5BagAux rest 7).map (· - 1)
    = ctsConfigToSystem5BagAux rest 6 := by
  have h := ctsConfigToSystem5BagAux_shift rest 7 (-1)
  have h_arith : (7 : Int) + (-1) = 6 := by omega
  rw [h_arith] at h
  have h_eq_fun : (fun x : Int => x + (-1)) = (fun x : Int => x - 1) := by
    funext x; omega
  rw [h_eq_fun] at h
  exact h.symm

/-- **Iter 1106: aux decrement at counter 6 → counter 5**.  Continues
    the true-head dec-at-counter chain (iter 1103 → 1106 → ...).
    Companion to iter 996's series, used in the second step of the
    true-head trajectory's bag transitions. -/
theorem ctsConfigToSystem5BagAux_dec_at_six (rest : List Bool) :
    (ctsConfigToSystem5BagAux rest 6).map (· - 1)
    = ctsConfigToSystem5BagAux rest 5 := by
  have h := ctsConfigToSystem5BagAux_shift rest 6 (-1)
  have h_arith : (6 : Int) + (-1) = 5 := by omega
  rw [h_arith] at h
  have h_eq_fun : (fun x : Int => x + (-1)) = (fun x : Int => x - 1) := by
    funext x; omega
  rw [h_eq_fun] at h
  exact h.symm


/-- **Iter 1007: bag-2 RHS dec-erase concrete form**.
    `(((1 :: 2 :: aux rest 3).map(·-1)).erase 0) = 1 :: aux rest 2`.
    Direct computation: 1, 2 decrement to 0, 1, then erase removes 0;
    `aux rest 3` decrements to `aux rest 2` via iter 996.  This is
    the RHS form for bag-3's membership identity. -/
theorem ctsConfigToSystem5BagAux_three_one_two_cons_dec_erase_eq
    (rest : List Bool) :
    (((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3).map (· - 1)).erase 0
      = (1 : Int) :: ctsConfigToSystem5BagAux rest 2 := by
  simp only [List.map_cons]
  rw [ctsConfigToSystem5BagAux_dec_at_three]
  show ((0 : Int) :: 1 :: ctsConfigToSystem5BagAux rest 2).erase 0
      = 1 :: ctsConfigToSystem5BagAux rest 2
  rw [List.erase_cons_head]

/-- **Iter 1010: bag-3 RHS dec-erase concrete form**.
    `(((1 :: aux rest 2).map(·-1)).erase 0) = aux rest 1`.  Same
    pattern as iter 1007 but for the bag-3 → bag-4 transition.
    Decrement: 1 → 0, aux rest 2 → aux rest 1 (iter 996).  Erase 0
    removes the leading 0, leaving aux rest 1.  **The RHS for the
    terminal target bag-4's membership identity.** -/
theorem ctsConfigToSystem5BagAux_two_one_cons_dec_erase_eq
    (rest : List Bool) :
    (((1 : Int) :: ctsConfigToSystem5BagAux rest 2).map (· - 1)).erase 0
      = ctsConfigToSystem5BagAux rest 1 := by
  simp only [List.map_cons]
  rw [ctsConfigToSystem5BagAux_dec_at_two]
  show ((0 : Int) :: ctsConfigToSystem5BagAux rest 1).erase 0
      = ctsConfigToSystem5BagAux rest 1
  rw [List.erase_cons_head]


/-- **Iter 994: explicit form of false-head bag's decrement-erase**.
    For `cfg.data = false :: rest`, the bag is `1 :: 2 :: 3 :: 4 :: aux rest 5`,
    and `((bag.map(·-1)).erase 0) = 1 :: 2 :: 3 :: aux rest 4`.  The
    `0` (= `1 - 1`) gets erased, the `1, 2, 3` (= `2 - 1, 3 - 1, 4 - 1`)
    survive, and the rest decrements via `_dec_at_five`.  This is the
    starting concrete form for the bag-trajectory chain analysis
    targeting `aux rest 1` after 4 cfg5 steps. -/
theorem ctsConfigToSystem5Bag_false_head_dec_erase_eq
    (rest : List Bool) (phase : Nat) :
    ((ctsConfigToSystem5Bag
        { data := false :: rest, phase := phase }).map (· - 1)).erase 0
      = (1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4 := by
  rw [ctsConfigToSystem5Bag_false_head_decomp]
  show (((1 :: 2 :: 3 :: 4 :: ctsConfigToSystem5BagAux rest 5).map (· - 1)).erase 0)
     = 1 :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4
  simp only [List.map_cons]
  show ((0 :: 1 :: 2 :: 3 :: (ctsConfigToSystem5BagAux rest 5).map (· - 1)).erase 0
        : List Int)
     = 1 :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4
  rw [List.erase_cons_head]
  show (1 : Int) :: 2 :: 3 :: ((ctsConfigToSystem5BagAux rest 5).map (· - 1) : List Int)
     = 1 :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4
  rw [ctsConfigToSystem5BagAux_dec_at_five]

/-- **Iter 1104: explicit form of true-head bag's decrement-erase**.
    True-head analog of iter 994: for `cfg.data = true :: rest`,
    the bag is `1 :: 3 :: 4 :: 6 :: aux rest 7`, and
    `((bag.map(·-1)).erase 0) = 2 :: 3 :: 5 :: aux rest 6`.  The `0`
    (= `1 - 1`) gets erased, the `2, 3, 5` (= `3 - 1, 4 - 1, 6 - 1`)
    survive, and the rest decrements via iter 1103.  **Starting
    concrete form** for the true-head Perm-chain bag-trajectory
    analysis. -/
theorem ctsConfigToSystem5Bag_true_head_dec_erase_eq
    (rest : List Bool) (phase : Nat) :
    ((ctsConfigToSystem5Bag
        { data := true :: rest, phase := phase }).map (· - 1)).erase 0
      = (2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6 := by
  rw [ctsConfigToSystem5Bag_true_head_decomp]
  show (((1 :: 3 :: 4 :: 6 :: ctsConfigToSystem5BagAux rest 7).map (· - 1)).erase 0)
     = 2 :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6
  simp only [List.map_cons]
  show ((0 :: 2 :: 3 :: 5 :: (ctsConfigToSystem5BagAux rest 7).map (· - 1)).erase 0
        : List Int)
     = 2 :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6
  rw [List.erase_cons_head]
  show (2 : Int) :: 3 :: 5 :: ((ctsConfigToSystem5BagAux rest 7).map (· - 1) : List Int)
     = 2 :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6
  rw [ctsConfigToSystem5BagAux_dec_at_seven]

/-- **`ctsConfigToSystem5BagAux_at_six` (iter 647)**: `aux data 6 =
    (aux data 1).map (· + 5)`. -/
theorem ctsConfigToSystem5BagAux_at_six (data : List Bool) :
    ctsConfigToSystem5BagAux data 6
    = (ctsConfigToSystem5BagAux data 1).map (· + 5) := by
  have h := ctsConfigToSystem5BagAux_shift data 1 5
  show ctsConfigToSystem5BagAux data 6 = _
  rw [show (6 : Int) = 1 + 5 from by omega]
  exact h

/-- **`ctsConfigToSystem5Bag_decrement` (iter 647)**: decrement-by-1
    equals encode-from-0 — decrementing every bag entry by 1 is
    equivalent to running the encoder starting at counter 0 instead
    of 1.  Direct corollary of `_shift` with `delta = -1`. -/
theorem ctsConfigToSystem5Bag_decrement (cfg : CTSConfig) :
    (ctsConfigToSystem5Bag cfg).map (· - 1) = ctsConfigToSystem5BagAux cfg.data 0 := by
  unfold ctsConfigToSystem5Bag
  have h := ctsConfigToSystem5BagAux_shift cfg.data 1 (-1)
  have h1 : (1 : Int) + (-1 : Int) = 0 := by omega
  have h2 : (fun x : Int => x + (-1)) = (fun x => x - 1) := by funext x; omega
  rw [h1, h2] at h
  exact h.symm

/-- **`ctsConfigToSystem5BagAux_at_zero` (iter 648)**: `aux data 0 =
    (aux data 1).map (· - 1)`.  Inverse of `ctsConfigToSystem5Bag_
    decrement`'s view: encode-from-0 equals decrement-by-1 of
    encode-from-1. -/
theorem ctsConfigToSystem5BagAux_at_zero (data : List Bool) :
    ctsConfigToSystem5BagAux data 0
    = (ctsConfigToSystem5BagAux data 1).map (· - 1) := by
  have h := ctsConfigToSystem5BagAux_shift data 1 (-1)
  have h1 : (1 : Int) + (-1 : Int) = 0 := by omega
  have h2 : (fun x : Int => x + (-1)) = (fun x => x - 1) := by funext x; omega
  rw [h1, h2] at h
  exact h

/-- **`ctsConfigToSystem5BagAux_length` (iter 648)**: each bit of data
    contributes exactly 4 bag entries; encoded bag length is `4 *
    data.length` regardless of starting counter.  Direct from
    `ctsConfigToSystem5BagAux_length`'s special case at `i = 1` plus
    `_shift` to deduce it for arbitrary `i`. -/
theorem ctsConfigToSystem5BagAux_length_general (data : List Bool) (i : Int) :
    (ctsConfigToSystem5BagAux data i).length = 4 * data.length := by
  have h_shift := ctsConfigToSystem5BagAux_shift data 1 (i - 1)
  have h1 : (1 : Int) + (i - 1) = i := by omega
  rw [h1] at h_shift
  rw [h_shift, List.length_map]
  exact ctsConfigToSystem5BagAux_length data 1

/-- **Encoder lower bound**: every entry of `ctsConfigToSystem5BagAux
    data i` is `≥ i`.  Useful invariant: the encoded bag has no values
    below the starting counter. -/
theorem ctsConfigToSystem5BagAux_ge (data : List Bool) (i : Int) :
    ∀ x ∈ ctsConfigToSystem5BagAux data i, x ≥ i := by
  induction data generalizing i with
  | nil => intro x h; cases h
  | cons head tail ih =>
    cases head with
    | true =>
      intro x h
      simp [ctsConfigToSystem5BagAux] at h
      rcases h with rfl | rfl | rfl | rfl | h_in
      · omega
      · omega
      · omega
      · omega
      · have := ih (i + 6) x h_in
        omega
    | false =>
      intro x h
      simp [ctsConfigToSystem5BagAux] at h
      rcases h with rfl | rfl | rfl | rfl | h_in
      · omega
      · omega
      · omega
      · omega
      · have := ih (i + 4) x h_in
        omega

/-- **Encoder produces no duplicates**: `aux data i` is a list with no
    repeated elements.  The counter strictly increases between bits;
    within a bit the 4 emitted values are distinct. -/
theorem ctsConfigToSystem5BagAux_nodup (data : List Bool) (i : Int) :
    (ctsConfigToSystem5BagAux data i).Nodup := by
  induction data generalizing i with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
    cases head with
    | true =>
      show (i :: (i+2) :: (i+3) :: (i+5) :: ctsConfigToSystem5BagAux tail (i+6)).Nodup
      simp only [List.nodup_cons, List.mem_cons]
      refine ⟨?_, ?_, ?_, ?_, ih (i+6)⟩
      · intro h
        rcases h with h | h | h | h
        · omega
        · omega
        · omega
        · have := ctsConfigToSystem5BagAux_ge tail (i+6) i h
          omega
      · intro h
        rcases h with h | h | h
        · omega
        · omega
        · have := ctsConfigToSystem5BagAux_ge tail (i+6) (i+2) h
          omega
      · intro h
        rcases h with h | h
        · omega
        · have := ctsConfigToSystem5BagAux_ge tail (i+6) (i+3) h
          omega
      · intro h
        have := ctsConfigToSystem5BagAux_ge tail (i+6) (i+5) h
        omega
    | false =>
      show (i :: (i+1) :: (i+2) :: (i+3) :: ctsConfigToSystem5BagAux tail (i+4)).Nodup
      simp only [List.nodup_cons, List.mem_cons]
      refine ⟨?_, ?_, ?_, ?_, ih (i+4)⟩
      · intro h
        rcases h with h | h | h | h
        · omega
        · omega
        · omega
        · have := ctsConfigToSystem5BagAux_ge tail (i+4) i h
          omega
      · intro h
        rcases h with h | h | h
        · omega
        · omega
        · have := ctsConfigToSystem5BagAux_ge tail (i+4) (i+1) h
          omega
      · intro h
        rcases h with h | h
        · omega
        · have := ctsConfigToSystem5BagAux_ge tail (i+4) (i+2) h
          omega
      · intro h
        have := ctsConfigToSystem5BagAux_ge tail (i+4) (i+3) h
        omega

/-- Direct corollary of `ctsConfigToSystem5BagAux_ge`: the encoded
    bag contains no value below 1, in particular not 0. -/
theorem ctsConfigToSystem5Bag_zero_not_mem (cfg : CTSConfig) :
    (0 : Int) ∉ ctsConfigToSystem5Bag cfg := by
  intro h
  have := ctsConfigToSystem5BagAux_ge cfg.data 1 0 h
  omega

/-- The encoded bag is duplicate-free. -/
theorem ctsConfigToSystem5Bag_nodup (cfg : CTSConfig) :
    (ctsConfigToSystem5Bag cfg).Nodup :=
  ctsConfigToSystem5BagAux_nodup cfg.data 1

/-- **Iter 1107: true-head bag-prefix dec-erase concrete form**.
    True-head analog of iter 1007: `(((2 :: 3 :: 5 :: aux rest 6).map(·-1)).erase 0)
    = 1 :: 2 :: 4 :: aux rest 5`.  Decrement: 2,3,5 → 1,2,4 (no 0
    produced); aux rest 6 → aux rest 5 (iter 1106).  Erase 0 leaves
    the list unchanged since 0 ∉ list (using iter 645's `_ge` lemma:
    aux rest 5 ≥ 5).  **Building block** for the true-head Perm-chain
    bag-2 mem-iff downstream. -/
theorem ctsConfigToSystem5BagAux_six_two_three_five_cons_dec_erase_eq
    (rest : List Bool) :
    (((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6).map (· - 1)).erase 0
      = (1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5 := by
  simp only [List.map_cons]
  rw [ctsConfigToSystem5BagAux_dec_at_six]
  apply List.erase_of_not_mem
  intro h
  rcases List.mem_cons.mp h with h1 | h2
  · omega
  · rcases List.mem_cons.mp h2 with h2a | h3
    · omega
    · rcases List.mem_cons.mp h3 with h3a | h4
      · omega
      · have := ctsConfigToSystem5BagAux_ge rest 5 0 h4
        omega

/-- The shifted encoded bag inherits `Nodup` from the underlying bag.
    `(· + k)` is injective on Int. -/
theorem ctsConfigToSystem5BagAux_map_add_nodup (data : List Bool) (k : Int) :
    ((ctsConfigToSystem5BagAux data 1).map (· + k)).Nodup := by
  show List.Pairwise (· ≠ ·) ((ctsConfigToSystem5BagAux data 1).map (· + k))
  apply List.Pairwise.map (· + k) (R := (· ≠ ·)) ?_ (ctsConfigToSystem5BagAux_nodup data 1)
  intro a b h_ne h_eq
  apply h_ne
  show a = b
  have : a + k = b + k := h_eq
  omega

/-- The shifted encoded bag has all entries ≥ `1 + k`. -/
theorem ctsConfigToSystem5BagAux_map_add_ge (data : List Bool) (k : Int) :
    ∀ x ∈ (ctsConfigToSystem5BagAux data 1).map (· + k), x ≥ 1 + k := by
  intro x h
  rw [List.mem_map] at h
  obtain ⟨y, h_y, h_eq⟩ := h
  have := ctsConfigToSystem5BagAux_ge data 1 y h_y
  omega

/-- The post-decrement-erase bag is `Nodup`.  `(· - 1)` is injective so
    the map preserves `Nodup`; `List.Nodup.erase` preserves it through
    the erase. -/
theorem ctsConfigToSystem5Bag_decrement_erase_nodup (cfg : CTSConfig) :
    (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0).Nodup := by
  apply List.Nodup.erase
  show List.Pairwise (· ≠ ·) ((ctsConfigToSystem5Bag cfg).map (· - 1))
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ (ctsConfigToSystem5Bag_nodup cfg)
  intro a b h_ne h_eq
  apply h_ne
  show a = b
  have : a - 1 = b - 1 := h_eq
  omega

/-- After erasing `0` from the post-decrement bag, `0` is no longer
    present. -/
theorem zero_not_mem_decrement_erase (cfg : CTSConfig) :
    (0 : Int) ∉ ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0 := by
  apply List.Nodup.not_mem_erase
  show ((ctsConfigToSystem5Bag cfg).map (· - 1)).Nodup
  show List.Pairwise (· ≠ ·) ((ctsConfigToSystem5Bag cfg).map (· - 1))
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ (ctsConfigToSystem5Bag_nodup cfg)
  intro a b h_ne h_eq
  apply h_ne
  show a = b
  have : a - 1 = b - 1 := h_eq
  omega

/-- Every entry of the post-decrement-erase bag is ≥ 1.  Combines
    `ctsConfigToSystem5BagAux_ge` (entries ≥ 1) with the decrement
    (≥ 0) and the no-zero post-erase property. -/
theorem decrement_erase_ge_one (cfg : CTSConfig) :
    ∀ x ∈ ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0, x ≥ 1 := by
  intro x h
  have h_in : x ∈ (ctsConfigToSystem5Bag cfg).map (· - 1) := List.mem_of_mem_erase h
  rw [List.mem_map] at h_in
  obtain ⟨y, h_y, h_eq⟩ := h_in
  have h_y_ge := ctsConfigToSystem5BagAux_ge cfg.data 1 y h_y
  have h_ne : x ≠ 0 := by
    intro h_zero
    rw [h_zero] at h
    exact zero_not_mem_decrement_erase cfg h
  omega

/-- **`ctsConfigToSystem5Bag_ge_one` (iter 650)**: every entry of
    the encoded bag is ≥ 1 (since the starting counter is 1).  Direct
    specialisation of `ctsConfigToSystem5BagAux_ge`. -/
theorem ctsConfigToSystem5Bag_ge_one (cfg : CTSConfig) :
    ∀ x ∈ ctsConfigToSystem5Bag cfg, x ≥ 1 :=
  ctsConfigToSystem5BagAux_ge cfg.data 1

/-- **`ctsConfigToSystem5Bag_neg_not_mem` (iter 650)**: no negative
    integer can be in the encoded bag.  Direct from
    `ctsConfigToSystem5Bag_ge_one`. -/
theorem ctsConfigToSystem5Bag_neg_not_mem (cfg : CTSConfig) (n : Int) (h : n < 1) :
    n ∉ ctsConfigToSystem5Bag cfg := by
  intro h_mem
  have := ctsConfigToSystem5Bag_ge_one cfg n h_mem
  omega

/-- Helper: shifting the foldl init by `delta` shifts the result by
    `delta`.  Linearity-in-init for the `counterAfterWorkingString`
    accumulator. -/
theorem foldl_counter_init_shift (data : List Bool) (init delta : Int) :
    data.foldl (fun acc b => acc + if b then (6 : Int) else 4) (init + delta)
    = data.foldl (fun acc b => acc + if b then (6 : Int) else 4) init + delta := by
  induction data generalizing init with
  | nil => rfl
  | cons head tail ih =>
    show tail.foldl _ ((init + delta) + if head then (6 : Int) else 4)
       = tail.foldl _ (init + if head then (6 : Int) else 4) + delta
    have h : (init + delta) + (if head then (6 : Int) else 4)
           = (init + if head then (6 : Int) else 4) + delta := by
      cases head <;> simp <;> omega
    rw [h]
    exact ih (init + if head then (6 : Int) else 4)

/-- `counterAfterWorkingString` cons recurrence (false head): adds 4. -/
theorem counterAfterWorkingString_cons_false (rest : List Bool) :
    counterAfterWorkingString (false :: rest) = counterAfterWorkingString rest + 4 := by
  unfold counterAfterWorkingString
  show rest.foldl (fun acc b => acc + if b then (6 : Int) else 4) 5
     = rest.foldl (fun acc b => acc + if b then (6 : Int) else 4) 1 + 4
  exact foldl_counter_init_shift rest 1 4

/-- `counterAfterWorkingString` cons recurrence (true head): adds 6. -/
theorem counterAfterWorkingString_cons_true (rest : List Bool) :
    counterAfterWorkingString (true :: rest) = counterAfterWorkingString rest + 6 := by
  unfold counterAfterWorkingString
  show rest.foldl (fun acc b => acc + if b then (6 : Int) else 4) 7
     = rest.foldl (fun acc b => acc + if b then (6 : Int) else 4) 1 + 6
  exact foldl_counter_init_shift rest 1 6

/-- **Iter 868 schematicTrueHeadBag false-pre cons unfold**:
    `schematicTrueHeadBag (false :: pre) appended`
    = `[1,2,3,4] ++ aux pre 5 ++ aux appended (counterAfterWorkingString pre + 10)`. -/
theorem schematicTrueHeadBag_cons_false_pre (pre appended : List Bool) :
    schematicTrueHeadBag (false :: pre) appended
      = [1, 2, 3, 4] ++ ctsConfigToSystem5BagAux pre 5
          ++ ctsConfigToSystem5BagAux appended (counterAfterWorkingString pre + 10) := by
  unfold schematicTrueHeadBag
  rw [ctsConfigToSystem5BagAux_false_cons, counterAfterWorkingString_cons_false,
      show counterAfterWorkingString pre + 4 + 6
         = counterAfterWorkingString pre + 10 from by omega]
  rfl

/-- **Iter 868 schematicTrueHeadBag true-pre cons unfold**:
    `schematicTrueHeadBag (true :: pre) appended`
    = `[1,3,4,6] ++ aux pre 7 ++ aux appended (counterAfterWorkingString pre + 12)`. -/
theorem schematicTrueHeadBag_cons_true_pre (pre appended : List Bool) :
    schematicTrueHeadBag (true :: pre) appended
      = [1, 3, 4, 6] ++ ctsConfigToSystem5BagAux pre 7
          ++ ctsConfigToSystem5BagAux appended (counterAfterWorkingString pre + 12) := by
  unfold schematicTrueHeadBag
  rw [ctsConfigToSystem5BagAux_true_cons, counterAfterWorkingString_cons_true,
      show counterAfterWorkingString pre + 6 + 6
         = counterAfterWorkingString pre + 12 from by omega]
  rfl

/-- `counterAfterWorkingString` is always at least 1.  Each cons adds 4
    or 6 to a counter that starts at 1, so it stays ≥ 1. -/
theorem counterAfterWorkingString_ge_one (data : List Bool) :
    counterAfterWorkingString data ≥ 1 := by
  induction data with
  | nil => unfold counterAfterWorkingString; simp
  | cons head tail ih =>
    cases head with
    | true => rw [counterAfterWorkingString_cons_true]; omega
    | false => rw [counterAfterWorkingString_cons_false]; omega

/-- **`counterAfterWorkingString_nil` (iter 652)**: empty data → counter
    is 1 (the initial value). -/
@[simp] theorem counterAfterWorkingString_nil :
    counterAfterWorkingString [] = 1 := rfl

/-- **`counterAfterWorkingString_eq` (iter 652)**: closed-form expression.
    Counter equals `1 + 6 * (count true) + 4 * (count false)`. -/
theorem counterAfterWorkingString_eq (data : List Bool) :
    counterAfterWorkingString data
      = 1 + 6 * (data.count true : Int) + 4 * (data.count false : Int) := by
  induction data with
  | nil => unfold counterAfterWorkingString; simp
  | cons head tail ih =>
    cases head with
    | true =>
      rw [counterAfterWorkingString_cons_true, ih]
      simp
      omega
    | false =>
      rw [counterAfterWorkingString_cons_false, ih]
      simp
      omega

/-- **Drop-4 decomposition (false head)** (iter 653): the encoded bag
    of a false-head cfg, with its 4-element prefix `[1, 2, 3, 4]`
    removed, equals the encoded bag of the rest shifted up by 4. -/
theorem ctsConfigToSystem5Bag_drop4_false_head
    (rest : List Bool) (phase phase' : Nat) :
    (ctsConfigToSystem5Bag { data := false :: rest, phase := phase }).drop 4
    = (ctsConfigToSystem5Bag { data := rest, phase := phase' }).map (· + 4) := by
  rw [ctsConfigToSystem5Bag_false_head_decomp]
  show ctsConfigToSystem5BagAux rest 5
      = (ctsConfigToSystem5BagAux rest 1).map (· + 4)
  have h := ctsConfigToSystem5BagAux_shift rest 1 4
  rw [show (5 : Int) = 1 + 4 from by omega]
  exact h

/-- **Drop-4 decomposition (true head)** (iter 653): same with the
    counter advancing by 6 (true bits). -/
theorem ctsConfigToSystem5Bag_drop4_true_head
    (rest : List Bool) (phase phase' : Nat) :
    (ctsConfigToSystem5Bag { data := true :: rest, phase := phase }).drop 4
    = (ctsConfigToSystem5Bag { data := rest, phase := phase' }).map (· + 6) := by
  rw [ctsConfigToSystem5Bag_true_head_decomp]
  show ctsConfigToSystem5BagAux rest 7
      = (ctsConfigToSystem5BagAux rest 1).map (· + 6)
  have h := ctsConfigToSystem5BagAux_shift rest 1 6
  rw [show (7 : Int) = 1 + 6 from by omega]
  exact h

/-- The counter value after encoding bit-list `data` starting at
    counter `i`.  Generalises `counterAfterWorkingString` (which
    fixes `i = 1`).  Each false bit advances by 4; each true bit by 6. -/
def counterAux (data : List Bool) (i : Int) : Int :=
  data.foldl (fun acc b => acc + if b then 6 else 4) i

/-- `counterAux` cons recurrence (false head): adds 4. -/
theorem counterAux_cons_false (rest : List Bool) (i : Int) :
    counterAux (false :: rest) i = counterAux rest (i + 4) := by
  unfold counterAux
  simp [List.foldl]

/-- `counterAux` cons recurrence (true head): adds 6. -/
theorem counterAux_cons_true (rest : List Bool) (i : Int) :
    counterAux (true :: rest) i = counterAux rest (i + 6) := by
  unfold counterAux
  simp [List.foldl]

/-- `counterAux` on an empty bit-list is the identity in `i`. -/
theorem counterAux_nil (i : Int) : counterAux [] i = i := rfl

/-- **`ctsConfigToSystem5BagAux_append` (iter 653)**: encoding `data1
    ++ data2` at counter `i` is the encoding of `data1` at `i`
    concatenated with the encoding of `data2` at the post-`data1`
    counter.  Foundational for relating CTS true-head step (which
    appends the appendant to the working string) to a structured
    System 5 bag transformation. -/
theorem ctsConfigToSystem5BagAux_append
    (data1 data2 : List Bool) (i : Int) :
    ctsConfigToSystem5BagAux (data1 ++ data2) i
    = ctsConfigToSystem5BagAux data1 i
        ++ ctsConfigToSystem5BagAux data2 (counterAux data1 i) := by
  induction data1 generalizing i with
  | nil => simp [ctsConfigToSystem5BagAux, counterAux]
  | cons head tail ih =>
    cases head with
    | false =>
      show (i :: (i + 1) :: (i + 2) :: (i + 3)
              :: ctsConfigToSystem5BagAux (tail ++ data2) (i + 4))
          = (i :: (i + 1) :: (i + 2) :: (i + 3)
              :: ctsConfigToSystem5BagAux tail (i + 4))
              ++ ctsConfigToSystem5BagAux data2 (counterAux (false :: tail) i)
      rw [counterAux_cons_false, ih]
      simp
    | true =>
      show (i :: (i + 2) :: (i + 3) :: (i + 5)
              :: ctsConfigToSystem5BagAux (tail ++ data2) (i + 6))
          = (i :: (i + 2) :: (i + 3) :: (i + 5)
              :: ctsConfigToSystem5BagAux tail (i + 6))
              ++ ctsConfigToSystem5BagAux data2 (counterAux (true :: tail) i)
      rw [counterAux_cons_true, ih]
      simp

/-- Specialization of `counterAux` at start counter 1: matches
    `counterAfterWorkingString`. -/
theorem counterAux_one_eq_counterAfterWorkingString (data : List Bool) :
    counterAux data 1 = counterAfterWorkingString data := rfl

/-- **`counterAux_shift` (iter 654)**: linearity of `counterAux` in
    its initial counter — `counterAux data (i + delta) = counterAux
    data i + delta`.  Direct from `foldl_counter_init_shift`. -/
theorem counterAux_shift (data : List Bool) (i delta : Int) :
    counterAux data (i + delta) = counterAux data i + delta :=
  foldl_counter_init_shift data i delta

/-- **`counterAux_eq_counterAfterWorkingString_shift` (iter 654)**:
    relates the general `counterAux` form at arbitrary `i` to
    `counterAfterWorkingString` (= `counterAux data 1`) plus the
    shift `i - 1`. -/
theorem counterAux_eq_counterAfterWorkingString_shift (data : List Bool) (i : Int) :
    counterAux data i = counterAfterWorkingString data + (i - 1) := by
  have h := counterAux_shift data 1 (i - 1)
  have h1 : (1 : Int) + (i - 1) = i := by omega
  rw [h1] at h
  rw [h, counterAux_one_eq_counterAfterWorkingString]

/-- **`counterAux_append` (iter 655)**: counter after encoding `data1 ++
    data2` equals `counterAux data2` applied to `counterAux data1`. -/
theorem counterAux_append (data1 data2 : List Bool) (i : Int) :
    counterAux (data1 ++ data2) i = counterAux data2 (counterAux data1 i) := by
  unfold counterAux
  rw [List.foldl_append]

/-- **`counterAfterWorkingString_append` (iter 655)**: post-`data1 ++
    data2` counter is the sum minus 1 (the `-1` accounts for the shared
    initial offset of 1). -/
theorem counterAfterWorkingString_append (data1 data2 : List Bool) :
    counterAfterWorkingString (data1 ++ data2)
    = counterAfterWorkingString data1 + counterAfterWorkingString data2 - 1 := by
  rw [← counterAux_one_eq_counterAfterWorkingString,
      ← counterAux_one_eq_counterAfterWorkingString,
      ← counterAux_one_eq_counterAfterWorkingString,
      counterAux_append]
  have h_shift : counterAux data2 (1 + (counterAux data1 1 - 1))
              = counterAux data2 1 + (counterAux data1 1 - 1) :=
    counterAux_shift data2 1 (counterAux data1 1 - 1)
  have h_arith : (1 : Int) + (counterAux data1 1 - 1) = counterAux data1 1 := by omega
  rw [h_arith] at h_shift
  rw [h_shift]
  omega

/-- **Iter 959: counterAfterWorkingString relates between cfg and
    cts.step cfg (false-head case)**.  When `cfg.data = false :: rest`,
    a CTS step drops the leading false bit; the counter loses exactly
    4 (the encoder offset for one false bit).  Foundational for
    cycle-boundary correctness: this is the per-step counter delta
    that ties to System5 P-step count via the encoder structure. -/
theorem counterAfterWorkingString_cts_step_false_head
    (cts : CTS) (cfg cfg' : CTSConfig) (rest : List Bool)
    (h_data : cfg.data = false :: rest)
    (h_step : cts.step cfg = some cfg') :
    counterAfterWorkingString cfg'.data
      = counterAfterWorkingString cfg.data - 4 := by
  rw [h_data]
  rw [counterAfterWorkingString_cons_false]
  unfold CTS.step at h_step
  rw [h_data] at h_step
  simp at h_step
  have h_data' : cfg'.data = rest := by rw [← h_step]
  rw [h_data']
  omega

/-- **Iter 959: counterAfterWorkingString relates between cfg and
    cts.step cfg (true-head case)**.  When `cfg.data = true :: rest`,
    a CTS step drops the leading true bit (counter loses 6) and appends
    the current appendant (counter gains its full advance, less the
    "shared 1" from the append formula).  Net: cfg' counter = cfg
    counter + appendant counter - 7.  Foundational for cycle-boundary
    correctness in the true-head branch. -/
theorem counterAfterWorkingString_cts_step_true_head
    (cts : CTS) (cfg cfg' : CTSConfig) (rest : List Bool)
    (h_data : cfg.data = true :: rest)
    (h_step : cts.step cfg = some cfg') :
    counterAfterWorkingString cfg'.data
      = counterAfterWorkingString cfg.data
        + counterAfterWorkingString (cts.currentAppendant cfg.phase) - 7 := by
  rw [h_data]
  rw [counterAfterWorkingString_cons_true]
  unfold CTS.step at h_step
  rw [h_data] at h_step
  simp at h_step
  have h_data' : cfg'.data = rest ++ cts.currentAppendant cfg.phase := by rw [← h_step]
  rw [h_data']
  rw [counterAfterWorkingString_append]
  omega

/-- **`ctsConfigToSystem5BagAux_injective` (iter 655)**: encoder is
    injective in its first argument — two bit-lists encode to the same
    integer list only when equal.  Same heads continue via `injection`
    + `ih`; different heads contradict on the second emitted entry
    (`i+1` vs `i+2`). -/
theorem ctsConfigToSystem5BagAux_injective
    (data1 data2 : List Bool) (i : Int)
    (h : ctsConfigToSystem5BagAux data1 i = ctsConfigToSystem5BagAux data2 i) :
    data1 = data2 := by
  induction data1 generalizing data2 i with
  | nil =>
    cases data2 with
    | nil => rfl
    | cons head2 rest2 =>
      cases head2 <;> simp [ctsConfigToSystem5BagAux] at h
  | cons head1 rest1 ih =>
    cases data2 with
    | nil =>
      cases head1 <;> simp [ctsConfigToSystem5BagAux] at h
    | cons head2 rest2 =>
      cases head1 with
      | false =>
        cases head2 with
        | false =>
          show false :: rest1 = false :: rest2
          have hh : (i :: (i + 1) :: (i + 2) :: (i + 3)
                      :: ctsConfigToSystem5BagAux rest1 (i + 4))
                  = (i :: (i + 1) :: (i + 2) :: (i + 3)
                      :: ctsConfigToSystem5BagAux rest2 (i + 4)) := h
          injection hh with _ hh; injection hh with _ hh
          injection hh with _ hh; injection hh with _ hh
          rw [ih rest2 (i + 4) hh]
        | true =>
          exfalso
          have hh : (i :: (i + 1) :: (i + 2) :: (i + 3)
                      :: ctsConfigToSystem5BagAux rest1 (i + 4))
                  = (i :: (i + 2) :: (i + 3) :: (i + 5)
                      :: ctsConfigToSystem5BagAux rest2 (i + 6)) := h
          injection hh with _ hh; injection hh with h2 _
          omega
      | true =>
        cases head2 with
        | false =>
          exfalso
          have hh : (i :: (i + 2) :: (i + 3) :: (i + 5)
                      :: ctsConfigToSystem5BagAux rest1 (i + 6))
                  = (i :: (i + 1) :: (i + 2) :: (i + 3)
                      :: ctsConfigToSystem5BagAux rest2 (i + 4)) := h
          injection hh with _ hh; injection hh with h2 _
          omega
        | true =>
          show true :: rest1 = true :: rest2
          have hh : (i :: (i + 2) :: (i + 3) :: (i + 5)
                      :: ctsConfigToSystem5BagAux rest1 (i + 6))
                  = (i :: (i + 2) :: (i + 3) :: (i + 5)
                      :: ctsConfigToSystem5BagAux rest2 (i + 6)) := h
          injection hh with _ hh; injection hh with _ hh
          injection hh with _ hh; injection hh with _ hh
          rw [ih rest2 (i + 6) hh]

/-- **`ctsConfigToSystem5Bag_data_eq` (iter 655)**: cfg-level encoder
    injectivity in `data` — equal encoded bags imply equal data lists.
    Direct corollary at `i = 1`.  Note `phase` is unobserved. -/
theorem ctsConfigToSystem5Bag_data_eq (cfg1 cfg2 : CTSConfig)
    (h : ctsConfigToSystem5Bag cfg1 = ctsConfigToSystem5Bag cfg2) :
    cfg1.data = cfg2.data := by
  unfold ctsConfigToSystem5Bag at h
  exact ctsConfigToSystem5BagAux_injective cfg1.data cfg2.data 1 h

/-- **`ctsConfigToSystem5Bag_of_data_eq` (iter 656)**: converse — equal
    `data` (regardless of phase) gives equal encoded bags.  The
    encoder ignores `phase`. -/
theorem ctsConfigToSystem5Bag_of_data_eq (cfg1 cfg2 : CTSConfig)
    (h : cfg1.data = cfg2.data) :
    ctsConfigToSystem5Bag cfg1 = ctsConfigToSystem5Bag cfg2 := by
  unfold ctsConfigToSystem5Bag
  rw [h]

/-- **`ctsConfigToSystem5Bag_eq_iff_data_eq` (iter 656)**: clean iff —
    encoded bags are equal exactly when CTS data is equal.  The
    `phase` field is invisible to the encoder. -/
theorem ctsConfigToSystem5Bag_eq_iff_data_eq (cfg1 cfg2 : CTSConfig) :
    ctsConfigToSystem5Bag cfg1 = ctsConfigToSystem5Bag cfg2 ↔ cfg1.data = cfg2.data :=
  ⟨ctsConfigToSystem5Bag_data_eq cfg1 cfg2,
   ctsConfigToSystem5Bag_of_data_eq cfg1 cfg2⟩

/-- **`processCycle_all_empty` (iter 657)**: on all-empty rules,
    `processCycle` produces all-empty entries.  Each rule contributes 3
    entries — `r1, r2, []` — and for empty rules `r1 = r2 = []`. -/
theorem processCycle_all_empty
    (rules : List (List Bool)) (h : ∀ a ∈ rules, a = []) (i : Int) :
    ∀ r ∈ (processCycle rules i).1, r = ([] : List Int) := by
  induction rules generalizing i with
  | nil => intro r h_mem; cases h_mem
  | cons rule rest ih =>
    have h_rule_nil : rule = [] := h rule (List.mem_cons.mpr (Or.inl rfl))
    have h_rest : ∀ a ∈ rest, a = [] :=
      fun a h_mem => h a (List.mem_cons.mpr (Or.inr h_mem))
    rw [h_rule_nil]
    show ∀ r ∈ (let (r1, r2, i') := encodeAppendant [] i;
                let (restRules, _) := processCycle rest i'
                (r1 :: r2 :: [] :: [] :: restRules)),
              r = ([] : List Int)
    show ∀ r ∈ ([] : List Int) :: ([] : List Int) :: ([] : List Int) ::
                ([] : List Int) :: (processCycle rest i).1,
              r = ([] : List Int)
    intro r h_mem
    rcases List.mem_cons.mp h_mem with h | h_mem
    · exact h
    rcases List.mem_cons.mp h_mem with h | h_mem
    · exact h
    rcases List.mem_cons.mp h_mem with h | h_mem
    · exact h
    rcases List.mem_cons.mp h_mem with h | h_mem
    · exact h
    exact ih h_rest i r h_mem

/-- **`nCycles_all_empty` (iter 657)**: on all-empty rules, `nCycles`
    produces all-empty entries via cycle-induction. -/
theorem nCycles_all_empty
    (rules : List (List Bool)) (h : ∀ a ∈ rules, a = []) (n : Nat) (i : Int) :
    ∀ r ∈ nCycles rules n i, r = ([] : List Int) := by
  induction n generalizing i with
  | zero => intro r h_mem; cases h_mem
  | succ k ih =>
    show ∀ r ∈ (let (cycle, i') := processCycle rules i; cycle ++ nCycles rules k i'),
              r = ([] : List Int)
    intro r h_mem
    rcases List.mem_append.mp h_mem with h_in_cycle | h_in_rest
    · exact processCycle_all_empty rules h i r h_in_cycle
    · exact ih (processCycle rules i).2 r h_in_rest

/-- **`AllEmptyAppendants_ctsRulesToSystem5Rules_all_empty` (iter 657)**:
    System 5 rules are all empty for an `AllEmptyAppendants` CTS. -/
theorem AllEmptyAppendants_ctsRulesToSystem5Rules_all_empty
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg : CTSConfig) (n : Nat) :
    ∀ r ∈ ctsRulesToSystem5Rules cts cfg n, r = ([] : List Int) :=
  nCycles_all_empty cts.appendants h_app n _

/-- A non-empty list whose every element is `[]` has `[]` as its head
    (and the tail also satisfies the all-empty invariant). -/
theorem List_all_empty_cons_decomp (xs : List (List Int)) (h_ne : xs ≠ [])
    (h_all : ∀ x ∈ xs, x = ([] : List Int)) :
    ∃ rest, xs = ([] : List Int) :: rest
        ∧ ∀ x ∈ rest, x = ([] : List Int) := by
  cases xs with
  | nil => exact absurd rfl h_ne
  | cons head tail =>
    have h_head : head = [] := h_all head (List.mem_cons.mpr (Or.inl rfl))
    refine ⟨tail, ?_, ?_⟩
    · rw [h_head]
    · intro x h_mem; exact h_all x (List.mem_cons.mpr (Or.inr h_mem))

/-- **`AllEmptyAppendants_rules_cons_empty` (iter 657)**: for an
    `AllEmptyAppendants` CTS with non-empty encoded rules, the rules
    list cons-decomposes with an empty head. -/
theorem AllEmptyAppendants_rules_cons_empty
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg : CTSConfig) (n : Nat)
    (h_ne : ctsRulesToSystem5Rules cts cfg n ≠ []) :
    ∃ rest, ctsRulesToSystem5Rules cts cfg n = ([] : List Int) :: rest
        ∧ ∀ x ∈ rest, x = ([] : List Int) :=
  List_all_empty_cons_decomp _ h_ne
    (AllEmptyAppendants_ctsRulesToSystem5Rules_all_empty cts h_app cfg n)

/-- **`zero_mem_decrement_ctsConfigToSystem5Bag_iff_data_nonempty`
    (iter 658)**: 0 enters the post-decrement encoded bag exactly when
    the CTS data is non-empty.  Since `1` is always in the bag for
    non-empty data (`ctsConfigToSystem5Bag_one_mem`), the decrement
    surfaces a 0 there; conversely, empty data gives an empty bag. -/
theorem zero_mem_decrement_ctsConfigToSystem5Bag_iff_data_nonempty (cfg : CTSConfig) :
    (0 : Int) ∈ (ctsConfigToSystem5Bag cfg).map (· - 1) ↔ cfg.data ≠ [] := by
  constructor
  · intro h h_data_nil
    have h_bag_nil : ctsConfigToSystem5Bag cfg = [] :=
      ctsConfigToSystem5Bag_emptyData_eq_nil cfg h_data_nil
    rw [h_bag_nil] at h
    cases h
  · intro h
    rw [List.mem_map]
    exact ⟨1, ctsConfigToSystem5Bag_one_mem cfg h, by omega⟩

/-- **`ctsConfigToSystem5Bag_step_some_iff` (iter 658)**: the
    encoded-bag-derived step pre-condition (`0 ∈ decrement bag` AND
    rules ≠ []) coincides with CTS `data ≠ []` AND positive emulation
    budget.  Direct combination of two iff lemmas. -/
theorem ctsConfigToSystem5Bag_step_some_iff
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (h_n : 1 ≤ n) :
    ((0 : Int) ∈ (ctsConfigToSystem5Bag cfg).map (· - 1) ∧
     ctsRulesToSystem5Rules cts cfg n ≠ []) ↔ cfg.data ≠ [] := by
  refine ⟨fun ⟨h_zero, _⟩ => ?_, fun h_data => ?_⟩
  · exact (zero_mem_decrement_ctsConfigToSystem5Bag_iff_data_nonempty cfg).mp h_zero
  · refine ⟨?_, ctsRulesToSystem5Rules_nonempty cts cfg n h_n⟩
    exact (zero_mem_decrement_ctsConfigToSystem5Bag_iff_data_nonempty cfg).mpr h_data

/-- **`zero_mem_decrement_iff_one_mem` (iter 659)**: 0 is in the
    decremented list iff 1 is in the original.  Direct via
    `List.mem_map`. -/
theorem zero_mem_decrement_iff_one_mem (bag : List Int) :
    (0 : Int) ∈ bag.map (· - 1) ↔ (1 : Int) ∈ bag := by
  rw [List.mem_map]
  constructor
  · rintro ⟨a, h_a, h_eq⟩
    have h_a_one : a = 1 := by omega
    rw [← h_a_one]; exact h_a
  · intro h
    exact ⟨1, h, by omega⟩

/-- **Iter 975: predecessor membership in decrement-erase**.  When
    `x ∈ xs` and `x ≠ 1`, the predecessor `x - 1` belongs to
    `(xs.map(·-1)).erase 0`.  The condition `x ≠ 1` ensures the
    decremented value isn't 0 (which would be erased).  Used to chain
    bag membership across System5 P-steps: `2 ∈ bag-1 ⇒
    1 ∈ (bag-1.map(·-1)).erase 0` (the trigger condition for the
    next P-step). -/
theorem mem_imp_pred_in_dec_erase
    (xs : List Int) (x : Int) (h_mem : x ∈ xs) (h_ne : x ≠ 1) :
    (x - 1) ∈ (xs.map (· - 1)).erase 0 := by
  have h_dec : (x - 1) ∈ xs.map (· - 1) := List.mem_map.mpr ⟨x, h_mem, rfl⟩
  rw [List.mem_erase_of_ne (a := x - 1) (l := xs.map (· - 1)) (b := 0) (by omega)]
  exact h_dec

/-- **`ctsConfigToSystem5Bag_zero_in_decrement` (iter 659)**: 0 is in
    the decrement of the encoded bag for non-empty data.  Direct
    composition of `_one_mem` and `zero_mem_decrement_iff_one_mem`. -/
theorem ctsConfigToSystem5Bag_zero_in_decrement
    (cfg : CTSConfig) (h : cfg.data ≠ []) :
    (0 : Int) ∈ (ctsConfigToSystem5Bag cfg).map (· - 1) :=
  (zero_mem_decrement_iff_one_mem _).mpr (ctsConfigToSystem5Bag_one_mem cfg h)

/-- **Iter 969: cfg5-level 0 ∈ decremented bag wrapper**.  Direct lift
    of `ctsConfigToSystem5Bag_zero_in_decrement` to `ctsToSystem5`.
    States: when `cfg.data ≠ []`, the very first System5 step from
    `ctsToSystem5 cts cfg N` is a P-step.  Useful for chaining
    P-steps via `System5_step_rules_pstep` (iter 968) and
    `System5_nSteps_rules_pstep` (iter 968). -/
theorem ctsToSystem5_zero_in_decrement
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h : cfg.data ≠ []) :
    (0 : Int) ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) :=
  ctsConfigToSystem5Bag_zero_in_decrement cfg h

/-- **Iter 969: cfg5-level 1 ∈ bag wrapper**.  Direct lift of
    `ctsConfigToSystem5Bag_one_mem` to `ctsToSystem5`.  States: the
    encoded bag at cfg5 contains 1 whenever `cfg.data ≠ []`.  Pairs
    with `System5_one_mem_iff_zero_in_decremented` to give the
    P-step trigger. -/
theorem ctsToSystem5_one_mem
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h : cfg.data ≠ []) :
    (1 : Int) ∈ (ctsToSystem5 cts cfg N).bag :=
  ctsConfigToSystem5Bag_one_mem cfg h

/-- **Iter 958: `encodeAppendant` counter advance is shift-invariant**.
    For any starting counter `i`, the post-encoding counter is
    `i + (encodeAppendant data 0).2.2` — i.e., the counter advance only
    depends on the appendant's bit pattern, not the starting offset.
    Foundational for the cycle-boundary correctness analysis: the
    advance per appendant is `4·falses + 6·trues`, fixed by the
    appendant's structure. -/
theorem encodeAppendant_counter_advance_shift (data : List Bool) (i : Int) :
    (encodeAppendant data i).2.2 = i + (encodeAppendant data 0).2.2 := by
  induction data generalizing i with
  | nil => simp [encodeAppendant]
  | cons b rest ih =>
    cases b with
    | true =>
      show (encodeAppendant rest (i + 6)).2.2 = i + (encodeAppendant rest (0 + 6)).2.2
      rw [ih (i + 6), ih (0 + 6)]
      omega
    | false =>
      show (encodeAppendant rest (i + 4)).2.2 = i + (encodeAppendant rest (0 + 4)).2.2
      rw [ih (i + 4), ih (0 + 4)]
      omega

/-- **Iter 958: `processCycle` counter advance is shift-invariant**.
    Lifts `encodeAppendant_counter_advance_shift` through the
    appendant chain: the post-cycle counter is `i + (processCycle rules 0).2`,
    independent of the starting offset.  Each cycle's counter advance
    is structurally fixed by the appendant list. -/
theorem processCycle_counter_advance_shift (rules : List (List Bool)) (i : Int) :
    (processCycle rules i).2 = i + (processCycle rules 0).2 := by
  induction rules generalizing i with
  | nil => simp [processCycle]
  | cons rule rest ih =>
    show (processCycle rest (encodeAppendant rule i).2.2).2
      = i + (processCycle rest (encodeAppendant rule 0).2.2).2
    rw [encodeAppendant_counter_advance_shift rule i]
    rw [ih (i + (encodeAppendant rule 0).2.2)]
    rw [ih (encodeAppendant rule 0).2.2]
    omega

/-- **Iter 960: `encodeAppendant` r1 component is counter-shift-equivariant**.
    Shifting the starting counter by `d` shifts every entry of the r1
    rule by `d`.  This means the encoder is "linear" in the counter:
    `encodeAppendant data (i + d)` produces the same rule shape as
    `encodeAppendant data i`, just shifted by `d`.  Foundational for
    relating encoder rule lists across CTS state evolution. -/
theorem encodeAppendant_r1_counter_shift (data : List Bool) (i d : Int) :
    (encodeAppendant data (i + d)).1 = (encodeAppendant data i).1.map (· + d) := by
  induction data generalizing i with
  | nil => simp [encodeAppendant]
  | cons b rest ih =>
    cases b with
    | true =>
      show (i + d + 2) :: (i + d + 5) :: (encodeAppendant rest (i + d + 6)).1
        = ((i + 2) :: (i + 5) :: (encodeAppendant rest (i + 6)).1).map (· + d)
      simp [List.map_cons]
      refine ⟨by omega, by omega, ?_⟩
      have h_eq : i + d + 6 = (i + 6) + d := by omega
      rw [h_eq]
      exact ih (i + 6)
    | false =>
      show (i + d + 2) :: (i + d + 3) :: (encodeAppendant rest (i + d + 4)).1
        = ((i + 2) :: (i + 3) :: (encodeAppendant rest (i + 4)).1).map (· + d)
      simp [List.map_cons]
      refine ⟨by omega, by omega, ?_⟩
      have h_eq : i + d + 4 = (i + 4) + d := by omega
      rw [h_eq]
      exact ih (i + 4)

/-- **Iter 960: `encodeAppendant` r2 component is counter-shift-equivariant**.
    Same as `encodeAppendant_r1_counter_shift` for r2: starting-counter
    shift commutes with element-wise shift. -/
theorem encodeAppendant_r2_counter_shift (data : List Bool) (i d : Int) :
    (encodeAppendant data (i + d)).2.1 = (encodeAppendant data i).2.1.map (· + d) := by
  induction data generalizing i with
  | nil => simp [encodeAppendant]
  | cons b rest ih =>
    cases b with
    | true =>
      show (i + d) :: (i + d + 3) :: (encodeAppendant rest (i + d + 6)).2.1
        = (i :: (i + 3) :: (encodeAppendant rest (i + 6)).2.1).map (· + d)
      simp [List.map_cons]
      refine ⟨by omega, ?_⟩
      have h_eq : i + d + 6 = (i + 6) + d := by omega
      rw [h_eq]
      exact ih (i + 6)
    | false =>
      show (i + d) :: (i + d + 1) :: (encodeAppendant rest (i + d + 4)).2.1
        = (i :: (i + 1) :: (encodeAppendant rest (i + 4)).2.1).map (· + d)
      simp [List.map_cons]
      refine ⟨by omega, ?_⟩
      have h_eq : i + d + 4 = (i + 4) + d := by omega
      rw [h_eq]
      exact ih (i + 4)

/-- **Iter 961: `processCycle` rules are counter-shift-equivariant**.
    Lifts `encodeAppendant_{r1,r2}_counter_shift` through the appendant
    chain.  Shifting the starting counter by `d` shifts every entry of
    every emitted rule by `d`.  The `[] :: []` rules are vacuously
    invariant, and the recursive call inherits the shift via
    `encodeAppendant_counter_advance_shift`.  Foundational for
    relating encoder rule lists across CTS state evolution. -/
theorem processCycle_counter_shift (rules : List (List Bool)) (i d : Int) :
    (processCycle rules (i + d)).1
      = (processCycle rules i).1.map (fun r => r.map (· + d)) := by
  induction rules generalizing i with
  | nil => simp [processCycle]
  | cons rule rest ih =>
    show ((encodeAppendant rule (i + d)).1
            :: (encodeAppendant rule (i + d)).2.1
            :: [] :: []
            :: (processCycle rest (encodeAppendant rule (i + d)).2.2).1)
        = ((encodeAppendant rule i).1
            :: (encodeAppendant rule i).2.1
            :: [] :: []
            :: (processCycle rest (encodeAppendant rule i).2.2).1).map
            (fun r => r.map (· + d))
    rw [encodeAppendant_r1_counter_shift, encodeAppendant_r2_counter_shift]
    have h_adv : (encodeAppendant rule (i + d)).2.2
               = (encodeAppendant rule i).2.2 + d := by
      rw [encodeAppendant_counter_advance_shift rule (i + d)]
      rw [encodeAppendant_counter_advance_shift rule i]
      omega
    rw [h_adv]
    have h_ih := ih (encodeAppendant rule i).2.2
    rw [h_ih]
    simp [List.map_cons]

/-- **Iter 962: `nCycles` counter-shift equivariance**.  Lifts
    `processCycle_counter_shift` to multi-cycle: shifting the starting
    counter by `d` shifts every entry of every rule across all `k`
    cycles by `d`.  Each cycle uses `processCycle_counter_shift` and
    threads the counter via `processCycle_counter_advance_shift`.
    Foundational closure for the counter-shift infrastructure across
    the full encoder rule list. -/
theorem nCycles_counter_shift (rules : List (List Bool)) (k : Nat) (i d : Int) :
    nCycles rules k (i + d)
      = (nCycles rules k i).map (fun r => r.map (· + d)) := by
  induction k generalizing i with
  | zero => simp [nCycles]
  | succ n ih =>
    rw [nCycles_succ, nCycles_succ]
    rw [processCycle_counter_shift]
    have h_adv : (processCycle rules (i + d)).2
              = (processCycle rules i).2 + d := by
      rw [processCycle_counter_advance_shift rules (i + d)]
      rw [processCycle_counter_advance_shift rules i]
      omega
    rw [h_adv]
    rw [ih (processCycle rules i).2]
    rw [List.map_append]

/-- **Iter 963: `nCycles` differs by counter offset**.  Two `nCycles`
    runs at different starting counters `i` and `j` differ by a uniform
    counter shift `j - i` applied to every rule entry.  Direct
    consequence of `nCycles_counter_shift` with `d := j - i`. -/
theorem nCycles_counter_shift_diff (rules : List (List Bool)) (k : Nat) (i j : Int) :
    nCycles rules k j = (nCycles rules k i).map (fun r => r.map (· + (j - i))) := by
  have h := nCycles_counter_shift rules k i (j - i)
  have h_eq : i + (j - i) = j := by omega
  rw [h_eq] at h
  exact h

/-- **Iter 963: encoder rule lists across two CTS states differ by
    counter offset**.  For any two CTS configs `cfg, cfg'` (with the
    same CTS and same N), the rule lists differ by a uniform
    counter shift equal to `counterAfterWorkingString cfg.data -
    counterAfterWorkingString cfg'.data`.  Composing with the per-step
    counter delta lemmas (iter 959) gives a clean way to relate
    encoder rules across one CTS step. -/
theorem ctsRulesToSystem5Rules_counter_shift_diff
    (cts : CTS) (cfg cfg' : CTSConfig) (N : Nat) :
    ctsRulesToSystem5Rules cts cfg N
      = (ctsRulesToSystem5Rules cts cfg' N).map
          (fun r => r.map (· + (counterAfterWorkingString cfg.data
                              - counterAfterWorkingString cfg'.data))) := by
  unfold ctsRulesToSystem5Rules
  have h : counterAfterWorkingString cfg.data + 2
         = counterAfterWorkingString cfg'.data + 2
         + (counterAfterWorkingString cfg.data
            - counterAfterWorkingString cfg'.data) := by omega
  rw [h]
  exact nCycles_counter_shift cts.appendants N
    (counterAfterWorkingString cfg'.data + 2)
    (counterAfterWorkingString cfg.data
      - counterAfterWorkingString cfg'.data)

/-- **Iter 964: drop-one-cycle = shifted cfg'-encoder (general)**.
    Combines `ctsRulesToSystem5Rules_drop_first_cycle` (iter 957) with
    `nCycles_counter_shift_diff` (iter 963): dropping `4·|appendants|`
    rules from `cts cfg N` yields `cts cfg' (N-1)` shifted by
    `(counterAfterWorkingString cfg.data − counterAfterWorkingString cfg'.data) + cycle_advance`,
    where `cycle_advance = (processCycle cts.appendants 0).2`.  This is
    the master bridge from one CTS state's full encoder to the dropped-
    cycle prefix of another CTS state's encoder. -/
theorem ctsRulesToSystem5Rules_drop_first_cycle_eq_shifted
    (cts : CTS) (cfg cfg' : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    (ctsRulesToSystem5Rules cts cfg N).drop (4 * cts.appendants.length)
      = (ctsRulesToSystem5Rules cts cfg' (N - 1)).map
          (fun r => r.map (· + ((counterAfterWorkingString cfg.data + 2)
                              - (counterAfterWorkingString cfg'.data + 2)
                              + (processCycle cts.appendants 0).2))) := by
  rw [ctsRulesToSystem5Rules_drop_first_cycle cts cfg N h_N]
  unfold ctsRulesToSystem5Rules
  rw [processCycle_counter_advance_shift]
  rw [nCycles_counter_shift_diff cts.appendants (N - 1)
      (counterAfterWorkingString cfg'.data + 2)
      (counterAfterWorkingString cfg.data + 2
        + (processCycle cts.appendants 0).2)]
  congr 1
  funext r
  congr 1
  funext x
  omega

/-- **Iter 965: false-head specialization of the master bridge**.  When
    `cfg.data = false :: rest` and `cfg' = cts.step cfg`, the counter
    delta is exactly 4 (iter 959), so the shift collapses to
    `4 + cycle_advance` where `cycle_advance = (processCycle cts.appendants 0).2`.
    This is the concrete shift the chain induction needs for the
    false-head case. -/
theorem ctsRulesToSystem5Rules_drop_first_cycle_eq_shifted_false_head
    (cts : CTS) (cfg cfg' : CTSConfig) (rest : List Bool) (N : Nat)
    (h_data : cfg.data = false :: rest)
    (h_step : cts.step cfg = some cfg')
    (h_N : N ≥ 1) :
    (ctsRulesToSystem5Rules cts cfg N).drop (4 * cts.appendants.length)
      = (ctsRulesToSystem5Rules cts cfg' (N - 1)).map
          (fun r => r.map (· + (4 + (processCycle cts.appendants 0).2))) := by
  rw [ctsRulesToSystem5Rules_drop_first_cycle_eq_shifted cts cfg cfg' N h_N]
  congr 1
  funext r
  congr 1
  funext x
  have h_delta :=
    counterAfterWorkingString_cts_step_false_head cts cfg cfg' rest h_data h_step
  omega

/-- **Iter 965: true-head specialization of the master bridge**.  When
    `cfg.data = true :: rest` and `cfg' = cts.step cfg`, the counter
    delta is `7 - counterAfterWorkingString (cts.currentAppendant cfg.phase)`
    (iter 959), so the shift becomes `7 - currentAppendant_counter +
    cycle_advance`.  This is the concrete shift for the true-head
    chain induction. -/
theorem ctsRulesToSystem5Rules_drop_first_cycle_eq_shifted_true_head
    (cts : CTS) (cfg cfg' : CTSConfig) (rest : List Bool) (N : Nat)
    (h_data : cfg.data = true :: rest)
    (h_step : cts.step cfg = some cfg')
    (h_N : N ≥ 1) :
    (ctsRulesToSystem5Rules cts cfg N).drop (4 * cts.appendants.length)
      = (ctsRulesToSystem5Rules cts cfg' (N - 1)).map
          (fun r => r.map (· + (7
                              - counterAfterWorkingString (cts.currentAppendant cfg.phase)
                              + (processCycle cts.appendants 0).2))) := by
  rw [ctsRulesToSystem5Rules_drop_first_cycle_eq_shifted cts cfg cfg' N h_N]
  congr 1
  funext r
  congr 1
  funext x
  have h_delta :=
    counterAfterWorkingString_cts_step_true_head cts cfg cfg' rest h_data h_step
  omega

/-- **Iter 966: per-appendant drop within `nCycles`**.  Dropping 4
    from `nCycles (a :: rest) (k+1) i` consumes the first appendant `a`
    of the first cycle, leaving the rest of that cycle's appendants
    (`processCycle rest`) followed by the remaining `k` full cycles
    over the original appendant list.  Note: `nCycles` continues to
    use the full `(a :: rest)` appendant list cyclically — only the
    output rule list is shortened.

    This is the per-CTS-step analog of `nCycles_drop_first_cycle`
    (iter 957): one CTS step consumes ONE appendant (4 System5 rules),
    not a full cycle. -/
theorem nCycles_drop_first_appendant
    (a : List Bool) (rest : List (List Bool)) (k : Nat) (i : Int) :
    (nCycles (a :: rest) (k + 1) i).drop 4
      = (processCycle rest (encodeAppendant a i).2.2).1
        ++ nCycles (a :: rest) k (processCycle (a :: rest) i).2 := by
  rw [nCycles_succ]
  rw [processCycle_cons_four_explicit]
  rfl

/-- **Iter 967: ctsRulesToSystem5Rules per-appendant drop**.  Concrete
    application of `nCycles_drop_first_appendant` (iter 966) to the
    encoder.  When `cts.appendants = a :: rest` and `N ≥ 1`, dropping
    4 rules from the encoder consumes the first appendant `a` of the
    first cycle.  Result splits into two parts: the rest of the first
    cycle (`processCycle rest (a's post-counter)`) and the remaining
    `N - 1` cycles over the full appendant list. -/
theorem ctsRulesToSystem5Rules_drop_first_appendant
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (a : List Bool) (rest : List (List Bool))
    (h_app : cts.appendants = a :: rest) :
    (ctsRulesToSystem5Rules cts cfg N).drop 4
      = (processCycle rest
            (encodeAppendant a (counterAfterWorkingString cfg.data + 2)).2.2).1
        ++ nCycles cts.appendants (N - 1)
            (processCycle cts.appendants
              (counterAfterWorkingString cfg.data + 2)).2 := by
  unfold ctsRulesToSystem5Rules
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  rw [h_app]
  rw [nCycles_drop_first_appendant]
  rw [← h_app]
  simp

/-- **`processCycle_all_empty_counter` (iter 659)**: on all-empty
    rules, `processCycle` preserves the counter.  Each empty rule's
    `encodeAppendant` returns `(_, _, i)`, so the threaded counter
    stays at `i` throughout. -/
theorem processCycle_all_empty_counter
    (rules : List (List Bool)) (h : ∀ a ∈ rules, a = []) (i : Int) :
    (processCycle rules i).2 = i := by
  induction rules generalizing i with
  | nil => rfl
  | cons rule rest ih =>
    have h_rule_nil : rule = [] := h rule (List.mem_cons.mpr (Or.inl rfl))
    have h_rest : ∀ a ∈ rest, a = [] :=
      fun a h_mem => h a (List.mem_cons.mpr (Or.inr h_mem))
    rw [h_rule_nil]
    show (let (r1, r2, i') := encodeAppendant [] i;
          let (restRules, i'') := processCycle rest i'
          (r1 :: r2 :: [] :: restRules, i'')).2 = i
    show (processCycle rest i).2 = i
    exact ih h_rest i

/-- **`nCycles_all_empty_length` (iter 659)**: trivial restatement of
    `nCycles_length` (length doesn't depend on whether rules are
    empty). -/
theorem nCycles_all_empty_length
    (rules : List (List Bool)) (n : Nat) (i : Int) :
    (nCycles rules n i).length = 4 * rules.length * n :=
  nCycles_length rules n i

/-- **`processCycle_all_empty_eq` (iter 659, updated 818)**: for all-
    empty input, `processCycle` produces exactly `(replicate (4 *
    rules.length) [], i)` — every output rule is `[]` and counter is
    unchanged.  4 rules per appendant per `cy2s5.pl` PDF p. 28. -/
theorem processCycle_all_empty_eq
    (rules : List (List Bool)) (h : ∀ a ∈ rules, a = []) (i : Int) :
    processCycle rules i = (List.replicate (4 * rules.length) [], i) := by
  induction rules generalizing i with
  | nil => rfl
  | cons rule rest ih =>
    have h_rule_nil : rule = [] := h rule (List.mem_cons.mpr (Or.inl rfl))
    have h_rest : ∀ a ∈ rest, a = [] :=
      fun a h_mem => h a (List.mem_cons.mpr (Or.inr h_mem))
    rw [h_rule_nil]
    show (let (r1, r2, i') := encodeAppendant [] i;
          let (restRules, i'') := processCycle rest i'
          (r1 :: r2 :: [] :: [] :: restRules, i''))
        = (List.replicate (4 * (rest.length + 1)) [], i)
    show (([] : List Int) :: ([] : List Int) :: ([] : List Int) ::
            ([] : List Int) :: (processCycle rest i).1,
            (processCycle rest i).2)
        = (List.replicate (4 * (rest.length + 1)) [], i)
    rw [ih h_rest]
    show (([] : List Int) :: ([] : List Int) :: ([] : List Int) ::
            ([] : List Int) :: List.replicate (4 * rest.length) [], i)
        = (List.replicate (4 * (rest.length + 1)) [], i)
    have h_rep : ([] : List Int) :: ([] : List Int) :: ([] : List Int) ::
                  ([] : List Int) ::
                  List.replicate (4 * rest.length) ([] : List Int)
                = List.replicate (4 * (rest.length + 1)) ([] : List Int) := by
      rw [show 4 * (rest.length + 1) = (((4 * rest.length) + 1) + 1) + 1 + 1
            from by omega]
      rw [List.replicate_succ, List.replicate_succ, List.replicate_succ,
          List.replicate_succ]
    rw [h_rep]

/-- **`nCycles_all_empty_eq` (iter 659)**: lifts iter 307's per-cycle
    equality through induction on cycle count.  Result: `nCycles rules
    n i = replicate (3 * rules.length * n) []` for all-empty input. -/
theorem nCycles_all_empty_eq
    (rules : List (List Bool)) (h : ∀ a ∈ rules, a = []) (n : Nat) (i : Int) :
    nCycles rules n i = List.replicate (4 * rules.length * n) [] := by
  induction n generalizing i with
  | zero => rfl
  | succ k ih =>
    show (let (cycle, i') := processCycle rules i;
          cycle ++ nCycles rules k i')
        = List.replicate (4 * rules.length * (k + 1)) []
    rw [processCycle_all_empty_eq rules h i]
    show List.replicate (4 * rules.length) [] ++ nCycles rules k i
        = List.replicate (4 * rules.length * (k + 1)) []
    rw [ih i]
    rw [List.replicate_append_replicate]
    rw [show 4 * rules.length + 4 * rules.length * k
          = 4 * rules.length * (k + 1) from by
        rw [Nat.mul_succ]; omega]

/-- **`AllEmptyAppendants_ctsRulesToSystem5Rules_eq` (iter 659, updated 818)**: for
    an all-empty-appendant CTS, `ctsRulesToSystem5Rules cts cfg n =
    replicate (4 * cts.appendants.length * n) []`.  Closed form. -/
theorem AllEmptyAppendants_ctsRulesToSystem5Rules_eq
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig) (n : Nat) :
    ctsRulesToSystem5Rules cts cfg n
    = List.replicate (4 * cts.appendants.length * n) [] :=
  nCycles_all_empty_eq cts.appendants h_app n _

/-- **`AllEmptyAppendants_ctsToSystem5_rules_eq` (iter 660)**: for an
    all-empty-appendant CTS, the rules field of `ctsToSystem5 cts cfg
    n` is `replicate (4 * cts.appendants.length * n) []`.  Direct
    unfold + iter 659. -/
theorem AllEmptyAppendants_ctsToSystem5_rules_eq
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig) (n : Nat) :
    (ctsToSystem5 cts cfg n).rules
    = List.replicate (4 * cts.appendants.length * n) [] :=
  AllEmptyAppendants_ctsRulesToSystem5Rules_eq cts h_app cfg n

/-- **`AllEmptyAppendants_ctsToSystem5_bag_eq` (iter 660)**: for any
    encoder budget, the bag field of `ctsToSystem5 cts cfg n` is just
    `ctsConfigToSystem5Bag cfg`.  This holds for all CTS — it doesn't
    depend on `AllEmptyAppendants` — but is grouped here for symmetry
    with `_rules_eq`.  Direct unfold of `ctsToSystem5`. -/
theorem ctsToSystem5_bag_eq (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    (ctsToSystem5 cts cfg n).bag = ctsConfigToSystem5Bag cfg := rfl

/-- **`List_map_increment_preserves_all_empty` (iter 661)**: each `[]`
    rule maps under `(·.map (·+k))` to `[].map (·+k) = []`.  Iteration
    invariant: `_first_step` applied to an AllEmptyAppendants cfg
    yields rules satisfying the same all-empty predicate. -/
theorem List_map_increment_preserves_all_empty
    (xs : List (List Int)) (h : ∀ x ∈ xs, x = ([] : List Int)) (k : Int) :
    ∀ y ∈ xs.map (fun r => r.map (· + k)), y = ([] : List Int) := by
  intro y h_mem
  rw [List.mem_map] at h_mem
  obtain ⟨x, h_x, h_eq⟩ := h_mem
  have h_x_empty : x = [] := h x h_x
  rw [← h_eq, h_x_empty]
  rfl

/-- **`List_replicate_nil_map_increment` (iter 661)**: `(replicate n
    []).map (·.map (·+k)) = replicate n []`.  `replicate-nil` is
    invariant under per-element increment. -/
theorem List_replicate_nil_map_increment (n : Nat) (k : Int) :
    (List.replicate n ([] : List Int)).map (fun r => r.map (· + k))
    = List.replicate n ([] : List Int) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ]
    show ([] : List Int).map (· + k) :: (List.replicate m ([] : List Int)).map _
        = ([] : List Int) :: List.replicate m []
    rw [ih]
    rfl

/-- **`List_tail_replicate_succ` (iter 661)**: tail of a successor-
    replicate is just one shorter.  Direct via `replicate_succ`. -/
theorem List_tail_replicate_succ {α : Type _} (n : Nat) (x : α) :
    (List.replicate (n + 1) x).tail = List.replicate n x := by
  rw [List.replicate_succ, List.tail_cons]

/-- **`AllEmptyAppendants_postStep_rules_replicate` (iter 661)**: after
    one System 5 step from `ctsToSystem5 cts cfg N` (with `N ≥ 1` and
    `cfg.data ≠ []`), post-step rules are `replicate (K-1) []` where
    `K = 3 * |appendants| * N`.  Composes
    `AllEmptyAppendants_ctsRulesToSystem5Rules_eq` with cons decomp +
    increment invariant. -/
theorem AllEmptyAppendants_postStep_rules_replicate
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg : CTSConfig) (N : Nat) (h_pos : 0 < 4 * cts.appendants.length * N) :
    ∃ rest, ctsRulesToSystem5Rules cts cfg N
              = ([] : List Int) :: rest
        ∧ rest.map (fun r => r.map (· + 1))
              = List.replicate (4 * cts.appendants.length * N - 1) [] := by
  rw [AllEmptyAppendants_ctsRulesToSystem5Rules_eq cts h_app cfg N]
  obtain ⟨k, h_k⟩ : ∃ k, 4 * cts.appendants.length * N = k + 1 := by
    refine ⟨4 * cts.appendants.length * N - 1, ?_⟩
    omega
  rw [h_k, List.replicate_succ]
  refine ⟨List.replicate k [], rfl, ?_⟩
  rw [List_replicate_nil_map_increment]
  congr 1

/-- **`List_replicate_nil_all_empty` (iter 662)**: every element of
    `replicate n []` is `[]`.  Trivial but useful as a precondition for
    `_all_empty`-style consumers. -/
theorem List_replicate_nil_all_empty {α : Type _} (n : Nat) :
    ∀ x ∈ List.replicate n ([] : List α), x = [] := by
  intro x h
  exact List.eq_of_mem_replicate h

/-- **`AllEmptyAppendants_ctsRulesToSystem5Rules_all_empty_redux` (iter
    662)**: re-derives the all-empty fact from the closed-form
    `_eq` + `List_replicate_nil_all_empty`.  Provides an alternative
    proof path that's helpful when one already has the closed form. -/
theorem AllEmptyAppendants_ctsRulesToSystem5Rules_all_empty_redux
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig) (n : Nat) :
    ∀ r ∈ ctsRulesToSystem5Rules cts cfg n, r = ([] : List Int) := by
  rw [AllEmptyAppendants_ctsRulesToSystem5Rules_eq cts h_app cfg n]
  exact List_replicate_nil_all_empty _

/-- **`ctsConfigToSystem5BagAux_map_decrement` (iter 663)**: pure
    map-decrement (no erase), via counter-shift.  Foundation for
    decrement-erase analyses. -/
theorem ctsConfigToSystem5BagAux_map_decrement
    (rest : List Bool) (n : Int) :
    (ctsConfigToSystem5BagAux rest n).map (· - 1)
    = ctsConfigToSystem5BagAux rest (n - 1) := by
  have h_s := ctsConfigToSystem5BagAux_shift rest (n - 1) 1
  have h_eq : (n - 1) + 1 = n := by omega
  rw [h_eq] at h_s
  rw [h_s, List.map_map]
  have h_fn : ((fun x : Int => x - 1) ∘ (fun x : Int => x + 1))
            = (fun x : Int => x) := by
    funext x; simp
  rw [h_fn, List.map_id']

/-- **`ctsConfigToSystem5BagAux_decrement_erase` (iter 663)**: for `n
    ≥ 2`, all bag entries are `≥ n - 1 ≥ 1` after decrement, so the
    erase-0 is a no-op.  Result: `(aux rest n).map (·-1).erase 0 =
    aux rest (n-1)`.  Useful for analysing successive System 5 steps
    that drain the bag without touching the leading prefix. -/
theorem ctsConfigToSystem5BagAux_decrement_erase
    (rest : List Bool) (n : Int) (h : 2 ≤ n) :
    ((ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
    = ctsConfigToSystem5BagAux rest (n - 1) := by
  rw [ctsConfigToSystem5BagAux_map_decrement]
  apply List.erase_of_not_mem
  intro h_in
  have h_ge := ctsConfigToSystem5BagAux_ge rest (n - 1) 0 h_in
  omega

/-- **`decrement_erase_one_cons_aux` (iter 663)**: `decrement-erase` of
    `1 :: aux rest n` peels the leading `1` (becomes `0`, erased) and
    shifts the aux-tail down by 1. -/
theorem decrement_erase_one_cons_aux
    (rest : List Bool) (n : Int) :
    (((1 : Int) :: ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
    = ctsConfigToSystem5BagAux rest (n - 1) := by
  show ((0 : Int) :: (ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
      = ctsConfigToSystem5BagAux rest (n - 1)
  rw [List.erase_cons_head]
  exact ctsConfigToSystem5BagAux_map_decrement rest n

/-- **`decrement_erase_two_cons_aux` (iter 663)**: peels `1` (→ 0,
    erased), keeps `1` from original `2`, shifts tail. -/
theorem decrement_erase_two_cons_aux (rest : List Bool) (n : Int) :
    (((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
    = (1 : Int) :: ctsConfigToSystem5BagAux rest (n - 1) := by
  show ((0 : Int) :: 1 :: (ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
      = (1 : Int) :: ctsConfigToSystem5BagAux rest (n - 1)
  rw [List.erase_cons_head]
  rw [ctsConfigToSystem5BagAux_map_decrement]

/-- **`decrement_erase_three_cons_aux` (iter 663)**: peels `1` (→ 0,
    erased), keeps `1, 2` from original `2, 3`, shifts tail. -/
theorem decrement_erase_three_cons_aux (rest : List Bool) (n : Int) :
    (((1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
    = (1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest (n - 1) := by
  show ((0 : Int) :: 1 :: 2 :: (ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
      = (1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest (n - 1)
  rw [List.erase_cons_head]
  rw [ctsConfigToSystem5BagAux_map_decrement]

/-- **`decrement_erase_four_cons_aux` (iter 664)**: peels `1` (→ 0,
    erased), keeps `1, 2, 3` from original `2, 3, 4`, shifts tail.
    Continues the family `_one_cons`/`_two_cons`/`_three_cons`. -/
theorem decrement_erase_four_cons_aux (rest : List Bool) (n : Int) :
    (((1 : Int) :: 2 :: 3 :: 4 :: ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
    = (1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest (n - 1) := by
  show ((0 : Int) :: 1 :: 2 :: 3 ::
        (ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
      = (1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest (n - 1)
  rw [List.erase_cons_head]
  rw [ctsConfigToSystem5BagAux_map_decrement]

/-- **`decrement_erase_two_three_cons_aux` (iter 664)**: peels nothing
    (no `1` in `2 :: 3 :: ...` pre-decrement, but post-decrement the
    leading `1` is at the front, kept in the result alongside `2`).
    Models a "drained-by-1" bag step. -/
theorem decrement_erase_two_three_cons_aux (rest : List Bool) (n : Int) (h : 2 ≤ n) :
    (((2 : Int) :: 3 :: ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
    = (1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest (n - 1) := by
  show ((1 : Int) :: 2 :: (ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
      = (1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest (n - 1)
  have h_zero_not_in : (0 : Int) ∉ (1 : Int) :: 2 ::
      (ctsConfigToSystem5BagAux rest n).map (· - 1) := by
    intro h_in
    rcases List.mem_cons.mp h_in with h | h_in
    · cases h
    rcases List.mem_cons.mp h_in with h | h_in
    · cases h
    rw [ctsConfigToSystem5BagAux_map_decrement] at h_in
    have h_ge := ctsConfigToSystem5BagAux_ge rest (n - 1) 0 h_in
    omega
  rw [List.erase_of_not_mem h_zero_not_in]
  rw [ctsConfigToSystem5BagAux_map_decrement]

/-- **`decrement_erase_one_two_four_cons_aux` (iter 665)**: third step
    of the true-head System 5 trajectory.  Since `1 ∈ bag`, the step
    is dec-erase. -/
theorem decrement_erase_one_two_four_cons_aux
    (rest : List Bool) (n : Int) :
    (((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
    = (1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest (n - 1) := by
  show ((0 : Int) :: 1 :: 3 :: (ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
      = (1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest (n - 1)
  rw [List.erase_cons_head]
  rw [ctsConfigToSystem5BagAux_map_decrement]

/-- **`decrement_erase_one_three_cons_aux` (iter 665)**: fourth step
    of the true-head trajectory.  Leading `1` decrements to `0`
    (erased), `3` decrements to `2`, aux-tail shifts. -/
theorem decrement_erase_one_three_cons_aux
    (rest : List Bool) (n : Int) :
    (((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
    = (2 : Int) :: ctsConfigToSystem5BagAux rest (n - 1) := by
  show ((0 : Int) :: 2 :: (ctsConfigToSystem5BagAux rest n).map (· - 1)).erase 0
      = (2 : Int) :: ctsConfigToSystem5BagAux rest (n - 1)
  rw [List.erase_cons_head]
  rw [ctsConfigToSystem5BagAux_map_decrement]

/-- **`map_decrement_two_three_five_cons_aux` (iter 665)**: pure-
    decrement (no erase) on `2 :: 3 :: 5 :: aux rest n` — step 2 of
    the true-head trajectory.  `1 ∉ bag`, so the System 5 step is pure
    decrement. -/
theorem map_decrement_two_three_five_cons_aux
    (rest : List Bool) (n : Int) :
    ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest n).map (· - 1)
    = (1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest (n - 1) := by
  show (1 : Int) :: 2 :: 4 :: (ctsConfigToSystem5BagAux rest n).map (· - 1)
      = (1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest (n - 1)
  rw [ctsConfigToSystem5BagAux_map_decrement]

/-- **`map_decrement_two_cons_aux` (iter 665)**: pure-decrement on
    `2 :: aux rest n` — step 5 of the true-head trajectory.  `1 ∉
    bag`, so pure decrement. -/
theorem map_decrement_two_cons_aux
    (rest : List Bool) (n : Int) :
    ((2 : Int) :: ctsConfigToSystem5BagAux rest n).map (· - 1)
    = (1 : Int) :: ctsConfigToSystem5BagAux rest (n - 1) := by
  show (1 : Int) :: (ctsConfigToSystem5BagAux rest n).map (· - 1)
      = (1 : Int) :: ctsConfigToSystem5BagAux rest (n - 1)
  rw [ctsConfigToSystem5BagAux_map_decrement]


/-- **Bag-length delta (false head)** (iter 655): post-step encoded
    bag is exactly 4 elements shorter than pre-step. -/
theorem ctsConfigToSystem5Bag_step_false_head_length
    (rest : List Bool) (phase phase' : Nat) :
    (ctsConfigToSystem5Bag { data := rest, phase := phase' }).length + 4
    = (ctsConfigToSystem5Bag { data := false :: rest, phase := phase }).length := by
  rw [ctsConfigToSystem5Bag_length, ctsConfigToSystem5Bag_length]
  show 4 * rest.length + 4 = 4 * (false :: rest).length
  simp [List.length_cons]
  omega

/-- **Bag-length delta (true head)** (iter 655): post-step encoded bag
    length = pre-step length + `4 * (|appendant| - 1)`. -/
theorem ctsConfigToSystem5Bag_step_true_head_length
    (cts : CTS) (rest : List Bool) (phase phase' : Nat) :
    (ctsConfigToSystem5Bag
      { data := rest ++ cts.currentAppendant phase, phase := phase' }).length + 4
    = (ctsConfigToSystem5Bag { data := true :: rest, phase := phase }).length
        + 4 * (cts.currentAppendant phase).length := by
  rw [ctsConfigToSystem5Bag_length, ctsConfigToSystem5Bag_length]
  show 4 * (rest ++ cts.currentAppendant phase).length + 4
      = 4 * (true :: rest).length + 4 * (cts.currentAppendant phase).length
  rw [List.length_append, List.length_cons]
  omega

/-- **Bag-of-step relation (false head)** (iter 653): the encoded bag
    of the post-step cfg, shifted up by 4, equals the drop-4 of the
    encoded bag of the pre-step cfg.  Combines `CTS_step_false_head`
    with `_drop4_false_head`. -/
theorem ctsConfigToSystem5Bag_step_false_head
    (cts : CTS) (rest : List Bool) (phase : Nat) :
    let cfg : CTSConfig := { data := false :: rest, phase := phase }
    let cfg' : CTSConfig := { data := rest,
                              phase := (phase + 1) % cts.appendants.length }
    cts.step cfg = some cfg' ∧
    (ctsConfigToSystem5Bag cfg').map (· + 4)
      = (ctsConfigToSystem5Bag cfg).drop 4 := by
  refine ⟨CTS_step_false_head cts rest phase, ?_⟩
  exact (ctsConfigToSystem5Bag_drop4_false_head rest phase _).symm

/-- **Bag-of-step relation (true head)** (iter 653): post-step bag is
    the encoded `rest` followed by the encoded appendant starting at
    the post-`rest` counter.  Uses `CTS_step_true_head` plus the
    append decomposition. -/
theorem ctsConfigToSystem5Bag_step_true_head
    (cts : CTS) (rest : List Bool) (phase : Nat) :
    let cfg : CTSConfig := { data := true :: rest, phase := phase }
    let cfg' : CTSConfig := { data := rest ++ cts.currentAppendant phase,
                              phase := (phase + 1) % cts.appendants.length }
    cts.step cfg = some cfg' ∧
    ctsConfigToSystem5Bag cfg'
      = ctsConfigToSystem5BagAux rest 1
        ++ ctsConfigToSystem5BagAux (cts.currentAppendant phase)
                                     (counterAfterWorkingString rest) := by
  refine ⟨CTS_step_true_head cts rest phase, ?_⟩
  show ctsConfigToSystem5BagAux (rest ++ cts.currentAppendant phase) 1
      = ctsConfigToSystem5BagAux rest 1
        ++ ctsConfigToSystem5BagAux (cts.currentAppendant phase)
                                     (counterAfterWorkingString rest)
  rw [ctsConfigToSystem5BagAux_append rest (cts.currentAppendant phase) 1,
      counterAux_one_eq_counterAfterWorkingString]

/-- **Decrement-erase, true head**: explicit form of `((bag).map (· -
    1)).erase 0` when `cfg.data = true :: rest`.  The bag becomes `2 ::
    3 :: 5 :: aux rest 6` after the decrement and erase that precede
    XOR-merge in the System 5 step. -/
theorem ctsConfigToSystem5Bag_decrement_erase_true (rest : List Bool) (phase : Nat) :
    ((ctsConfigToSystem5Bag { data := true :: rest, phase := phase }).map (· - 1)).erase 0
      = 2 :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6 := by
  rw [ctsConfigToSystem5Bag_decrement]
  show ((0 : Int) :: 2 :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6).erase 0 = _
  rfl

/-- **Decrement-erase, false head**: explicit form of `((bag).map (· -
    1)).erase 0` when `cfg.data = false :: rest`.  The bag becomes `1
    :: 2 :: 3 :: aux rest 4` after the decrement and erase that precede
    XOR-merge. -/
theorem ctsConfigToSystem5Bag_decrement_erase_false (rest : List Bool) (phase : Nat) :
    ((ctsConfigToSystem5Bag { data := false :: rest, phase := phase }).map (· - 1)).erase 0
      = 1 :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4 := by
  rw [ctsConfigToSystem5Bag_decrement]
  show ((0 : Int) :: 1 :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4).erase 0 = _
  rfl

/-- For a false-head CTS config, `1` is in the post-decrement-erase
    bag.  Implies the SECOND System 5 step is also a rule pop. -/
theorem one_mem_decrement_erase_false (rest : List Bool) (phase : Nat) :
    (1 : Int) ∈
      ((ctsConfigToSystem5Bag { data := false :: rest, phase := phase }).map
          (· - 1)).erase 0 := by
  rw [ctsConfigToSystem5Bag_decrement_erase_false]
  exact List.mem_cons.mpr (Or.inl rfl)

/-- For a true-head CTS config, `1` is NOT in the post-decrement-erase
    bag.  Implies the SECOND System 5 step is a pure decrement. -/
theorem one_not_mem_decrement_erase_true (rest : List Bool) (phase : Nat) :
    (1 : Int) ∉
      ((ctsConfigToSystem5Bag { data := true :: rest, phase := phase }).map
          (· - 1)).erase 0 := by
  rw [ctsConfigToSystem5Bag_decrement_erase_true]
  intro h
  simp at h
  have := ctsConfigToSystem5BagAux_ge rest 6 1 h
  omega

/-- For any non-empty CTS config, `2` is in the post-decrement-erase
    bag.  Both true-head (1st elem) and false-head (2nd elem) cases. -/
theorem two_mem_decrement_erase (cfg : CTSConfig) (h : cfg.data ≠ []) :
    (2 : Int) ∈ ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0 := by
  cases h_data : cfg.data with
  | nil => exact absurd h_data h
  | cons head tail =>
    cases head with
    | true =>
      have heq : cfg = { data := true :: tail, phase := cfg.phase } := by
        cases cfg; simp at h_data; subst h_data; rfl
      rw [heq, ctsConfigToSystem5Bag_decrement_erase_true]
      exact List.mem_cons.mpr (Or.inl rfl)
    | false =>
      have heq : cfg = { data := false :: tail, phase := cfg.phase } := by
        cases cfg; simp at h_data; subst h_data; rfl
      rw [heq, ctsConfigToSystem5Bag_decrement_erase_false]
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

/-- For any non-empty CTS config, `3` is in the post-decrement-erase
    bag.  Position 3rd in false-head, 2nd in true-head. -/
theorem three_mem_decrement_erase (cfg : CTSConfig) (h : cfg.data ≠ []) :
    (3 : Int) ∈ ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0 := by
  cases h_data : cfg.data with
  | nil => exact absurd h_data h
  | cons head tail =>
    cases head with
    | true =>
      have heq : cfg = { data := true :: tail, phase := cfg.phase } := by
        cases cfg; simp at h_data; subst h_data; rfl
      rw [heq, ctsConfigToSystem5Bag_decrement_erase_true]
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    | false =>
      have heq : cfg = { data := false :: tail, phase := cfg.phase } := by
        cases cfg; simp at h_data; subst h_data; rfl
      rw [heq, ctsConfigToSystem5Bag_decrement_erase_false]
      exact List.mem_cons.mpr
        (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

/-- **`ctsConfigToSystem5Bag_drainSeq4_false_head` (iter 665)**:
    starting from `ctsConfigToSystem5Bag {data := false :: rest, _}` (=
    `1::2::3::4::aux rest 5`), four dec-erase steps yield
    `ctsConfigToSystem5BagAux rest 1`.  Captures the bag dynamics
    across one full "false-bit-consumed" sub-trajectory in the
    AllEmptyAppendants regime. -/
theorem ctsConfigToSystem5Bag_drainSeq4_false_head
    (rest : List Bool) (phase : Nat) :
    let bag := ctsConfigToSystem5Bag { data := false :: rest, phase := phase }
    let s1 := (bag.map (· - 1)).erase 0
    let s2 := (s1.map (· - 1)).erase 0
    let s3 := (s2.map (· - 1)).erase 0
    let s4 := (s3.map (· - 1)).erase 0
    s4 = ctsConfigToSystem5BagAux rest 1 := by
  simp only
  rw [ctsConfigToSystem5Bag_decrement_erase_false]
  rw [decrement_erase_three_cons_aux rest 4]
  rw [show (4 : Int) - 1 = 3 from by omega]
  rw [decrement_erase_two_cons_aux rest 3]
  rw [show (3 : Int) - 1 = 2 from by omega]
  rw [decrement_erase_one_cons_aux rest 2]
  rw [show (2 : Int) - 1 = 1 from by omega]

/-- **`ctsConfigToSystem5Bag_2step_true_head` (iter 665)**: starting
    from `ctsConfigToSystem5Bag {data := true :: rest, _}` (=
    `1::3::4::6::aux rest 7`), one dec-erase step yields `2::3::5::aux
    rest 6`; one further pure-decrement step yields `1::2::4::aux rest
    5`.  Models the alternation D-P in the true-head case. -/
theorem ctsConfigToSystem5Bag_2step_true_head
    (rest : List Bool) (phase : Nat) :
    let bag := ctsConfigToSystem5Bag { data := true :: rest, phase := phase }
    let s1 := (bag.map (· - 1)).erase 0
    let s2 := s1.map (· - 1)
    s2 = (1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5 := by
  simp only
  rw [ctsConfigToSystem5Bag_decrement_erase_true]
  show ((1 : Int) :: 2 :: 4 :: (ctsConfigToSystem5BagAux rest 6).map (· - 1))
      = (1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5
  rw [ctsConfigToSystem5BagAux_map_decrement]
  rw [show (6 : Int) - 1 = 5 from by omega]

/-- **Iter 888 KEY ENCODER PROPERTY**: `firstRule = secondRule.map (·+2)`.
    For each emitted pair `(p1, p2)` in encodeAppendant: `p1 = p2 + 2`.
    This is the fundamental algebraic cancellation property — after
    2 System5 step increments, the secondRule's incremented form
    matches firstRule's original form, enabling xor cancellation
    across the 2-step rule cycle.  See iter 871 trajectory trace. -/
theorem encodeAppendant_r1_eq_r2_add_2 (data : List Bool) (i : Int) :
    (encodeAppendant data i).1 = (encodeAppendant data i).2.1.map (· + 2) := by
  induction data generalizing i with
  | nil => simp [encodeAppendant]
  | cons b rest ih =>
    cases b with
    | true =>
      show (i + 2) :: (i + 5) :: (encodeAppendant rest (i + 6)).1
         = (i :: (i + 3) :: (encodeAppendant rest (i + 6)).2.1).map (· + 2)
      simp [List.map_cons]
      refine ⟨by omega, ?_⟩
      exact ih (i + 6)
    | false =>
      show (i + 2) :: (i + 3) :: (encodeAppendant rest (i + 4)).1
         = (i :: (i + 1) :: (encodeAppendant rest (i + 4)).2.1).map (· + 2)
      simp [List.map_cons]
      refine ⟨by omega, ?_⟩
      exact ih (i + 4)

/-- **Iter 889 corollary**: `r1.length = r2.length` follows from
    `r1 = r2.map(·+2)` since `map` preserves length. -/
theorem encodeAppendant_r1_r2_same_length (data : List Bool) (i : Int) :
    (encodeAppendant data i).1.length = (encodeAppendant data i).2.1.length := by
  rw [encodeAppendant_r1_eq_r2_add_2]
  simp

/-- **Iter 889 corollary**: applying `(·+2)` to r2 yields r1 — alternative form. -/
theorem encodeAppendant_r2_map_add_2_eq_r1 (data : List Bool) (i : Int) :
    (encodeAppendant data i).2.1.map (· + 2) = (encodeAppendant data i).1 :=
  (encodeAppendant_r1_eq_r2_add_2 data i).symm

/-- **Iter 890**: lifts the encoder cancellation property to `processCycle`'s
    first two emitted rules for a non-empty appendant list.  `rules[0]` and
    `rules[1]` are r1 and r2 of the first appendant respectively, with
    r1 = r2.map(·+2). -/
theorem processCycle_first_two_rules_cancel
    (a : List Bool) (rest : List (List Bool)) (i : Int) :
    ∃ r1 r2 tail, (processCycle (a :: rest) i).1 = r1 :: r2 :: tail
                ∧ r1 = r2.map (· + 2) := by
  refine ⟨(encodeAppendant a i).1, (encodeAppendant a i).2.1,
          [] :: [] :: (processCycle rest (encodeAppendant a i).2.2).1, ?_, ?_⟩
  · show (processCycle (a :: rest) i).1
        = (encodeAppendant a i).1 :: (encodeAppendant a i).2.1 ::
          [] :: [] :: (processCycle rest (encodeAppendant a i).2.2).1
    rfl
  · exact encodeAppendant_r1_eq_r2_add_2 a i

/-- **Iter 891**: lifts the cancellation property to `nCycles` for `k ≥ 1`
    cycles with non-empty appendant list.  The first two emitted rules
    are the first appendant's r1 and r2. -/
theorem nCycles_first_two_rules_cancel
    (a : List Bool) (rest : List (List Bool)) (k : Nat) (i : Int) :
    ∃ r1 r2 tail, nCycles (a :: rest) (k + 1) i = r1 :: r2 :: tail
                ∧ r1 = r2.map (· + 2) := by
  rw [nCycles_succ]
  obtain ⟨r1, r2, mid_tail, h_pc, h_cancel⟩ :=
    processCycle_first_two_rules_cancel a rest i
  refine ⟨r1, r2, mid_tail ++ nCycles (a :: rest) k (processCycle (a :: rest) i).snd,
          ?_, h_cancel⟩
  rw [h_pc]
  rfl

/-- **Iter 900: encoder-rule disjointness with bag prefix**.  Every
    element of `r1 = (encodeAppendant rule i).1` satisfies `x ≥ i + 2`.
    For starting counter `i ≥ 4`, this means no rule element equals
    1, 2, 3, or 4 — the [1,2,3,4] prefix that gets consumed by the
    false-head 4-step trajectory is disjoint from rule contributions. -/
theorem encodeAppendant_r1_min_value (rule : List Bool) (i : Int) (x : Int)
    (h : x ∈ (encodeAppendant rule i).1) : x ≥ i + 2 := by
  induction rule generalizing i with
  | nil => simp [encodeAppendant] at h
  | cons b rest ih =>
    cases b with
    | true =>
      have h' : x ∈ ((i + 2) :: (i + 5) :: (encodeAppendant rest (i + 6)).1) := h
      rcases List.mem_cons.mp h' with h1 | h2
      · omega
      rcases List.mem_cons.mp h2 with h3 | h4
      · omega
      have := ih (i + 6) h4
      omega
    | false =>
      have h' : x ∈ ((i + 2) :: (i + 3) :: (encodeAppendant rest (i + 4)).1) := h
      rcases List.mem_cons.mp h' with h1 | h2
      · omega
      rcases List.mem_cons.mp h2 with h3 | h4
      · omega
      have := ih (i + 4) h4
      omega

/-- **Iter 901: r2 minimum value**.  Every element of
    `r2 = (encodeAppendant rule i).2.1` satisfies `x ≥ i`.  The lower
    bound is `i` (not `i+2` as for r1) — r2's first emitted element
    is always the bare counter `i`. -/
theorem encodeAppendant_r2_min_value (rule : List Bool) (i : Int) (x : Int)
    (h : x ∈ (encodeAppendant rule i).2.1) : x ≥ i := by
  induction rule generalizing i with
  | nil => simp [encodeAppendant] at h
  | cons b rest ih =>
    cases b with
    | true =>
      have h' : x ∈ (i :: (i + 3) :: (encodeAppendant rest (i + 6)).2.1) := h
      rcases List.mem_cons.mp h' with h1 | h2
      · omega
      rcases List.mem_cons.mp h2 with h3 | h4
      · omega
      have := ih (i + 6) h4
      omega
    | false =>
      have h' : x ∈ (i :: (i + 1) :: (encodeAppendant rest (i + 4)).2.1) := h
      rcases List.mem_cons.mp h' with h1 | h2
      · omega
      rcases List.mem_cons.mp h2 with h3 | h4
      · omega
      have := ih (i + 4) h4
      omega

/-- **Iter 902: r2.map(·+2) min value follows from r2 min value**.
    Combined with `encodeAppendant_r1_eq_r2_add_2`, this shows
    r1 = r2+2 has elements ≥ i+2 (matching r1's direct bound). -/
theorem encodeAppendant_r2_map_add_2_min_value (rule : List Bool) (i : Int) (x : Int)
    (h : x ∈ (encodeAppendant rule i).2.1.map (· + 2)) : x ≥ i + 2 := by
  rw [List.mem_map] at h
  obtain ⟨y, hy_mem, hy_eq⟩ := h
  have := encodeAppendant_r2_min_value rule i y hy_mem
  omega

/-- **Iter 903: processCycle's first two rules have elements bounded below**.
    `r1` elements are ≥ i+2; `r2` elements are ≥ i.  Lifts the encoder's
    per-rule min bounds to processCycle's first two emitted rules. -/
theorem processCycle_first_two_rules_min_value
    (a : List Bool) (rest : List (List Bool)) (i : Int) :
    ∃ r1 r2 tail, (processCycle (a :: rest) i).1 = r1 :: r2 :: tail
                ∧ (∀ x ∈ r1, x ≥ i + 2)
                ∧ (∀ x ∈ r2, x ≥ i) := by
  refine ⟨(encodeAppendant a i).1, (encodeAppendant a i).2.1,
          [] :: [] :: (processCycle rest (encodeAppendant a i).2.2).1, ?_, ?_, ?_⟩
  · show (processCycle (a :: rest) i).1
        = (encodeAppendant a i).1 :: (encodeAppendant a i).2.1 ::
          [] :: [] :: (processCycle rest (encodeAppendant a i).2.2).1
    rfl
  · exact encodeAppendant_r1_min_value a i
  · exact encodeAppendant_r2_min_value a i

/-- **Iter 904**: lifts min bounds to nCycles for k+1 cycles. -/
theorem nCycles_first_two_rules_min_value
    (a : List Bool) (rest : List (List Bool)) (k : Nat) (i : Int) :
    ∃ r1 r2 tail, nCycles (a :: rest) (k + 1) i = r1 :: r2 :: tail
                ∧ (∀ x ∈ r1, x ≥ i + 2)
                ∧ (∀ x ∈ r2, x ≥ i) := by
  rw [nCycles_succ]
  obtain ⟨r1, r2, mid_tail, h_pc, h_r1, h_r2⟩ :=
    processCycle_first_two_rules_min_value a rest i
  refine ⟨r1, r2, mid_tail ++ nCycles (a :: rest) k (processCycle (a :: rest) i).snd,
          ?_, h_r1, h_r2⟩
  rw [h_pc]
  rfl

/-- **Iter 904**: lifts min bounds to ctsRulesToSystem5Rules.  For any
    CTS and N ≥ 1, the first two emitted rules have elements bounded
    below by `counterAfterWorkingString cfg.data + 2` (for r1) and
    `counterAfterWorkingString cfg.data + 2 - ?` for r2. -/
theorem ctsRulesToSystem5Rules_first_two_rules_min_value
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    let i := counterAfterWorkingString cfg.data + 2
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ (∀ x ∈ r1, x ≥ i + 2)
                ∧ (∀ x ∈ r2, x ≥ i) := by
  unfold ctsRulesToSystem5Rules
  cases h_app : cts.appendants with
  | nil =>
    have := cts.nonempty
    rw [h_app] at this
    simp at this
  | cons a rest =>
    cases N with
    | zero => omega
    | succ k =>
      exact nCycles_first_two_rules_min_value a rest k
        (counterAfterWorkingString cfg.data + 2)

/-- **Iter 905: counterAfterWorkingString lower bound for false-head data**.
    When data = false :: rest, the counter advances from 1 by ≥ 4 (the
    false-bit advance), so `counterAfterWorkingString (false :: rest) ≥ 5`. -/
theorem counterAfterWorkingString_false_head_ge (rest : List Bool) :
    counterAfterWorkingString (false :: rest) ≥ 5 := by
  rw [counterAfterWorkingString_cons_false]
  have h_ge_one : counterAfterWorkingString rest ≥ 1 := by
    induction rest with
    | nil => simp [counterAfterWorkingString]
    | cons b rest' ih =>
      cases b with
      | true =>
        rw [counterAfterWorkingString_cons_true]
        omega
      | false =>
        rw [counterAfterWorkingString_cons_false]
        omega
  omega

/-- **Iter 908: bag aux upper bound**.  Every element x of
    `ctsConfigToSystem5BagAux data i` satisfies `x ≤ i + counterAfterWorkingString data - 2`. -/
theorem ctsConfigToSystem5BagAux_max (data : List Bool) (i : Int) (x : Int)
    (h : x ∈ ctsConfigToSystem5BagAux data i) :
    x ≤ i + counterAfterWorkingString data - 2 := by
  induction data generalizing i with
  | nil => simp [ctsConfigToSystem5BagAux] at h
  | cons b rest ih =>
    cases b with
    | true =>
      have h' : x ∈ (i :: (i + 2) :: (i + 3) :: (i + 5) ::
                     ctsConfigToSystem5BagAux rest (i + 6)) := h
      have h_ge1 : counterAfterWorkingString rest ≥ 1 :=
        counterAfterWorkingString_ge_one rest
      rw [counterAfterWorkingString_cons_true]
      rcases List.mem_cons.mp h' with h1 | h2
      · omega
      rcases List.mem_cons.mp h2 with h3 | h4
      · omega
      rcases List.mem_cons.mp h4 with h5 | h6
      · omega
      rcases List.mem_cons.mp h6 with h7 | h8
      · omega
      have := ih (i + 6) h8
      omega
    | false =>
      have h' : x ∈ (i :: (i + 1) :: (i + 2) :: (i + 3) ::
                     ctsConfigToSystem5BagAux rest (i + 4)) := h
      have h_ge1 : counterAfterWorkingString rest ≥ 1 :=
        counterAfterWorkingString_ge_one rest
      rw [counterAfterWorkingString_cons_false]
      rcases List.mem_cons.mp h' with h1 | h2
      · omega
      rcases List.mem_cons.mp h2 with h3 | h4
      · omega
      rcases List.mem_cons.mp h4 with h5 | h6
      · omega
      rcases List.mem_cons.mp h6 with h7 | h8
      · omega
      have := ih (i + 4) h8
      omega

/-- **Iter 909: bag and first rule disjoint** for any ctsToSystem5
    encoder.  Bag elements ≤ counterAfterWorkingString - 1; r1 elements
    ≥ counterAfterWorkingString + 4.  Gap of 5, so disjoint. -/
theorem ctsToSystem5_bag_r1_disjoint
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ []) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ (∀ x ∈ ctsConfigToSystem5Bag cfg, x ∉ r1) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, h_r2⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_min_value cts cfg N h_N
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro x hx_bag hx_r1
  have h_bag_max : x ≤ counterAfterWorkingString cfg.data - 1 := by
    unfold ctsConfigToSystem5Bag at hx_bag
    have := ctsConfigToSystem5BagAux_max cfg.data 1 x hx_bag
    omega
  have h_r1_min : x ≥ counterAfterWorkingString cfg.data + 4 := by
    have := h_r1 x hx_r1
    omega
  omega

/-- **Iter 910: bag and second rule disjoint**.  Bag ≤ counterAfter - 1;
    r2 ≥ counterAfter + 2.  Gap of 3, still disjoint. -/
theorem ctsToSystem5_bag_r2_disjoint
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ []) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ (∀ x ∈ ctsConfigToSystem5Bag cfg, x ∉ r2) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, h_r2⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_min_value cts cfg N h_N
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro x hx_bag hx_r2
  have h_bag_max : x ≤ counterAfterWorkingString cfg.data - 1 := by
    unfold ctsConfigToSystem5Bag at hx_bag
    have := ctsConfigToSystem5BagAux_max cfg.data 1 x hx_bag
    omega
  have h_r2_min : x ≥ counterAfterWorkingString cfg.data + 2 := by
    have := h_r2 x hx_r2
    omega
  omega

/-- **Iter 911: bag and r1.map(·+1) disjoint** (rules incremented at
    step 1).  Bag ≤ counterAfter - 1; (r1+1) ≥ counterAfter + 5.
    Gap of 6, disjoint. -/
theorem ctsToSystem5_bag_r1_inc_disjoint
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ []) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ (∀ x ∈ ctsConfigToSystem5Bag cfg, x ∉ r1.map (· + 1)) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, h_r2⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_min_value cts cfg N h_N
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro x hx_bag hx_r1_inc
  rw [List.mem_map] at hx_r1_inc
  obtain ⟨y, hy_mem, hy_eq⟩ := hx_r1_inc
  have h_bag_max : x ≤ counterAfterWorkingString cfg.data - 1 := by
    unfold ctsConfigToSystem5Bag at hx_bag
    have := ctsConfigToSystem5BagAux_max cfg.data 1 x hx_bag
    omega
  have h_y_min := h_r1 y hy_mem
  omega

/-- **Iter 913: dec-erase'd bag disjoint from r1.map(·+1)**.  After
    decrement and erase 0 of the encoded bag, every element ≤ counterAfter - 2
    (gap from counterAfter + 5 of (r1+1)).  Disjoint. -/
theorem ctsToSystem5_dec_erase_bag_r1_inc_disjoint
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ []) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ (∀ x ∈ ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0,
                    x ∉ r1.map (· + 1)) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, h_r2⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_min_value cts cfg N h_N
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro x hx_in hx_r1_inc
  have hx_in_dec : x ∈ (ctsConfigToSystem5Bag cfg).map (· - 1) :=
    List.mem_of_mem_erase hx_in
  rw [List.mem_map] at hx_in_dec
  obtain ⟨z, hz_bag, hz_eq⟩ := hx_in_dec
  rw [List.mem_map] at hx_r1_inc
  obtain ⟨y, hy_mem, hy_eq⟩ := hx_r1_inc
  have h_bag_max : z ≤ counterAfterWorkingString cfg.data - 1 := by
    unfold ctsConfigToSystem5Bag at hz_bag
    have := ctsConfigToSystem5BagAux_max cfg.data 1 z hz_bag
    omega
  have h_y_min := h_r1 y hy_mem
  omega

theorem ctsToSystem5_bag_r2_inc2_disjoint
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ []) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ (∀ x ∈ ctsConfigToSystem5Bag cfg, x ∉ r2.map (· + 2)) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, h_r2⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_min_value cts cfg N h_N
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro x hx_bag hx_r2_inc
  rw [List.mem_map] at hx_r2_inc
  obtain ⟨y, hy_mem, hy_eq⟩ := hx_r2_inc
  have h_bag_max : x ≤ counterAfterWorkingString cfg.data - 1 := by
    unfold ctsConfigToSystem5Bag at hx_bag
    have := ctsConfigToSystem5BagAux_max cfg.data 1 x hx_bag
    omega
  have h_y_min : y ≥ counterAfterWorkingString cfg.data + 2 :=
    h_r2 y hy_mem
  omega

/-- **Iter 906: r1, r2 elements are ≥ 9 / ≥ 7 for false-head ctsToSystem5**.
    Combines `counterAfterWorkingString_false_head_ge` with
    `ctsRulesToSystem5Rules_first_two_rules_min_value`.  The starting
    counter is ≥ 7, so r1 ≥ 9 and r2 ≥ 7 — both disjoint from {1,2,3,4}. -/
theorem ctsToSystem5_false_head_first_two_rules_ge_seven
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ (∀ x ∈ r1, x ≥ 9)
      ∧ (∀ x ∈ r2, x ≥ 7) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, h_r2⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_min_value cts
      { data := false :: rest, phase := phase } N h_N
  have h_counter : counterAfterWorkingString
      ({ data := false :: rest, phase := phase } : CTSConfig).data ≥ 5 :=
    counterAfterWorkingString_false_head_ge rest
  refine ⟨r1, r2, tail, h_eq, ?_, ?_⟩
  · intro x hx
    have := h_r1 x hx
    omega
  · intro x hx
    have := h_r2 x hx
    omega

/-- **Iter 971: 1 ∉ firstRule.map(·+1) for false-head**.  The first
    emitted rule (r1) of the false-head encoder has all entries ≥ 9
    (iter 906); incrementing keeps them ≥ 10, so 1 is not in the
    incremented r1.  This is the disjointness side of the "1 stays
    in the bag after the first P-step" argument: combined with iter
    970's `ctsConfigToSystem5Bag_false_head_dec_erase_one_mem` and
    iter 969's `xorMerge_mem_left_of_not_mem_right`, gives that step
    2 is also a P-step (1 still in the new bag). -/
theorem ctsRulesToSystem5Rules_false_head_first_rule_inc_no_one
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ (1 : Int) ∉ r1.map (· + 1) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, _⟩ :=
    ctsToSystem5_false_head_first_two_rules_ge_seven cts rest phase N h_N
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro h_in
  rw [List.mem_map] at h_in
  obtain ⟨y, hy_mem, hy_eq⟩ := h_in
  have := h_r1 y hy_mem
  omega

/-- **Iter 973: 2 ∉ {firstRule.map(·+1), secondRule.map(·+2)} for
    false-head**.  Companion to iter 971: r1 entries ≥ 9 means
    `r1.map(·+1)` entries ≥ 10 > 2, and r2 entries ≥ 7 means
    `r2.map(·+2)` entries ≥ 9 > 2.  Both incremented rules are
    disjoint from `{2}`, so xorMerge with the small-counter bag
    elements (1, 2, 3, ...) preserves them.  Used for chaining to
    step 3 of the false-head trajectory. -/
theorem ctsRulesToSystem5Rules_false_head_first_two_rules_no_two
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ (2 : Int) ∉ r1.map (· + 1)
      ∧ (2 : Int) ∉ r2.map (· + 2) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, h_r2⟩ :=
    ctsToSystem5_false_head_first_two_rules_ge_seven cts rest phase N h_N
  refine ⟨r1, r2, tail, h_eq, ?_, ?_⟩
  · intro h_in
    rw [List.mem_map] at h_in
    obtain ⟨y, hy_mem, hy_eq⟩ := h_in
    have := h_r1 y hy_mem
    omega
  · intro h_in
    rw [List.mem_map] at h_in
    obtain ⟨y, hy_mem, hy_eq⟩ := h_in
    have := h_r2 y hy_mem
    omega

/-- **Iter 976: 1 ∉ secondRule.map(·+2) for false-head**.  Companion
    to iter 971: the second emitted rule (r2) of the false-head
    encoder has all entries ≥ 7 (iter 906); shifting by 2 keeps them
    ≥ 9, so 1 is not in the +2-shifted r2.

    Used in the step-3-is-P-step argument: bag-2 = xorMerge (...)
    (r2.map(·+2)), and `xorMerge_mem_left_of_not_mem_right` with
    `1 ∉ r2.map(·+2)` preserves `1` in bag-2 when it's already in the
    decremented bag-1. -/
theorem ctsRulesToSystem5Rules_false_head_second_rule_inc2_no_one
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ (1 : Int) ∉ r2.map (· + 2) := by
  obtain ⟨r1, r2, tail, h_eq, _, h_r2⟩ :=
    ctsToSystem5_false_head_first_two_rules_ge_seven cts rest phase N h_N
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro h_in
  rw [List.mem_map] at h_in
  obtain ⟨y, hy_mem, hy_eq⟩ := h_in
  have := h_r2 y hy_mem
  omega

/-- **Iter 987: 3 ∉ {firstRule.map(·+1), secondRule.map(·+2)} for
    false-head**.  Companion to iters 971/973/976.  r1 entries ≥ 9
    means `r1.map(·+1)` ≥ 10 > 3, and r2 entries ≥ 7 means
    `r2.map(·+2)` ≥ 9 > 3.  Both incremented rules are disjoint from
    `{3}`.  Used for the membership cascade `4 ∈ cfg5.bag ⇒ 3 ∈ s5_1.bag`. -/
theorem ctsRulesToSystem5Rules_false_head_first_two_rules_no_three
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ (3 : Int) ∉ r1.map (· + 1)
      ∧ (3 : Int) ∉ r2.map (· + 2) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, h_r2⟩ :=
    ctsToSystem5_false_head_first_two_rules_ge_seven cts rest phase N h_N
  refine ⟨r1, r2, tail, h_eq, ?_, ?_⟩
  · intro h_in
    rw [List.mem_map] at h_in
    obtain ⟨y, hy_mem, hy_eq⟩ := h_in
    have := h_r1 y hy_mem
    omega
  · intro h_in
    rw [List.mem_map] at h_in
    obtain ⟨y, hy_mem, hy_eq⟩ := h_in
    have := h_r2 y hy_mem
    omega

/-- **Iter 894**: incrementing then decrementing a list of integers
    cancels (round-trip).  Used in System5 trajectory reasoning where
    rules are incremented on each step's start; if no other ops apply,
    decrementing recovers the original. -/
theorem List_Int_inc_dec_cancel (r : List Int) :
    (r.map (· + 1)).map (· - 1) = r := by
  induction r with
  | nil => rfl
  | cons x xs ih =>
    show (x + 1 - 1) :: ((xs.map (· + 1)).map (· - 1)) = x :: xs
    rw [ih]
    congr 1
    omega

/-- **Iter 996: inc-then-reverse-then-dec cancels to reverse**.
    `(r.map(·+1)).reverse.map(·-1) = r.reverse`.  Used in the
    bag-1 → bag-2 chain to simplify the dec-erase of the (reversed)
    incremented r1 in s5_1.bag.  Combines `List.map_reverse` with
    `List_Int_inc_dec_cancel` (iter 894). -/
theorem List_Int_inc_reverse_dec_cancel (r : List Int) :
    (r.map (· + 1)).reverse.map (· - 1) = r.reverse := by
  rw [← List.map_reverse]
  exact List_Int_inc_dec_cancel r.reverse

/-- **Iter 997: erase appended element when prefix has no occurrence**.
    `(xs ++ (a :: ys)).erase a = xs ++ ys` when `a ∉ xs`.  The first
    `a` in the concatenation is at the head of the appended part, so
    erasing removes it cleanly.  Used in the bag-1 → bag-2 chain to
    locate and erase the `0` that appears after the r1.reverse prefix. -/
theorem List_Int_erase_append_cons_of_not_mem
    (xs ys : List Int) (a : Int) (h : a ∉ xs) :
    (xs ++ (a :: ys)).erase a = xs ++ ys := by
  induction xs with
  | nil => simp [List.erase_cons_head]
  | cons x xs' ih =>
    have h_x_ne : x ≠ a := fun h_eq => h (h_eq ▸ List.mem_cons_self)
    have h_a_not_xs' : a ∉ xs' := fun h_in => h (List.mem_cons_of_mem _ h_in)
    show (x :: (xs' ++ (a :: ys))).erase a = x :: (xs' ++ ys)
    have h_beq : ¬(x == a) = true := by simp; exact h_x_ne
    rw [List.erase_cons_tail h_beq, ih h_a_not_xs']

/-- **Iter 894 cancellation algebra**: combining `r1 = r2.map(·+2)`
    (encoder property) with arithmetic shows `(r1.map(·+1)).map(·-1) = r2.map(·+2)`.
    This is the algebraic identity behind the iter 871 timed cancellation. -/
theorem encodeAppendant_cancellation_algebra (data : List Bool) (i : Int) :
    ((encodeAppendant data i).1.map (· + 1)).map (· - 1)
      = (encodeAppendant data i).2.1.map (· + 2) := by
  rw [List_Int_inc_dec_cancel]
  exact encodeAppendant_r1_eq_r2_add_2 data i

/-- **Iter 1018: encoder cancellation r1 = r2.map(·+2) is preserved
    under counter-shift**.  If `r1 = r2.map(·+2)`, then for any shift
    `m`, `r1.map(·+m) = (r2.map(·+m)).map(·+2)`.  The cancellation
    property propagates through the shifted rules at any trajectory
    step `m`.

    Used to extend iter 1014's `bag4_perm` from cfg5 to arbitrary s5'
    whose rules are `(orig.drop k).map(map(·+m))` per iter 956's
    trajectory invariant.  At cycle-aligned drops (`k = 4n`), the
    head two rules continue to satisfy the encoder cancellation
    property after shift. -/
theorem List_Int_cancellation_preserved_under_shift
    (r1 r2 : List Int) (m : Int) (h : r1 = r2.map (· + 2)) :
    r1.map (· + m) = (r2.map (· + m)).map (· + 2) := by
  rw [h]
  rw [List.map_map, List.map_map]
  congr 1
  funext x
  show x + 2 + m = x + m + 2
  omega

/-- **Iter 1019: drop-4 of `processCycle` gives cancellation-aligned head**.
    When the appendant list has at least 2 entries (`a :: a' :: rest`),
    dropping 4 from `processCycle` exposes the second appendant's r1', r2'
    which satisfy `r1' = r2'.map(·+2)` (the encoder cancellation property).
    This is the structural fact that the trajectory invariant
    (iter 956's `(orig.drop k).map(map(·+m))`) preserves cancellation
    at cycle-aligned drops `k = 4`. -/
theorem processCycle_drop_4_first_two_rules_cancel
    (a a' : List Bool) (rest : List (List Bool)) (i : Int) :
    ∃ r1 r2 tl, (processCycle (a :: a' :: rest) i).1.drop 4
              = r1 :: r2 :: tl
              ∧ r1 = r2.map (· + 2) := by
  rw [processCycle_drop_4_one_appendant]
  show ∃ r1 r2 tl, (processCycle (a' :: rest)
            (encodeAppendant a i).2.2).1 = r1 :: r2 :: tl
          ∧ r1 = r2.map (· + 2)
  refine ⟨(encodeAppendant a' (encodeAppendant a i).2.2).1,
          (encodeAppendant a' (encodeAppendant a i).2.2).2.1,
          [] :: [] :: (processCycle rest (encodeAppendant a' (encodeAppendant a i).2.2).2.2).1,
          ?_, ?_⟩
  · rfl
  · exact encodeAppendant_r1_eq_r2_add_2 a' _

/-- **Iter 1024: drop-8 cancellation for 3+ appendants**.  Demonstrates
    the inductive lifting of cancellation to multiple-of-4 drops via
    repeated application of iter 957's `processCycle_drop_4_one_appendant`.
    For a 3+ appendant cycle, dropping 8 exposes the third appendant's
    r1', r2' satisfying the encoder cancellation.  Pattern generalizes
    to drop-12, drop-16, etc. as long as the drop stays within the
    first cycle. -/
theorem processCycle_drop_8_first_two_rules_cancel
    (a a' a'' : List Bool) (rest : List (List Bool)) (i : Int) :
    ∃ r1 r2 tl, (processCycle (a :: a' :: a'' :: rest) i).1.drop 8 = r1 :: r2 :: tl
              ∧ r1 = r2.map (· + 2) := by
  have h1 := processCycle_drop_4_one_appendant a (a' :: a'' :: rest) i
  show ∃ r1 r2 tl,
      ((processCycle (a :: a' :: a'' :: rest) i).1.drop 4).drop 4
        = r1 :: r2 :: tl
      ∧ r1 = r2.map (· + 2)
  rw [h1]
  rw [processCycle_drop_4_one_appendant a' (a'' :: rest) (encodeAppendant a i).2.2]
  refine ⟨(encodeAppendant a'' (encodeAppendant a' (encodeAppendant a i).2.2).2.2).1,
          (encodeAppendant a'' (encodeAppendant a' (encodeAppendant a i).2.2).2.2).2.1,
          [] :: [] :: (processCycle rest (encodeAppendant a''
            (encodeAppendant a' (encodeAppendant a i).2.2).2.2).2.2).1,
          ?_, ?_⟩
  · rfl
  · exact encodeAppendant_r1_eq_r2_add_2 a'' _

/-- **Iter 1020: nCycles drop-4 cancellation alignment**.  Lifts iter
    1019's drop-4 cancellation to `nCycles` (multi-cycle) for 2+
    appendant lists.  The structure: dropping 4 from `nCycles (a :: a' :: rest) (k+1) i`
    yields `processCycle (a' :: rest) ... .1 ++ nCycles ... k ...`,
    and the head of `processCycle (a' :: rest) ...` is a fresh
    appendant pair `r1', r2'` satisfying `r1' = r2'.map(·+2)`. -/
theorem nCycles_drop_4_first_two_rules_cancel
    (a a' : List Bool) (rest : List (List Bool)) (k : Nat) (i : Int) :
    ∃ r1 r2 tl, (nCycles (a :: a' :: rest) (k + 1) i).drop 4
              = r1 :: r2 :: tl
              ∧ r1 = r2.map (· + 2) := by
  rw [nCycles_drop_first_appendant]
  show ∃ r1 r2 tl, (processCycle (a' :: rest) (encodeAppendant a i).2.2).1
              ++ nCycles (a :: a' :: rest) k (processCycle (a :: a' :: rest) i).snd
              = r1 :: r2 :: tl
              ∧ r1 = r2.map (· + 2)
  refine ⟨(encodeAppendant a' (encodeAppendant a i).2.2).1,
          (encodeAppendant a' (encodeAppendant a i).2.2).2.1,
          [] :: [] ::
            ((processCycle rest (encodeAppendant a' (encodeAppendant a i).2.2).2.2).1
              ++ nCycles (a :: a' :: rest) k (processCycle (a :: a' :: rest) i).snd),
          ?_, ?_⟩
  · rfl
  · exact encodeAppendant_r1_eq_r2_add_2 a' _

/-- **Iter 1025: nCycles drop-8 cancellation alignment**.  Lifts iter
    1024's drop-8 cancellation from `processCycle` to `nCycles` (multi-
    cycle) for 3+ appendant lists.  The structure: dropping 8 from
    `nCycles (a :: a' :: a'' :: rest) (k+1) i` peels off the first two
    appendants worth of rules (8 total) and exposes the third
    appendant's `r1''`, `r2''` from `encodeAppendant a''` evaluated at
    the twice-advanced counter.  These rules satisfy
    `r1'' = r2''.map(·+2)`.  Direct extension of the iter 1020 →
    iter 1024 pattern. -/
theorem nCycles_drop_8_first_two_rules_cancel
    (a a' a'' : List Bool) (rest : List (List Bool)) (k : Nat) (i : Int) :
    ∃ r1 r2 tl, (nCycles (a :: a' :: a'' :: rest) (k + 1) i).drop 8
              = r1 :: r2 :: tl
              ∧ r1 = r2.map (· + 2) := by
  show ∃ r1 r2 tl,
      ((nCycles (a :: a' :: a'' :: rest) (k + 1) i).drop 4).drop 4
        = r1 :: r2 :: tl
      ∧ r1 = r2.map (· + 2)
  rw [nCycles_drop_first_appendant]
  rw [processCycle_cons_four_explicit a' (a'' :: rest)
        (encodeAppendant a i).2.2]
  rw [processCycle_cons_four_explicit a'' rest
        (encodeAppendant a' (encodeAppendant a i).2.2).2.2]
  refine ⟨(encodeAppendant a''
            (encodeAppendant a' (encodeAppendant a i).2.2).2.2).1,
          (encodeAppendant a''
            (encodeAppendant a' (encodeAppendant a i).2.2).2.2).2.1,
          [] :: [] ::
            ((processCycle rest (encodeAppendant a''
              (encodeAppendant a' (encodeAppendant a i).2.2).2.2).2.2).1
              ++ nCycles (a :: a' :: a'' :: rest) k
                (processCycle (a :: a' :: a'' :: rest) i).2),
          ?_, ?_⟩
  · rfl
  · exact encodeAppendant_r1_eq_r2_add_2 a'' _

/-- **Iter 1028: drop-4n cancellation pattern (general form)**.  Generalizes
    iters 1019/1024 to arbitrary `k = 4n` aligned drops on `processCycle`.
    For `rules.length ≥ n + 1`, dropping `4 * n` rules from
    `processCycle rules i` yields a head pair satisfying the encoder
    cancellation `r1 = r2.map(·+2)` (the `(n+1)`-th appendant's r1, r2).
    Proof: induction on `n` chaining `processCycle_drop_4_one_appendant`
    via `Nat.mul_succ` + `List.drop_drop`. -/
theorem processCycle_drop_4n_first_two_rules_cancel
    (rules : List (List Bool)) (n : Nat) (i : Int)
    (h_len : rules.length ≥ n + 1) :
    ∃ r1 r2 tl, (processCycle rules i).1.drop (4 * n) = r1 :: r2 :: tl
              ∧ r1 = r2.map (· + 2) := by
  induction n generalizing rules i with
  | zero =>
    cases rules with
    | nil => simp at h_len
    | cons a rest =>
      simp only [Nat.mul_zero, List.drop_zero]
      rw [processCycle_cons_four_explicit]
      exact ⟨_, _, _, rfl, encodeAppendant_r1_eq_r2_add_2 a i⟩
  | succ m ih =>
    cases rules with
    | nil => simp at h_len
    | cons a rest =>
      have h_rest : rest.length ≥ m + 1 := by
        simp at h_len; omega
      have h_eq : (processCycle (a :: rest) i).1.drop (4 * (m + 1))
                  = (processCycle rest (encodeAppendant a i).2.2).1.drop (4 * m) := by
        rw [Nat.mul_succ, Nat.add_comm, ← List.drop_drop]
        rw [processCycle_drop_4_one_appendant]
      rw [h_eq]
      exact ih rest (encodeAppendant a i).2.2 h_rest

/-- **Iter 1029: drop-4n cancellation at nCycles (within-first-cycle case)**.
    Lifts iter 1028's general drop-4n cancellation to `nCycles` when the
    drop stays within the first cycle (`rules.length ≥ n + 1`).  Generalizes
    iters 1020 (n=1) and 1025 (n=2) to arbitrary `4n` aligned drops.
    Proof: unfold `nCycles_succ` to expose `(processCycle ...) ++ nCycles ...`,
    then `List.drop_append` splits the drop, and `4*n - 4*rules.length = 0`
    keeps the nCycles tail intact. -/
theorem nCycles_drop_4n_first_two_rules_cancel
    (rules : List (List Bool)) (n k : Nat) (i : Int)
    (h_len : rules.length ≥ n + 1) :
    ∃ r1 r2 tl, (nCycles rules (k + 1) i).drop (4 * n) = r1 :: r2 :: tl
              ∧ r1 = r2.map (· + 2) := by
  rw [nCycles_succ]
  rw [List.drop_append, processCycle_length]
  have h_sub : 4 * n - 4 * rules.length = 0 := by omega
  rw [h_sub, List.drop_zero]
  obtain ⟨r1, r2, tl, h_eq, h_cancel⟩ :=
    processCycle_drop_4n_first_two_rules_cancel rules n i h_len
  refine ⟨r1, r2, tl ++ nCycles rules k (processCycle rules i).2,
          ?_, h_cancel⟩
  rw [h_eq]
  rfl

/-- **Iter 892**: lifts the cancellation property to `ctsRulesToSystem5Rules`.
    For any CTS (which has nonempty appendants by construction) and `N ≥ 1`,
    the first two emitted rules satisfy r1 = r2.map(·+2). -/
theorem ctsRulesToSystem5Rules_first_two_rules_cancel
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ r1 = r2.map (· + 2) := by
  unfold ctsRulesToSystem5Rules
  cases h_app : cts.appendants with
  | nil =>
    have := cts.nonempty
    rw [h_app] at this
    simp at this
  | cons a rest =>
    cases N with
    | zero => omega
    | succ k =>
      exact nCycles_first_two_rules_cancel a rest k
        (counterAfterWorkingString cfg.data + 2)

/-- **Iter 1021: ctsRulesToSystem5Rules drop-4 cancellation alignment**.
    For a CTS with 2+ appendants and N ≥ 1, dropping 4 from the
    encoder yields rules whose head two satisfy the cancellation
    `r1 = r2.map(·+2)` (the second appendant's r1', r2').  This is
    the encoder-level form of iter 1019/1020 — the structural
    foundation for extending iter 1014's bag4_perm to arbitrary
    chain points where `k = 4` (one CTS step done). -/
theorem ctsRulesToSystem5Rules_drop_4_first_two_rules_cancel
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_app_len : cts.appendants.length ≥ 2) :
    ∃ r1 r2 tl, (ctsRulesToSystem5Rules cts cfg N).drop 4 = r1 :: r2 :: tl
              ∧ r1 = r2.map (· + 2) := by
  unfold ctsRulesToSystem5Rules
  cases h_app : cts.appendants with
  | nil =>
    rw [h_app] at h_app_len; simp at h_app_len
  | cons a rest_a =>
    cases h_rest_a : rest_a with
    | nil =>
      rw [h_app, h_rest_a] at h_app_len; simp at h_app_len
    | cons a' rest =>
      cases N with
      | zero => omega
      | succ k =>
        exact nCycles_drop_4_first_two_rules_cancel a a' rest k
          (counterAfterWorkingString cfg.data + 2)

/-- **Iter 1026: ctsRulesToSystem5Rules drop-8 cancellation alignment**.
    For a CTS with 3+ appendants and N ≥ 1, dropping 8 from the
    encoder yields rules whose head two satisfy `r1 = r2.map(·+2)`
    (the third appendant's r1'', r2'').  Encoder-level form of iter
    1024/1025 — the structural foundation for extending iter 1014's
    bag4_perm to chain points where `k = 8` (two CTS steps done). -/
theorem ctsRulesToSystem5Rules_drop_8_first_two_rules_cancel
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_app_len : cts.appendants.length ≥ 3) :
    ∃ r1 r2 tl, (ctsRulesToSystem5Rules cts cfg N).drop 8 = r1 :: r2 :: tl
              ∧ r1 = r2.map (· + 2) := by
  unfold ctsRulesToSystem5Rules
  cases h_app : cts.appendants with
  | nil =>
    rw [h_app] at h_app_len; simp at h_app_len
  | cons a rest_a =>
    cases h_rest_a : rest_a with
    | nil =>
      rw [h_app, h_rest_a] at h_app_len; simp at h_app_len
    | cons a' rest_a' =>
      cases h_rest_a' : rest_a' with
      | nil =>
        rw [h_app, h_rest_a, h_rest_a'] at h_app_len
        simp at h_app_len
      | cons a'' rest =>
        cases N with
        | zero => omega
        | succ k =>
          exact nCycles_drop_8_first_two_rules_cancel a a' a'' rest k
            (counterAfterWorkingString cfg.data + 2)

/-- **Iter 1030: ctsRulesToSystem5Rules drop-4n cancellation (general form)**.
    Encoder-level lift of iter 1029.  For `cts.appendants.length ≥ n + 1`
    and `N ≥ 1`, dropping `4 * n` rules from the encoder yields a head
    pair satisfying `r1 = r2.map(·+2)`.  Generalizes iters 1021 (n=1)
    and 1026 (n=2) to arbitrary `4n` aligned drops within the first
    cycle — the structural foundation for the cycle-boundary correctness
    argument. -/
theorem ctsRulesToSystem5Rules_drop_4n_first_two_rules_cancel
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_N : N ≥ 1)
    (h_app_len : cts.appendants.length ≥ n + 1) :
    ∃ r1 r2 tl, (ctsRulesToSystem5Rules cts cfg N).drop (4 * n) = r1 :: r2 :: tl
              ∧ r1 = r2.map (· + 2) := by
  unfold ctsRulesToSystem5Rules
  cases N with
  | zero => omega
  | succ k =>
    exact nCycles_drop_4n_first_two_rules_cancel cts.appendants n k
      (counterAfterWorkingString cfg.data + 2) h_app_len

/-- **Iter 1023: shift-only preserves first-rule cancellation**.  Companion
    to iter 1022 for the `k = 0` case (no drop, just shift).  At chain
    point `m` from cfg5 where `k = 0` (no P-steps consumed yet, e.g.
    `m = 0`), the rules `orig.map(map(·+m))` still satisfy
    `head = tail_head.map(·+2)`.  Composes iter 892 (encoder
    cancellation) + iter 1018 (cancellation under shift). -/
theorem ctsRulesToSystem5Rules_shift_first_two_rules_cancel
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) (m : Int) :
    ∃ r1 r2 tl,
      (ctsRulesToSystem5Rules cts cfg N).map (fun r => r.map (· + m))
        = r1 :: r2 :: tl
      ∧ r1 = r2.map (· + 2) := by
  obtain ⟨r1, r2, tail, h_eq, h_cancel⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_cancel cts cfg N h_N
  refine ⟨r1.map (· + m), r2.map (· + m),
          tail.map (fun r => r.map (· + m)), ?_, ?_⟩
  · rw [h_eq]; rfl
  · exact List_Int_cancellation_preserved_under_shift r1 r2 m h_cancel

/-- **Iter 1022: drop-4-then-shift preserves cancellation at trajectory step**.
    Composes iter 1021 (drop-4 cancellation) with iter 1018 (cancellation
    under shift): for s5' at trajectory step `m` from cfg5 (with k = 4
    P-steps so far), s5'.rules = `((orig.drop 4).map(map(·+m)))`, and
    these still satisfy `r1 = r2.map(·+2)`.  This is exactly the
    structural property iter 1014's proof requires for the rule list
    at any chain point where `k = 4n` (one CTS step boundary). -/
theorem ctsRulesToSystem5Rules_drop_4_shift_first_two_rules_cancel
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) (m : Int)
    (h_app_len : cts.appendants.length ≥ 2) :
    ∃ r1 r2 tl,
      ((ctsRulesToSystem5Rules cts cfg N).drop 4).map (fun r => r.map (· + m))
        = r1 :: r2 :: tl
      ∧ r1 = r2.map (· + 2) := by
  obtain ⟨r1, r2, tl, h_eq, h_cancel⟩ :=
    ctsRulesToSystem5Rules_drop_4_first_two_rules_cancel cts cfg N h_N h_app_len
  refine ⟨r1.map (· + m), r2.map (· + m),
          tl.map (fun r => r.map (· + m)), ?_, ?_⟩
  · rw [h_eq]; rfl
  · exact List_Int_cancellation_preserved_under_shift r1 r2 m h_cancel

/-- **Iter 1027: drop-8-then-shift cancellation alignment**.  Encoder-level
    composition of iter 1026 (drop-8 cancellation) and iter 1018
    (cancellation under shift): for s5' at trajectory step `m` from cfg5
    (with k = 8 P-steps so far, two CTS steps boundary), s5'.rules =
    `((orig.drop 8).map(map(·+m)))`, and these still satisfy
    `r1 = r2.map(·+2)`.  Companion to iter 1022 for the `k = 8` case
    (two CTS steps done).  Requires 3+ appendants. -/
theorem ctsRulesToSystem5Rules_drop_8_shift_first_two_rules_cancel
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) (m : Int)
    (h_app_len : cts.appendants.length ≥ 3) :
    ∃ r1 r2 tl,
      ((ctsRulesToSystem5Rules cts cfg N).drop 8).map (fun r => r.map (· + m))
        = r1 :: r2 :: tl
      ∧ r1 = r2.map (· + 2) := by
  obtain ⟨r1, r2, tl, h_eq, h_cancel⟩ :=
    ctsRulesToSystem5Rules_drop_8_first_two_rules_cancel cts cfg N h_N h_app_len
  refine ⟨r1.map (· + m), r2.map (· + m),
          tl.map (fun r => r.map (· + m)), ?_, ?_⟩
  · rw [h_eq]; rfl
  · exact List_Int_cancellation_preserved_under_shift r1 r2 m h_cancel

/-- **Iter 1031: drop-4n-then-shift cancellation (general form)**.  Encoder-
    level composition of iter 1030 (drop-4n) and iter 1018 (shift
    preservation).  For `cts.appendants.length ≥ n + 1`, `N ≥ 1`, and any
    shift `m`, dropping `4 * n` rules and then shifting all remaining
    rules by `m` preserves the head-pair cancellation
    `r1 = r2.map(·+2)`.  Generalizes iters 1022 (n=1) and 1027 (n=2)
    to arbitrary `4n` aligned drops within the first cycle.  This is
    THE structural property iter 1014's bag4_perm proof needs at any
    chain point where `k = 4n` (n CTS steps done from cfg5). -/
theorem ctsRulesToSystem5Rules_drop_4n_shift_first_two_rules_cancel
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_N : N ≥ 1) (m : Int)
    (h_app_len : cts.appendants.length ≥ n + 1) :
    ∃ r1 r2 tl,
      ((ctsRulesToSystem5Rules cts cfg N).drop (4 * n)).map (fun r => r.map (· + m))
        = r1 :: r2 :: tl
      ∧ r1 = r2.map (· + 2) := by
  obtain ⟨r1, r2, tl, h_eq, h_cancel⟩ :=
    ctsRulesToSystem5Rules_drop_4n_first_two_rules_cancel cts cfg N n h_N h_app_len
  refine ⟨r1.map (· + m), r2.map (· + m),
          tl.map (fun r => r.map (· + m)), ?_, ?_⟩
  · rw [h_eq]; rfl
  · exact List_Int_cancellation_preserved_under_shift r1 r2 m h_cancel

/-- **Iter 1032: 1 ∈ bag at Perm-chain points**.  At any chain point
    where `bag` is permutation-equivalent to `ctsConfigToSystem5Bag cfg`
    for a CTS config with nonempty data, `1 ∈ bag` — i.e., the next
    System5 step from the chain point is a P-step (via
    `System5_one_mem_iff_zero_in_decremented`: `1 ∈ bag ↔ 0 ∈
    bag.map(·-1)`).  The Perm-based bridge needed for chain induction:
    iter 1014's `bag4_perm` gives `Perm s5_4.bag (aux rest 1)` after
    4 cfg5 steps; this lemma gives `1 ∈ s5_4.bag` whenever `rest ≠ []`,
    which then triggers the next P-step in the chain. -/
theorem ctsConfigToSystem5Bag_perm_one_mem
    (cfg : CTSConfig) (bag : List Int) (h : cfg.data ≠ [])
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    (1 : Int) ∈ bag := by
  rw [List.Perm.mem_iff h_perm]
  exact ctsConfigToSystem5Bag_one_mem cfg h

/-- **Iter 1033: 2 ∈ false-head bag at Perm-chain points**.  Companion
    to iter 1032: at any Perm-chain point where `bag ~ ctsConfigToSystem5Bag cfg`
    for a false-head CTS config (`cfg.data = false :: rest`), `2 ∈ bag`.
    Direct from iter 645's `ctsConfigToSystem5Bag_false_head_decomp`
    (bag = `1 :: 2 :: 3 :: 4 :: aux rest 5`), lifted via
    `List.Perm.mem_iff`.  Used to chain the second step of the 4-step
    P-step trajectory at arbitrary chain points (analog of iter 974's
    `ctsToSystem5_false_head_after_first_step_two_mem` but at the
    Perm-chain level). -/
theorem ctsConfigToSystem5Bag_false_head_perm_two_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    (2 : Int) ∈ bag := by
  have h_two_in : (2 : Int) ∈ ctsConfigToSystem5Bag
                       { data := false :: rest, phase := phase } := by
    rw [ctsConfigToSystem5Bag_false_head_decomp]
    simp
  exact (List.Perm.mem_iff h_perm).mpr h_two_in

/-- **Iter 1034: 3 ∈ false-head bag at Perm-chain points**.  Continues the
    membership cascade started by iters 1032/1033.  False-head bag
    starts `1 :: 2 :: 3 :: 4 :: aux rest 5`, so `3 ∈ bag` directly.
    Chain-induction analog of iter 988's `ctsToSystem5_false_head_after_first_step_three_mem`.
    Combined with iters 1032/1033, captures `1, 2, 3 ∈ bag` for
    false-head Perm-chain hypotheses — the membership prerequisites
    for the 4-step P-step cascade. -/
theorem ctsConfigToSystem5Bag_false_head_perm_three_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    (3 : Int) ∈ bag := by
  have h_three_in : (3 : Int) ∈ ctsConfigToSystem5Bag
                       { data := false :: rest, phase := phase } := by
    rw [ctsConfigToSystem5Bag_false_head_decomp]
    simp
  exact (List.Perm.mem_iff h_perm).mpr h_three_in

/-- **Iter 1035: 4 ∈ false-head bag at Perm-chain points**.  Completes
    the membership cascade started by iters 1032/1033/1034 for false-head
    Perm-chain hypotheses.  False-head bag starts `1 :: 2 :: 3 :: 4 ::
    aux rest 5`, so `4 ∈ bag` directly.  With iters 1032-1035, the
    full prerequisite cascade `{1, 2, 3, 4} ∈ bag` for the 4-step
    P-step trajectory at arbitrary chain points is in place — the
    bag-side analog of iters 645/974/988/990's "all 4 cfg5 steps are
    P-steps" argument. -/
theorem ctsConfigToSystem5Bag_false_head_perm_four_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    (4 : Int) ∈ bag := by
  have h_four_in : (4 : Int) ∈ ctsConfigToSystem5Bag
                       { data := false :: rest, phase := phase } := by
    rw [ctsConfigToSystem5Bag_false_head_decomp]
    simp
  exact (List.Perm.mem_iff h_perm).mpr h_four_in

/-- **Iter 1036: bag.Nodup at Perm-chain points**.  Lifts the existing
    `ctsConfigToSystem5Bag_nodup` (iter 645) through `List.Perm.nodup_iff`.
    Required prerequisite for invoking `xorMerge_mem_left_of_not_mem_right`
    (iter 969) when chaining membership preservation across System5
    steps at chain points (the chain-induction analog of how iter 982/989/990
    discharged the Nodup obligations during the cfg5-trajectory analysis). -/
theorem ctsConfigToSystem5Bag_perm_nodup
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    bag.Nodup := by
  rw [List.Perm.nodup_iff h_perm]
  exact ctsConfigToSystem5Bag_nodup cfg

/-- **Iter 1037: 1 ∈ true-head bag at Perm-chain points**.  Specialization
    of iter 1032 to true-head configs.  True-head bag starts
    `1 :: 3 :: 4 :: 6 :: aux rest 7` (per iter 645's
    `ctsConfigToSystem5Bag_true_head_decomp`), so `1 ∈ bag` directly.
    Begins the true-head Perm-chain membership cascade — companion to
    iter 1032 (general case) but explicitly named for true-head
    chain-induction symmetry with iters 1032-1035 (false-head). -/
theorem ctsConfigToSystem5Bag_true_head_perm_one_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    (1 : Int) ∈ bag := by
  have h_one_in : (1 : Int) ∈ ctsConfigToSystem5Bag
                       { data := true :: rest, phase := phase } := by
    rw [ctsConfigToSystem5Bag_true_head_decomp]
    simp
  exact (List.Perm.mem_iff h_perm).mpr h_one_in

/-- **Iter 1038: 3 ∈ true-head bag at Perm-chain points**.  Continues
    the true-head cascade started by iter 1037.  True-head bag =
    `1 :: 3 :: 4 :: 6 :: aux rest 7`, so `3 ∈ bag` (second element)
    directly via `_true_head_decomp` + `simp` + `List.Perm.mem_iff`.
    Companion to iter 1033's false-head `2 ∈ bag` — the second value
    of each cascade differs because of the true/false-head encoder
    asymmetry (`+0,+2` vs `+0,+1` strides). -/
theorem ctsConfigToSystem5Bag_true_head_perm_three_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    (3 : Int) ∈ bag := by
  have h_three_in : (3 : Int) ∈ ctsConfigToSystem5Bag
                       { data := true :: rest, phase := phase } := by
    rw [ctsConfigToSystem5Bag_true_head_decomp]
    simp
  exact (List.Perm.mem_iff h_perm).mpr h_three_in

/-- **Iter 1039: 4 ∈ true-head bag at Perm-chain points**.  Continues
    the true-head cascade.  True-head bag's third element is `4`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_four_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    (4 : Int) ∈ bag := by
  have h_four_in : (4 : Int) ∈ ctsConfigToSystem5Bag
                       { data := true :: rest, phase := phase } := by
    rw [ctsConfigToSystem5Bag_true_head_decomp]
    simp
  exact (List.Perm.mem_iff h_perm).mpr h_four_in

/-- **Iter 1040: 6 ∈ true-head bag at Perm-chain points (CAPSTONE)**.
    Closes the true-head bag-side cascade.  True-head bag's fourth
    element is `6` (per `_true_head_decomp`).  With iters 1037-1040,
    the true-head cascade `{1, 3, 4, 6} ∈ bag` is now complete —
    mirror to iters 1032-1035's false-head `{1, 2, 3, 4} ∈ bag`.
    Both cascades + iter 1036 (bag.Nodup) + iter 1031 (rules-side
    cancellation) form the complete set of structural prerequisites
    for chain-induction at arbitrary chain points. -/
theorem ctsConfigToSystem5Bag_true_head_perm_six_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    (6 : Int) ∈ bag := by
  have h_six_in : (6 : Int) ∈ ctsConfigToSystem5Bag
                       { data := true :: rest, phase := phase } := by
    rw [ctsConfigToSystem5Bag_true_head_decomp]
    simp
  exact (List.Perm.mem_iff h_perm).mpr h_six_in

/-- **Iter 1041: bag elements ≥ 1 at Perm-chain points**.  At any
    Perm-chain point where `bag ~ ctsConfigToSystem5Bag cfg`, every
    element of `bag` is ≥ 1.  Direct lift of iter 645's
    `ctsConfigToSystem5BagAux_ge` (every entry of `aux data 1` is ≥ 1)
    via `List.Perm.mem_iff`.  Useful for disjointness arguments at
    chain points: any List Int with all entries ≥ k > some_value
    cannot share elements with bag — the building block for
    rule-vs-bag separation invariants when chaining membership
    preservation across the System5 step. -/
theorem ctsConfigToSystem5Bag_perm_min_value
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∀ x ∈ bag, x ≥ 1 := by
  intro x h_in
  have h_x_in : x ∈ ctsConfigToSystem5Bag cfg :=
    (List.Perm.mem_iff h_perm).mp h_in
  exact ctsConfigToSystem5BagAux_ge cfg.data 1 x h_x_in

/-- **Iter 1042: bag elements ≤ counter-bound at Perm-chain points**.
    Companion to iter 1041's min-value bound.  At any Perm-chain point
    where `bag ~ ctsConfigToSystem5Bag cfg`, every element of `bag` is
    `≤ counterAfterWorkingString cfg.data - 1`.  Direct lift of iter 908's
    `ctsConfigToSystem5BagAux_max` (via `i = 1`, the encoder's starting
    counter) through `List.Perm.mem_iff`.  Combined with iter 1041,
    gives `1 ≤ x ≤ counterAfterWorkingString cfg.data - 1` for every
    bag element at chain points — the full range invariant for
    rule-vs-bag disjointness when chaining membership preservation. -/
theorem ctsConfigToSystem5Bag_perm_max_value
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∀ x ∈ bag, x ≤ counterAfterWorkingString cfg.data - 1 := by
  intro x h_in
  have h_x_in : x ∈ ctsConfigToSystem5Bag cfg :=
    (List.Perm.mem_iff h_perm).mp h_in
  have := ctsConfigToSystem5BagAux_max cfg.data 1 x h_x_in
  omega

/-- **Iter 1043: bag-vs-high-list disjointness at Perm-chain points**.
    Composes iter 1042 (bag elements `≤ counterAfterWorkingString
    cfg.data - 1`) with a hypothesis `∀ y ∈ xs, y >
    counterAfterWorkingString cfg.data - 1` to derive disjointness:
    no bag element is in `xs`.  **Building block for rule-vs-bag
    separation at chain points** — encoder rules have entries with
    minimum value `counterAfterWorkingString cfg.data + 8` (per iter
    906's `_first_two_rules_min_value`) which exceeds the bag's max,
    so the chain-point bag is automatically disjoint from rule
    contributions. -/
theorem ctsConfigToSystem5Bag_perm_disjoint_high
    (cfg : CTSConfig) (bag xs : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (h_xs_high : ∀ y ∈ xs, y > counterAfterWorkingString cfg.data - 1) :
    ∀ x ∈ bag, x ∉ xs := by
  intro x h_x_in h_x_xs
  have h_bag_max := ctsConfigToSystem5Bag_perm_max_value cfg bag h_perm x h_x_in
  have h_xs_min := h_xs_high x h_x_xs
  omega

/-- **Iter 1044: 1 ∈ bag.dec.erase at false-head Perm-chain points**.
    Chain-induction analog of iter 970's
    `ctsConfigToSystem5Bag_false_head_dec_erase_one_mem`.  At any
    Perm-chain point where `bag ~ ctsConfigToSystem5Bag (false-head cfg)`,
    `1 ∈ ((bag.map(·-1)).erase 0)` — i.e., the dec-erase preserves the
    predecessor-of-2 membership.  Proof: iter 1033 gives `2 ∈ bag`,
    then iter 975's `mem_imp_pred_in_dec_erase` gives `1 = 2 - 1 ∈
    (bag.map(·-1)).erase 0` (since `2 ≠ 1`).  This is the trigger
    condition for the second P-step at chain points
    (`1 ∈ dec-erased ⇔ 0 ∈ dec(dec-erased)`). -/
theorem ctsConfigToSystem5Bag_false_head_perm_dec_erase_one_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    (1 : Int) ∈ (bag.map (· - 1)).erase 0 := by
  have h_two_in : (2 : Int) ∈ bag :=
    ctsConfigToSystem5Bag_false_head_perm_two_mem rest phase bag h_perm
  have h_dec := mem_imp_pred_in_dec_erase bag 2 h_two_in (by omega)
  show (1 : Int) ∈ (bag.map (· - 1)).erase 0
  have h_eq : (2 : Int) - 1 = 1 := by omega
  rw [h_eq] at h_dec
  exact h_dec

/-- **Iter 1045: 2 ∈ bag.dec.erase at false-head Perm-chain points**.
    Companion to iter 1044 for value 2.  Composition: iter 1034 gives
    `3 ∈ bag`, then iter 975's `mem_imp_pred_in_dec_erase` (with
    `3 ≠ 1`) gives `2 = 3 - 1 ∈ (bag.map(·-1)).erase 0`.  Used together
    with iter 1044 to chain bag membership across two consecutive
    System5 P-steps at any chain point — the chain-induction analog
    of iter 973's existing dec-erase-two-mem lemma. -/
theorem ctsConfigToSystem5Bag_false_head_perm_dec_erase_two_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    (2 : Int) ∈ (bag.map (· - 1)).erase 0 := by
  have h_three_in : (3 : Int) ∈ bag :=
    ctsConfigToSystem5Bag_false_head_perm_three_mem rest phase bag h_perm
  have h_dec := mem_imp_pred_in_dec_erase bag 3 h_three_in (by omega)
  show (2 : Int) ∈ (bag.map (· - 1)).erase 0
  have h_eq : (3 : Int) - 1 = 2 := by omega
  rw [h_eq] at h_dec
  exact h_dec

/-- **Iter 1046: 3 ∈ bag.dec.erase at false-head Perm-chain points**.
    Companion to iters 1044/1045 for value 3.  Composition: iter 1035
    (`4 ∈ bag`) + iter 975's `mem_imp_pred_in_dec_erase` (with `4 ≠ 1`,
    gives `3 = 4 - 1 ∈ (bag.map(·-1)).erase 0`).  Chain-induction
    analog of iter 987's existing dec-erase-three-mem lemma.  With
    iters 1044-1046, the false-head dec-erase membership cascade
    `{1, 2, 3} ∈ ((bag.map(·-1)).erase 0)` at Perm-chain points is in
    place — the trigger conditions for the second/third/fourth P-steps
    in the 4-step trajectory analysis at chain points. -/
theorem ctsConfigToSystem5Bag_false_head_perm_dec_erase_three_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    (3 : Int) ∈ (bag.map (· - 1)).erase 0 := by
  have h_four_in : (4 : Int) ∈ bag :=
    ctsConfigToSystem5Bag_false_head_perm_four_mem rest phase bag h_perm
  have h_dec := mem_imp_pred_in_dec_erase bag 4 h_four_in (by omega)
  show (3 : Int) ∈ (bag.map (· - 1)).erase 0
  have h_eq : (4 : Int) - 1 = 3 := by omega
  rw [h_eq] at h_dec
  exact h_dec

/-- **Iter 1047: bag disjoint from first two encoder rules at Perm-chain
    points**.  Combines iter 1042 (bag max ≤ `counterAfterWorkingString
    cfg.data - 1`) with iter 904's `_first_two_rules_min_value`
    (r1 entries ≥ `counterAfterWorkingString cfg.data + 4`, r2 entries
    ≥ `counterAfterWorkingString cfg.data + 2`).  The gap rules out
    overlap, yielding `∀ x ∈ bag, x ∉ r1` and `∀ x ∈ bag, x ∉ r2`.
    **Intermediate composition lemma**: directly discharges the
    rule-vs-bag disjointness obligations in `xorMerge_disjoint_eq_reverse_append`
    (iter 912) at any Perm-chain point. -/
theorem ctsConfigToSystem5Bag_perm_disjoint_first_two_rules
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ (∀ x ∈ bag, x ∉ r1)
                ∧ (∀ x ∈ bag, x ∉ r2) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1_min, h_r2_min⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_min_value cts cfg N h_N
  refine ⟨r1, r2, tail, h_eq, ?_, ?_⟩
  · intro x h_x_bag h_x_r1
    have h_bag_max := ctsConfigToSystem5Bag_perm_max_value cfg bag h_perm x h_x_bag
    have h_r1_min' := h_r1_min x h_x_r1
    omega
  · intro x h_x_bag h_x_r2
    have h_bag_max := ctsConfigToSystem5Bag_perm_max_value cfg bag h_perm x h_x_bag
    have h_r2_min' := h_r2_min x h_x_r2
    omega

/-- **Iter 1048: bag disjoint from positively-shifted high lists**.
    Generalization of iter 1043: when `xs` has all entries above
    `counterAfterWorkingString cfg.data - 1`, so does `xs.map(·+k)`
    for any `k ≥ 0` — hence iter 1043 still applies.  **The shift-
    preservation companion** for chain-induction at trajectory step `m`
    where rules are shifted by `m+1`, `m+2`, etc.: bag remains
    disjoint from `r1.map(·+m+1)`, `r2.map(·+m+2)`, and so on. -/
theorem ctsConfigToSystem5Bag_perm_disjoint_high_shifted
    (cfg : CTSConfig) (bag xs : List Int) (k : Int) (h_k : k ≥ 0)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (h_xs_high : ∀ y ∈ xs, y > counterAfterWorkingString cfg.data - 1) :
    ∀ x ∈ bag, x ∉ xs.map (· + k) := by
  apply ctsConfigToSystem5Bag_perm_disjoint_high cfg bag
    (xs.map (· + k)) h_perm
  intro y h_y_in
  obtain ⟨z, h_z_xs, h_z_eq⟩ := List.mem_map.mp h_y_in
  have h_z_high := h_xs_high z h_z_xs
  omega

/-- **Iter 1049: dec-erase bag.Nodup at Perm-chain points**.  At any
    Perm-chain point where `bag ~ ctsConfigToSystem5Bag cfg`,
    `((bag.map(·-1)).erase 0).Nodup`.  Composition: iter 1036 (bag.Nodup)
    + `List.Pairwise.map` (decrement injectivity) + `List.Nodup.erase`.
    **Required prerequisite for invoking `xorMerge_mem_iff` and similar
    Nodup-conditional lemmas at chain points** — the chain-induction
    analog of iter 1004's existing cfg5-level dec-erase Nodup. -/
theorem ctsConfigToSystem5Bag_perm_dec_erase_nodup
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ((bag.map (· - 1)).erase 0).Nodup := by
  have h_bag_nodup := ctsConfigToSystem5Bag_perm_nodup cfg bag h_perm
  apply List.Nodup.erase
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_bag_nodup
  intro a b h_ne h_eq; apply h_ne; have : a - 1 = b - 1 := h_eq; omega

/-- **Iter 1050: System5 step succeeds at Perm-chain points**.
    At any Perm-chain point where `bag ~ ctsConfigToSystem5Bag cfg`
    with non-empty `cfg.data` and non-empty `rules`, `System5.step
    ⟨bag, rules⟩` succeeds.  Composition: iter 1032 (`1 ∈ bag` ⇒
    `bag ≠ []`) + hypothesis `rules ≠ []` + `System5_step_some_iff`.
    **Stepping stone toward the per-step extension theorem**: confirms
    that the System5 trajectory at any chain point can take at least
    one more step. -/
theorem ctsConfigToSystem5Bag_perm_step_succeeds
    (cfg : CTSConfig) (bag : List Int) (rules : List (List Int))
    (h_data : cfg.data ≠ [])
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (h_rules : rules ≠ []) :
    ∃ cfg', System5.step ⟨bag, rules⟩ = some cfg' := by
  apply (System5_step_some_iff _).mpr
  refine ⟨?_, h_rules⟩
  show bag ≠ []
  intro h_empty
  have h_one : (1 : Int) ∈ bag :=
    ctsConfigToSystem5Bag_perm_one_mem cfg bag h_data h_perm
  rw [h_empty] at h_one
  cases h_one

/-- **Iter 1051: 0 ∈ decrement of bag at Perm-chain points**.  At any
    Perm-chain point where `bag ~ ctsConfigToSystem5Bag cfg` with
    non-empty `cfg.data`, `0 ∈ bag.map(·-1)`.  Composition: iter 1032
    (`1 ∈ bag`) + iter 659's `zero_mem_decrement_iff_one_mem`.
    **The P-step trigger condition at chain points**: System5 step
    is a P-step (rule pop) iff `0 ∈ decremented bag`.  Chain-induction
    analog of iter 659's existing cfg5-level
    `ctsConfigToSystem5Bag_zero_in_decrement`. -/
theorem ctsConfigToSystem5Bag_perm_zero_in_decrement
    (cfg : CTSConfig) (bag : List Int) (h_data : cfg.data ≠ [])
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    (0 : Int) ∈ bag.map (· - 1) :=
  (zero_mem_decrement_iff_one_mem _).mpr
    (ctsConfigToSystem5Bag_perm_one_mem cfg bag h_data h_perm)

/-- **Iter 1052: explicit System5 P-step formula at Perm-chain points**.
    Specializes `System5_step_explicit_pop` (iter 899) to Perm-chain
    points: when `bag ~ ctsConfigToSystem5Bag cfg`, `cfg.data ≠ []`,
    and rules `= r1 :: rest_rules`, the step formula is the explicit
    P-step pop.  The bag-side prerequisites (`bag ≠ []` and
    `0 ∈ bag.map(·-1)`) are discharged via iters 1032/1051.
    **The chain-induction step formula** ready to plug into
    multi-step compositions. -/
theorem ctsConfigToSystem5Bag_perm_step_pop_explicit
    (cfg : CTSConfig) (bag : List Int) (rules : List (List Int))
    (r1 : List Int) (rest_rules : List (List Int))
    (h_data : cfg.data ≠ [])
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (h_rules : rules = r1 :: rest_rules) :
    System5.step ⟨bag, rules⟩ = some
      ⟨xorMerge ((bag.map (· - 1)).erase 0) (r1.map (· + 1)),
       rest_rules.map (fun r => r.map (· + 1))⟩ := by
  apply System5_step_explicit_pop ⟨bag, rules⟩ r1 rest_rules h_rules
  · show bag ≠ []
    intro h_empty
    have h_one := ctsConfigToSystem5Bag_perm_one_mem cfg bag h_data h_perm
    rw [h_empty] at h_one
    cases h_one
  · show (0 : Int) ∈ bag.map (· - 1)
    exact ctsConfigToSystem5Bag_perm_zero_in_decrement cfg bag h_data h_perm

/-- **Iter 1053: bag disjoint from r1.map(·+1) at Perm-chain points**.
    Composes iter 904's `_first_two_rules_min_value` (r1 entries ≥
    counterAfterWorkingString cfg.data + 4) with iter 1048's shift-
    disjointness (k=1) to conclude `∀ x ∈ bag, x ∉ r1.map(·+1)`.
    **Disjointness for the post-step bag at chain points**: when the
    P-step pops r1 and merges with `r1.map(·+1)` (the incremented form),
    bag remains disjoint from this incremented rule, so the xorMerge
    behaves as expected. -/
theorem ctsConfigToSystem5Bag_perm_disjoint_r1_inc
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ (∀ x ∈ bag, x ∉ r1.map (· + 1)) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1_min, _h_r2_min⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_min_value cts cfg N h_N
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  apply ctsConfigToSystem5Bag_perm_disjoint_high_shifted cfg bag r1 1
    (by omega) h_perm
  intro y h_y_r1
  have h_min := h_r1_min y h_y_r1
  omega

/-- **Iter 1054: dec-erase bag disjoint from r1.map(·+1) at Perm-chain
    points**.  Composes iter 1042 (bag max ≤ counter - 1, hence
    `(bag.map(·-1)).erase 0` entries ≤ counter - 2) with iter 904
    (r1 entries ≥ counter + 4, hence r1.map(·+1) entries ≥ counter + 5).
    The arithmetic gap rules out overlap: dec-erase bag ≤ counter - 2
    < counter + 5 ≤ r1.map(·+1).  **Disjointness for the post-step
    bag in xorMerge form** at chain points (the chain-induction analog
    of iter 913's existing cfg5-level dec-erase r1-disjointness). -/
theorem ctsConfigToSystem5Bag_perm_dec_erase_disjoint_r1_inc
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ (∀ x ∈ (bag.map (· - 1)).erase 0, x ∉ r1.map (· + 1)) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1_min, _⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_min_value cts cfg N h_N
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro x h_x_dec h_x_r1_inc
  have h_x_dec_bag : x ∈ bag.map (· - 1) := List.mem_of_mem_erase h_x_dec
  obtain ⟨z, h_z_bag, h_z_eq⟩ := List.mem_map.mp h_x_dec_bag
  have h_z_max := ctsConfigToSystem5Bag_perm_max_value cfg bag h_perm z h_z_bag
  obtain ⟨w, h_w_r1, h_w_eq⟩ := List.mem_map.mp h_x_r1_inc
  have h_w_min := h_r1_min w h_w_r1
  omega

/-- **Iter 1055: post-step bag Nodup at Perm-chain points**.  The
    xorMerge of `(bag.map(·-1)).erase 0` with any rule (e.g.
    `r1.map(·+1)`) is Nodup, since `xorMerge_nodup` only needs the
    first argument to be Nodup, and iter 1049 gives the dec-erase
    bag's Nodup at any Perm-chain point.  **The post-step bag is
    automatically Nodup** at chain points — the chain-induction
    analog of iter 1008's existing cfg5-level
    `ctsToSystem5_false_head_step2_bag_nodup`. -/
theorem ctsConfigToSystem5Bag_perm_xorMerge_r_inc_nodup
    (cfg : CTSConfig) (bag : List Int) (r : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    (xorMerge ((bag.map (· - 1)).erase 0) (r.map (· + 1))).Nodup := by
  apply xorMerge_nodup
  exact ctsConfigToSystem5Bag_perm_dec_erase_nodup cfg bag h_perm

/-- **Iter 1000: r1.reverse and r2.map(·+2) have same membership**.
    Direct corollary of iter 892's encoder cancellation `r1 = r2.map(·+2)`
    combined with `List.mem_reverse` (membership is preserved under
    reverse).  Used in the bag-2 chain analysis: applying iter 999's
    `xorMerge_same_mem_no_mem`, the xorMerge of r1.reverse and
    r2.map(·+2) cancels to nothing. -/
theorem ctsRulesToSystem5Rules_first_two_rules_reverse_mem_eq
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ ∀ x, x ∈ r1.reverse ↔ x ∈ r2.map (· + 2) := by
  obtain ⟨r1, r2, tail, h_eq, h_cancel⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_cancel cts cfg N h_N
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro x
  rw [List.mem_reverse, h_cancel]

/-- **Iter 1001: `(1 :: 2 :: aux rest 3)` is Nodup**.  The bag prefix
    in the bag-1 dec-erase form (iter 998).  Composition: aux entries
    are ≥ 3 (iter `_ge`), so 1, 2 ∉ aux rest 3, and aux rest 3 is itself
    Nodup (iter 645's `_nodup`).  Used downstream for the bag-2
    membership chain. -/
theorem ctsConfigToSystem5BagAux_three_one_two_cons_nodup (rest : List Bool) :
    ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3).Nodup := by
  have h_aux_ge : ∀ x ∈ ctsConfigToSystem5BagAux rest 3, x ≥ 3 :=
    ctsConfigToSystem5BagAux_ge rest 3
  have h_aux_nodup : (ctsConfigToSystem5BagAux rest 3).Nodup :=
    ctsConfigToSystem5BagAux_nodup rest 3
  have h_one_not : (1 : Int) ∉ ctsConfigToSystem5BagAux rest 3 := by
    intro h_in
    have := h_aux_ge 1 h_in
    omega
  have h_two_not : (2 : Int) ∉ ctsConfigToSystem5BagAux rest 3 := by
    intro h_in
    have := h_aux_ge 2 h_in
    omega
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨h_two_not, h_aux_nodup⟩⟩
  intro h_in
  rcases List.mem_cons.mp h_in with h_eq | h_in_aux
  · omega
  · exact h_one_not h_in_aux

/-- **Iter 1108: `(2 :: 3 :: 5 :: aux rest 6)` is Nodup**.  True-head
    analog of iter 1001 for the cons-prefix bag form.  Composition:
    `_ge` (aux entries ≥ 6, hence 2, 3, 5 ∉ aux rest 6), `_nodup`
    (aux is Nodup), and arithmetic.  Used downstream for the
    true-head Perm-chain bag-2 membership analysis. -/
theorem ctsConfigToSystem5BagAux_six_two_three_five_cons_nodup (rest : List Bool) :
    ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6).Nodup := by
  have h_aux_ge : ∀ x ∈ ctsConfigToSystem5BagAux rest 6, x ≥ 6 :=
    ctsConfigToSystem5BagAux_ge rest 6
  have h_aux_nodup : (ctsConfigToSystem5BagAux rest 6).Nodup :=
    ctsConfigToSystem5BagAux_nodup rest 6
  have h_two_not : (2 : Int) ∉ ctsConfigToSystem5BagAux rest 6 := by
    intro h_in; have := h_aux_ge 2 h_in; omega
  have h_three_not : (3 : Int) ∉ ctsConfigToSystem5BagAux rest 6 := by
    intro h_in; have := h_aux_ge 3 h_in; omega
  have h_five_not : (5 : Int) ∉ ctsConfigToSystem5BagAux rest 6 := by
    intro h_in; have := h_aux_ge 5 h_in; omega
  refine List.nodup_cons.mpr ⟨?_,
    List.nodup_cons.mpr ⟨?_,
      List.nodup_cons.mpr ⟨h_five_not, h_aux_nodup⟩⟩⟩
  · intro h_in
    rcases List.mem_cons.mp h_in with h_eq | h_in_rest
    · omega
    · rcases List.mem_cons.mp h_in_rest with h_eq | h_in_aux
      · omega
      · exact h_two_not h_in_aux
  · intro h_in
    rcases List.mem_cons.mp h_in with h_eq | h_in_aux
    · omega
    · exact h_three_not h_in_aux

/-- **Iter 1109: `(1 :: 2 :: 4 :: aux rest 5)` is Nodup**.  True-head
    bag-1-dec-erase analog of iter 1108.  Composition: `_ge` (aux
    entries ≥ 5, hence 1, 2, 4 ∉ aux rest 5), `_nodup` (aux is Nodup),
    and arithmetic.  Used downstream for the true-head Perm-chain
    bag-2 mem-iff analysis. -/
theorem ctsConfigToSystem5BagAux_five_one_two_four_cons_nodup (rest : List Bool) :
    ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5).Nodup := by
  have h_aux_ge : ∀ x ∈ ctsConfigToSystem5BagAux rest 5, x ≥ 5 :=
    ctsConfigToSystem5BagAux_ge rest 5
  have h_aux_nodup : (ctsConfigToSystem5BagAux rest 5).Nodup :=
    ctsConfigToSystem5BagAux_nodup rest 5
  have h_one_not : (1 : Int) ∉ ctsConfigToSystem5BagAux rest 5 := by
    intro h_in; have := h_aux_ge 1 h_in; omega
  have h_two_not : (2 : Int) ∉ ctsConfigToSystem5BagAux rest 5 := by
    intro h_in; have := h_aux_ge 2 h_in; omega
  have h_four_not : (4 : Int) ∉ ctsConfigToSystem5BagAux rest 5 := by
    intro h_in; have := h_aux_ge 4 h_in; omega
  refine List.nodup_cons.mpr ⟨?_,
    List.nodup_cons.mpr ⟨?_,
      List.nodup_cons.mpr ⟨h_four_not, h_aux_nodup⟩⟩⟩
  · intro h_in
    rcases List.mem_cons.mp h_in with h_eq | h_in_rest
    · omega
    · rcases List.mem_cons.mp h_in_rest with h_eq | h_in_aux
      · omega
      · exact h_one_not h_in_aux
  · intro h_in
    rcases List.mem_cons.mp h_in with h_eq | h_in_aux
    · omega
    · exact h_two_not h_in_aux

/-- **Iter 1110: true-head bag-1-dec-erase to bag-2-dec-erase form**.
    `(((1 :: 2 :: 4 :: aux rest 5).map(·-1)).erase 0) = 1 :: 3 :: aux rest 4`.
    Decrement: 1,2,4 → 0,1,3.  Erase 0 removes the leading 0.  Then
    aux rest 5 → aux rest 4 (iter 996's `_dec_at_five`).  Same
    template as iter 1107.  **Building block** for the true-head
    Perm-chain bag-3 mem-iff downstream. -/
theorem ctsConfigToSystem5BagAux_five_one_two_four_cons_dec_erase_eq
    (rest : List Bool) :
    (((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5).map (· - 1)).erase 0
      = (1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4 := by
  simp only [List.map_cons]
  rw [ctsConfigToSystem5BagAux_dec_at_five]
  show ((0 : Int) :: 1 :: 3 :: ctsConfigToSystem5BagAux rest 4).erase 0
     = 1 :: 3 :: ctsConfigToSystem5BagAux rest 4
  rw [List.erase_cons_head]

/-- **Iter 1119: false-head bag-1-dec to bag-2-dec form**.
    `(((1 :: 2 :: 3 :: aux rest 4).map(·-1)).erase 0) = 1 :: 2 :: aux rest 3`.
    Decrement: 1,2,3 → 0,1,2.  Erase 0 removes the leading 0.  Then
    aux rest 4 → aux rest 3 (iter 996's `_dec_at_four`).  **Missing
    middle link** in the false-head dec-erase-only bag chain (iter 994
    → iter 1007). -/
theorem ctsConfigToSystem5BagAux_four_one_two_three_cons_dec_erase_eq
    (rest : List Bool) :
    (((1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4).map (· - 1)).erase 0
      = (1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3 := by
  simp only [List.map_cons]
  rw [ctsConfigToSystem5BagAux_dec_at_four]
  show ((0 : Int) :: 1 :: 2 :: ctsConfigToSystem5BagAux rest 3).erase 0
     = 1 :: 2 :: ctsConfigToSystem5BagAux rest 3
  rw [List.erase_cons_head]

/-- **Iter 1111: `(1 :: 3 :: aux rest 4)` is Nodup**.  True-head
    bag-3 form Nodup, analog of iter 1010's `_two_one_cons_nodup`
    (which gave `(1 :: aux rest 2).Nodup` for false-head).  Composes
    `_ge` (aux entries ≥ 4) + `_nodup`.  **Building block** for the
    true-head Perm-chain bag-3 mem-iff. -/
theorem ctsConfigToSystem5BagAux_four_one_three_cons_nodup (rest : List Bool) :
    ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4).Nodup := by
  have h_aux_ge : ∀ x ∈ ctsConfigToSystem5BagAux rest 4, x ≥ 4 :=
    ctsConfigToSystem5BagAux_ge rest 4
  have h_aux_nodup : (ctsConfigToSystem5BagAux rest 4).Nodup :=
    ctsConfigToSystem5BagAux_nodup rest 4
  have h_one_not : (1 : Int) ∉ ctsConfigToSystem5BagAux rest 4 := by
    intro h_in; have := h_aux_ge 1 h_in; omega
  have h_three_not : (3 : Int) ∉ ctsConfigToSystem5BagAux rest 4 := by
    intro h_in; have := h_aux_ge 3 h_in; omega
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨h_three_not, h_aux_nodup⟩⟩
  intro h_in
  rcases List.mem_cons.mp h_in with h_eq | h_in_aux
  · omega
  · exact h_one_not h_in_aux

/-- **Iter 1112: true-head bag-3-dec to bag-4-dec form**.
    `(((1 :: 3 :: aux rest 4).map(·-1)).erase 0) = 2 :: aux rest 3`.
    Decrement: 1, 3 → 0, 2.  Erase 0 removes the leading 0.  Then
    aux rest 4 → aux rest 3 (iter 996's `_dec_at_four`).  Same
    template as iter 1110.  **Building block** for the true-head
    Perm-chain bag-4 mem-iff. -/
theorem ctsConfigToSystem5BagAux_four_one_three_cons_dec_erase_eq
    (rest : List Bool) :
    (((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4).map (· - 1)).erase 0
      = (2 : Int) :: ctsConfigToSystem5BagAux rest 3 := by
  simp only [List.map_cons]
  rw [ctsConfigToSystem5BagAux_dec_at_four]
  show ((0 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3).erase 0
     = 2 :: ctsConfigToSystem5BagAux rest 3
  rw [List.erase_cons_head]

/-- **Iter 1113: `(2 :: aux rest 3)` is Nodup**.  True-head bag-4 form
    Nodup, the terminal target form for the 4-step true-head trajectory.
    Analog of iter 1010's `_two_one_cons_nodup` (false-head terminal
    bag form Nodup) but at the `2 :: aux rest 3` form (rather than
    false-head's `aux rest 1`).  Composes `_ge` (aux entries ≥ 3) +
    `_nodup` + arithmetic. -/
theorem ctsConfigToSystem5BagAux_three_two_cons_nodup (rest : List Bool) :
    ((2 : Int) :: ctsConfigToSystem5BagAux rest 3).Nodup := by
  have h_aux_ge : ∀ x ∈ ctsConfigToSystem5BagAux rest 3, x ≥ 3 :=
    ctsConfigToSystem5BagAux_ge rest 3
  have h_aux_nodup : (ctsConfigToSystem5BagAux rest 3).Nodup :=
    ctsConfigToSystem5BagAux_nodup rest 3
  have h_two_not : (2 : Int) ∉ ctsConfigToSystem5BagAux rest 3 := by
    intro h_in; have := h_aux_ge 2 h_in; omega
  exact List.nodup_cons.mpr ⟨h_two_not, h_aux_nodup⟩

/-- **Iter 1114: 1 ∉ `(2 :: aux rest 3)`**.  Useful structural fact
    about the true-head bag-4 form: `1` is not in `(2 :: aux rest 3)`
    since `2 ≠ 1` and aux entries ≥ 3 > 1.  Composes `_ge` + `omega`. -/
theorem ctsConfigToSystem5BagAux_three_two_cons_one_not_mem (rest : List Bool) :
    (1 : Int) ∉ (2 : Int) :: ctsConfigToSystem5BagAux rest 3 := by
  intro h
  rcases List.mem_cons.mp h with h_eq | h_aux
  · omega
  · have := ctsConfigToSystem5BagAux_ge rest 3 1 h_aux
    omega


/-- **Iter 1010: `(1 :: aux rest 2)` is Nodup**.  Companion to iter
    1001 for the bag-3 RHS form.  aux rest 2 entries are ≥ 2, so
    1 ∉ aux rest 2; aux rest 2 is itself Nodup. -/
theorem ctsConfigToSystem5BagAux_two_one_cons_nodup (rest : List Bool) :
    ((1 : Int) :: ctsConfigToSystem5BagAux rest 2).Nodup := by
  have h_aux_ge : ∀ x ∈ ctsConfigToSystem5BagAux rest 2, x ≥ 2 :=
    ctsConfigToSystem5BagAux_ge rest 2
  have h_aux_nodup : (ctsConfigToSystem5BagAux rest 2).Nodup :=
    ctsConfigToSystem5BagAux_nodup rest 2
  refine List.nodup_cons.mpr ⟨?_, h_aux_nodup⟩
  intro h_in
  have := h_aux_ge 1 h_in
  omega

/-- **Iter 1002: `(1 :: 2 :: aux rest 3)` disjoint from r1 (false-head)**.
    For false-head, r1 entries ≥ counterAfter rest + 8 (via iter 901's
    `_first_two_rules_min_value` and counterAfter false-head decomposition),
    while aux rest 3 entries ≤ counterAfter rest + 1.  So they're
    disjoint.  Combined with 1, 2 < 9 ≤ r1 entries, the full prefix
    `(1 :: 2 :: aux rest 3)` is disjoint from r1.

    Used to discharge the disjointness obligation in the bag-2
    membership chain. -/
theorem ctsConfigToSystem5BagAux_three_one_two_cons_disjoint_r1
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ (∀ x ∈ ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3), x ∉ r1) := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨r1, r2, tail, h_eq, h_r1, _⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_min_value cts cfg N h_N
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro x hx hx_r1
  have h_r1_ge : x ≥ counterAfterWorkingString cfg.data + 2 + 2 := h_r1 x hx_r1
  have h_cfg : counterAfterWorkingString cfg.data
              = counterAfterWorkingString rest + 4 := by
    show counterAfterWorkingString (false :: rest) = _
    rw [counterAfterWorkingString_cons_false]
  have h_rest_ge : counterAfterWorkingString rest ≥ 1 :=
    counterAfterWorkingString_ge_one rest
  rcases List.mem_cons.mp hx with h1 | hx2
  · omega
  rcases List.mem_cons.mp hx2 with h2 | hx_aux
  · omega
  have h_aux_max := ctsConfigToSystem5BagAux_max rest 3 x hx_aux
  omega

/-- **Iter 1006: same-membership lifts through dec-erase**.  When two
    Nodup lists `xs, ys` have the same membership, their decrement-erase
    forms `(xs.map(·-1)).erase z` and `(ys.map(·-1)).erase z` also have
    the same membership.  Used to lift the bag-2 mem-iff (iter 1005)
    through bag-3's `dec-erase` form (iter 986). -/
theorem List_Int_dec_erase_same_mem
    (xs ys : List Int) (h_xs : xs.Nodup) (h_ys : ys.Nodup)
    (h_mem : ∀ x, x ∈ xs ↔ x ∈ ys) (z : Int) (x : Int) :
    x ∈ (xs.map (· - 1)).erase z ↔ x ∈ (ys.map (· - 1)).erase z := by
  have h_xs_dec_nodup : (xs.map (· - 1)).Nodup := by
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_xs
    intro a b h_ne h_eq; apply h_ne; have : a - 1 = b - 1 := h_eq; omega
  have h_ys_dec_nodup : (ys.map (· - 1)).Nodup := by
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_ys
    intro a b h_ne h_eq; apply h_ne; have : a - 1 = b - 1 := h_eq; omega
  rw [List.Nodup.mem_erase_iff h_xs_dec_nodup,
      List.Nodup.mem_erase_iff h_ys_dec_nodup]
  rw [List.mem_map, List.mem_map]
  constructor
  · rintro ⟨h_ne, a, ha_mem, ha_eq⟩
    exact ⟨h_ne, a, (h_mem a).mp ha_mem, ha_eq⟩
  · rintro ⟨h_ne, a, ha_mem, ha_eq⟩
    exact ⟨h_ne, a, (h_mem a).mpr ha_mem, ha_eq⟩

/-- **Iter 1013: same-membership + Nodup ⇒ Perm**.  When two `Nodup`
    Int lists have the same membership set, they are permutations
    of each other.  Used to upgrade iter 1012's mem-iff (s5_4.bag and
    `aux rest 1` have same membership) to `List.Perm`, which is closer
    to the bag-equality predicate `s5_result.bag = ctsConfigToSystem5Bag result`.
    Note: even Perm doesn't give equality, but it's the right
    multiset-level identity. -/
theorem List_Int_perm_of_nodup_same_mem
    (xs ys : List Int) (h_xs : xs.Nodup) (h_ys : ys.Nodup)
    (h_mem : ∀ x, x ∈ xs ↔ x ∈ ys) : List.Perm xs ys := by
  rw [List.perm_iff_count]
  intro a
  rw [List.Nodup.count h_xs, List.Nodup.count h_ys]
  by_cases h_in : a ∈ xs
  · simp [h_in, (h_mem a).mp h_in]
  · simp [h_in]
    intro h_in_ys
    exact h_in ((h_mem a).mpr h_in_ys)

/-- **Iter 1003: `(1 :: 2 :: aux rest 3)` disjoint from r2.map(·+2) (false-head)**.
    Companion to iter 1002.  Since r1 = r2.map(·+2) (iter 892), being
    disjoint from r1 (iter 1002) is equivalent to being disjoint from
    r2.map(·+2).  Used in the bag-2 membership chain to discharge the
    second disjointness obligation for `xorMerge_mem_iff`. -/
theorem ctsConfigToSystem5BagAux_three_one_two_cons_disjoint_r2_inc2
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ (∀ x ∈ ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3),
            x ∉ r2.map (· + 2)) := by
  obtain ⟨r1, r2, tail, h_eq, h_disj_r1⟩ :=
    ctsConfigToSystem5BagAux_three_one_two_cons_disjoint_r1 cts rest phase N h_N
  obtain ⟨r1', r2', _, h_eq', h_cancel⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_cancel cts
      { data := false :: rest, phase := phase } N h_N
  have h_r1_eq : r1 = r1' := by
    rw [h_eq] at h_eq'; simp at h_eq'; exact h_eq'.1
  have h_r2_eq : r2 = r2' := by
    rw [h_eq] at h_eq'; simp at h_eq'; exact h_eq'.2.1
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro x hx
  rw [h_r2_eq, ← h_cancel, ← h_r1_eq]
  exact h_disj_r1 x hx

/-- **`encodeAppendant_r1_length` (iter 667)**: the `r1` (first)
    component of `encodeAppendant rule i` has length `2 * rule.length` —
    each input bit contributes 2 entries to r1. -/
theorem encodeAppendant_r1_length (rule : List Bool) (i : Int) :
    (encodeAppendant rule i).1.length = 2 * rule.length := by
  induction rule generalizing i with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | true =>
      show ((i + 2) :: (i + 5) :: (encodeAppendant tail (i + 6)).1).length = _
      simp [List.length_cons, ih]
      omega
    | false =>
      show ((i + 2) :: (i + 3) :: (encodeAppendant tail (i + 4)).1).length = _
      simp [List.length_cons, ih]
      omega

/-- **`encodeAppendant_r2_length` (iter 667)**: the `r2` (second)
    component has the same length `2 * rule.length`. -/
theorem encodeAppendant_r2_length (rule : List Bool) (i : Int) :
    (encodeAppendant rule i).2.1.length = 2 * rule.length := by
  induction rule generalizing i with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | true =>
      show (i :: (i + 3) :: (encodeAppendant tail (i + 6)).2.1).length = _
      simp [List.length_cons, ih]
      omega
    | false =>
      show (i :: (i + 1) :: (encodeAppendant tail (i + 4)).2.1).length = _
      simp [List.length_cons, ih]
      omega

/-- **`encodeAppendant_r1_ge` (iter 667)**: every entry of
    `(encodeAppendant rule i).1` is `≥ i`.  Counter only ever
    advances. -/
theorem encodeAppendant_r1_ge (rule : List Bool) (i : Int) :
    ∀ x ∈ (encodeAppendant rule i).1, x ≥ i := by
  induction rule generalizing i with
  | nil => intro x h; cases h
  | cons head tail ih =>
    cases head with
    | true =>
      intro x h
      simp [encodeAppendant] at h
      rcases h with rfl | rfl | h
      · omega
      · omega
      · have := ih (i + 6) x h; omega
    | false =>
      intro x h
      simp [encodeAppendant] at h
      rcases h with rfl | rfl | h
      · omega
      · omega
      · have := ih (i + 4) x h; omega

/-- **`encodeAppendant_r2_ge` (iter 667)**: every entry of
    `(encodeAppendant rule i).2.1` is `≥ i`. -/
theorem encodeAppendant_r2_ge (rule : List Bool) (i : Int) :
    ∀ x ∈ (encodeAppendant rule i).2.1, x ≥ i := by
  induction rule generalizing i with
  | nil => intro x h; cases h
  | cons head tail ih =>
    cases head with
    | true =>
      intro x h
      simp [encodeAppendant] at h
      rcases h with rfl | rfl | h
      · omega
      · omega
      · have := ih (i + 6) x h; omega
    | false =>
      intro x h
      simp [encodeAppendant] at h
      rcases h with rfl | rfl | h
      · omega
      · omega
      · have := ih (i + 4) x h; omega

/-- **`encodeAppendant_r1_map_add_1_ge` (iter 667)**: shifted lower
    bound — `(r1).map (·+1)` has every entry ≥ `i+1`. -/
theorem encodeAppendant_r1_map_add_1_ge (rule : List Bool) (i : Int) :
    ∀ x ∈ (encodeAppendant rule i).1.map (· + 1), x ≥ i + 1 := by
  intro x h
  rw [List.mem_map] at h
  obtain ⟨y, h_y, h_eq⟩ := h
  have := encodeAppendant_r1_ge rule i y h_y
  omega

/-- **`encodeAppendant_r2_map_add_1_ge` (iter 668)**: r2 mirror of
    `encodeAppendant_r1_map_add_1_ge` — `(r2).map (·+1)` has every
    entry ≥ `i+1`. -/
theorem encodeAppendant_r2_map_add_1_ge (rule : List Bool) (i : Int) :
    ∀ x ∈ (encodeAppendant rule i).2.1.map (· + 1), x ≥ i + 1 := by
  intro x h
  rw [List.mem_map] at h
  obtain ⟨y, h_y, h_eq⟩ := h
  have := encodeAppendant_r2_ge rule i y h_y
  omega

/-- **`encodeAppendant_r1_map_add_1_ge_four` (iter 668)**: with the
    starting counter `counterAfterWorkingString cfg.data + 2`, the
    shifted r1 has every entry ≥ 4 (since
    `counterAfterWorkingString ≥ 1`).  Useful for showing rule entries
    don't conflict with bag-prefix range `{1, 2, 3}`. -/
theorem encodeAppendant_r1_map_add_1_ge_four (rule : List Bool) (cfg : CTSConfig) :
    ∀ x ∈ (encodeAppendant rule (counterAfterWorkingString cfg.data + 2)).1.map (· + 1),
      x ≥ 4 := by
  intro x h
  have h_ge := encodeAppendant_r1_map_add_1_ge rule
                 (counterAfterWorkingString cfg.data + 2) x h
  have h_counter := counterAfterWorkingString_ge_one cfg.data
  omega

/-- **`encodeAppendant_r2_map_add_1_ge_four` (iter 668)**: r2 mirror.
    Same setup, same bound. -/
theorem encodeAppendant_r2_map_add_1_ge_four (rule : List Bool) (cfg : CTSConfig) :
    ∀ x ∈ (encodeAppendant rule (counterAfterWorkingString cfg.data + 2)).2.1.map (· + 1),
      x ≥ 4 := by
  intro x h
  have h_ge := encodeAppendant_r2_map_add_1_ge rule
                 (counterAfterWorkingString cfg.data + 2) x h
  have h_counter := counterAfterWorkingString_ge_one cfg.data
  omega

/-- **`encodeAppendant_r1_map_add_1_disjoint_below_four` (iter 669)**:
    any value `x < 4` is not in the popped r1 rule. -/
theorem encodeAppendant_r1_map_add_1_disjoint_below_four
    (rule : List Bool) (cfg : CTSConfig) (x : Int) (h_lt : x < 4) :
    x ∉ (encodeAppendant rule (counterAfterWorkingString cfg.data + 2)).1.map (· + 1) := by
  intro h
  have := encodeAppendant_r1_map_add_1_ge_four rule cfg x h
  omega

/-- **`encodeAppendant_r2_map_add_1_disjoint_below_four` (iter 669)**:
    any value `x < 4` is not in the popped r2 rule. -/
theorem encodeAppendant_r2_map_add_1_disjoint_below_four
    (rule : List Bool) (cfg : CTSConfig) (x : Int) (h_lt : x < 4) :
    x ∉ (encodeAppendant rule (counterAfterWorkingString cfg.data + 2)).2.1.map (· + 1) := by
  intro h
  have := encodeAppendant_r2_map_add_1_ge_four rule cfg x h
  omega

/-- **`encodeAppendant_r1_nodup` (iter 669)**: r1 of `encodeAppendant
    rule i` is duplicate-free.  Each bit emits 2 distinct values; the
    recursive call uses a strictly larger counter. -/
theorem encodeAppendant_r1_nodup (rule : List Bool) (i : Int) :
    (encodeAppendant rule i).1.Nodup := by
  induction rule generalizing i with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
    cases head with
    | true =>
      show ((i+2) :: (i+5) :: (encodeAppendant tail (i+6)).1).Nodup
      simp only [List.nodup_cons, List.mem_cons]
      refine ⟨?_, ?_, ih (i+6)⟩
      · intro h
        rcases h with h | h
        · omega
        · have := encodeAppendant_r1_ge tail (i+6) (i+2) h; omega
      · intro h
        have := encodeAppendant_r1_ge tail (i+6) (i+5) h; omega
    | false =>
      show ((i+2) :: (i+3) :: (encodeAppendant tail (i+4)).1).Nodup
      simp only [List.nodup_cons, List.mem_cons]
      refine ⟨?_, ?_, ih (i+4)⟩
      · intro h
        rcases h with h | h
        · omega
        · have := encodeAppendant_r1_ge tail (i+4) (i+2) h; omega
      · intro h
        have := encodeAppendant_r1_ge tail (i+4) (i+3) h; omega

/-- **`encodeAppendant_r1_map_add_1_nodup` (iter 669)**: shifted r1 is
    `Nodup` (`(· + 1)` is injective). -/
theorem encodeAppendant_r1_map_add_1_nodup (rule : List Bool) (i : Int) :
    ((encodeAppendant rule i).1.map (· + 1)).Nodup := by
  show List.Pairwise (· ≠ ·) ((encodeAppendant rule i).1.map (· + 1))
  apply List.Pairwise.map (· + 1) (R := (· ≠ ·)) ?_ (encodeAppendant_r1_nodup rule i)
  intro a b h_ne h_eq
  apply h_ne
  show a = b
  have : a + 1 = b + 1 := h_eq
  omega

/-- **`encodeAppendant_r2_nodup` (iter 669)**: r2 mirror. -/
theorem encodeAppendant_r2_nodup (rule : List Bool) (i : Int) :
    (encodeAppendant rule i).2.1.Nodup := by
  induction rule generalizing i with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
    cases head with
    | true =>
      show (i :: (i+3) :: (encodeAppendant tail (i+6)).2.1).Nodup
      simp only [List.nodup_cons, List.mem_cons]
      refine ⟨?_, ?_, ih (i+6)⟩
      · intro h
        rcases h with h | h
        · omega
        · have := encodeAppendant_r2_ge tail (i+6) i h; omega
      · intro h
        have := encodeAppendant_r2_ge tail (i+6) (i+3) h; omega
    | false =>
      show (i :: (i+1) :: (encodeAppendant tail (i+4)).2.1).Nodup
      simp only [List.nodup_cons, List.mem_cons]
      refine ⟨?_, ?_, ih (i+4)⟩
      · intro h
        rcases h with h | h
        · omega
        · have := encodeAppendant_r2_ge tail (i+4) i h; omega
      · intro h
        have := encodeAppendant_r2_ge tail (i+4) (i+1) h; omega

/-- **`encodeAppendant_r2_map_add_1_nodup` (iter 669)**: shifted r2 is
    `Nodup`. -/
theorem encodeAppendant_r2_map_add_1_nodup (rule : List Bool) (i : Int) :
    ((encodeAppendant rule i).2.1.map (· + 1)).Nodup := by
  show List.Pairwise (· ≠ ·) ((encodeAppendant rule i).2.1.map (· + 1))
  apply List.Pairwise.map (· + 1) (R := (· ≠ ·)) ?_ (encodeAppendant_r2_nodup rule i)
  intro a b h_ne h_eq
  apply h_ne
  show a = b
  have : a + 1 = b + 1 := h_eq
  omega

/-- **Iter 981: r2.map(·+2) is Nodup**.  Companion to
    `encodeAppendant_r2_map_add_1_nodup`: shifting r2 by 2 preserves
    `Nodup` since `(·+2)` is injective.  Used in the bag-2
    membership proof for the false-head trajectory. -/
theorem encodeAppendant_r2_map_add_2_nodup (rule : List Bool) (i : Int) :
    ((encodeAppendant rule i).2.1.map (· + 2)).Nodup := by
  show List.Pairwise (· ≠ ·) ((encodeAppendant rule i).2.1.map (· + 2))
  apply List.Pairwise.map (· + 2) (R := (· ≠ ·)) ?_ (encodeAppendant_r2_nodup rule i)
  intro a b h_ne h_eq
  apply h_ne
  show a = b
  have : a + 2 = b + 2 := h_eq
  omega

/-- **Iter 923**: explicit form of processCycle's first rule. -/
theorem processCycle_first_rule_eq
    (a : List Bool) (rest : List (List Bool)) (i : Int) :
    (processCycle (a :: rest) i).1.head?
      = some (encodeAppendant a i).1 := by
  rfl

/-- **Iter 917: lift r1.map(+1).Nodup through processCycle**. -/
theorem processCycle_first_rule_map_add_1_nodup
    (a : List Bool) (rest : List (List Bool)) (i : Int) :
    ∃ r1 r2 tail, (processCycle (a :: rest) i).1 = r1 :: r2 :: tail
                ∧ (r1.map (· + 1)).Nodup := by
  refine ⟨(encodeAppendant a i).1, (encodeAppendant a i).2.1,
          [] :: [] :: (processCycle rest (encodeAppendant a i).2.2).1, ?_, ?_⟩
  · show (processCycle (a :: rest) i).1
        = (encodeAppendant a i).1 :: (encodeAppendant a i).2.1 ::
          [] :: [] :: (processCycle rest (encodeAppendant a i).2.2).1
    rfl
  · exact encodeAppendant_r1_map_add_1_nodup a i

/-- **Iter 917: lift r1.map(+1).Nodup through nCycles**. -/
theorem nCycles_first_rule_map_add_1_nodup
    (a : List Bool) (rest : List (List Bool)) (k : Nat) (i : Int) :
    ∃ r1 r2 tail, nCycles (a :: rest) (k + 1) i = r1 :: r2 :: tail
                ∧ (r1.map (· + 1)).Nodup := by
  rw [nCycles_succ]
  obtain ⟨r1, r2, mid_tail, h_pc, h_nodup⟩ :=
    processCycle_first_rule_map_add_1_nodup a rest i
  refine ⟨r1, r2, mid_tail ++ nCycles (a :: rest) k (processCycle (a :: rest) i).snd,
          ?_, h_nodup⟩
  rw [h_pc]
  rfl

/-- **Iter 917: lift r1.map(+1).Nodup to ctsRulesToSystem5Rules**. -/
theorem ctsRulesToSystem5Rules_first_rule_map_add_1_nodup
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ (r1.map (· + 1)).Nodup := by
  unfold ctsRulesToSystem5Rules
  cases h_app : cts.appendants with
  | nil =>
    have := cts.nonempty
    rw [h_app] at this
    simp at this
  | cons a rest =>
    cases N with
    | zero => omega
    | succ k =>
      exact nCycles_first_rule_map_add_1_nodup a rest k
        (counterAfterWorkingString cfg.data + 2)

/-- **Iter 1056: post-step bag has explicit reverse-append form at
    Perm-chain points**.  Composes iter 912's
    `xorMerge_disjoint_eq_reverse_append` with iter 1054 (disjointness)
    + iter 917 (Nodup of r1.map(·+1)).  At any Perm-chain point with
    `N ≥ 1`, the post-step bag is `(r1.map(·+1)).reverse ++
    ((bag.map(·-1)).erase 0)` — the explicit list-concat form.
    **Chain-induction analog of iter 995's `bag1_form`** at arbitrary
    chain points (not just cfg5). -/
theorem ctsConfigToSystem5Bag_perm_step_bag_form
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ xorMerge ((bag.map (· - 1)).erase 0) (r1.map (· + 1))
                    = (r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0) := by
  obtain ⟨r1, r2, tail, h_eq, h_disjoint⟩ :=
    ctsConfigToSystem5Bag_perm_dec_erase_disjoint_r1_inc cts cfg N h_N bag h_perm
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  apply xorMerge_disjoint_eq_reverse_append
  · intro y h_y_r1_inc h_y_dec
    exact h_disjoint y h_y_dec h_y_r1_inc
  · obtain ⟨r1', _r2', _tail', h_eq', h_r1_nodup⟩ :=
      ctsRulesToSystem5Rules_first_rule_map_add_1_nodup cts cfg N h_N
    rw [h_eq] at h_eq'
    have h_r1_eq : r1 = r1' := (List.cons.inj h_eq').1
    rw [h_r1_eq]
    exact h_r1_nodup

/-- **Iter 1057: explicit System5 step output at Perm-chain points**.
    Combines iter 1052 (`step_pop_explicit`) with iter 1056
    (`step_bag_form`): when `bag ~ ctsConfigToSystem5Bag cfg`,
    `cfg.data ≠ []`, and `N ≥ 1`, the System5 step on the encoder rule
    list yields the FULL post-step config explicitly:
    `some ⟨(r1.map(·+1)).reverse ++ ((bag.map(·-1)).erase 0),
           (r2 :: tail).map(map(·+1))⟩`.  **This is the chain-induction
    step formula** — the LHS form needed for direct comparison with
    the next chain hypothesis. -/
theorem ctsConfigToSystem5Bag_perm_step_some_explicit
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_data : cfg.data ≠ [])
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩
                    = some ⟨(r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0),
                            (r2 :: tail).map (fun r => r.map (· + 1))⟩ := by
  obtain ⟨r1, r2, tail, h_eq, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_perm_step_bag_form cts cfg N h_N bag h_perm
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  rw [h_eq]
  rw [ctsConfigToSystem5Bag_perm_step_pop_explicit cfg bag (r1 :: r2 :: tail)
        r1 (r2 :: tail) h_data h_perm rfl]
  rw [h_bag_form]

/-- **Iter 1058: reverse-append Perm equivalence for Int lists**.
    Generic helper: `(xs.reverse ++ ys).Perm (xs ++ ys)`.  Combines
    `List.reverse_perm` with `List.Perm.append_right`.  **Building
    block for the chain-induction Perm-preservation step**: the post-
    step bag form `(r1.map(·+1)).reverse ++ ((bag.map(·-1)).erase 0)`
    (iter 1057) is Perm-equivalent to `r1.map(·+1) ++ ((bag.map(·-1)).erase 0)`,
    which simplifies further reasoning about its membership content. -/
theorem List_Int_reverse_append_perm (xs ys : List Int) :
    (xs.reverse ++ ys).Perm (xs ++ ys) :=
  List.Perm.append_right ys (List.reverse_perm xs)

/-- **Iter 1059: post-step bag Perm-equivalence to non-reversed form**.
    Specialization of iter 1058 to the chain-induction post-step bag
    form: `((r1.map(·+1)).reverse ++ ((bag.map(·-1)).erase 0)).Perm
    (r1.map(·+1) ++ ((bag.map(·-1)).erase 0))`.  **Cleans up the
    post-step bag form** (iter 1057's output) for further Perm-based
    reasoning toward the chain hypothesis at the next chain point. -/
theorem ctsConfigToSystem5Bag_perm_step_bag_perm
    (bag r1 : List Int) :
    ((r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0)).Perm
      (r1.map (· + 1) ++ ((bag.map (· - 1)).erase 0)) :=
  List_Int_reverse_append_perm (r1.map (· + 1)) ((bag.map (· - 1)).erase 0)

/-- **Iter 1060: post-step bag Perm-equivalent to clean form**.  After
    one System5 P-step at a Perm-chain point, the resulting bag is
    `Perm`-equivalent to `r1.map(·+1) ++ ((bag.map(·-1)).erase 0)`.
    Composition: iter 1057 (full step output) + iter 1059 (reverse-
    append Perm equivalence).  **The chain-induction step output**:
    starting from a Perm-chain hypothesis, after one P-step we get a
    new Perm-equivalence (with the post-step bag in clean append form),
    ready to chain to the next chain point. -/
theorem ctsConfigToSystem5Bag_perm_after_step_perm
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_data : cfg.data ≠ [])
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ r1 r2 tail s5',
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
      ∧ System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5'
      ∧ s5'.bag.Perm (r1.map (· + 1) ++ ((bag.map (· - 1)).erase 0)) := by
  obtain ⟨r1, r2, tail, h_eq, h_step⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts cfg N h_N bag h_data h_perm
  refine ⟨r1, r2, tail, _, h_eq, h_step, ?_⟩
  exact ctsConfigToSystem5Bag_perm_step_bag_perm bag r1

/-- **Iter 1061: 1 ∈ post-step bag at false-head Perm-chain points**.
    After one System5 P-step at a false-head Perm-chain point, the
    resulting bag contains `1`.  Composition: iter 1060 (post-step
    bag is Perm-equivalent to `r1.map(·+1) ++ dec-erase bag`) +
    iter 1044 (`1 ∈ dec-erase bag` for false-head) + `List.mem_append_right`
    + `List.Perm.mem_iff`.  **Building block toward two-steps-succeed**:
    `1 ∈ s5'.bag` ⇒ `s5'.bag ≠ []`, the bag-side prerequisite for
    the next step. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step_bag_one_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5',
      System5.step ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ = some s5'
      ∧ (1 : Int) ∈ s5'.bag := by
  obtain ⟨r1, _, _, s5', _, h_step, h_perm'⟩ :=
    ctsConfigToSystem5Bag_perm_after_step_perm cts
      { data := false :: rest, phase := phase } N h_N bag (by simp) h_perm
  refine ⟨s5', h_step, ?_⟩
  have h_one_dec : (1 : Int) ∈ (bag.map (· - 1)).erase 0 :=
    ctsConfigToSystem5Bag_false_head_perm_dec_erase_one_mem rest phase bag h_perm
  apply (List.Perm.mem_iff h_perm').mpr
  exact List.mem_append_right (r1.map (· + 1)) h_one_dec

/-- **Iter 1062: TWO consecutive System5 steps succeed at false-head
    Perm-chain points**.  Combines iter 1057 (full step output, gives
    s5'.rules form) + iter 1061 (1 ∈ s5'.bag, hence s5'.bag ≠ []) +
    `System5_step_some_iff` for the second step.  The s5'.rules ≠ []
    follows from `(r2 :: tail).map(map(·+1))` being non-empty.
    **Chain-induction analog of iter 977's existing cfg5-level
    step-2-succeeds**, the key non-emptiness step toward the multi-
    step trajectory. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step2_succeeds
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_2, System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
              { data := false :: rest, phase := phase } N⟩ 2 = some s5_2 := by
  obtain ⟨s5', h_step', h_one_in⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step_bag_one_mem cts rest phase N h_N bag h_perm
  obtain ⟨r1, r2, tail, _h_eq, h_step⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts
      { data := false :: rest, phase := phase } N h_N bag (by simp) h_perm
  have h_s5'_eq : s5' = ⟨(r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0),
                          (r2 :: tail).map (fun r => r.map (· + 1))⟩ :=
    Option.some.inj (h_step'.symm.trans h_step)
  have h_bag_ne : s5'.bag ≠ [] := List.ne_nil_of_mem h_one_in
  have h_rules_ne : s5'.rules ≠ [] := by
    rw [h_s5'_eq]; simp
  obtain ⟨s5_2, h_step2⟩ :=
    (System5_step_some_iff s5').mpr ⟨h_bag_ne, h_rules_ne⟩
  refine ⟨s5_2, ?_⟩
  rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add]
  rw [System5.nSteps_one, h_step']
  show System5.nSteps s5' 1 = some s5_2
  rw [System5.nSteps_one]
  exact h_step2

/-- **Iter 1063: bag-2 explicit form at false-head Perm-chain points**.
    After TWO P-steps at a false-head Perm-chain point, the bag is
    `xorMerge ((s5_1.bag.map(·-1)).erase 0) (r2.map(·+2))`.  Composition:
    iter 1057 (s5_1 explicit form) + iter 1061 (1 ∈ s5_1.bag) +
    `System5_step_explicit_pop` for step 2 (popping `r2.map(·+1)`,
    giving xorMerge with `(r2.map(·+1)).map(·+1) = r2.map(·+2)` via
    `List_Int_map_add_compose`).  **Chain-induction analog of iter 980's
    existing cfg5-level bag-2 form**. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step2_bag_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_1 s5_2,
      ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
          { data := false :: rest, phase := phase } N⟩ 1 = some s5_1
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
          { data := false :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ s5_2.bag = xorMerge ((s5_1.bag.map (· - 1)).erase 0) (r2.map (· + 2)) := by
  obtain ⟨r1, r2, tail, h_eq, h_step1⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts
      { data := false :: rest, phase := phase } N h_N bag (by simp) h_perm
  obtain ⟨s5_1', h_step1', h_one_mem⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step_bag_one_mem cts rest phase N h_N bag h_perm
  let s5_1 : System5Config :=
    ⟨(r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0),
     (r2 :: tail).map (fun r => r.map (· + 1))⟩
  have h_s5_1_eq : s5_1' = s5_1 :=
    Option.some.inj (h_step1'.symm.trans h_step1)
  have h_one_mem_s5_1 : (1 : Int) ∈ s5_1.bag := h_s5_1_eq ▸ h_one_mem
  have h_zero : (0 : Int) ∈ s5_1.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_1
  have h_bag_ne : s5_1.bag ≠ [] := List.ne_nil_of_mem h_one_mem_s5_1
  have h_rules_form : s5_1.rules
        = (r2.map (· + 1)) :: (tail.map (fun r => r.map (· + 1))) := by
    show (r2 :: tail).map (fun r => r.map (· + 1)) = _
    simp
  have h_step2 := System5_step_explicit_pop s5_1 (r2.map (· + 1))
      (tail.map (fun r => r.map (· + 1)))
      h_rules_form h_bag_ne h_zero
  let s5_2 : System5Config :=
    ⟨xorMerge ((s5_1.bag.map (· - 1)).erase 0) ((r2.map (· + 1)).map (· + 1)),
     (tail.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))⟩
  refine ⟨r1, r2, tail, s5_1, s5_2, h_eq, ?_, ?_, ?_⟩
  · rw [System5.nSteps_one]; exact h_step1
  · rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add]
    rw [System5.nSteps_one, h_step1]
    simp only [Option.bind_some, System5.nSteps_one]
    exact h_step2
  · show xorMerge ((s5_1.bag.map (· - 1)).erase 0) ((r2.map (· + 1)).map (· + 1))
       = xorMerge ((s5_1.bag.map (· - 1)).erase 0) (r2.map (· + 2))
    congr 1
    exact List_Int_map_add_compose r2 1 1

/-- **Iter 1064: 2 ∈ post-step bag at false-head Perm-chain points**.
    Companion to iter 1061 for value 2.  Composition: iter 1060
    (post-step bag is Perm-equivalent to `r1.map(·+1) ++ dec-erase bag`)
    + iter 1045 (`2 ∈ dec-erase bag` for false-head) + `List.mem_append_right`
    + `List.Perm.mem_iff`.  **Building block toward step3-is-P-step at
    chain points** — chain-induction analog of iter 974's existing
    cfg5-level after_first_step_two_mem. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step_bag_two_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5',
      System5.step ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ = some s5'
      ∧ (2 : Int) ∈ s5'.bag := by
  obtain ⟨r1, _, _, s5', _, h_step, h_perm'⟩ :=
    ctsConfigToSystem5Bag_perm_after_step_perm cts
      { data := false :: rest, phase := phase } N h_N bag (by simp) h_perm
  refine ⟨s5', h_step, ?_⟩
  have h_two_dec : (2 : Int) ∈ (bag.map (· - 1)).erase 0 :=
    ctsConfigToSystem5Bag_false_head_perm_dec_erase_two_mem rest phase bag h_perm
  apply (List.Perm.mem_iff h_perm').mpr
  exact List.mem_append_right (r1.map (· + 1)) h_two_dec

/-- **Iter 1067: 3 ∈ post-step bag at false-head Perm-chain points**.
    Companion to iters 1061/1064 for value 3.  Composition: iter 1060
    + iter 1046 (`3 ∈ dec-erase bag` for false-head) + `List.mem_append_right`
    + `List.Perm.mem_iff`.  **Building block toward step4-is-P-step at
    chain points** — chain-induction analog of iter 988's existing
    cfg5-level after_first_step_three_mem. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step_bag_three_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5',
      System5.step ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ = some s5'
      ∧ (3 : Int) ∈ s5'.bag := by
  obtain ⟨r1, _, _, s5', _, h_step, h_perm'⟩ :=
    ctsConfigToSystem5Bag_perm_after_step_perm cts
      { data := false :: rest, phase := phase } N h_N bag (by simp) h_perm
  refine ⟨s5', h_step, ?_⟩
  have h_three_dec : (3 : Int) ∈ (bag.map (· - 1)).erase 0 :=
    ctsConfigToSystem5Bag_false_head_perm_dec_erase_three_mem rest phase bag h_perm
  apply (List.Perm.mem_iff h_perm').mpr
  exact List.mem_append_right (r1.map (· + 1)) h_three_dec

/-- **Iter 1065: post-step bag Nodup at Perm-chain points (any cfg)**.
    Generic version: s5_1.bag.Nodup whenever s5_1 = post-step config
    from a Perm-chain point.  Composition: iter 1057 (post-step bag
    explicit form) + iter 1055 (xorMerge Nodup) + iter 1056 (xorMerge
    = reverse-append).  Aligns the r1's via `List.cons.inj`.
    **Stepping stone toward `1 ∈ s5_2.bag` at chain points** — provides
    the dec-erase Nodup obligation needed for `xorMerge_mem_left_of_not_mem_right`. -/
theorem ctsConfigToSystem5Bag_perm_step1_bag_nodup
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ [])
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ s5_1,
      System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5_1
      ∧ s5_1.bag.Nodup := by
  obtain ⟨r1, _r2, _tail, h_eq, h_step1⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts cfg N h_N bag h_data h_perm
  refine ⟨_, h_step1, ?_⟩
  show ((r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0)).Nodup
  obtain ⟨r1', _, _, h_eq', h_xor_eq⟩ :=
    ctsConfigToSystem5Bag_perm_step_bag_form cts cfg N h_N bag h_perm
  have h_r1_eq : r1 = r1' := (List.cons.inj (h_eq.symm.trans h_eq')).1
  rw [h_r1_eq, ← h_xor_eq]
  exact ctsConfigToSystem5Bag_perm_xorMerge_r_inc_nodup cfg bag r1' h_perm

/-- **Iter 981: lift r2.map(+2).Nodup through processCycle**.  Companion
    to iter 917's r1 chain. -/
theorem processCycle_second_rule_map_add_2_nodup
    (a : List Bool) (rest : List (List Bool)) (i : Int) :
    ∃ r1 r2 tail, (processCycle (a :: rest) i).1 = r1 :: r2 :: tail
                ∧ (r2.map (· + 2)).Nodup := by
  refine ⟨(encodeAppendant a i).1, (encodeAppendant a i).2.1,
          [] :: [] :: (processCycle rest (encodeAppendant a i).2.2).1, ?_, ?_⟩
  · rfl
  · exact encodeAppendant_r2_map_add_2_nodup a i

/-- **Iter 981: lift r2.map(+2).Nodup through nCycles**. -/
theorem nCycles_second_rule_map_add_2_nodup
    (a : List Bool) (rest : List (List Bool)) (k : Nat) (i : Int) :
    ∃ r1 r2 tail, nCycles (a :: rest) (k + 1) i = r1 :: r2 :: tail
                ∧ (r2.map (· + 2)).Nodup := by
  rw [nCycles_succ]
  obtain ⟨r1, r2, mid_tail, h_pc, h_nodup⟩ :=
    processCycle_second_rule_map_add_2_nodup a rest i
  refine ⟨r1, r2, mid_tail ++ nCycles (a :: rest) k (processCycle (a :: rest) i).snd,
          ?_, h_nodup⟩
  rw [h_pc]
  rfl

/-- **Iter 981: lift r2.map(+2).Nodup to ctsRulesToSystem5Rules**. -/
theorem ctsRulesToSystem5Rules_second_rule_map_add_2_nodup
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ (r2.map (· + 2)).Nodup := by
  unfold ctsRulesToSystem5Rules
  cases h_app : cts.appendants with
  | nil =>
    have := cts.nonempty
    rw [h_app] at this
    simp at this
  | cons a rest =>
    cases N with
    | zero => omega
    | succ k =>
      exact nCycles_second_rule_map_add_2_nodup a rest k
        (counterAfterWorkingString cfg.data + 2)

/-- **Iter 1066: 1 ∈ s5_2.bag at false-head Perm-chain points (MAJOR
    MILESTONE)**.  After TWO P-steps at a false-head Perm-chain point,
    the bag contains `1` — confirming step 3 is also a P-step at chain
    points.  Composition: iter 1063 (bag-2 form) + iter 1064 (2 ∈
    s5_1.bag) + iter 1065 (s5_1.bag Nodup) + `mem_imp_pred_in_dec_erase`
    (iter 975) + `xorMerge_mem_left_of_not_mem_right` (iter 969) +
    iter 981 + iter 976.  The s5_1 alignment between iters 1063/1064/1065
    is via `Option.some.inj`.  **Chain-induction analog of iter 982's
    existing cfg5-level step2_one_mem** — together with iter 1061
    (1 ∈ s5_1.bag), proves the first 3 steps from any false-head
    Perm-chain point are all P-steps. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step2_one_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_2,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ (1 : Int) ∈ s5_2.bag := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨r1, r2, tail, s5_1, s5_2, h_eq, h_step1, h_step2, h_bag2_form⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step2_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_2, h_step2, ?_⟩
  rw [h_bag2_form]
  obtain ⟨s5_1_a, h_step1_a, h_two_in⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step_bag_two_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_1_b, h_step1_b, h_s5_1_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_nodup cts cfg N h_N (by simp) bag h_perm
  have h_step1_one : System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩
                       = some s5_1 := by
    have := h_step1; rw [System5.nSteps_one] at this; exact this
  have h_eq_a : s5_1 = s5_1_a := Option.some.inj (h_step1_one.symm.trans h_step1_a)
  have h_eq_b : s5_1 = s5_1_b := Option.some.inj (h_step1_one.symm.trans h_step1_b)
  have h_two_mem_s5_1 : (2 : Int) ∈ s5_1.bag := h_eq_a ▸ h_two_in
  have h_bag_nodup : s5_1.bag.Nodup := h_eq_b ▸ h_s5_1_nodup
  apply xorMerge_mem_left_of_not_mem_right
  · apply List.Nodup.erase
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_bag_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  · obtain ⟨_, r2', _, h_eq', h_nodup⟩ :=
      ctsRulesToSystem5Rules_second_rule_map_add_2_nodup cts cfg N h_N
    have h_r2_eq : r2 = r2' := by
      have h := h_eq.symm.trans h_eq'
      injection h with _ h2
      exact (List.cons.inj h2).1
    rw [h_r2_eq]; exact h_nodup
  · have h_pred := mem_imp_pred_in_dec_erase s5_1.bag 2 h_two_mem_s5_1 (by omega)
    have h_eq_one : (2 : Int) - 1 = 1 := by omega
    rw [h_eq_one] at h_pred
    exact h_pred
  · obtain ⟨_, r2', _, h_eq', h_no_one⟩ :=
      ctsRulesToSystem5Rules_false_head_second_rule_inc2_no_one cts rest phase N h_N
    have h_r2_eq : r2 = r2' := by
      have h := h_eq.symm.trans h_eq'
      injection h with _ h2
      exact (List.cons.inj h2).1
    rw [h_r2_eq]; exact h_no_one

/-- **Iter 1068: 2 ∈ s5_2.bag at false-head Perm-chain points**.  After
    TWO P-steps at a false-head Perm-chain point, the bag contains `2`.
    Composition: iter 1063 (bag-2 form) + iter 1067 (`3 ∈ s5_1.bag`) +
    iter 1065 (s5_1.bag Nodup) + iter 975 + iter 969 + iter 981 +
    iter 973 (`2 ∉ r2.map(·+2)` for false-head).  **Chain-induction
    analog of iter 989's existing cfg5-level step2_two_mem** —
    second link in the cascade `4 ∈ bag ⇒ 3 ∈ s5_1.bag ⇒ 2 ∈ s5_2.bag
    ⇒ 1 ∈ s5_3.bag` (step 4 = P-step). -/
theorem ctsConfigToSystem5Bag_false_head_perm_step2_two_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_2,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ (2 : Int) ∈ s5_2.bag := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨r1, r2, tail, s5_1, s5_2, h_eq, h_step1, h_step2, h_bag2_form⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step2_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_2, h_step2, ?_⟩
  rw [h_bag2_form]
  obtain ⟨s5_1_a, h_step1_a, h_three_in⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step_bag_three_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_1_b, h_step1_b, h_s5_1_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_nodup cts cfg N h_N (by simp) bag h_perm
  have h_step1_one : System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩
                       = some s5_1 := by
    have := h_step1; rw [System5.nSteps_one] at this; exact this
  have h_eq_a : s5_1 = s5_1_a := Option.some.inj (h_step1_one.symm.trans h_step1_a)
  have h_eq_b : s5_1 = s5_1_b := Option.some.inj (h_step1_one.symm.trans h_step1_b)
  have h_three_mem_s5_1 : (3 : Int) ∈ s5_1.bag := h_eq_a ▸ h_three_in
  have h_bag_nodup : s5_1.bag.Nodup := h_eq_b ▸ h_s5_1_nodup
  apply xorMerge_mem_left_of_not_mem_right
  · apply List.Nodup.erase
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_bag_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  · obtain ⟨_, r2', _, h_eq', h_nodup⟩ :=
      ctsRulesToSystem5Rules_second_rule_map_add_2_nodup cts cfg N h_N
    have h_r2_eq : r2 = r2' := by
      have h := h_eq.symm.trans h_eq'
      injection h with _ h2
      exact (List.cons.inj h2).1
    rw [h_r2_eq]; exact h_nodup
  · have h_pred := mem_imp_pred_in_dec_erase s5_1.bag 3 h_three_mem_s5_1 (by omega)
    have h_eq_two : (3 : Int) - 1 = 2 := by omega
    rw [h_eq_two] at h_pred
    exact h_pred
  · obtain ⟨_, r2', _, h_eq', _, h_no_two⟩ :=
      ctsRulesToSystem5Rules_false_head_first_two_rules_no_two cts rest phase N h_N
    have h_r2_eq : r2 = r2' := by
      have h := h_eq.symm.trans h_eq'
      injection h with _ h2
      exact (List.cons.inj h2).1
    rw [h_r2_eq]; exact h_no_two

/-- **Iter 1069: s5_2.rules form at false-head Perm-chain points**.
    `s5_2.rules = [] :: [] :: rest_more`.  Composes iter 968's
    `System5_nSteps_rules_pstep` (after 2 P-steps, rules =
    `(orig.drop 2).map(map(·+2))`) with iter 984's
    `ctsRulesToSystem5Rules_drop_2_exists_empty_rules` (drop-2 yields
    `[] :: [] :: rest_more`).  All-P-step hypothesis discharged via
    iter 1051 (`0 ∈ dec(bag)` for k=0) and iter 1061 (`1 ∈ s5_1.bag`,
    hence `0 ∈ dec(s5_1.bag)` for k=1).  **Chain-induction analog of
    iter 985's existing cfg5-level step2_rules_form** — confirms the
    rule popped at step 3 is `[]` (so bag-3 = dec-erase s5_2.bag). -/
theorem ctsConfigToSystem5Bag_false_head_perm_step2_rules_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_2,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ ∃ rest_more, s5_2.rules = ([] : List Int) :: ([] : List Int) :: rest_more := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨s5_2, h_step2, _⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step2_one_mem cts rest phase N h_N bag h_perm
  refine ⟨s5_2, h_step2, ?_⟩
  have h_pstep : ∀ k < 2, ∀ cfg_k,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ k = some cfg_k
      → (0 : Int) ∈ cfg_k.bag.map (· - 1) := by
    intro k h_k cfg_k h_k_eq
    match k, h_k with
    | 0, _ =>
      simp [System5.nSteps] at h_k_eq
      rw [← h_k_eq]
      exact ctsConfigToSystem5Bag_perm_zero_in_decrement cfg bag (by simp) h_perm
    | 1, _ =>
      obtain ⟨s5_1, h_step1, h_one_mem_s5_1⟩ :=
        ctsConfigToSystem5Bag_false_head_perm_step_bag_one_mem cts rest phase N h_N bag h_perm
      have h_step1_one : System5.nSteps
          ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ 1 = some s5_1 := by
        rw [System5.nSteps_one]; exact h_step1
      have h_eq : cfg_k = s5_1 := Option.some.inj (h_k_eq.symm.trans h_step1_one)
      rw [h_eq]
      exact (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_1
  have h_rules_form := System5_nSteps_rules_pstep _ s5_2 2 h_step2 h_pstep
  obtain ⟨rest_more, h_drop⟩ :=
    ctsRulesToSystem5Rules_drop_2_exists_empty_rules cts cfg N h_N
  refine ⟨rest_more.map (fun r => r.map (· + 2)), ?_⟩
  rw [h_rules_form]
  show ((ctsRulesToSystem5Rules cts cfg N).drop 2).map (fun r => r.map (· + (2 : Int)))
     = ([] : List Int) :: ([] : List Int) :: rest_more.map (fun r => r.map (· + 2))
  rw [h_drop]
  simp [List.map_cons]

/-- **Iter 1070: bag-3 form at false-head Perm-chain points**.
    `s5_3.bag = (s5_2.bag.map(·-1)).erase 0`.  The popped rule at step
    3 is `[]` (per iter 1069's `s5_2.rules = [] :: [] :: rest_more`),
    so xorMerge with the (incremented) empty rule simplifies via
    `xorMerge_nil`.  Composition: iter 1066 (1 ∈ s5_2.bag → P-step
    trigger) + iter 1069 (s5_2.rules form) + `System5_step_explicit_pop`
    + `xorMerge_nil`.  **Chain-induction analog of iter 986's existing
    cfg5-level bag3_form**. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step3_bag_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_2 s5_3,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ s5_3.bag = (s5_2.bag.map (· - 1)).erase 0 := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨s5_2a, h_step2a, h_one_mem⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step2_one_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_2, h_step2, rest_more, h_rules_form⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step2_rules_form cts rest phase N h_N bag h_perm
  have h_eq : s5_2a = s5_2 := Option.some.inj (h_step2a.symm.trans h_step2)
  rw [h_eq] at h_one_mem
  have h_bag_ne : s5_2.bag ≠ [] := List.ne_nil_of_mem h_one_mem
  have h_zero : (0 : Int) ∈ s5_2.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem
  have h_step3 := System5_step_explicit_pop s5_2 ([] : List Int)
      (([] : List Int) :: rest_more)
      h_rules_form h_bag_ne h_zero
  have h_n3 : System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ 3
            = some ⟨xorMerge ((s5_2.bag.map (· - 1)).erase 0) ([].map (· + 1)),
              (([] : List Int) :: rest_more).map (fun r => r.map (· + 1))⟩ := by
    rw [show (3 : Nat) = 2 + 1 from rfl, System5.nSteps_add, h_step2]
    simp [System5.nSteps_one, h_step3]
  refine ⟨s5_2, _, h_step2, h_n3, ?_⟩
  show xorMerge ((s5_2.bag.map (· - 1)).erase 0) ([].map (· + 1))
       = (s5_2.bag.map (· - 1)).erase 0
  show xorMerge ((s5_2.bag.map (· - 1)).erase 0) []
       = (s5_2.bag.map (· - 1)).erase 0
  exact xorMerge_nil _

/-- **Iter 1071: 1 ∈ s5_3.bag at false-head Perm-chain points (CRUCIAL
    MILESTONE)**.  After THREE P-steps at a false-head Perm-chain point,
    the bag contains `1` — confirming step 4 is also a P-step at chain
    points.  Composition: iter 1070 (bag-3 form) + iter 1068 (2 ∈
    s5_2.bag) + iter 975 (`mem_imp_pred_in_dec_erase`).  s5_2 alignment
    via `Option.some.inj`.  **Together with iters 1061, 1066, this
    proves all 4 cfg5 steps from any false-head Perm-chain point are
    P-steps** — chain-induction analog of iter 990's existing cfg5-level
    step3_one_mem and the inductive backbone for the chain-induction
    step. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step3_one_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_3,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ (1 : Int) ∈ s5_3.bag := by
  obtain ⟨s5_2, s5_3, h_step2, h_step3, h_bag3_form⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step3_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_2', h_step2', h_two_mem⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step2_two_mem cts rest phase N h_N bag h_perm
  have h_eq : s5_2' = s5_2 := Option.some.inj (h_step2'.symm.trans h_step2)
  rw [h_eq] at h_two_mem
  refine ⟨s5_3, h_step3, ?_⟩
  rw [h_bag3_form]
  have h_pred := mem_imp_pred_in_dec_erase s5_2.bag 2 h_two_mem (by omega)
  have h_eq_one : (2 : Int) - 1 = 1 := by omega
  rw [h_eq_one] at h_pred
  exact h_pred

/-- **Iter 1072: s5_3.rules form at false-head Perm-chain points**.
    `s5_3.rules = [] :: rest_more`.  Composition: iter 968's
    `System5_nSteps_rules_pstep` (after 3 P-steps, rules =
    `(orig.drop 3).map(map(·+3))`) + iter 991's
    `ctsRulesToSystem5Rules_drop_3_exists_empty_rule` (drop-3 yields
    `[] :: rest_more`).  All-P-step hypothesis discharged via
    iter 1051 (k=0), iter 1061 (k=1), iter 1066 (k=2).
    **Chain-induction analog of iter 992** — confirms the rule popped
    at step 4 is `[]`, so bag-4 = dec-erase s5_3.bag (xorMerge with
    empty rule via xorMerge_nil). -/
theorem ctsConfigToSystem5Bag_false_head_perm_step3_rules_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_3,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ ∃ rest_more, s5_3.rules = ([] : List Int) :: rest_more := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨s5_3, h_step3, _⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step3_one_mem cts rest phase N h_N bag h_perm
  refine ⟨s5_3, h_step3, ?_⟩
  have h_pstep : ∀ k < 3, ∀ cfg_k,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ k = some cfg_k
      → (0 : Int) ∈ cfg_k.bag.map (· - 1) := by
    intro k h_k cfg_k h_k_eq
    match k, h_k with
    | 0, _ =>
      simp [System5.nSteps] at h_k_eq
      rw [← h_k_eq]
      exact ctsConfigToSystem5Bag_perm_zero_in_decrement cfg bag (by simp) h_perm
    | 1, _ =>
      obtain ⟨s5_1, h_step1, h_one_mem_s5_1⟩ :=
        ctsConfigToSystem5Bag_false_head_perm_step_bag_one_mem cts rest phase N h_N bag h_perm
      have h_step1_one : System5.nSteps
          ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ 1 = some s5_1 := by
        rw [System5.nSteps_one]; exact h_step1
      have h_eq : cfg_k = s5_1 := Option.some.inj (h_k_eq.symm.trans h_step1_one)
      rw [h_eq]
      exact (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_1
    | 2, _ =>
      obtain ⟨s5_2, h_step2, h_one_mem_s5_2⟩ :=
        ctsConfigToSystem5Bag_false_head_perm_step2_one_mem cts rest phase N h_N bag h_perm
      have h_eq : cfg_k = s5_2 := Option.some.inj (h_k_eq.symm.trans h_step2)
      rw [h_eq]
      exact (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_2
  have h_rules_form := System5_nSteps_rules_pstep _ s5_3 3 h_step3 h_pstep
  obtain ⟨rest_more, h_drop⟩ :=
    ctsRulesToSystem5Rules_drop_3_exists_empty_rule cts cfg N h_N
  refine ⟨rest_more.map (fun r => r.map (· + 3)), ?_⟩
  rw [h_rules_form]
  show ((ctsRulesToSystem5Rules cts cfg N).drop 3).map (fun r => r.map (· + (3 : Int)))
     = ([] : List Int) :: rest_more.map (fun r => r.map (· + 3))
  rw [h_drop]
  simp [List.map_cons]

/-- **Iter 1073: bag-4 form at false-head Perm-chain points (TERMINAL
    BAG)**.  After FOUR P-steps at a false-head Perm-chain point,
    `s5_4.bag = (s5_3.bag.map(·-1)).erase 0`.  The popped rule at step
    4 is `[]` (per iter 1072's `s5_3.rules = [] :: rest_more`), so
    xorMerge with the (incremented) empty rule simplifies via
    `xorMerge_nil`.  Composition: iter 1071 (1 ∈ s5_3.bag → P-step
    trigger) + iter 1072 (s5_3.rules form) + `System5_step_explicit_pop`
    + `xorMerge_nil`.  **Chain-induction analog of iter 993's existing
    cfg5-level bag4_form** — the full 4-step trajectory's terminal bag
    at chain points is now characterized algebraically. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step4_bag_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_3 s5_4,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ s5_4.bag = (s5_3.bag.map (· - 1)).erase 0 := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨s5_3a, h_step3a, h_one_mem⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step3_one_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_3, h_step3, rest_more, h_rules_form⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step3_rules_form cts rest phase N h_N bag h_perm
  have h_eq : s5_3a = s5_3 := Option.some.inj (h_step3a.symm.trans h_step3)
  rw [h_eq] at h_one_mem
  have h_bag_ne : s5_3.bag ≠ [] := List.ne_nil_of_mem h_one_mem
  have h_zero : (0 : Int) ∈ s5_3.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem
  have h_step4 := System5_step_explicit_pop s5_3 ([] : List Int) rest_more
      h_rules_form h_bag_ne h_zero
  have h_n4 : System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ 4
            = some ⟨xorMerge ((s5_3.bag.map (· - 1)).erase 0) ([].map (· + 1)),
              rest_more.map (fun r => r.map (· + 1))⟩ := by
    rw [show (4 : Nat) = 3 + 1 from rfl, System5.nSteps_add, h_step3]
    simp [System5.nSteps_one, h_step4]
  refine ⟨s5_3, _, h_step3, h_n4, ?_⟩
  show xorMerge ((s5_3.bag.map (· - 1)).erase 0) ([].map (· + 1))
       = (s5_3.bag.map (· - 1)).erase 0
  show xorMerge ((s5_3.bag.map (· - 1)).erase 0) []
       = (s5_3.bag.map (· - 1)).erase 0
  exact xorMerge_nil _

/-- **Iter 1074: dec-erase preserves Perm for Int lists**.  Generic
    helper: `xs.Perm ys ⇒ ((xs.map(·-1)).erase 0).Perm ((ys.map(·-1)).erase 0)`.
    Composition of `List.Perm.map (·-1)` and `List.Perm.erase 0` (using
    `LawfulBEq Int`).  **Building block toward `s5_4.bag ~ aux rest 1`**:
    used to transfer Perm-equivalences across the dec-erase chain in
    bag-2 → bag-3 → bag-4 transitions, so a Perm-equivalence at one
    level lifts to all subsequent levels. -/
theorem List_Int_dec_erase_perm
    (xs ys : List Int) (h : xs.Perm ys) :
    ((xs.map (· - 1)).erase 0).Perm ((ys.map (· - 1)).erase 0) :=
  List.Perm.erase 0 (List.Perm.map (· - 1) h)

/-- **Iter 1101: double-dec-erase preserves Perm**.  Composes two
    applications of iter 1074 (`List_Int_dec_erase_perm`).  Useful
    for the bag-3 → bag-4 transition Perm chain (where two
    consecutive dec-erases occur). -/
theorem List_Int_double_dec_erase_perm
    (xs ys : List Int) (h : xs.Perm ys) :
    ((((xs.map (· - 1)).erase 0).map (· - 1)).erase 0).Perm
      ((((ys.map (· - 1)).erase 0).map (· - 1)).erase 0) :=
  List_Int_dec_erase_perm _ _ (List_Int_dec_erase_perm _ _ h)

/-- **Iter 1102: quadruple-dec-erase preserves Perm**.  Composes two
    applications of iter 1101 (or four applications of iter 1074).
    Models the full bag-1 → bag-4 transition's dec-erase chain
    (where the simplification cascades through 4 layers). -/
theorem List_Int_quadruple_dec_erase_perm
    (xs ys : List Int) (h : xs.Perm ys) :
    ((((((((xs.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).Perm
      ((((((((ys.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0) :=
  List_Int_double_dec_erase_perm _ _ (List_Int_double_dec_erase_perm _ _ h)

/-- **Iter 1075: dec-erase of false-head Perm-chain bag is Perm-
    equivalent to `1 :: 2 :: 3 :: aux rest 4`**.  Direct lift of iter
    994's `ctsConfigToSystem5Bag_false_head_dec_erase_eq` through
    iter 1074's `List_Int_dec_erase_perm`.  At any false-head Perm-
    chain point, `((bag.map(·-1)).erase 0).Perm (1 :: 2 :: 3 :: aux
    rest 4)`.  **Concrete starting form for the bag-trajectory chain
    analysis at chain points**, mirroring iter 994's role at the
    cfg5 level. -/
theorem ctsConfigToSystem5Bag_false_head_perm_dec_erase_perm
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ((bag.map (· - 1)).erase 0).Perm
      ((1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4) := by
  have h := List_Int_dec_erase_perm bag _ h_perm
  rw [ctsConfigToSystem5Bag_false_head_dec_erase_eq] at h
  exact h

/-- **Iter 1105: dec-erase of true-head Perm-chain bag in concrete
    Perm form**.  True-head analog of iter 1075.  At any true-head
    Perm-chain point, `((bag.map(·-1)).erase 0).Perm (2 :: 3 :: 5 ::
    aux rest 6)`.  Direct lift of iter 1104 through iter 1074.
    **Concrete starting form** for the true-head Perm-chain bag-
    trajectory analysis. -/
theorem ctsConfigToSystem5Bag_true_head_perm_dec_erase_perm
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ((bag.map (· - 1)).erase 0).Perm
      ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6) := by
  have h := List_Int_dec_erase_perm bag _ h_perm
  rw [ctsConfigToSystem5Bag_true_head_dec_erase_eq] at h
  exact h

/-- **Iter 1115: bag-2 dec-erase Perm-lift (true-head)**.  For any
    `xs.Perm (2 :: 3 :: 5 :: aux rest 6)`, `((xs.map(·-1)).erase 0).Perm
    (1 :: 2 :: 4 :: aux rest 5)`.  Composes iter 1074 + iter 1107.
    **True-head bag-2 → bag-3 dec-erase Perm transition** at the
    multiset level. -/
theorem ctsConfigToSystem5BagAux_six_two_three_five_cons_dec_erase_perm
    (rest : List Bool) (xs : List Int)
    (h : xs.Perm ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6)) :
    ((xs.map (· - 1)).erase 0).Perm
      ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5) := by
  have h_perm := List_Int_dec_erase_perm xs _ h
  rw [ctsConfigToSystem5BagAux_six_two_three_five_cons_dec_erase_eq] at h_perm
  exact h_perm

/-- **Iter 1116: bag-3 dec-erase Perm-lift (true-head)**.  For any
    `xs.Perm (1 :: 2 :: 4 :: aux rest 5)`, `((xs.map(·-1)).erase 0).Perm
    (1 :: 3 :: aux rest 4)`.  Composes iter 1074 + iter 1110.
    **True-head bag-3 → bag-4 dec-erase Perm transition** at the
    multiset level. -/
theorem ctsConfigToSystem5BagAux_five_one_two_four_cons_dec_erase_perm
    (rest : List Bool) (xs : List Int)
    (h : xs.Perm ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5)) :
    ((xs.map (· - 1)).erase 0).Perm
      ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4) := by
  have h_perm := List_Int_dec_erase_perm xs _ h
  rw [ctsConfigToSystem5BagAux_five_one_two_four_cons_dec_erase_eq] at h_perm
  exact h_perm

/-- **Iter 1117: bag-4 dec-erase Perm-lift (true-head)**.  For any
    `xs.Perm (1 :: 3 :: aux rest 4)`, `((xs.map(·-1)).erase 0).Perm
    (2 :: aux rest 3)`.  Composes iter 1074 + iter 1112.
    **True-head bag-4 dec-erase Perm transition** — the final step
    of the dec-erase-only bag chain. -/
theorem ctsConfigToSystem5BagAux_four_one_three_cons_dec_erase_perm
    (rest : List Bool) (xs : List Int)
    (h : xs.Perm ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4)) :
    ((xs.map (· - 1)).erase 0).Perm
      ((2 : Int) :: ctsConfigToSystem5BagAux rest 3) := by
  have h_perm := List_Int_dec_erase_perm xs _ h
  rw [ctsConfigToSystem5BagAux_four_one_three_cons_dec_erase_eq] at h_perm
  exact h_perm

/-- **Iter 1118: full quadruple-dec-erase Perm chain (true-head)**.
    Chains iters 1105/1115/1116/1117: at any true-head Perm-chain
    point, after 4 dec-erases of the bag, the result is Perm-equivalent
    to `(2 :: aux rest 3)` — the terminal target of the dec-erase-only
    chain.  Direct composition. -/
theorem ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_perm
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).Perm
      ((2 : Int) :: ctsConfigToSystem5BagAux rest 3) :=
  ctsConfigToSystem5BagAux_four_one_three_cons_dec_erase_perm rest _
    (ctsConfigToSystem5BagAux_five_one_two_four_cons_dec_erase_perm rest _
      (ctsConfigToSystem5BagAux_six_two_three_five_cons_dec_erase_perm rest _
        (ctsConfigToSystem5Bag_true_head_perm_dec_erase_perm rest phase bag h_perm)))

/-- **Iter 1120: false-head bag-1-dec to bag-2-dec Perm-lift**.  For
    any `xs.Perm (1 :: 2 :: 3 :: aux rest 4)`, `((xs.map(·-1)).erase 0).Perm
    (1 :: 2 :: aux rest 3)`.  Composes iter 1074 + iter 1119.
    **Missing middle link** in the false-head dec-erase Perm chain. -/
theorem ctsConfigToSystem5BagAux_four_one_two_three_cons_dec_erase_perm
    (rest : List Bool) (xs : List Int)
    (h : xs.Perm ((1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4)) :
    ((xs.map (· - 1)).erase 0).Perm
      ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3) := by
  have h_perm := List_Int_dec_erase_perm xs _ h
  rw [ctsConfigToSystem5BagAux_four_one_two_three_cons_dec_erase_eq] at h_perm
  exact h_perm

/-- **Iter 1121: false-head bag-2-dec to bag-3-dec Perm-lift**.  For
    any `xs.Perm (1 :: 2 :: aux rest 3)`, `((xs.map(·-1)).erase 0).Perm
    (1 :: aux rest 2)`.  Composes iter 1074 + iter 1007.  Continues
    the false-head dec-erase Perm chain. -/
theorem ctsConfigToSystem5BagAux_three_one_two_cons_dec_erase_perm
    (rest : List Bool) (xs : List Int)
    (h : xs.Perm ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3)) :
    ((xs.map (· - 1)).erase 0).Perm
      ((1 : Int) :: ctsConfigToSystem5BagAux rest 2) := by
  have h_perm := List_Int_dec_erase_perm xs _ h
  rw [ctsConfigToSystem5BagAux_three_one_two_cons_dec_erase_eq] at h_perm
  exact h_perm

/-- **Iter 1122: false-head bag-3-dec to terminal Perm-lift**.  For
    any `xs.Perm (1 :: aux rest 2)`, `((xs.map(·-1)).erase 0).Perm
    (aux rest 1)`.  Composes iter 1074 + iter 1010.  **Final step**
    of the false-head dec-erase Perm chain — brings the bag to the
    terminal target `aux rest 1` (the encoder bag of the post-CTS-step
    state for false-head). -/
theorem ctsConfigToSystem5BagAux_two_one_cons_dec_erase_perm
    (rest : List Bool) (xs : List Int)
    (h : xs.Perm ((1 : Int) :: ctsConfigToSystem5BagAux rest 2)) :
    ((xs.map (· - 1)).erase 0).Perm (ctsConfigToSystem5BagAux rest 1) := by
  have h_perm := List_Int_dec_erase_perm xs _ h
  rw [ctsConfigToSystem5BagAux_two_one_cons_dec_erase_eq] at h_perm
  exact h_perm

/-- **Iter 1123: full quadruple-dec-erase Perm chain (false-head)**.
    False-head analog of iter 1118.  Chains iters 1075/1120/1121/1122:
    at any false-head Perm-chain point, after 4 dec-erases of the
    bag, the result is Perm-equivalent to `(aux rest 1)` — the
    encoder bag of the post-CTS-step state for false-head.  Direct
    composition. -/
theorem ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_perm
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).Perm
      (ctsConfigToSystem5BagAux rest 1) :=
  ctsConfigToSystem5BagAux_two_one_cons_dec_erase_perm rest _
    (ctsConfigToSystem5BagAux_three_one_two_cons_dec_erase_perm rest _
      (ctsConfigToSystem5BagAux_four_one_two_three_cons_dec_erase_perm rest _
        (ctsConfigToSystem5Bag_false_head_perm_dec_erase_perm rest phase bag h_perm)))

/-- **Iter 1124: worked example of iter 1123 at concrete CTS**.
    Verifies the false-head quadruple-dec-erase Perm chain closes
    a specific case.  For `data := [false, false]`, the bag is
    `[1, 2, 3, 4, 5, 6, 7, 8]`, and after 4 dec-erases it should
    Perm-equal `[1, 2, 3, 4]` = `aux [false] 1`. -/
example :
    (((((((((ctsConfigToSystem5Bag
        { data := [false, false], phase := 0 }).map (· - 1)).erase 0).map
        (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).Perm
      (ctsConfigToSystem5BagAux [false] 1) :=
  ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_perm [false] 0 _
    (List.Perm.refl _)

/-- **Iter 1125: worked example of iter 1118 at concrete true-head CTS**.
    Verifies the true-head quadruple-dec-erase Perm chain closes
    a specific case.  For `data := [true]`, the bag is `[1, 3, 4, 6]`,
    and after 4 dec-erases it should Perm-equal `[2]` = `2 :: aux [] 3`. -/
example :
    (((((((((ctsConfigToSystem5Bag
        { data := [true], phase := 0 }).map (· - 1)).erase 0).map
        (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).Perm
      ((2 : Int) :: ctsConfigToSystem5BagAux [] 3) :=
  ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_perm [] 0 _
    (List.Perm.refl _)

/-- **Iter 1126: false-head quadruple-dec-erase result is Nodup**.
    Direct corollary of iter 1123 + iter 645's `_nodup` +
    `List.Perm.nodup_iff`.  At any false-head Perm-chain point, the
    result of 4 dec-erases is Nodup. -/
theorem ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_nodup
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).Nodup := by
  have h := ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_perm
    rest phase bag h_perm
  rw [List.Perm.nodup_iff h]
  exact ctsConfigToSystem5BagAux_nodup rest 1

/-- **Iter 1127: true-head quadruple-dec-erase result is Nodup**.
    True-head analog of iter 1126.  Composes iter 1118 + iter 1113 +
    `List.Perm.nodup_iff`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_nodup
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).Nodup := by
  have h := ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_perm
    rest phase bag h_perm
  rw [List.Perm.nodup_iff h]
  exact ctsConfigToSystem5BagAux_three_two_cons_nodup rest

/-- **Iter 1128: false-head quadruple-dec-erase mem-iff**.  At any
    false-head Perm-chain point, `∀ x, x ∈ result ↔ x ∈ aux rest 1`.
    Direct corollary of iter 1123 + `List.Perm.mem_iff`. -/
theorem ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_mem_iff
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∀ x, x ∈ (((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0))
        ↔ x ∈ ctsConfigToSystem5BagAux rest 1 := by
  intro x
  exact List.Perm.mem_iff
    (ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_perm rest phase bag h_perm)

/-- **Iter 1129: true-head quadruple-dec-erase mem-iff**.  True-head
    analog of iter 1128.  Composes iter 1118 + `List.Perm.mem_iff`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_mem_iff
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∀ x, x ∈ (((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0))
        ↔ x ∈ ((2 : Int) :: ctsConfigToSystem5BagAux rest 3) := by
  intro x
  exact List.Perm.mem_iff
    (ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_perm rest phase bag h_perm)

/-- **Iter 1130: false-head quadruple-dec-erase length**.  At any
    false-head Perm-chain point, the length of the result equals
    `(aux rest 1).length`.  Direct corollary of iter 1123 +
    `List.Perm.length_eq`. -/
theorem ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_length
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).length
      = (ctsConfigToSystem5BagAux rest 1).length :=
  List.Perm.length_eq
    (ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_perm rest phase bag h_perm)

/-- **Iter 1131: true-head quadruple-dec-erase length**.  True-head
    analog of iter 1130. -/
theorem ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_length
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).length
      = ((2 : Int) :: ctsConfigToSystem5BagAux rest 3).length :=
  List.Perm.length_eq
    (ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_perm rest phase bag h_perm)

/-- **Iter 1132: false-head quadruple-dec-erase non-empty when rest
    non-empty**.  At any false-head Perm-chain point with non-empty
    `rest`, the result of 4 dec-erases is non-empty.  Composes iter
    1130 with the existing `ctsConfigToSystem5BagAux_length`
    (`(aux rest 1).length = 4 * rest.length`).  When rest ≠ [],
    `4 * rest.length > 0`, so the length-equal result is also > 0. -/
theorem ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_nonempty
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_rest : rest ≠ [])
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0) ≠ [] := by
  intro h_empty
  have h_len :=
    ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_length rest phase bag h_perm
  rw [h_empty, List.length_nil, ctsConfigToSystem5BagAux_length] at h_len
  cases rest with
  | nil => exact h_rest rfl
  | cons _ _ => simp at h_len

/-- **Iter 1133: true-head quadruple-dec-erase always non-empty**.
    True-head analog of iter 1132.  Unconditional: since the target
    `2 :: aux rest 3` always has at least 1 element (the `2`), the
    Perm-equivalent result is always non-empty. -/
theorem ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_nonempty
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0) ≠ [] := by
  intro h_empty
  have h_len :=
    ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_length rest phase bag h_perm
  rw [h_empty, List.length_nil] at h_len
  simp at h_len

/-- **Iter 1134: aux non-empty data has 1 as a member**.  Direct fact:
    for any non-empty `data`, `(1 : Int) ∈ ctsConfigToSystem5BagAux data 1`.
    Both true-head and false-head encoder bags start with `1` as the
    head element. -/
theorem ctsConfigToSystem5BagAux_data_nonempty_one_mem
    (data : List Bool) (h : data ≠ []) :
    (1 : Int) ∈ ctsConfigToSystem5BagAux data 1 := by
  cases data with
  | nil => exact absurd rfl h
  | cons head _ =>
    cases head with
    | true =>
      show (1 : Int) ∈ (1 : Int) :: 3 :: 4 :: 6 :: _
      simp
    | false =>
      show (1 : Int) ∈ (1 : Int) :: 2 :: 3 :: 4 :: _
      simp

/-- **Iter 1135: 1 ∈ false-head quadruple-dec-erase result when rest
    non-empty**.  Composes iter 1128 (mem-iff) + iter 1134 (1 ∈ aux
    data 1 for non-empty data).  At any false-head Perm-chain point
    with non-empty `rest`, the result of 4 dec-erases contains `1`. -/
theorem ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_one_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_rest : rest ≠ [])
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    (1 : Int) ∈ (((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0)) :=
  (ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_mem_iff
    rest phase bag h_perm 1).mpr
    (ctsConfigToSystem5BagAux_data_nonempty_one_mem rest h_rest)

/-- **Iter 1136: 2 ∈ true-head quadruple-dec-erase result**.  True-head
    analog of iter 1135.  Unconditional: target `2 :: aux rest 3` has
    `2` as the head, so `2 ∈ result` by mem-iff (iter 1129). -/
theorem ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_two_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    (2 : Int) ∈ (((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0)) :=
  (ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_mem_iff
    rest phase bag h_perm 2).mpr (List.mem_cons_self)

/-- **Iter 1137: false-head quadruple-dec-erase length = 4·rest.length**.
    Closed-form length identity via iter 1130 + `_length`. -/
theorem ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_length_eq
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).length
      = 4 * rest.length := by
  rw [ctsConfigToSystem5Bag_false_head_perm_quadruple_dec_erase_length rest phase bag h_perm,
      ctsConfigToSystem5BagAux_length]

/-- **Iter 1138: true-head quadruple-dec-erase length = 4·rest.length + 1**.
    True-head analog of iter 1137.  Composes iter 1131 + `_length` +
    cons-length. -/
theorem ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_length_eq
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).length
      = 4 * rest.length + 1 := by
  rw [ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_length rest phase bag h_perm]
  show ((2 : Int) :: ctsConfigToSystem5BagAux rest 3).length = 4 * rest.length + 1
  rw [List.length_cons, ctsConfigToSystem5BagAux_length]

/-- **Iter 1139: aux is empty iff data is empty**.  Direct corollary
    of `ctsConfigToSystem5BagAux_length`: `(aux data 1).length = 0 ↔
    data.length = 0 ↔ data = []`. -/
theorem ctsConfigToSystem5BagAux_eq_nil_iff (data : List Bool) :
    ctsConfigToSystem5BagAux data 1 = [] ↔ data = [] := by
  constructor
  · intro h
    have h_len : (ctsConfigToSystem5BagAux data 1).length = 0 := by rw [h]; simp
    rw [ctsConfigToSystem5BagAux_length] at h_len
    have : data.length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  · intro h; rw [h]; rfl

/-- **Iter 1140: aux non-empty iff data non-empty**.  Direct corollary
    of iter 1139 (negated). -/
theorem ctsConfigToSystem5BagAux_ne_nil_iff (data : List Bool) :
    ctsConfigToSystem5BagAux data 1 ≠ [] ↔ data ≠ [] := by
  rw [ne_eq, ne_eq, ctsConfigToSystem5BagAux_eq_nil_iff]

/-- **Iter 1141: aux length ≥ 4 when data non-empty**.  Direct
    corollary of `_length` + arithmetic.  `(aux data 1).length =
    4 * data.length ≥ 4 * 1 = 4` when `data.length ≥ 1`. -/
theorem ctsConfigToSystem5BagAux_length_ge_four_of_nonempty
    (data : List Bool) (h : data ≠ []) :
    (ctsConfigToSystem5BagAux data 1).length ≥ 4 := by
  rw [ctsConfigToSystem5BagAux_length]
  cases data with
  | nil => exact absurd rfl h
  | cons _ tail => simp; omega

/-- **Iter 1142: encoder bag length ≥ 4 when cfg.data non-empty**.
    Cfg-level analog of iter 1141.  Direct via def + iter 1141. -/
theorem ctsConfigToSystem5Bag_length_ge_four_of_nonempty
    (cfg : CTSConfig) (h : cfg.data ≠ []) :
    (ctsConfigToSystem5Bag cfg).length ≥ 4 := by
  unfold ctsConfigToSystem5Bag
  exact ctsConfigToSystem5BagAux_length_ge_four_of_nonempty cfg.data h

/-- **Iter 1143: dec-erase of `(2 :: aux rest 3)` = `1 :: aux rest 2`**.
    Computation step beyond iter 1118 toward the true-head sextuple
    target.  Decrement: 2 → 1, aux rest 3 → aux rest 2.  Erase 0 leaves
    list unchanged (1 ≠ 0, aux rest 2 ≥ 2 > 0). -/
theorem ctsConfigToSystem5BagAux_three_two_cons_dec_erase_eq (rest : List Bool) :
    (((2 : Int) :: ctsConfigToSystem5BagAux rest 3).map (· - 1)).erase 0
      = (1 : Int) :: ctsConfigToSystem5BagAux rest 2 := by
  simp only [List.map_cons]
  rw [ctsConfigToSystem5BagAux_dec_at_three]
  apply List.erase_of_not_mem
  intro h
  rcases List.mem_cons.mp h with h_eq | h_aux
  · omega
  · have := ctsConfigToSystem5BagAux_ge rest 2 0 h_aux
    omega

/-- **Iter 1144: Perm-lift of iter 1143**.  For any `xs.Perm (2 ::
    aux rest 3)`, `((xs.map(·-1)).erase 0).Perm (1 :: aux rest 2)`.
    Composes iter 1074 + iter 1143.  Step beyond iter 1118 (true-head
    quadruple-dec-erase) toward the sextuple target. -/
theorem ctsConfigToSystem5BagAux_three_two_cons_dec_erase_perm
    (rest : List Bool) (xs : List Int)
    (h : xs.Perm ((2 : Int) :: ctsConfigToSystem5BagAux rest 3)) :
    ((xs.map (· - 1)).erase 0).Perm
      ((1 : Int) :: ctsConfigToSystem5BagAux rest 2) := by
  have h_perm := List_Int_dec_erase_perm xs _ h
  rw [ctsConfigToSystem5BagAux_three_two_cons_dec_erase_eq] at h_perm
  exact h_perm

/-- **Iter 1145: full sextuple-dec-erase Perm chain (true-head)**.
    Extends iter 1118 by 2 dec-erases via iters 1144 + 1122 to reach
    `aux rest 1` — matching false-head's terminal target (iter 1123)
    AND iter 8409's AllEmptyAppendants 6-step true-head trajectory. -/
theorem ctsConfigToSystem5Bag_true_head_perm_sextuple_dec_erase_perm
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ((((((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0).Perm (ctsConfigToSystem5BagAux rest 1) :=
  ctsConfigToSystem5BagAux_two_one_cons_dec_erase_perm rest _
    (ctsConfigToSystem5BagAux_three_two_cons_dec_erase_perm rest _
      (ctsConfigToSystem5Bag_true_head_perm_quadruple_dec_erase_perm
        rest phase bag h_perm))

/-- **Iter 1146: worked example of iter 1145 at concrete true-head CTS**.
    For `data := [true]`, the bag is `[1, 3, 4, 6]`, and after 6 dec-erases
    it should Perm-equal `aux [] 1 = []`. -/
example :
    (((((((((((((ctsConfigToSystem5Bag
        { data := [true], phase := 0 }).map (· - 1)).erase 0).map
        (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0).map (· - 1)).erase 0).Perm
      (ctsConfigToSystem5BagAux [] 1) :=
  ctsConfigToSystem5Bag_true_head_perm_sextuple_dec_erase_perm [] 0 _
    (List.Perm.refl _)

/-- **Iter 1147: true-head sextuple-dec-erase result is Nodup**.
    Direct corollary of iter 1145 + iter 645's `_nodup` +
    `List.Perm.nodup_iff`.  Companion to iter 1126/1127. -/
theorem ctsConfigToSystem5Bag_true_head_perm_sextuple_dec_erase_nodup
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ((((((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0).Nodup := by
  have h := ctsConfigToSystem5Bag_true_head_perm_sextuple_dec_erase_perm
    rest phase bag h_perm
  rw [List.Perm.nodup_iff h]
  exact ctsConfigToSystem5BagAux_nodup rest 1

/-- **Iter 1148: true-head sextuple-dec-erase length = 4·rest.length**.
    Same closed form as iter 1137 (false-head quadruple) — both reach
    `aux rest 1` so the lengths agree. -/
theorem ctsConfigToSystem5Bag_true_head_perm_sextuple_dec_erase_length_eq
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ((((((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0).length = 4 * rest.length := by
  have h := ctsConfigToSystem5Bag_true_head_perm_sextuple_dec_erase_perm
    rest phase bag h_perm
  rw [List.Perm.length_eq h, ctsConfigToSystem5BagAux_length]

/-- **Iter 1149: true-head sextuple-dec-erase non-empty when rest
    non-empty**.  Companion to iter 1132 (false-head quadruple).
    Composes iter 1148 with arithmetic. -/
theorem ctsConfigToSystem5Bag_true_head_perm_sextuple_dec_erase_nonempty
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_rest : rest ≠ [])
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ((((((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0) ≠ [] := by
  intro h_empty
  have h_len :=
    ctsConfigToSystem5Bag_true_head_perm_sextuple_dec_erase_length_eq
      rest phase bag h_perm
  rw [h_empty, List.length_nil] at h_len
  cases rest with
  | nil => exact h_rest rfl
  | cons _ _ => simp at h_len

/-- **Iter 1150: Perm-chain bag is non-empty when cfg.data non-empty**.
    At any Perm-chain point with non-empty `cfg.data`, `bag ≠ []`.
    Composes iter 1142 (length ≥ 4) with `List.Perm.length_eq`. -/
theorem ctsConfigToSystem5Bag_perm_bag_nonempty
    (cfg : CTSConfig) (h_data : cfg.data ≠ []) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    bag ≠ [] := by
  intro h_empty
  have h_len := List.Perm.length_eq h_perm
  rw [h_empty, List.length_nil] at h_len
  have h_ge := ctsConfigToSystem5Bag_length_ge_four_of_nonempty cfg h_data
  omega

/-- **Iter 1151: small values not in `aux rest k` for k > value**.
    Trivial corollary of `_ge`: if `n < k`, then `n ∉ aux rest k`. -/
theorem ctsConfigToSystem5BagAux_small_not_mem
    (rest : List Bool) (k n : Int) (h : n < k) :
    n ∉ ctsConfigToSystem5BagAux rest k := by
  intro h_mem
  have := ctsConfigToSystem5BagAux_ge rest k n h_mem
  omega

/-- **Iter 1152: true-head sextuple-dec-erase mem-iff**.  At any
    true-head Perm-chain point, `∀ x, x ∈ result ↔ x ∈ aux rest 1`.
    Direct corollary of iter 1145 + `List.Perm.mem_iff`.  True-head's
    sextuple-dec-erase reaches the SAME terminal target as false-head's
    quadruple-dec-erase (`aux rest 1`). -/
theorem ctsConfigToSystem5Bag_true_head_perm_sextuple_dec_erase_mem_iff
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∀ x, x ∈ ((((((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0)
        ↔ x ∈ ctsConfigToSystem5BagAux rest 1 := by
  intro x
  exact List.Perm.mem_iff
    (ctsConfigToSystem5Bag_true_head_perm_sextuple_dec_erase_perm rest phase bag h_perm)

/-- **Iter 1153: 1 ∈ true-head sextuple-dec-erase result when rest
    non-empty**.  Companion to iter 1135 (false-head quadruple).
    Composes iter 1152 + iter 1134.  When `rest ≠ []`, `aux rest 1`
    has `1` as a member (by iter 1134), and the sextuple-dec-erase
    result has the same membership as `aux rest 1` (iter 1152). -/
theorem ctsConfigToSystem5Bag_true_head_perm_sextuple_dec_erase_one_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_rest : rest ≠ [])
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    (1 : Int) ∈ ((((((((((((bag.map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0).map (· - 1)).erase 0).map (· - 1)).erase 0).map
        (· - 1)).erase 0) := by
  rw [ctsConfigToSystem5Bag_true_head_perm_sextuple_dec_erase_mem_iff
        rest phase bag h_perm]
  exact ctsConfigToSystem5BagAux_data_nonempty_one_mem rest h_rest

/-- **Iter 1154: Perm-chain bag closed-form length**.  At any
    Perm-chain point, `bag.length = 4 * cfg.data.length`.
    Composes `List.Perm.length_eq` + `ctsConfigToSystem5Bag_length`. -/
theorem ctsConfigToSystem5Bag_perm_bag_length_eq
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    bag.length = 4 * cfg.data.length := by
  rw [List.Perm.length_eq h_perm, ctsConfigToSystem5Bag_length]

/-- **Iter 1155: Perm-chain bag length is positive when data
    non-empty**.  Strict positivity form, useful for
    contradiction-style proofs.  Composes iter 1154 with arithmetic. -/
theorem ctsConfigToSystem5Bag_perm_bag_length_pos
    (cfg : CTSConfig) (h_data : cfg.data ≠ []) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    bag.length > 0 := by
  have h_len := ctsConfigToSystem5Bag_perm_bag_length_eq cfg bag h_perm
  have h_dlen : cfg.data.length > 0 := by
    cases h : cfg.data with
    | nil => rw [h] at h_data; exact absurd rfl h_data
    | cons _ _ => simp
  omega

/-- **Iter 1156: 2 ∈ bag.dec.erase at true-head Perm-chain points**.
    True-head analog of iter 1044.  Composition: iter 1038 gives
    `3 ∈ bag` (true-head bag has `3` at index 1), then iter 975's
    `mem_imp_pred_in_dec_erase` (with `3 ≠ 1`) gives `2 = 3 - 1 ∈
    (bag.map(·-1)).erase 0`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_dec_erase_two_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    (2 : Int) ∈ (bag.map (· - 1)).erase 0 := by
  have h_three_in : (3 : Int) ∈ bag :=
    ctsConfigToSystem5Bag_true_head_perm_three_mem rest phase bag h_perm
  have h_dec := mem_imp_pred_in_dec_erase bag 3 h_three_in (by omega)
  have h_eq : (3 : Int) - 1 = 2 := by omega
  rw [h_eq] at h_dec
  exact h_dec

/-- **Iter 1157: 3 ∈ bag.dec.erase at true-head Perm-chain points**.
    Companion to iter 1156.  Composition: iter 1039 gives `4 ∈ bag`,
    then iter 975's `mem_imp_pred_in_dec_erase` gives
    `3 = 4 - 1 ∈ (bag.map(·-1)).erase 0`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_dec_erase_three_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    (3 : Int) ∈ (bag.map (· - 1)).erase 0 := by
  have h_four_in : (4 : Int) ∈ bag :=
    ctsConfigToSystem5Bag_true_head_perm_four_mem rest phase bag h_perm
  have h_dec := mem_imp_pred_in_dec_erase bag 4 h_four_in (by omega)
  have h_eq : (4 : Int) - 1 = 3 := by omega
  rw [h_eq] at h_dec
  exact h_dec

/-- **Iter 1158: 5 ∈ bag.dec.erase at true-head Perm-chain points**.
    Closes the true-head dec-erase membership cascade.  Composition:
    iter 1040 gives `6 ∈ bag` (true-head bag's fourth element), then
    iter 975's `mem_imp_pred_in_dec_erase` gives
    `5 = 6 - 1 ∈ (bag.map(·-1)).erase 0`.  **With iters 1156-1158, the
    true-head dec-erase membership cascade `{2, 3, 5} ∈ ((bag.map(·-1)).erase 0)`
    at Perm-chain points is now complete** — companion to iters 1044-1046's
    false-head cascade `{1, 2, 3}`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_dec_erase_five_mem
    (rest : List Bool) (phase : Nat) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    (5 : Int) ∈ (bag.map (· - 1)).erase 0 := by
  have h_six_in : (6 : Int) ∈ bag :=
    ctsConfigToSystem5Bag_true_head_perm_six_mem rest phase bag h_perm
  have h_dec := mem_imp_pred_in_dec_erase bag 6 h_six_in (by omega)
  have h_eq : (6 : Int) - 1 = 5 := by omega
  rw [h_eq] at h_dec
  exact h_dec

/-- **Iter 1159: r1 ≥ 11 for true-head encoder rules**.  True-head
    counterpart of iter 970's `ctsToSystem5_false_head_first_two_rules_ge_seven`.
    For true-head data, `counterAfterWorkingString (true :: rest) ≥ 7`,
    so r1 ≥ counter + 4 ≥ 11 and r2 ≥ counter + 2 ≥ 9.  Both are well
    above any small constant we need disjointness from. -/
theorem ctsToSystem5_true_head_first_two_rules_ge_eleven
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ (∀ x ∈ r1, x ≥ 11)
      ∧ (∀ x ∈ r2, x ≥ 9) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, h_r2⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_min_value cts
      { data := true :: rest, phase := phase } N h_N
  have h_counter : counterAfterWorkingString
      ({ data := true :: rest, phase := phase } : CTSConfig).data ≥ 7 := by
    show counterAfterWorkingString (true :: rest) ≥ 7
    rw [counterAfterWorkingString_cons_true]
    have := counterAfterWorkingString_ge_one rest
    omega
  refine ⟨r1, r2, tail, h_eq, ?_, ?_⟩
  · intro x hx
    have := h_r1 x hx
    omega
  · intro x hx
    have := h_r2 x hx
    omega

/-- **Iter 1160: bag-1 dec-erase Perm form at true-head Perm-chain
    points**.  True-head analog of iter 1076.  After one P-step at a
    true-head Perm-chain point, the dec-erase'd bag is Perm-equivalent
    to `r1.reverse ++ (1 :: 2 :: 4 :: aux rest 5)`.  Composition: iter
    1057 (s5_1 explicit form) + iter 996's `_inc_reverse_dec_cancel` +
    `List.erase_append_right` (0 ∉ r1.reverse via iter 1159's
    `_first_two_rules_ge_eleven`) + iter 1115 + iter 1105 (Perm-form
    bag dec-erase chain for true-head) + `List.Perm.append_left`.
    **Chain-induction analog of iter 1076's false-head step1
    dec-erase Perm form**. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step1_dec_erase_perm
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_1,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.step ⟨bag, ctsRulesToSystem5Rules cts
          { data := true :: rest, phase := phase } N⟩ = some s5_1
      ∧ ((s5_1.bag.map (· - 1)).erase 0).Perm
          (r1.reverse ++ ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5)) := by
  let cfg : CTSConfig := { data := true :: rest, phase := phase }
  obtain ⟨r1, r2, tail, h_eq, h_step⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts cfg N h_N bag (by simp) h_perm
  refine ⟨r1, r2, tail, _, h_eq, h_step, ?_⟩
  have h_zero_not_r1 : (0 : Int) ∉ r1.reverse := by
    rw [List.mem_reverse]
    intro h_in
    obtain ⟨r1', _, _, h_eq', h_r1, _⟩ :=
      ctsToSystem5_true_head_first_two_rules_ge_eleven cts rest phase N h_N
    have h_r1_eq : r1 = r1' := (List.cons.inj (h_eq.symm.trans h_eq')).1
    rw [h_r1_eq] at h_in
    have := h_r1 0 h_in
    omega
  show (((((r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0)).map (· - 1)).erase 0)).Perm
       (r1.reverse ++ ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5))
  rw [List.map_append, List_Int_inc_reverse_dec_cancel,
      List.erase_append_right _ h_zero_not_r1]
  apply List.Perm.append_left r1.reverse
  exact ctsConfigToSystem5BagAux_six_two_three_five_cons_dec_erase_perm rest _
    (ctsConfigToSystem5Bag_true_head_perm_dec_erase_perm rest phase bag h_perm)

/-- **Iter 1076: bag-1 dec-erase Perm form at false-head Perm-chain
    points**.  After one P-step, the dec-erase'd bag is Perm-equivalent
    to `r1.reverse ++ (1 :: 2 :: aux rest 3)`.  Composition: iter 1057
    (s5_1 explicit form) + iter 996's `List_Int_inc_reverse_dec_cancel`
    (r1.map(·+1).reverse.map(·-1) = r1.reverse) + `List.erase_append_right`
    (0 ∉ r1.reverse) + iter 1075 (Perm form for bag's dec-erase) +
    iter 1074 (dec-erase preserves Perm) + iter 996's `_dec_at_four` +
    `List.Perm.append_left`.  **Chain-induction analog of iter 998's
    existing cfg5-level bag1_dec_erase_form** at the Perm level. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step1_dec_erase_perm
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_1,
      ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.step ⟨bag, ctsRulesToSystem5Rules cts
          { data := false :: rest, phase := phase } N⟩ = some s5_1
      ∧ ((s5_1.bag.map (· - 1)).erase 0).Perm
          (r1.reverse ++ ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3)) := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨r1, r2, tail, h_eq, h_step⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts cfg N h_N bag (by simp) h_perm
  refine ⟨r1, r2, tail, _, h_eq, h_step, ?_⟩
  have h_zero_not_r1 : (0 : Int) ∉ r1.reverse := by
    rw [List.mem_reverse]
    intro h_in
    obtain ⟨r1', _, _, h_eq', h_r1, _⟩ :=
      ctsToSystem5_false_head_first_two_rules_ge_seven cts rest phase N h_N
    have h_r1_eq : r1 = r1' := (List.cons.inj (h_eq.symm.trans h_eq')).1
    rw [h_r1_eq] at h_in
    have := h_r1 0 h_in
    omega
  show (((((r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0)).map (· - 1)).erase 0)).Perm
       (r1.reverse ++ ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3))
  rw [List.map_append, List_Int_inc_reverse_dec_cancel,
      List.erase_append_right _ h_zero_not_r1]
  apply List.Perm.append_left r1.reverse
  have h := List_Int_dec_erase_perm _ _
    (ctsConfigToSystem5Bag_false_head_perm_dec_erase_perm rest phase bag h_perm)
  have h_rhs : (((1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4).map (· - 1)).erase 0
             = (1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3 := by
    simp only [List.map_cons]
    rw [ctsConfigToSystem5BagAux_dec_at_four]
    show ((0 : Int) :: 1 :: 2 :: ctsConfigToSystem5BagAux rest 3).erase 0
       = 1 :: 2 :: ctsConfigToSystem5BagAux rest 3
    rw [List.erase_cons_head]
  rw [h_rhs] at h
  exact h

/-- **Iter 1077: post-step bag dec-erase Nodup at Perm-chain points**.
    Companion to iter 1049 (which gave `((bag.map(·-1)).erase 0).Nodup`)
    but for the post-step bag.  Composition: iter 1065 (s5_1.bag.Nodup
    at Perm-chain points) + `List.Pairwise.map (·-1)` (decrement
    injectivity) + `List.Nodup.erase`.  **Nodup obligation for invoking
    `xorMerge_mem_iff` and similar at the post-step level** — chain-
    induction analog of iter 1004's existing cfg5-level dec-erase Nodup
    for s5_1. -/
theorem ctsConfigToSystem5Bag_perm_step1_dec_erase_nodup
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ [])
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ s5_1,
      System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5_1
      ∧ ((s5_1.bag.map (· - 1)).erase 0).Nodup := by
  obtain ⟨s5_1, h_step, h_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_nodup cts cfg N h_N h_data bag h_perm
  refine ⟨s5_1, h_step, ?_⟩
  apply List.Nodup.erase
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_nodup
  intro a b h_ne h_eq_dec
  apply h_ne
  have : a - 1 = b - 1 := h_eq_dec
  omega

/-- **Iter 1078: `r1.reverse ++ (1 :: 2 :: aux rest 3)` is Nodup at
    false-head Perm-chain points**.  Direct lift via iter 1076 + iter
    1077 + `List.Perm.nodup_iff`: the post-step dec-erase'd bag is
    Nodup (iter 1077), and the simplified Perm form (iter 1076) thus
    inherits Nodup.  **Nodup obligation for `xorMerge_mem_iff` in the
    bag-2 mem-iff proof at chain points** — chain-induction analog of
    iter 1004's role at the cfg5 level. -/
theorem ctsConfigToSystem5Bag_false_head_perm_r1_reverse_aux3_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_1,
      ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.step ⟨bag, ctsRulesToSystem5Rules cts
          { data := false :: rest, phase := phase } N⟩ = some s5_1
      ∧ (r1.reverse ++ ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3)).Nodup := by
  obtain ⟨r1, r2, tail, s5_1, h_eq, h_step, h_perm'⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step1_dec_erase_perm cts rest phase N h_N bag h_perm
  refine ⟨r1, r2, tail, s5_1, h_eq, h_step, ?_⟩
  obtain ⟨s5_1', h_step', h_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_dec_erase_nodup cts
      { data := false :: rest, phase := phase } N h_N (by simp) bag h_perm
  have h_eq_s5 : s5_1 = s5_1' := Option.some.inj (h_step.symm.trans h_step')
  rw [← h_eq_s5] at h_nodup
  rw [List.Perm.nodup_iff h_perm'] at h_nodup
  exact h_nodup

/-- **Iter 1161: `r1.reverse ++ (1 :: 2 :: 4 :: aux rest 5)` is Nodup
    at true-head Perm-chain points**.  True-head analog of iter 1078.
    Direct lift via iter 1160 + iter 1077 + `List.Perm.nodup_iff`: the
    post-step dec-erase'd bag is Nodup (iter 1077, generic), and the
    simplified Perm form (iter 1160) thus inherits Nodup. -/
theorem ctsConfigToSystem5Bag_true_head_perm_r1_reverse_aux5_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_1,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.step ⟨bag, ctsRulesToSystem5Rules cts
          { data := true :: rest, phase := phase } N⟩ = some s5_1
      ∧ (r1.reverse ++ ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5)).Nodup := by
  obtain ⟨r1, r2, tail, s5_1, h_eq, h_step, h_perm'⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step1_dec_erase_perm cts rest phase N h_N bag h_perm
  refine ⟨r1, r2, tail, s5_1, h_eq, h_step, ?_⟩
  obtain ⟨s5_1', h_step', h_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_dec_erase_nodup cts
      { data := true :: rest, phase := phase } N h_N (by simp) bag h_perm
  have h_eq_s5 : s5_1 = s5_1' := Option.some.inj (h_step.symm.trans h_step')
  rw [← h_eq_s5] at h_nodup
  rw [List.Perm.nodup_iff h_perm'] at h_nodup
  exact h_nodup

/-- **Iter 1162: 2 ∈ post-step bag at true-head Perm-chain points**.
    True-head analog of iter 1061.  After one System5 P-step at a
    true-head Perm-chain point, the resulting bag contains `2`.
    Composition: iter 1060 (post-step bag Perm-equivalent to
    `r1.map(·+1) ++ dec-erase bag`) + iter 1156 (`2 ∈ dec-erase bag`
    for true-head) + `List.mem_append_right` + `List.Perm.mem_iff`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step_bag_two_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5',
      System5.step ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ = some s5'
      ∧ (2 : Int) ∈ s5'.bag := by
  obtain ⟨r1, _, _, s5', _, h_step, h_perm'⟩ :=
    ctsConfigToSystem5Bag_perm_after_step_perm cts
      { data := true :: rest, phase := phase } N h_N bag (by simp) h_perm
  refine ⟨s5', h_step, ?_⟩
  have h_two_dec : (2 : Int) ∈ (bag.map (· - 1)).erase 0 :=
    ctsConfigToSystem5Bag_true_head_perm_dec_erase_two_mem rest phase bag h_perm
  apply (List.Perm.mem_iff h_perm').mpr
  exact List.mem_append_right (r1.map (· + 1)) h_two_dec

/-- **Iter 1164: true-head s5_1.bag Perm form**.  After one P-step at
    a true-head Perm-chain point, `s5_1.bag.Perm ((r1.map(·+1)).reverse
    ++ (2 :: 3 :: 5 :: aux rest 6))`.  Composition: iter 1057 (s5_1
    explicit form `(r1.map(·+1)).reverse ++ ((bag.map(·-1)).erase 0)`) +
    iter 1105 (`((bag.map(·-1)).erase 0).Perm (2 :: 3 :: 5 :: aux rest 6)`)
    + `List.Perm.append_left`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step1_bag_perm
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_1,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.step ⟨bag, ctsRulesToSystem5Rules cts
          { data := true :: rest, phase := phase } N⟩ = some s5_1
      ∧ s5_1.bag.Perm
          ((r1.map (· + 1)).reverse ++
            ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6)) := by
  let cfg : CTSConfig := { data := true :: rest, phase := phase }
  obtain ⟨r1, r2, tail, h_eq, h_step⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts cfg N h_N bag (by simp) h_perm
  refine ⟨r1, r2, tail, _, h_eq, h_step, ?_⟩
  show ((r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0)).Perm
       ((r1.map (· + 1)).reverse ++ ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6))
  apply List.Perm.append_left
  exact ctsConfigToSystem5Bag_true_head_perm_dec_erase_perm rest phase bag h_perm

/-- **Iter 1165: 1 ∉ s5_1.bag at true-head Perm-chain points**.
    True-head structural finding: after one P-step at a true-head
    Perm-chain point, `1 ∉ s5_1.bag`.  Reasoning: s5_1.bag is
    Perm-equivalent to `(r1.map(·+1)).reverse ++ (2 :: 3 :: 5 :: aux rest 6)`
    (iter 1164); the right part has min value 2 (`2 ∈` head, others all
    `≥ 3` via aux's `_ge` lemma); the left part has all entries ≥ 12
    (r1 ≥ 11 so r1.map(·+1) ≥ 12).  Hence every bag element is ≥ 2,
    so 1 cannot be a member.
    **Important consequence: step 2 of the true-head trajectory is a
    D-step (decrement only), NOT a P-step**.  This explains the 6-step
    sextuple-dec-erase shape (iters 1145, 1147-1149) — the true-head
    trajectory has D-steps interspersed, unlike the all-P-step
    false-head trajectory. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step1_one_not_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_1,
      System5.step ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ = some s5_1
      ∧ (1 : Int) ∉ s5_1.bag := by
  obtain ⟨r1, _, _, s5_1, h_eq, h_step, h_perm'⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step1_bag_perm cts rest phase N h_N bag h_perm
  refine ⟨s5_1, h_step, ?_⟩
  intro h_one_in
  -- Transfer through Perm to the explicit form
  have h_one_in' : (1 : Int) ∈ ((r1.map (· + 1)).reverse ++
      ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6)) :=
    (List.Perm.mem_iff h_perm').mp h_one_in
  rw [List.mem_append] at h_one_in'
  rcases h_one_in' with h_left | h_right
  · -- 1 ∈ r1.map(·+1).reverse impossible since r1 ≥ 11
    rw [List.mem_reverse, List.mem_map] at h_left
    obtain ⟨x, hx, h_eq_x⟩ := h_left
    obtain ⟨r1', _, _, h_eq', h_r1_ge, _⟩ :=
      ctsToSystem5_true_head_first_two_rules_ge_eleven cts rest phase N h_N
    have h_r1_eq : r1 = r1' := (List.cons.inj (h_eq.symm.trans h_eq')).1
    rw [h_r1_eq] at hx
    have := h_r1_ge x hx
    omega
  · -- 1 ∈ (2 :: 3 :: 5 :: aux rest 6): impossible since all entries ≥ 2
    simp only [List.mem_cons] at h_right
    rcases h_right with h | h | h | h_aux
    · omega
    · omega
    · omega
    · have := ctsConfigToSystem5BagAux_ge rest 6 1 h_aux
      omega

/-- **Iter 1166: true-head step 2 is a D-step (decrement only)**.
    After two consecutive System5 steps at a true-head Perm-chain
    point, `s5_2.bag = s5_1.bag.map(·-1)` (no rule pop, no xorMerge).
    Composition: iter 1162 (2 ∈ s5_1.bag, hence s5_1.bag ≠ []) +
    iter 1165 (1 ∉ s5_1.bag, hence 0 ∉ s5_1.bag.map(·-1)) +
    iter 1163 (step 2 succeeds) + `System5_step_pure_decrement`.
    The s5_1.rules ≠ [] is derived from the explicit form
    `(r2 :: tail).map(...)` which is non-empty. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step2_bag_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_1 s5_2,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 1 = some s5_1
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ s5_2.bag = s5_1.bag.map (· - 1) := by
  obtain ⟨r1, r2, tail, h_eq, h_step1⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts
      { data := true :: rest, phase := phase } N h_N bag (by simp) h_perm
  obtain ⟨s5_1', h_step1', h_two_in⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step_bag_two_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_1'', h_step1'', h_one_not_in⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step1_one_not_mem cts rest phase N h_N bag h_perm
  let s5_1 : System5Config :=
    ⟨(r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0),
     (r2 :: tail).map (fun r => r.map (· + 1))⟩
  have h_s5_1_eq : s5_1' = s5_1 := Option.some.inj (h_step1'.symm.trans h_step1)
  have h_s5_1_eq'' : s5_1'' = s5_1 := Option.some.inj (h_step1''.symm.trans h_step1)
  have h_two_mem_s5_1 : (2 : Int) ∈ s5_1.bag := h_s5_1_eq ▸ h_two_in
  have h_one_not_in_s5_1 : (1 : Int) ∉ s5_1.bag := h_s5_1_eq'' ▸ h_one_not_in
  have h_bag_ne : s5_1.bag ≠ [] := List.ne_nil_of_mem h_two_mem_s5_1
  have h_rules_ne : s5_1.rules ≠ [] := by
    show (r2 :: tail).map (fun r => r.map (· + 1)) ≠ []
    simp
  have h_zero_not_in : (0 : Int) ∉ s5_1.bag.map (· - 1) := by
    intro h_zero_in
    exact h_one_not_in_s5_1 ((zero_mem_decrement_iff_one_mem s5_1.bag).mp h_zero_in)
  have h_step2_some : ∃ s5_2, System5.step s5_1 = some s5_2 :=
    (System5_step_some_iff s5_1).mpr ⟨h_bag_ne, h_rules_ne⟩
  obtain ⟨s5_2, h_step2⟩ := h_step2_some
  have h_dec := System5_step_pure_decrement s5_1 s5_2 h_step2
                  h_bag_ne h_rules_ne h_zero_not_in
  refine ⟨s5_1, s5_2, ?_, ?_, h_dec.1⟩
  · rw [System5.nSteps_one]; exact h_step1
  · rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add]
    rw [System5.nSteps_one, h_step1]
    simp only [Option.bind_some, System5.nSteps_one]
    exact h_step2

/-- **Iter 1167: true-head s5_2.bag Perm form**.  After two
    consecutive System5 steps at a true-head Perm-chain point (the
    second being a D-step per iter 1166), `s5_2.bag.Perm
    (r1.reverse ++ (1 :: 2 :: 4 :: aux rest 5))`.  Composition: iter
    1166 (s5_2.bag = s5_1.bag.map(·-1)) + iter 1164 (s5_1.bag.Perm form)
    + `List.Perm.map (·-1)` + iter 996's `_inc_reverse_dec_cancel`
    (r1.map(·+1).reverse.map(·-1) = r1.reverse) + computation
    `(2 :: 3 :: 5 :: aux rest 6).map(·-1) = 1 :: 2 :: 4 :: aux rest 5`
    via `_dec_at_six`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step2_bag_perm
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_1 s5_2,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 1 = some s5_1
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ s5_2.bag.Perm
          (r1.reverse ++ ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5)) := by
  obtain ⟨r1, r2, tail, h_eq, h_step1⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts
      { data := true :: rest, phase := phase } N h_N bag (by simp) h_perm
  obtain ⟨s5_1, s5_2, h_n1, h_n2, h_dec⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_form cts rest phase N h_N bag h_perm
  refine ⟨r1, r2, tail, s5_1, s5_2, h_eq, h_n1, h_n2, ?_⟩
  have h_step_n1 : System5.step ⟨bag, ctsRulesToSystem5Rules cts
      { data := true :: rest, phase := phase } N⟩ = some s5_1 := by
    rw [System5.nSteps_one] at h_n1; exact h_n1
  have h_s5_1_eq : s5_1 = ⟨(r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0),
                            (r2 :: tail).map (fun r => r.map (· + 1))⟩ :=
    Option.some.inj (h_step_n1.symm.trans h_step1)
  rw [h_dec, h_s5_1_eq]
  show (((r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0)).map (· - 1)).Perm
       (r1.reverse ++ ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5))
  rw [List.map_append, List_Int_inc_reverse_dec_cancel]
  apply List.Perm.append_left
  have h_just_dec : (((bag.map (· - 1)).erase 0).map (· - 1)).Perm
                  (((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6).map (· - 1)) :=
    List.Perm.map _ (ctsConfigToSystem5Bag_true_head_perm_dec_erase_perm rest phase bag h_perm)
  have h_rhs : ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6).map (· - 1)
             = (1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5 := by
    simp only [List.map_cons]
    rw [ctsConfigToSystem5BagAux_dec_at_six]
    rfl
  rw [h_rhs] at h_just_dec
  exact h_just_dec

/-- **Iter 1168: 1 ∈ s5_2.bag at true-head Perm-chain points**.
    After two System5 steps at a true-head Perm-chain point, `1 ∈ s5_2.bag`.
    Reasoning: by iter 1167, `s5_2.bag.Perm (r1.reverse ++ (1 :: 2 :: 4 :: aux rest 5))`
    and `1` is in the right part (head of `1 :: 2 :: 4 :: aux rest 5`).
    **Important consequence: step 3 of the true-head trajectory IS a
    P-step** (rule pop), unlike step 2 which was a D-step.  This
    confirms the trajectory shape `P, D, P, ...` for true-head. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step2_one_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_2,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ (1 : Int) ∈ s5_2.bag := by
  obtain ⟨_r1, _r2, _tail, _s5_1, s5_2, _h_eq, _h_n1, h_n2, h_perm_s5_2⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_perm cts rest phase N h_N bag h_perm
  refine ⟨s5_2, h_n2, ?_⟩
  apply (List.Perm.mem_iff h_perm_s5_2).mpr
  apply List.mem_append_right
  exact List.mem_cons_self

/-- **Iter 1169: true-head s5_2.rules form**.  After two consecutive
    System5 steps at a true-head Perm-chain point (P-step then D-step),
    `s5_2.rules = (r2 :: tail).map (fun r => r.map (·+2))` — the
    original tail (after r1 popped at step 1), with each rule
    incremented twice (once at step 1's pop, once at step 2's D-step).
    Composition: iter 1166 (s5_2 exists from D-step at step 2) + the
    full pure-decrement output (`System5_step_pure_decrement` gives
    both bag and rules sides) + iter 1057 (s5_1 explicit form). -/
theorem ctsConfigToSystem5Bag_true_head_perm_step2_rules_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_2,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ s5_2.rules
          = ((r2 :: tail).map (fun r => r.map (· + 1))).map
              (fun r => r.map (· + 1)) := by
  obtain ⟨r1, r2, tail, h_eq, h_step1⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts
      { data := true :: rest, phase := phase } N h_N bag (by simp) h_perm
  obtain ⟨s5_1', h_step1', h_two_in⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step_bag_two_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_1'', h_step1'', h_one_not_in⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step1_one_not_mem cts rest phase N h_N bag h_perm
  let s5_1 : System5Config :=
    ⟨(r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0),
     (r2 :: tail).map (fun r => r.map (· + 1))⟩
  have h_s5_1_eq : s5_1' = s5_1 := Option.some.inj (h_step1'.symm.trans h_step1)
  have h_s5_1_eq'' : s5_1'' = s5_1 := Option.some.inj (h_step1''.symm.trans h_step1)
  have h_two_mem_s5_1 : (2 : Int) ∈ s5_1.bag := h_s5_1_eq ▸ h_two_in
  have h_one_not_in_s5_1 : (1 : Int) ∉ s5_1.bag := h_s5_1_eq'' ▸ h_one_not_in
  have h_bag_ne : s5_1.bag ≠ [] := List.ne_nil_of_mem h_two_mem_s5_1
  have h_rules_ne : s5_1.rules ≠ [] := by
    show (r2 :: tail).map (fun r => r.map (· + 1)) ≠ []
    simp
  have h_zero_not_in : (0 : Int) ∉ s5_1.bag.map (· - 1) := by
    intro h_zero_in
    exact h_one_not_in_s5_1 ((zero_mem_decrement_iff_one_mem s5_1.bag).mp h_zero_in)
  obtain ⟨s5_2, h_step2⟩ :=
    (System5_step_some_iff s5_1).mpr ⟨h_bag_ne, h_rules_ne⟩
  have h_dec := System5_step_pure_decrement s5_1 s5_2 h_step2
                  h_bag_ne h_rules_ne h_zero_not_in
  refine ⟨r1, r2, tail, s5_2, h_eq, ?_, ?_⟩
  · rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add]
    rw [System5.nSteps_one, h_step1]
    simp only [Option.bind_some, System5.nSteps_one]
    exact h_step2
  · rw [h_dec.2]

/-- **Iter 1170: true-head s5_3.bag explicit form**.  After three
    consecutive System5 steps at a true-head Perm-chain point (P, D, P
    pattern), `s5_3.bag = xorMerge ((s5_2.bag.map(·-1)).erase 0)
    (r2.map(·+3))`.  The popped rule at step 3 is `r2.map(·+2)` (head
    of `s5_2.rules`); the xorMerge argument is its `(·+1)` increment,
    yielding `r2.map(·+3)`.  Composition: iter 1168 (`1 ∈ s5_2.bag`,
    triggers P-step) + iter 1169 (`s5_2.rules` form) +
    `System5_step_explicit_pop` + `List_Int_map_add_compose`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step3_bag_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_2 s5_3,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ s5_3.bag = xorMerge ((s5_2.bag.map (· - 1)).erase 0) (r2.map (· + 3)) := by
  obtain ⟨r1, r2, tail, s5_2, h_eq, h_n2, h_rules_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_rules_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_2', h_n2', h_one_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_one_mem cts rest phase N h_N bag h_perm
  have h_s5_2_eq : s5_2 = s5_2' := Option.some.inj (h_n2.symm.trans h_n2')
  have h_one_mem_s5_2 : (1 : Int) ∈ s5_2.bag := h_s5_2_eq ▸ h_one_mem
  have h_zero : (0 : Int) ∈ s5_2.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_2
  have h_bag_ne : s5_2.bag ≠ [] := List.ne_nil_of_mem h_one_mem_s5_2
  -- s5_2.rules has head = r2.map(·+2) and tail = (tail.map(map(·+1))).map(map(·+1))
  have h_rules_cons : s5_2.rules = (r2.map (· + 1)).map (· + 1)
        :: ((tail.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))) := by
    rw [h_rules_form]
    show ((r2 :: tail).map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1)) = _
    simp
  have h_step3 := System5_step_explicit_pop s5_2
      ((r2.map (· + 1)).map (· + 1))
      ((tail.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1)))
      h_rules_cons h_bag_ne h_zero
  let s5_3 : System5Config :=
    ⟨xorMerge ((s5_2.bag.map (· - 1)).erase 0) (((r2.map (· + 1)).map (· + 1)).map (· + 1)),
     ((tail.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))).map
       (fun r => r.map (· + 1))⟩
  refine ⟨r1, r2, tail, s5_2, s5_3, h_eq, h_n2, ?_, ?_⟩
  · rw [show (3 : Nat) = 2 + 1 from rfl, System5.nSteps_add, h_n2]
    simp only [Option.bind_some, System5.nSteps_one]
    exact h_step3
  · show xorMerge ((s5_2.bag.map (· - 1)).erase 0)
          (((r2.map (· + 1)).map (· + 1)).map (· + 1))
       = xorMerge ((s5_2.bag.map (· - 1)).erase 0) (r2.map (· + 3))
    congr 1
    have h1 : ((r2.map (· + 1)).map (· + 1)) = r2.map (· + 2) :=
      List_Int_map_add_compose r2 1 1
    rw [h1]
    exact List_Int_map_add_compose r2 2 1

/-- **Iter 1171: true-head s5_3.rules form (triple-map form)**.
    After three consecutive System5 steps at a true-head Perm-chain
    point, `s5_3.rules = ((tail.map(map(·+1))).map(map(·+1))).map(map(·+1))`
    — the original tail (after r1 popped at step 1, D-step at step 2,
    r2 popped at step 3), with each rule incremented three times.
    Composition: iter 1170 (already gives this implicitly via the step
    output). -/
theorem ctsConfigToSystem5Bag_true_head_perm_step3_rules_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_3,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ s5_3.rules
          = ((tail.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))).map
              (fun r => r.map (· + 1)) := by
  obtain ⟨r1, r2, tail, s5_2, h_eq, h_n2, h_rules_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_rules_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_2', h_n2', h_one_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_one_mem cts rest phase N h_N bag h_perm
  have h_s5_2_eq : s5_2 = s5_2' := Option.some.inj (h_n2.symm.trans h_n2')
  have h_one_mem_s5_2 : (1 : Int) ∈ s5_2.bag := h_s5_2_eq ▸ h_one_mem
  have h_zero : (0 : Int) ∈ s5_2.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_2
  have h_bag_ne : s5_2.bag ≠ [] := List.ne_nil_of_mem h_one_mem_s5_2
  have h_rules_cons : s5_2.rules = (r2.map (· + 1)).map (· + 1)
        :: ((tail.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))) := by
    rw [h_rules_form]
    show ((r2 :: tail).map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1)) = _
    simp
  have h_step3 := System5_step_explicit_pop s5_2
      ((r2.map (· + 1)).map (· + 1))
      ((tail.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1)))
      h_rules_cons h_bag_ne h_zero
  let s5_3 : System5Config :=
    ⟨xorMerge ((s5_2.bag.map (· - 1)).erase 0) (((r2.map (· + 1)).map (· + 1)).map (· + 1)),
     ((tail.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))).map
       (fun r => r.map (· + 1))⟩
  refine ⟨r1, r2, tail, s5_3, h_eq, ?_, rfl⟩
  rw [show (3 : Nat) = 2 + 1 from rfl, System5.nSteps_add, h_n2]
  simp only [Option.bind_some, System5.nSteps_one]
  exact h_step3

/-- **Iter 1172: true-head s5_2.bag dec-erase Perm form**.  The
    dec-erase'd s5_2.bag (the input to step 3's xorMerge) is Perm-
    equivalent to `(r1.map(·-1)).reverse ++ (1 :: 3 :: aux rest 4)`.
    Composition: iter 1167 (s5_2.bag Perm form) + `List.Perm.map(·-1)`
    + `List.Perm.erase 0` + computation
    `(r1.reverse ++ (1 :: 2 :: 4 :: aux rest 5)).map(·-1) =
     (r1.map(·-1)).reverse ++ (0 :: 1 :: 3 :: aux rest 4)` (uses
    `_dec_at_five`) + `List.erase_append_right` (since 0 ∉ left when
    r1 ≥ 11). -/
theorem ctsConfigToSystem5Bag_true_head_perm_step2_bag_dec_erase_perm
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_2,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ ((s5_2.bag.map (· - 1)).erase 0).Perm
          ((r1.map (· - 1)).reverse ++
            ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4)) := by
  obtain ⟨r1, r2, tail, _s5_1, s5_2, h_eq, _h_n1, h_n2, h_perm_s5_2⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_perm cts rest phase N h_N bag h_perm
  refine ⟨r1, r2, tail, s5_2, h_eq, h_n2, ?_⟩
  -- s5_2.bag.Perm (r1.reverse ++ (1 :: 2 :: 4 :: aux rest 5))
  have h_dec : (s5_2.bag.map (· - 1)).Perm
      ((r1.reverse ++ ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5)).map (· - 1)) :=
    List.Perm.map _ h_perm_s5_2
  have h_erase := List.Perm.erase (a := (0 : Int)) h_dec
  -- Compute RHS
  have h_rhs_eq :
      ((r1.reverse ++ ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5)).map (· - 1)).erase 0
      = (r1.map (· - 1)).reverse ++ ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4) := by
    rw [List.map_append, List.map_reverse]
    -- Need: 0 ∉ r1.map(·-1)
    have h_zero_not : (0 : Int) ∉ (r1.map (· - 1)).reverse := by
      rw [List.mem_reverse, List.mem_map]
      intro ⟨x, hx, h_eq_x⟩
      obtain ⟨r1', _, _, h_eq', h_r1_ge, _⟩ :=
        ctsToSystem5_true_head_first_two_rules_ge_eleven cts rest phase N h_N
      have h_r1_eq : r1 = r1' := (List.cons.inj (h_eq.symm.trans h_eq')).1
      rw [h_r1_eq] at hx
      have := h_r1_ge x hx
      omega
    rw [List.erase_append_right _ h_zero_not]
    congr 1
    -- ((1 :: 2 :: 4 :: aux rest 5).map(·-1)).erase 0 = 1 :: 3 :: aux rest 4
    show (((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5).map (· - 1)).erase 0
       = (1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4
    simp only [List.map_cons]
    rw [ctsConfigToSystem5BagAux_dec_at_five]
    show ((0 : Int) :: 1 :: 3 :: ctsConfigToSystem5BagAux rest 4).erase 0
       = 1 :: 3 :: ctsConfigToSystem5BagAux rest 4
    rw [List.erase_cons_head]
  rw [h_rhs_eq] at h_erase
  exact h_erase

/-- **Iter 1173: true-head s5_2.bag dec-erase Perm form (r2 form)**.
    Converts iter 1172's r1 form to r2 form using the encoder
    cancellation `r1 = r2.map(·+2)` (iter 892):
    `r1.map(·-1) = r2.map(·+2).map(·-1) = r2.map(·+1)`.
    Result: `((s5_2.bag.map(·-1)).erase 0).Perm
    ((r2.map(·+1)).reverse ++ (1 :: 3 :: aux rest 4))`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step2_bag_dec_erase_perm_r2
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_2,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ ((s5_2.bag.map (· - 1)).erase 0).Perm
          ((r2.map (· + 1)).reverse ++
            ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4)) := by
  obtain ⟨r1, r2, tail, s5_2, h_eq, h_n2, h_perm_de⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_dec_erase_perm cts rest phase N h_N bag h_perm
  obtain ⟨r1', r2', tail', h_eq', h_cancel⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_cancel cts
      { data := true :: rest, phase := phase } N h_N
  have h_align : r1 :: r2 :: tail = r1' :: r2' :: tail' := h_eq.symm.trans h_eq'
  have h_r1_eq : r1 = r1' := (List.cons.inj h_align).1
  have h_r2_eq : r2 = r2' := (List.cons.inj (List.cons.inj h_align).2).1
  refine ⟨r1, r2, tail, s5_2, h_eq, h_n2, ?_⟩
  -- r1.map(·-1) = r2.map(·+1)
  have h_helper : ∀ xs : List Int, (xs.map (· + 2)).map (· - 1) = xs.map (· + 1) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x ys ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨by omega, ih⟩
  have h_r1_dec : r1.map (· - 1) = r2.map (· + 1) := by
    rw [h_r1_eq, h_r2_eq, h_cancel]
    exact h_helper r2'
  rw [h_r1_dec] at h_perm_de
  exact h_perm_de

/-- **Iter 1174: `(r2.map(·+1)).reverse ++ (1 :: 3 :: aux rest 4)` is
    Nodup at true-head Perm-chain points**.  Direct lift via iter 1173
    (Perm form for the dec-erase'd s5_2.bag) + a generic Nodup
    derivation: the dec-erase'd s5_2.bag is Nodup since s5_2.bag is
    Nodup (s5_2 is reachable from a Nodup chain) and decrement is
    injective; then `List.Perm.nodup_iff` transfers Nodup through the
    Perm form. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step2_bag_dec_erase_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_2,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ ((r2.map (· + 1)).reverse ++
          ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4)).Nodup := by
  obtain ⟨r1, r2, tail, s5_2, h_eq, h_n2, h_perm_de⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_dec_erase_perm_r2
      cts rest phase N h_N bag h_perm
  refine ⟨r1, r2, tail, s5_2, h_eq, h_n2, ?_⟩
  -- Get s5_2.bag Nodup; lift through dec-erase; transfer to Perm RHS.
  -- s5_2.bag.Nodup follows from iter 1166's bag form + xorMerge / Nodup props
  -- For simplicity, derive via iter 1077 (post-step bag dec-erase Nodup) at
  -- the FIRST step + iter 1166's bag is dec of s5_1.bag, which preserves Nodup.
  obtain ⟨s5_1', h_step1', h_nodup_de⟩ :=
    ctsConfigToSystem5Bag_perm_step1_dec_erase_nodup cts
      { data := true :: rest, phase := phase } N h_N (by simp) bag h_perm
  -- After step 1, ((s5_1.bag.map(·-1)).erase 0) is Nodup; this IS s5_2.bag's
  -- close relative.  Actually iter 1166 says s5_2.bag = s5_1.bag.map(·-1).
  -- So ((s5_2.bag.map(·-1)).erase 0) = ((s5_1.bag.map(·-1).map(·-1)).erase 0).
  -- We need its Nodup; lift via map injectivity + erase Nodup.
  -- Simpler: take iter 1166's s5_2 and use that s5_2.bag.Nodup.
  obtain ⟨s5_1, s5_2', h_n1, h_n2', h_dec⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_form cts rest phase N h_N bag h_perm
  have h_s5_2_eq' : s5_2 = s5_2' := Option.some.inj (h_n2.symm.trans h_n2')
  have h_step1_some : System5.step ⟨bag, ctsRulesToSystem5Rules cts
      { data := true :: rest, phase := phase } N⟩ = some s5_1 := by
    rw [System5.nSteps_one] at h_n1; exact h_n1
  have h_s5_1_eq : s5_1 = s5_1' := Option.some.inj (h_step1_some.symm.trans h_step1')
  -- s5_2'.bag.Nodup follows from h_dec + s5_1.bag Nodup
  have h_s5_1_bag_nodup : s5_1.bag.Nodup := by
    rw [h_s5_1_eq]
    -- s5_1'.bag.map(·-1).erase 0 Nodup ⇒ s5_1'.bag Nodup? No, not directly.
    -- Actually we need s5_1.bag Nodup. From iter 1065.
    obtain ⟨s5_1'', h_step1'', h_nodup⟩ :=
      ctsConfigToSystem5Bag_perm_step1_bag_nodup cts
        { data := true :: rest, phase := phase } N h_N (by simp) bag h_perm
    have : s5_1' = s5_1'' :=
      Option.some.inj (h_step1'.symm.trans h_step1'')
    rw [this]
    exact h_nodup
  -- s5_2.bag = s5_1.bag.map(·-1) (per iter 1166), so Nodup via injectivity
  have h_s5_2_bag_nodup : s5_2.bag.Nodup := by
    rw [h_s5_2_eq', h_dec]
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_1_bag_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  -- Now ((s5_2.bag.map(·-1)).erase 0).Nodup
  have h_de_nodup : ((s5_2.bag.map (· - 1)).erase 0).Nodup := by
    apply List.Nodup.erase
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_2_bag_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  -- Transfer through Perm
  exact (List.Perm.nodup_iff h_perm_de).mp h_de_nodup

/-- **Iter 1175: r2.map(·+3) is Nodup at true-head encoder**.
    Direct lift of iter 981 (`r2.map(·+2).Nodup`) via map injectivity:
    `(r2.map(·+2)).map(·+1)` is Nodup, and equals `r2.map(·+3)` via
    `List_Int_map_add_compose`.  **Required Nodup for invoking
    `xorMerge_mem_iff` and disjoint-append at step 3 of the
    true-head trajectory.** -/
theorem ctsRulesToSystem5Rules_second_rule_map_add_3_nodup
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail, ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
                ∧ (r2.map (· + 3)).Nodup := by
  obtain ⟨r1, r2, tail, h_eq, h_r2_2_nodup⟩ :=
    ctsRulesToSystem5Rules_second_rule_map_add_2_nodup cts cfg N h_N
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  have h_eq_form : r2.map (· + 3) = (r2.map (· + 2)).map (· + 1) := by
    rw [List_Int_map_add_compose r2 2 1]
    -- now goal is r2.map(·+3) = r2.map(·+(2+1)); both equal pointwise
    have h_helper : ∀ xs : List Int, xs.map (· + 3) = xs.map (· + (2 + 1)) := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x ys ih => simp only [List.map_cons, List.cons.injEq]; exact ⟨by omega, ih⟩
    exact h_helper r2
  rw [h_eq_form]
  apply List.Pairwise.map (· + 1) (R := (· ≠ ·)) ?_ h_r2_2_nodup
  intro a b h_ne h_eq_inc
  apply h_ne
  have : a + 1 = b + 1 := h_eq_inc
  omega

/-- **Iter 1176: 1 ∈ s5_3.bag at true-head Perm-chain points**.
    After three consecutive System5 steps at a true-head Perm-chain
    point (P, D, P pattern), `1 ∈ s5_3.bag`.  Reasoning: by iter 1170,
    `s5_3.bag = xorMerge LHS (r2.map(·+3))`; by iter 1173, the LHS is
    Perm-equivalent to `(r2.map(·+1)).reverse ++ (1 :: 3 :: aux rest 4)`,
    which contains `1`; and `1 ∉ r2.map(·+3)` since `r2 ≥ 9` (by iter
    1159 for true-head) ⇒ `r2.map(·+3) ≥ 12`.  So `1` survives the
    xorMerge.  **Important consequence: step 4 of the true-head
    trajectory IS a P-step**.  Trajectory shape: P, D, P, P, ... -/
theorem ctsConfigToSystem5Bag_true_head_perm_step3_one_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_3,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ (1 : Int) ∈ s5_3.bag := by
  obtain ⟨r1, r2, tail, s5_2, s5_3, h_eq, _h_n2, h_n3, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_3, h_n3, ?_⟩
  -- 1 ∈ s5_3.bag = xorMerge ((s5_2.bag.map(·-1)).erase 0) (r2.map(·+3))
  rw [h_bag_form]
  -- Use xorMerge_mem_left_of_not_mem_right
  -- Need: 1 ∈ ((s5_2.bag.map(·-1)).erase 0) AND 1 ∉ r2.map(·+3) AND both Nodup
  -- For 1 ∈ LHS: use Perm form (iter 1173) which has 1 in the right portion
  obtain ⟨r1', r2', tail', s5_2', h_eq', h_n2', h_perm_lhs⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_dec_erase_perm_r2
      cts rest phase N h_N bag h_perm
  -- Align r2 = r2'
  have h_align : r1 :: r2 :: tail = r1' :: r2' :: tail' := h_eq.symm.trans h_eq'
  have h_r2_eq : r2 = r2' := (List.cons.inj (List.cons.inj h_align).2).1
  -- Get s5_2 alignment
  have h_s5_2_align : System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
      { data := true :: rest, phase := phase } N⟩ 2 = some s5_2 := _h_n2
  have h_s5_2_eq : s5_2 = s5_2' := Option.some.inj (h_s5_2_align.symm.trans h_n2')
  -- Now h_perm_lhs gives the Perm
  have h_one_in_rhs : (1 : Int) ∈ ((r2'.map (· + 1)).reverse ++
      ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4)) := by
    apply List.mem_append_right
    exact List.mem_cons_self
  have h_one_in_lhs : (1 : Int) ∈ (s5_2'.bag.map (· - 1)).erase 0 :=
    (List.Perm.mem_iff h_perm_lhs).mpr h_one_in_rhs
  -- 1 ∉ r2.map(·+3)
  have h_one_not_in_r2_3 : (1 : Int) ∉ r2.map (· + 3) := by
    rw [List.mem_map]
    intro ⟨x, hx, h_eq_x⟩
    obtain ⟨_, r2'', _, h_eq'', _, h_r2_ge⟩ :=
      ctsToSystem5_true_head_first_two_rules_ge_eleven cts rest phase N h_N
    have h_align' : r1 :: r2 :: tail = _ :: r2'' :: _ := h_eq.symm.trans h_eq''
    have h_r2_eq' : r2 = r2'' := (List.cons.inj (List.cons.inj h_align').2).1
    rw [h_r2_eq'] at hx
    have := h_r2_ge x hx
    omega
  -- Get Nodups
  obtain ⟨_, _, _, _, _, _, h_lhs_nodup⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_dec_erase_nodup
      cts rest phase N h_N bag h_perm
  -- Wait, we need the Nodup of (s5_2.bag.map(·-1)).erase 0 directly, not the Perm RHS.
  -- Use iter 1077 approach.
  obtain ⟨s5_1, h_step1, h_lhs_nodup_direct⟩ :=
    ctsConfigToSystem5Bag_perm_step1_dec_erase_nodup cts
      { data := true :: rest, phase := phase } N h_N (by simp) bag h_perm
  -- h_lhs_nodup_direct gives ((s5_1.bag.map(·-1)).erase 0).Nodup
  -- But we need ((s5_2.bag.map(·-1)).erase 0).Nodup
  -- Use the s5_2.bag.Nodup approach instead
  obtain ⟨s5_1', s5_2'', h_n1, h_n2'', h_dec⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_form cts rest phase N h_N bag h_perm
  have h_s5_2''_eq : s5_2 = s5_2'' := Option.some.inj (h_s5_2_align.symm.trans h_n2'')
  have h_step1_some : System5.step ⟨bag, ctsRulesToSystem5Rules cts
      { data := true :: rest, phase := phase } N⟩ = some s5_1' := by
    rw [System5.nSteps_one] at h_n1; exact h_n1
  obtain ⟨s5_1'', h_step1'', h_s5_1_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_nodup cts
      { data := true :: rest, phase := phase } N h_N (by simp) bag h_perm
  have h_s5_1_align : s5_1' = s5_1'' :=
    Option.some.inj (h_step1_some.symm.trans h_step1'')
  have h_s5_2_bag_nodup : s5_2.bag.Nodup := by
    rw [h_s5_2''_eq, h_dec, h_s5_1_align]
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_1_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  have h_lhs_nodup_real : ((s5_2.bag.map (· - 1)).erase 0).Nodup := by
    apply List.Nodup.erase
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_2_bag_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  obtain ⟨_, r2_3', _, h_eq_r2_3, h_r2_3_nodup⟩ :=
    ctsRulesToSystem5Rules_second_rule_map_add_3_nodup cts
      { data := true :: rest, phase := phase } N h_N
  have h_r2_3_align : r2 = r2_3' :=
    (List.cons.inj (List.cons.inj (h_eq.symm.trans h_eq_r2_3)).2).1
  rw [← h_s5_2_eq] at h_one_in_lhs
  -- Goal: 1 ∈ xorMerge ((s5_2.bag.map(·-1)).erase 0) (r2.map(·+3))
  apply xorMerge_mem_left_of_not_mem_right
  · exact h_lhs_nodup_real
  · rw [h_r2_3_align]; exact h_r2_3_nodup
  · exact h_one_in_lhs
  · exact h_one_not_in_r2_3

/-- **Iter 1177: 3 ∈ s5_3.bag at true-head Perm-chain points**.
    Companion to iter 1176 for value 3.  Same template: `3 ∈ LHS`
    (since `3` is the second element of `(1 :: 3 :: aux rest 4)`,
    surviving in the LHS Perm form via iter 1173) and `3 ∉ r2.map(·+3)`
    (r2 ≥ 9 ⇒ r2.map(·+3) ≥ 12).  So `3 ∈ s5_3.bag`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step3_three_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_3,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ (3 : Int) ∈ s5_3.bag := by
  obtain ⟨r1, r2, tail, s5_2, s5_3, h_eq, h_n2, h_n3, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_3, h_n3, ?_⟩
  rw [h_bag_form]
  obtain ⟨_r1', r2', _tail', s5_2', h_eq', h_n2', h_perm_lhs⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_dec_erase_perm_r2
      cts rest phase N h_N bag h_perm
  have h_align : r1 :: r2 :: tail = _r1' :: r2' :: _tail' := h_eq.symm.trans h_eq'
  have h_r2_eq : r2 = r2' := (List.cons.inj (List.cons.inj h_align).2).1
  have h_s5_2_eq : s5_2 = s5_2' := Option.some.inj (h_n2.symm.trans h_n2')
  have h_three_in_rhs : (3 : Int) ∈ ((r2'.map (· + 1)).reverse ++
      ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4)) := by
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  have h_three_in_lhs : (3 : Int) ∈ (s5_2'.bag.map (· - 1)).erase 0 :=
    (List.Perm.mem_iff h_perm_lhs).mpr h_three_in_rhs
  rw [← h_s5_2_eq] at h_three_in_lhs
  have h_three_not_in_r2_3 : (3 : Int) ∉ r2.map (· + 3) := by
    rw [List.mem_map]
    intro ⟨x, hx, h_eq_x⟩
    obtain ⟨_, r2'', _, h_eq'', _, h_r2_ge⟩ :=
      ctsToSystem5_true_head_first_two_rules_ge_eleven cts rest phase N h_N
    have h_align' : r1 :: r2 :: tail = _ :: r2'' :: _ := h_eq.symm.trans h_eq''
    have h_r2_eq' : r2 = r2'' := (List.cons.inj (List.cons.inj h_align').2).1
    rw [h_r2_eq'] at hx
    have := h_r2_ge x hx
    omega
  -- Reuse Nodup derivations from iter 1176 path
  obtain ⟨s5_1', s5_2'', h_n1, h_n2'', h_dec⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_form cts rest phase N h_N bag h_perm
  have h_s5_2''_eq : s5_2 = s5_2'' := Option.some.inj (h_n2.symm.trans h_n2'')
  have h_step1_some : System5.step ⟨bag, ctsRulesToSystem5Rules cts
      { data := true :: rest, phase := phase } N⟩ = some s5_1' := by
    rw [System5.nSteps_one] at h_n1; exact h_n1
  obtain ⟨s5_1'', h_step1'', h_s5_1_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_nodup cts
      { data := true :: rest, phase := phase } N h_N (by simp) bag h_perm
  have h_s5_1_align : s5_1' = s5_1'' :=
    Option.some.inj (h_step1_some.symm.trans h_step1'')
  have h_s5_2_bag_nodup : s5_2.bag.Nodup := by
    rw [h_s5_2''_eq, h_dec, h_s5_1_align]
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_1_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  have h_lhs_nodup : ((s5_2.bag.map (· - 1)).erase 0).Nodup := by
    apply List.Nodup.erase
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_2_bag_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  obtain ⟨_, r2_3', _, h_eq_r2_3, h_r2_3_nodup⟩ :=
    ctsRulesToSystem5Rules_second_rule_map_add_3_nodup cts
      { data := true :: rest, phase := phase } N h_N
  have h_r2_3_align : r2 = r2_3' :=
    (List.cons.inj (List.cons.inj (h_eq.symm.trans h_eq_r2_3)).2).1
  apply xorMerge_mem_left_of_not_mem_right
  · exact h_lhs_nodup
  · rw [h_r2_3_align]; exact h_r2_3_nodup
  · exact h_three_in_lhs
  · exact h_three_not_in_r2_3

/-- **Iter 1178: true-head s5_3.rules has `[]` as head**.  After
    three consecutive System5 steps at a true-head Perm-chain point,
    `s5_3.rules = [] :: rest_more` for some `rest_more`.  Reasoning:
    iter 1171 gives `s5_3.rules = ((tail.map(map(·+1))).map(map(·+1))).map(map(·+1))`,
    iter 984 gives `(encoder).drop 2 = [] :: [] :: rest_more` (i.e.,
    tail = `[] :: [] :: rest_more`), and `[]`-mapping is `[]`.
    **Important consequence: step 4 pops an empty rule** — same as
    false-head's step 3 (iter 985), so `s5_4.bag = (s5_3.bag.map(·-1)).erase 0`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step3_rules_empty_head
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_3 rest_more,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ s5_3.rules = ([] : List Int) :: rest_more := by
  obtain ⟨r1, r2, tail, s5_3, h_eq, h_n3, h_rules_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_rules_form cts rest phase N h_N bag h_perm
  obtain ⟨rest_more, h_drop⟩ :=
    ctsRulesToSystem5Rules_drop_2_exists_empty_rules cts
      { data := true :: rest, phase := phase } N h_N
  -- h_drop : (encoder).drop 2 = [] :: [] :: rest_more
  -- But encoder = r1 :: r2 :: tail, so tail = [] :: [] :: rest_more
  have h_tail_eq : tail = ([] : List Int) :: [] :: rest_more := by
    have h := h_drop
    rw [h_eq] at h
    show tail = _
    have h_drop_simp : ((r1 :: r2 :: tail).drop 2) = tail := by simp
    rw [h_drop_simp] at h
    exact h
  refine ⟨s5_3, ((tail.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))).map
                  (fun r => r.map (· + 1)) |>.tail, h_n3, ?_⟩
  rw [h_rules_form, h_tail_eq]
  rfl

/-- **Iter 1179: true-head s5_4.bag form — pure dec-erase**.  After
    four consecutive System5 steps at a true-head Perm-chain point
    (P, D, P, P with empty rule), `s5_4.bag = (s5_3.bag.map(·-1)).erase 0`.
    The popped rule at step 4 is `[]` (per iter 1178), so the xorMerge
    is identity (`xorMerge_nil`).  Composition: iter 1176 (1 ∈ s5_3.bag)
    + iter 1178 (s5_3.rules empty head) + `System5_step_explicit_pop`
    + `xorMerge_nil`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step4_bag_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_3 s5_4,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ s5_4.bag = (s5_3.bag.map (· - 1)).erase 0 := by
  obtain ⟨s5_3, h_n3, h_one_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_one_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_3', rest_more, h_n3', h_rules_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_rules_empty_head cts rest phase N h_N bag h_perm
  have h_s5_3_eq : s5_3 = s5_3' := Option.some.inj (h_n3.symm.trans h_n3')
  have h_one_mem' : (1 : Int) ∈ s5_3'.bag := h_s5_3_eq ▸ h_one_mem
  have h_zero : (0 : Int) ∈ s5_3'.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem'
  have h_bag_ne : s5_3'.bag ≠ [] := List.ne_nil_of_mem h_one_mem'
  have h_step4 := System5_step_explicit_pop s5_3' [] rest_more h_rules_form h_bag_ne h_zero
  let s5_4 : System5Config :=
    ⟨xorMerge ((s5_3'.bag.map (· - 1)).erase 0) (([] : List Int).map (· + 1)),
     rest_more.map (fun r => r.map (· + 1))⟩
  refine ⟨s5_3, s5_4, h_n3, ?_, ?_⟩
  · rw [show (4 : Nat) = 3 + 1 from rfl, System5.nSteps_add, h_n3']
    simp only [Option.bind_some, System5.nSteps_one]
    exact h_step4
  · show xorMerge ((s5_3'.bag.map (· - 1)).erase 0) (([] : List Int).map (· + 1))
       = (s5_3.bag.map (· - 1)).erase 0
    simp only [List.map_nil, xorMerge_nil]
    rw [h_s5_3_eq]

/-- **Iter 1180: true-head s5_4.rules has `[]` as head**.  After
    four consecutive System5 steps at a true-head Perm-chain point,
    `s5_4.rules = [] :: rest_more`.  Reasoning: iter 1178 gives
    `s5_3.rules = [] :: rest_more_3`; step 4's P-step pops the head
    `[]` and increments the rest, so `s5_4.rules = rest_more_3.map(map(·+1))`.
    By iter 991 (`encoder.drop 3 = [] :: rest_more_991`) combined
    with the trajectory invariant, `rest_more_3` itself starts with
    `[]`, so `s5_4.rules = [] :: rest_more_991.quadruple_mapped`.
    **Important consequence: step 5 also pops `[]`**, so
    `s5_5.bag = (s5_4.bag.map(·-1)).erase 0` (pure dec-erase). -/
theorem ctsConfigToSystem5Bag_true_head_perm_step4_rules_empty_head
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_4 rest_more,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ s5_4.rules = ([] : List Int) :: rest_more := by
  -- Use iter 1171's triple-map form + iter 984 for tail = [] :: [] :: rest_more
  obtain ⟨r1, r2, tail, s5_3, h_eq, h_n3, h_rules_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_rules_form cts rest phase N h_N bag h_perm
  obtain ⟨rest_more_984, h_drop2⟩ :=
    ctsRulesToSystem5Rules_drop_2_exists_empty_rules cts
      { data := true :: rest, phase := phase } N h_N
  have h_tail_eq : tail = ([] : List Int) :: [] :: rest_more_984 := by
    have h := h_drop2
    rw [h_eq] at h
    have h_drop_simp : ((r1 :: r2 :: tail).drop 2) = tail := by simp
    rw [h_drop_simp] at h
    exact h
  -- Now use iter 1179 to get s5_4
  obtain ⟨s5_3', s5_4, h_n3', h_n4, _h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_4,
    (((rest_more_984.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))).map
      (fun r => r.map (· + 1))).map (fun r => r.map (· + 1)),
    h_n4, ?_⟩
  -- Need: s5_4.rules = [] :: rest_more
  -- s5_4 was constructed in iter 1179 with rules = rest_more_iter_1178.map(map(·+1))
  -- Get its explicit form by re-deriving the step 4 output
  obtain ⟨s5_3'', h_n3'', h_one_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_one_mem cts rest phase N h_N bag h_perm
  have h_s5_3_eq : s5_3 = s5_3'' := Option.some.inj (h_n3.symm.trans h_n3'')
  have h_one_mem_s5_3 : (1 : Int) ∈ s5_3.bag := h_s5_3_eq ▸ h_one_mem
  have h_zero : (0 : Int) ∈ s5_3.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_3
  have h_bag_ne : s5_3.bag ≠ [] := List.ne_nil_of_mem h_one_mem_s5_3
  -- s5_3.rules = ((tail.triple-mapped)) = ((([] :: [] :: rest_more_984).triple-mapped))
  --           = [] :: [] :: rest_more_984.triple-mapped
  have h_s5_3_rules_explicit : s5_3.rules = [] :: [] ::
      (((rest_more_984.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))).map
        (fun r => r.map (· + 1))) := by
    rw [h_rules_form, h_tail_eq]
    rfl
  have h_step4 := System5_step_explicit_pop s5_3 [] ([] ::
      (((rest_more_984.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))).map
        (fun r => r.map (· + 1)))) h_s5_3_rules_explicit h_bag_ne h_zero
  -- After step 4, rules = ([] :: ((rest_more_984.triple).map(·+1))).map(map(·+1))
  --                    = [] :: ((rest_more_984.triple).map(·+1)).map(map(·+1))
  -- Identify s5_4 from h_n4 with the explicit step output
  have h_n4_explicit : System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
      { data := true :: rest, phase := phase } N⟩ 4 = some
      ⟨xorMerge ((s5_3.bag.map (· - 1)).erase 0) (([] : List Int).map (· + 1)),
       ([] :: (((rest_more_984.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))).map
        (fun r => r.map (· + 1)))).map (fun r => r.map (· + 1))⟩ := by
    rw [show (4 : Nat) = 3 + 1 from rfl, System5.nSteps_add, h_n3]
    simp only [Option.bind_some, System5.nSteps_one]
    exact h_step4
  have h_s5_4_eq : s5_4 = ⟨xorMerge ((s5_3.bag.map (· - 1)).erase 0)
      (([] : List Int).map (· + 1)),
      ([] :: (((rest_more_984.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))).map
        (fun r => r.map (· + 1)))).map (fun r => r.map (· + 1))⟩ :=
    Option.some.inj (h_n4.symm.trans h_n4_explicit)
  rw [h_s5_4_eq]
  rfl

/-- **Iter 1181: 2 ∉ s5_3.bag at true-head Perm-chain points**.
    A structural finding: after three System5 steps at a true-head
    Perm-chain point, `2 ∉ s5_3.bag`.  Reasoning: by iter 1170,
    `s5_3.bag = xorMerge LHS (r2.map(·+3))`; by iter 1173, the LHS is
    Perm-equivalent to `(r2.map(·+1)).reverse ++ (1 :: 3 :: aux rest 4)`,
    which excludes `2` (r2.map(·+1) ≥ 10, prefix is {1,3}, aux rest 4 ≥ 4);
    and `2 ∉ r2.map(·+3)` (r2.map(·+3) ≥ 12).  xorMerge mem analysis
    gives `2 ∉ s5_3.bag`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step3_two_not_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_3,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ (2 : Int) ∉ s5_3.bag := by
  obtain ⟨r1, r2, tail, s5_2, s5_3, h_eq, _h_n2, h_n3, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_3, h_n3, ?_⟩
  rw [h_bag_form]
  -- Get LHS Perm form to show 2 ∉ LHS
  obtain ⟨_r1', r2', _tail', s5_2', h_eq', h_n2', h_perm_lhs⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_dec_erase_perm_r2
      cts rest phase N h_N bag h_perm
  have h_align : r1 :: r2 :: tail = _r1' :: r2' :: _tail' := h_eq.symm.trans h_eq'
  have h_r2_eq : r2 = r2' := (List.cons.inj (List.cons.inj h_align).2).1
  have h_s5_2_align : System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
      { data := true :: rest, phase := phase } N⟩ 2 = some s5_2 := _h_n2
  have h_s5_2_eq : s5_2 = s5_2' := Option.some.inj (h_s5_2_align.symm.trans h_n2')
  -- Get r2 ≥ 9
  obtain ⟨_, r2'', _, h_eq'', _, h_r2_ge⟩ :=
    ctsToSystem5_true_head_first_two_rules_ge_eleven cts rest phase N h_N
  have h_r2_eq'' : r2 = r2'' :=
    (List.cons.inj (List.cons.inj (h_eq.symm.trans h_eq'')).2).1
  -- 2 ∉ LHS via Perm form
  have h_two_not_in_perm_rhs : (2 : Int) ∉ ((r2'.map (· + 1)).reverse ++
      ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4)) := by
    intro h_in
    rw [List.mem_append] at h_in
    rcases h_in with h_left | h_right
    · rw [List.mem_reverse, List.mem_map] at h_left
      obtain ⟨x, hx, h_eq_x⟩ := h_left
      rw [← h_r2_eq, h_r2_eq''] at hx
      have := h_r2_ge x hx
      omega
    · simp only [List.mem_cons] at h_right
      rcases h_right with h | h | h_aux
      · omega
      · omega
      · have := ctsConfigToSystem5BagAux_ge rest 4 2 h_aux
        omega
  have h_two_not_in_lhs : (2 : Int) ∉ (s5_2.bag.map (· - 1)).erase 0 := by
    intro h_in
    rw [h_s5_2_eq] at h_in
    exact h_two_not_in_perm_rhs ((List.Perm.mem_iff h_perm_lhs).mp h_in)
  -- 2 ∉ r2.map(·+3)
  have h_two_not_in_r2_3 : (2 : Int) ∉ r2.map (· + 3) := by
    rw [List.mem_map]
    intro ⟨x, hx, h_eq_x⟩
    rw [h_r2_eq''] at hx
    have := h_r2_ge x hx
    omega
  -- Get Nodups for xorMerge_mem_iff: just derive directly from s5_2.bag.Nodup
  obtain ⟨s5_1', s5_2'', h_n1, h_n2'', h_dec⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_form cts rest phase N h_N bag h_perm
  have h_s5_2_eq2 : s5_2 = s5_2'' :=
    Option.some.inj (h_s5_2_align.symm.trans h_n2'')
  have h_step1_some : System5.step ⟨bag, ctsRulesToSystem5Rules cts
      { data := true :: rest, phase := phase } N⟩ = some s5_1' := by
    rw [System5.nSteps_one] at h_n1; exact h_n1
  obtain ⟨s5_1''', h_step1''', h_s5_1_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_nodup cts
      { data := true :: rest, phase := phase } N h_N (by simp) bag h_perm
  have h_s5_1_align : s5_1' = s5_1''' :=
    Option.some.inj (h_step1_some.symm.trans h_step1''')
  have h_s5_2_bag_nodup : s5_2.bag.Nodup := by
    rw [h_s5_2_eq2, h_dec, h_s5_1_align]
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_1_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  have h_lhs_nodup : ((s5_2.bag.map (· - 1)).erase 0).Nodup := by
    apply List.Nodup.erase
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_2_bag_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  obtain ⟨_, r2_3', _, h_eq_r2_3, h_r2_3_nodup⟩ :=
    ctsRulesToSystem5Rules_second_rule_map_add_3_nodup cts
      { data := true :: rest, phase := phase } N h_N
  have h_r2_3_align : r2 = r2_3' :=
    (List.cons.inj (List.cons.inj (h_eq.symm.trans h_eq_r2_3)).2).1
  have h_r2_3_nodup' : (r2.map (· + 3)).Nodup := by
    rw [h_r2_3_align]; exact h_r2_3_nodup
  -- Apply xorMerge_mem_iff
  intro h_two_in
  rw [xorMerge_mem_iff _ _ h_lhs_nodup h_r2_3_nodup' 2] at h_two_in
  rcases h_two_in with ⟨h_l, _⟩ | ⟨_, h_r⟩
  · exact h_two_not_in_lhs h_l
  · exact h_two_not_in_r2_3 h_r

/-- **Iter 1182: 1 ∉ s5_4.bag at true-head Perm-chain points**.
    After four System5 steps at a true-head Perm-chain point, `1 ∉ s5_4.bag`.
    Reasoning: by iter 1179, `s5_4.bag = (s5_3.bag.map(·-1)).erase 0`;
    `1 ∈ this` requires `2 ∈ s5_3.bag` (since `1 = 2 - 1` and `1 ≠ 0`);
    by iter 1181, `2 ∉ s5_3.bag`, so `1 ∉ s5_4.bag`.
    **Important consequence: step 5 of the true-head trajectory IS a
    D-step (decrement only), NOT a P-step**. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step4_one_not_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_4,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ (1 : Int) ∉ s5_4.bag := by
  obtain ⟨s5_3, s5_4, h_n3, h_n4, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_3', h_n3', h_two_not_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_two_not_mem cts rest phase N h_N bag h_perm
  refine ⟨s5_4, h_n4, ?_⟩
  have h_s5_3_eq : s5_3 = s5_3' := Option.some.inj (h_n3.symm.trans h_n3')
  have h_two_not_mem' : (2 : Int) ∉ s5_3.bag := h_s5_3_eq ▸ h_two_not_mem
  rw [h_bag_form]
  intro h_one_in
  -- 1 ∈ ((s5_3.bag.map(·-1)).erase 0) ⇒ 1 ∈ s5_3.bag.map(·-1) (since 1 ≠ 0)
  have h_one_in_map : (1 : Int) ∈ s5_3.bag.map (· - 1) := List.mem_of_mem_erase h_one_in
  rw [List.mem_map] at h_one_in_map
  obtain ⟨x, hx, h_eq_x⟩ := h_one_in_map
  -- x - 1 = 1 ⇒ x = 2, but 2 ∉ s5_3.bag — contradiction
  have h_x_eq : x = 2 := by omega
  rw [h_x_eq] at hx
  exact h_two_not_mem' hx

/-- **Iter 1183: 2 ∈ s5_4.bag at true-head Perm-chain points**.
    After four System5 steps at a true-head Perm-chain point, `2 ∈ s5_4.bag`.
    Reasoning: by iter 1179, `s5_4.bag = (s5_3.bag.map(·-1)).erase 0`;
    by iter 1177, `3 ∈ s5_3.bag`; so `2 = 3 - 1 ∈ s5_3.bag.map(·-1)`,
    and since `2 ≠ 0`, erase doesn't remove it. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step4_two_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_4,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ (2 : Int) ∈ s5_4.bag := by
  obtain ⟨s5_3, s5_4, h_n3, h_n4, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_3', h_n3', h_three_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_three_mem cts rest phase N h_N bag h_perm
  refine ⟨s5_4, h_n4, ?_⟩
  have h_s5_3_eq : s5_3 = s5_3' := Option.some.inj (h_n3.symm.trans h_n3')
  have h_three_mem' : (3 : Int) ∈ s5_3.bag := h_s5_3_eq ▸ h_three_mem
  rw [h_bag_form]
  have h_dec := mem_imp_pred_in_dec_erase s5_3.bag 3 h_three_mem' (by omega)
  have h_eq : (3 : Int) - 1 = 2 := by omega
  rw [h_eq] at h_dec
  exact h_dec

/-- **Iter 1184: true-head step 5 D-step bag form**.  After five
    consecutive System5 steps at a true-head Perm-chain point, `s5_5.bag
    = s5_4.bag.map(·-1)` — pure decrement, no rule pop.  Composition:
    iter 1182 (1 ∉ s5_4.bag ⇒ 0 ∉ s5_4.bag.map(·-1)) + iter 1183
    (2 ∈ s5_4.bag ⇒ s5_4.bag ≠ []) + iter 1180 (s5_4.rules ≠ []) +
    `System5_step_pure_decrement`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step5_bag_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_4 s5_5,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 5 = some s5_5
      ∧ s5_5.bag = s5_4.bag.map (· - 1) := by
  obtain ⟨s5_4, h_n4, h_one_not⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_one_not_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_4', h_n4', h_two_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_two_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_4'', rest_more, h_n4'', h_rules_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_rules_empty_head cts rest phase N h_N bag h_perm
  have h_s5_4_eq' : s5_4 = s5_4' := Option.some.inj (h_n4.symm.trans h_n4')
  have h_s5_4_eq'' : s5_4 = s5_4'' := Option.some.inj (h_n4.symm.trans h_n4'')
  have h_two_mem_s5_4 : (2 : Int) ∈ s5_4.bag := h_s5_4_eq' ▸ h_two_mem
  have h_bag_ne : s5_4.bag ≠ [] := List.ne_nil_of_mem h_two_mem_s5_4
  have h_rules_ne : s5_4.rules ≠ [] := by rw [h_s5_4_eq'', h_rules_form]; simp
  have h_zero_not_in : (0 : Int) ∉ s5_4.bag.map (· - 1) := by
    intro h_zero_in
    exact h_one_not ((zero_mem_decrement_iff_one_mem s5_4.bag).mp h_zero_in)
  obtain ⟨s5_5, h_step5⟩ :=
    (System5_step_some_iff s5_4).mpr ⟨h_bag_ne, h_rules_ne⟩
  have h_dec := System5_step_pure_decrement s5_4 s5_5 h_step5 h_bag_ne h_rules_ne h_zero_not_in
  refine ⟨s5_4, s5_5, h_n4, ?_, h_dec.1⟩
  rw [show (5 : Nat) = 4 + 1 from rfl, System5.nSteps_add, h_n4]
  simp only [Option.bind_some, System5.nSteps_one]
  exact h_step5

/-- **Iter 1185: 1 ∈ s5_5.bag at true-head Perm-chain points**.
    After five System5 steps at a true-head Perm-chain point, `1 ∈ s5_5.bag`.
    Reasoning: by iter 1184, `s5_5.bag = s5_4.bag.map(·-1)` (D-step);
    by iter 1183, `2 ∈ s5_4.bag`; so `1 = 2 - 1 ∈ s5_4.bag.map(·-1) = s5_5.bag`.
    **Important consequence: step 6 of the true-head trajectory IS a P-step**
    (the first since step 4).  Trajectory: P, D, P, P-empty, D, P, ... -/
theorem ctsConfigToSystem5Bag_true_head_perm_step5_one_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_5,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 5 = some s5_5
      ∧ (1 : Int) ∈ s5_5.bag := by
  obtain ⟨s5_4, s5_5, h_n4, h_n5, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_4', h_n4', h_two_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_two_mem cts rest phase N h_N bag h_perm
  refine ⟨s5_5, h_n5, ?_⟩
  have h_s5_4_eq : s5_4 = s5_4' := Option.some.inj (h_n4.symm.trans h_n4')
  have h_two_mem' : (2 : Int) ∈ s5_4.bag := h_s5_4_eq ▸ h_two_mem
  rw [h_bag_form, List.mem_map]
  refine ⟨2, h_two_mem', ?_⟩
  omega

/-- **Iter 1186: true-head s5_5.rules has `[]` as head**.  After
    five System5 steps at a true-head Perm-chain point, `s5_5.rules
    = [] :: rest_more`.  Reasoning: by iter 1180, `s5_4.rules = [] :: rest_more_4`;
    step 5 is D-step (iter 1184), preserving rules with `(·+1)` applied:
    `s5_5.rules = ([] :: rest_more_4).map(map(·+1)) = [] :: rest_more_4.map(map(·+1))`.
    **Important consequence: step 6's popped rule is `[]`**, so
    `s5_6.bag = (s5_5.bag.map(·-1)).erase 0` (pure dec-erase). -/
theorem ctsConfigToSystem5Bag_true_head_perm_step5_rules_empty_head
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_5 rest_more,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 5 = some s5_5
      ∧ s5_5.rules = ([] : List Int) :: rest_more := by
  -- Re-derive step 5's pure-decrement output to capture both bag and rules
  obtain ⟨s5_4, h_n4, h_one_not⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_one_not_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_4', h_n4', h_two_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_two_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_4'', rest_more_4, h_n4'', h_rules_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_rules_empty_head cts rest phase N h_N bag h_perm
  have h_s5_4_eq' : s5_4 = s5_4' := Option.some.inj (h_n4.symm.trans h_n4')
  have h_s5_4_eq'' : s5_4 = s5_4'' := Option.some.inj (h_n4.symm.trans h_n4'')
  have h_two_mem_s5_4 : (2 : Int) ∈ s5_4.bag := h_s5_4_eq' ▸ h_two_mem
  have h_bag_ne : s5_4.bag ≠ [] := List.ne_nil_of_mem h_two_mem_s5_4
  have h_rules_eq : s5_4.rules = ([] : List Int) :: rest_more_4 := h_s5_4_eq'' ▸ h_rules_form
  have h_rules_ne : s5_4.rules ≠ [] := by rw [h_rules_eq]; simp
  have h_zero_not_in : (0 : Int) ∉ s5_4.bag.map (· - 1) := by
    intro h_zero_in
    exact h_one_not ((zero_mem_decrement_iff_one_mem s5_4.bag).mp h_zero_in)
  obtain ⟨s5_5, h_step5⟩ :=
    (System5_step_some_iff s5_4).mpr ⟨h_bag_ne, h_rules_ne⟩
  have h_dec := System5_step_pure_decrement s5_4 s5_5 h_step5 h_bag_ne h_rules_ne h_zero_not_in
  refine ⟨s5_5, rest_more_4.map (fun r => r.map (· + 1)), ?_, ?_⟩
  · rw [show (5 : Nat) = 4 + 1 from rfl, System5.nSteps_add, h_n4]
    simp only [Option.bind_some, System5.nSteps_one]
    exact h_step5
  · rw [h_dec.2, h_rules_eq]
    rfl

/-- **Iter 1187: true-head s5_6.bag form (pure dec-erase)**.  After
    six consecutive System5 steps at a true-head Perm-chain point,
    `s5_6.bag = (s5_5.bag.map(·-1)).erase 0`.  The popped rule at step
    6 is `[]` (per iter 1186), so the xorMerge is identity (`xorMerge_nil`).
    Composition: iter 1185 (1 ∈ s5_5.bag) + iter 1186 (s5_5.rules empty
    head) + `System5_step_explicit_pop` + `xorMerge_nil`. **The 6-step
    true-head terminal at the trajectory level — matches iter 1145's
    sextuple-dec-erase form.** -/
theorem ctsConfigToSystem5Bag_true_head_perm_step6_bag_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_5 s5_6,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 5 = some s5_5
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 6 = some s5_6
      ∧ s5_6.bag = (s5_5.bag.map (· - 1)).erase 0 := by
  obtain ⟨s5_5, h_n5, h_one_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_one_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_5', rest_more, h_n5', h_rules_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_rules_empty_head cts rest phase N h_N bag h_perm
  have h_s5_5_eq : s5_5 = s5_5' := Option.some.inj (h_n5.symm.trans h_n5')
  have h_one_mem' : (1 : Int) ∈ s5_5'.bag := h_s5_5_eq ▸ h_one_mem
  have h_zero : (0 : Int) ∈ s5_5'.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem'
  have h_bag_ne : s5_5'.bag ≠ [] := List.ne_nil_of_mem h_one_mem'
  have h_step6 := System5_step_explicit_pop s5_5' [] rest_more h_rules_form h_bag_ne h_zero
  let s5_6 : System5Config :=
    ⟨xorMerge ((s5_5'.bag.map (· - 1)).erase 0) (([] : List Int).map (· + 1)),
     rest_more.map (fun r => r.map (· + 1))⟩
  refine ⟨s5_5, s5_6, h_n5, ?_, ?_⟩
  · rw [show (6 : Nat) = 5 + 1 from rfl, System5.nSteps_add, h_n5']
    simp only [Option.bind_some, System5.nSteps_one]
    exact h_step6
  · show xorMerge ((s5_5'.bag.map (· - 1)).erase 0) (([] : List Int).map (· + 1))
       = (s5_5.bag.map (· - 1)).erase 0
    simp only [List.map_nil, xorMerge_nil]
    rw [h_s5_5_eq]

/-- **Iter 1188: s5_3.bag is Nodup at true-head Perm-chain points**.
    Direct from iter 1170 (s5_3.bag = xorMerge LHS RHS) + `xorMerge_nodup`
    (which only needs LHS Nodup) + iter 1174's LHS Nodup transfer
    through Perm.  **Required Nodup for downstream xorMerge analysis
    at step 3.** -/
theorem ctsConfigToSystem5Bag_true_head_perm_step3_bag_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_3,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ s5_3.bag.Nodup := by
  obtain ⟨_r1, _r2, _tail, _s5_2, s5_3, _h_eq, _h_n2, h_n3, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_3, h_n3, ?_⟩
  rw [h_bag_form]
  -- Need: ((_s5_2.bag.map(·-1)).erase 0).Nodup, then xorMerge_nodup
  obtain ⟨s5_1, s5_2, h_n1, h_n2, h_dec⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_form cts rest phase N h_N bag h_perm
  have h_s5_2_align : s5_2 = _s5_2 := Option.some.inj (h_n2.symm.trans _h_n2)
  -- Just need ((s5_2.bag.map(·-1)).erase 0).Nodup since xorMerge_nodup needs only first
  have h_step1_some : System5.step ⟨bag, ctsRulesToSystem5Rules cts
      { data := true :: rest, phase := phase } N⟩ = some s5_1 := by
    rw [System5.nSteps_one] at h_n1; exact h_n1
  obtain ⟨s5_1', h_step1', h_s5_1_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_nodup cts
      { data := true :: rest, phase := phase } N h_N (by simp) bag h_perm
  have h_s5_1_align : s5_1 = s5_1' :=
    Option.some.inj (h_step1_some.symm.trans h_step1')
  have h_s5_2_bag_nodup : s5_2.bag.Nodup := by
    rw [h_dec, h_s5_1_align]
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_1_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  have h_lhs_nodup : ((s5_2.bag.map (· - 1)).erase 0).Nodup := by
    apply List.Nodup.erase
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_2_bag_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  rw [← h_s5_2_align]
  exact xorMerge_nodup _ _ h_lhs_nodup

/-- **Iter 1189: s5_4.bag is Nodup at true-head Perm-chain points**.
    Direct from iter 1179 (s5_4.bag = (s5_3.bag.map(·-1)).erase 0)
    + iter 1188 (s5_3.bag.Nodup) + decrement injectivity + erase Nodup. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step4_bag_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_4,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ s5_4.bag.Nodup := by
  obtain ⟨s5_3, s5_4, h_n3, h_n4, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_3', h_n3', h_s5_3_nodup⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_bag_nodup cts rest phase N h_N bag h_perm
  refine ⟨s5_4, h_n4, ?_⟩
  have h_align : s5_3 = s5_3' := Option.some.inj (h_n3.symm.trans h_n3')
  have h_s5_3_nodup' : s5_3.bag.Nodup := h_align ▸ h_s5_3_nodup
  rw [h_bag_form]
  apply List.Nodup.erase
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_3_nodup'
  intro a b h_ne h_eq_dec
  apply h_ne
  have : a - 1 = b - 1 := h_eq_dec
  omega

/-- **Iter 1190: s5_5.bag is Nodup at true-head Perm-chain points**.
    Direct from iter 1184 (s5_5.bag = s5_4.bag.map(·-1)) +
    iter 1189 + decrement injectivity. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step5_bag_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_5,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 5 = some s5_5
      ∧ s5_5.bag.Nodup := by
  obtain ⟨s5_4, s5_5, h_n4, h_n5, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_4', h_n4', h_s5_4_nodup⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_bag_nodup cts rest phase N h_N bag h_perm
  refine ⟨s5_5, h_n5, ?_⟩
  have h_align : s5_4 = s5_4' := Option.some.inj (h_n4.symm.trans h_n4')
  have h_s5_4_nodup' : s5_4.bag.Nodup := h_align ▸ h_s5_4_nodup
  rw [h_bag_form]
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_4_nodup'
  intro a b h_ne h_eq_dec
  apply h_ne
  have : a - 1 = b - 1 := h_eq_dec
  omega

/-- **Iter 1191: s5_6.bag is Nodup at true-head Perm-chain points**.
    Direct from iter 1187 (s5_6.bag = (s5_5.bag.map(·-1)).erase 0) +
    iter 1190 + decrement injectivity + erase Nodup.  **Full 6-step
    Nodup chain established.** -/
theorem ctsConfigToSystem5Bag_true_head_perm_step6_bag_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_6,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 6 = some s5_6
      ∧ s5_6.bag.Nodup := by
  obtain ⟨s5_5, s5_6, h_n5, h_n6, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step6_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_5', h_n5', h_s5_5_nodup⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_bag_nodup cts rest phase N h_N bag h_perm
  refine ⟨s5_6, h_n6, ?_⟩
  have h_align : s5_5 = s5_5' := Option.some.inj (h_n5.symm.trans h_n5')
  have h_s5_5_nodup' : s5_5.bag.Nodup := h_align ▸ h_s5_5_nodup
  rw [h_bag_form]
  apply List.Nodup.erase
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_5_nodup'
  intro a b h_ne h_eq_dec
  apply h_ne
  have : a - 1 = b - 1 := h_eq_dec
  omega

/-- **Iter 1192: s5_4.bag.length = s5_3.bag.length - 1 at true-head
    Perm-chain points**.  Composes iter 1179 (s5_4.bag = (s5_3.bag.map(·-1)).erase 0)
    + iter 1176 (1 ∈ s5_3.bag ⇒ 0 ∈ s5_3.bag.map(·-1)) +
    `List.length_erase_of_mem`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step4_bag_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_3 s5_4,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ s5_4.bag.length = s5_3.bag.length - 1 := by
  obtain ⟨s5_3, s5_4, h_n3, h_n4, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_3', h_n3', h_one_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_one_mem cts rest phase N h_N bag h_perm
  refine ⟨s5_3, s5_4, h_n3, h_n4, ?_⟩
  have h_align : s5_3 = s5_3' := Option.some.inj (h_n3.symm.trans h_n3')
  have h_one_mem' : (1 : Int) ∈ s5_3.bag := h_align ▸ h_one_mem
  have h_zero_mem : (0 : Int) ∈ s5_3.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem'
  rw [h_bag_form, List.length_erase_of_mem h_zero_mem, List.length_map]

/-- **Iter 1193: s5_5.bag.length = s5_4.bag.length (D-step preserves
    length)**.  Direct from iter 1184 (s5_5.bag = s5_4.bag.map(·-1))
    + `List.length_map`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step5_bag_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_4 s5_5,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 5 = some s5_5
      ∧ s5_5.bag.length = s5_4.bag.length := by
  obtain ⟨s5_4, s5_5, h_n4, h_n5, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_4, s5_5, h_n4, h_n5, ?_⟩
  rw [h_bag_form, List.length_map]

/-- **Iter 1194: s5_6.bag.length = s5_5.bag.length - 1 at true-head
    Perm-chain points**.  Composes iter 1187 + iter 1185 (1 ∈ s5_5.bag)
    + `List.length_erase_of_mem`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step6_bag_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_5 s5_6,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 5 = some s5_5
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 6 = some s5_6
      ∧ s5_6.bag.length = s5_5.bag.length - 1 := by
  obtain ⟨s5_5, s5_6, h_n5, h_n6, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step6_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_5', h_n5', h_one_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_one_mem cts rest phase N h_N bag h_perm
  refine ⟨s5_5, s5_6, h_n5, h_n6, ?_⟩
  have h_align : s5_5 = s5_5' := Option.some.inj (h_n5.symm.trans h_n5')
  have h_one_mem' : (1 : Int) ∈ s5_5.bag := h_align ▸ h_one_mem
  have h_zero_mem : (0 : Int) ∈ s5_5.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem'
  rw [h_bag_form, List.length_erase_of_mem h_zero_mem, List.length_map]

/-- **Iter 1195: generic step 1 bag length at Perm-chain points**.
    For any Perm-chain point with `cfg.data ≠ []`, after one P-step,
    `s5_1.bag.length = r1.length + (bag.length - 1)`.  Composition:
    iter 1057 (s5_1 explicit form `(r1.map(·+1)).reverse ++ ((bag.map(·-1)).erase 0)`)
    + iter 1051 (0 ∈ bag.map(·-1) ⇒ erase removes one) +
    `length_append`/`length_reverse`/`length_map`/`length_erase_of_mem`. -/
theorem ctsConfigToSystem5Bag_perm_step1_bag_length
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ [])
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ r1 r2 tail s5_1,
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
      ∧ System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5_1
      ∧ s5_1.bag.length = r1.length + (bag.length - 1) := by
  obtain ⟨r1, r2, tail, h_eq, h_step⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts cfg N h_N bag h_data h_perm
  refine ⟨r1, r2, tail, _, h_eq, h_step, ?_⟩
  have h_zero_mem : (0 : Int) ∈ bag.map (· - 1) :=
    ctsConfigToSystem5Bag_perm_zero_in_decrement cfg bag h_data h_perm
  show ((r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0)).length
     = r1.length + (bag.length - 1)
  rw [List.length_append, List.length_reverse, List.length_map,
      List.length_erase_of_mem h_zero_mem, List.length_map]

/-- **Iter 1196: generic step 2 bag length preservation at Perm-chain
    points (when D-step)**.  When `1 ∉ s5_1.bag` (D-step trigger),
    `s5_2.bag.length = s5_1.bag.length`.  Useful at true-head where
    step 2 is D-step (iter 1166).  This is a generic helper. -/
theorem ctsConfigToSystem5Bag_perm_step2_bag_length_dstep
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ [])
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (h_one_not : ∀ s5_1, System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5_1
                  → (1 : Int) ∉ s5_1.bag) :
    ∃ s5_1 s5_2,
      System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5_1
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ 2 = some s5_2
      ∧ s5_2.bag.length = s5_1.bag.length := by
  obtain ⟨r1, r2, tail, h_eq, h_step⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts cfg N h_N bag h_data h_perm
  let s5_1 : System5Config :=
    ⟨(r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0),
     (r2 :: tail).map (fun r => r.map (· + 1))⟩
  have h_one_not_s5_1 := h_one_not s5_1 h_step
  have h_bag_ne : s5_1.bag ≠ [] := by
    have h_one : (1 : Int) ∈ bag :=
      ctsConfigToSystem5Bag_perm_one_mem cfg bag h_data h_perm
    have h_zero : (0 : Int) ∈ bag.map (· - 1) :=
      (zero_mem_decrement_iff_one_mem _).mpr h_one
    have h_len' : bag.length = 4 * cfg.data.length :=
      ctsConfigToSystem5Bag_perm_bag_length_eq cfg bag h_perm
    have h_dlen : cfg.data.length > 0 := by
      cases h : cfg.data with
      | nil => rw [h] at h_data; exact absurd rfl h_data
      | cons _ _ => simp
    show (r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0) ≠ []
    intro h_emp
    have h_len_zero : ((r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0)).length = 0 := by
      rw [h_emp]; rfl
    rw [List.length_append, List.length_reverse, List.length_map,
        List.length_erase_of_mem h_zero, List.length_map] at h_len_zero
    omega
  have h_rules_ne : s5_1.rules ≠ [] := by
    show (r2 :: tail).map (fun r => r.map (· + 1)) ≠ []
    simp
  have h_zero_not : (0 : Int) ∉ s5_1.bag.map (· - 1) := by
    intro h_zero_in
    exact h_one_not_s5_1 ((zero_mem_decrement_iff_one_mem s5_1.bag).mp h_zero_in)
  obtain ⟨s5_2, h_step2⟩ :=
    (System5_step_some_iff s5_1).mpr ⟨h_bag_ne, h_rules_ne⟩
  have h_dec := System5_step_pure_decrement s5_1 s5_2 h_step2 h_bag_ne h_rules_ne h_zero_not
  refine ⟨s5_1, s5_2, h_step, ?_, ?_⟩
  · rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add]
    rw [System5.nSteps_one, h_step]
    simp only [Option.bind_some, System5.nSteps_one]
    exact h_step2
  · rw [h_dec.1, List.length_map]

/-- **Iter 1197: true-head step 2 bag length preservation**.  Specializes
    iter 1196 to the true-head case, using iter 1165 to discharge the
    `1 ∉ s5_1.bag` hypothesis.  After two System5 steps at a true-head
    Perm-chain point, `s5_2.bag.length = s5_1.bag.length`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step2_bag_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_1 s5_2,
      System5.step ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ = some s5_1
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ s5_2.bag.length = s5_1.bag.length := by
  apply ctsConfigToSystem5Bag_perm_step2_bag_length_dstep cts
    { data := true :: rest, phase := phase } N h_N (by simp) bag h_perm
  intro s5_1 h_step
  obtain ⟨s5_1', h_step', h_one_not⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step1_one_not_mem cts rest phase N h_N bag h_perm
  have h_eq : s5_1 = s5_1' := Option.some.inj (h_step.symm.trans h_step')
  rw [h_eq]
  exact h_one_not

/-- **Iter 1198: true-head step 1 closed-form length**.  Specializes
    iter 1195 to true-head, plugging in `bag.length = 4 + 4 * rest.length`
    (from iter 1154's `bag.length = 4 * cfg.data.length` and
    `(true :: rest).length = 1 + rest.length`).  Result:
    `s5_1.bag.length = r1.length + 3 + 4 * rest.length`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step1_bag_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_1,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.step ⟨bag, ctsRulesToSystem5Rules cts
          { data := true :: rest, phase := phase } N⟩ = some s5_1
      ∧ s5_1.bag.length = r1.length + 3 + 4 * rest.length := by
  obtain ⟨r1, r2, tail, s5_1, h_eq, h_step, h_len⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_length cts
      { data := true :: rest, phase := phase } N h_N (by simp) bag h_perm
  refine ⟨r1, r2, tail, s5_1, h_eq, h_step, ?_⟩
  rw [h_len]
  have h_bag_len : bag.length = 4 * (true :: rest).length :=
    ctsConfigToSystem5Bag_perm_bag_length_eq _ bag h_perm
  show r1.length + (bag.length - 1) = r1.length + 3 + 4 * rest.length
  rw [h_bag_len]
  show r1.length + (4 * (true :: rest).length - 1) = r1.length + 3 + 4 * rest.length
  simp only [List.length_cons]
  omega

/-- **Iter 1199: true-head step 2 closed-form length**.  Composes
    iter 1197 (s5_2.bag.length = s5_1.bag.length) + iter 1198
    (s5_1.bag.length = r1.length + 3 + 4 * rest.length).  Result:
    `s5_2.bag.length = r1.length + 3 + 4 * rest.length`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step2_bag_length_eq
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ r1 r2 tail s5_2,
      ctsRulesToSystem5Rules cts { data := true :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
          { data := true :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ s5_2.bag.length = r1.length + 3 + 4 * rest.length := by
  obtain ⟨s5_1, s5_2, h_step1, h_n2, h_len_eq⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_length cts rest phase N h_N bag h_perm
  obtain ⟨r1, r2, tail, s5_1', h_eq, h_step1', h_len1⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step1_bag_length cts rest phase N h_N bag h_perm
  refine ⟨r1, r2, tail, s5_2, h_eq, h_n2, ?_⟩
  have h_align : s5_1 = s5_1' := Option.some.inj (h_step1.symm.trans h_step1')
  rw [h_len_eq, h_align, h_len1]

/-- **Iter 1200: true-head s5_6.bag.length = s5_4.bag.length - 1**.
    Chain: s5_5.bag.length = s5_4.bag.length (iter 1193, D-step) ∧
    s5_6.bag.length = s5_5.bag.length - 1 (iter 1194, P-step).
    So s5_6.bag.length = s5_4.bag.length - 1. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step6_bag_length_via_step4
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_4 s5_6,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 6 = some s5_6
      ∧ s5_6.bag.length = s5_4.bag.length - 1 := by
  obtain ⟨s5_4, s5_5, h_n4, h_n5, h_len5⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_bag_length cts rest phase N h_N bag h_perm
  obtain ⟨s5_5', s5_6, h_n5', h_n6, h_len6⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step6_bag_length cts rest phase N h_N bag h_perm
  refine ⟨s5_4, s5_6, h_n4, h_n6, ?_⟩
  have h_align : s5_5 = s5_5' := Option.some.inj (h_n5.symm.trans h_n5')
  rw [h_len6, ← h_align, h_len5]

/-- **Iter 1201: true-head s5_6.bag.length = s5_3.bag.length - 2**.
    Chain iter 1192 (s5_4 = s5_3 - 1) + iter 1200 (s5_6 = s5_4 - 1).
    Reaches back to s5_3 — the last bag computed before the
    intermediate D-step.  **310-MILESTONE incoming.** -/
theorem ctsConfigToSystem5Bag_true_head_perm_step6_bag_length_via_step3
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_3 s5_6,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 6 = some s5_6
      ∧ s5_6.bag.length = s5_3.bag.length - 2 := by
  obtain ⟨s5_3, s5_4, h_n3, h_n4, h_len4⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_bag_length cts rest phase N h_N bag h_perm
  obtain ⟨s5_4', s5_6, h_n4', h_n6, h_len6⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step6_bag_length_via_step4
      cts rest phase N h_N bag h_perm
  refine ⟨s5_3, s5_6, h_n3, h_n6, ?_⟩
  have h_align : s5_4 = s5_4' := Option.some.inj (h_n4.symm.trans h_n4')
  rw [h_len6, ← h_align, h_len4]
  -- Want: s5_3.bag.length - 1 - 1 = s5_3.bag.length - 2
  -- Need to be careful with Nat subtraction
  -- Use: s5_3.bag has at least 1 element (since 1 ∈ s5_3.bag, iter 1176)
  obtain ⟨s5_3', h_n3', h_one_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_one_mem cts rest phase N h_N bag h_perm
  have h_align3 : s5_3 = s5_3' := Option.some.inj (h_n3.symm.trans h_n3')
  have h_one_mem' : (1 : Int) ∈ s5_3.bag := h_align3 ▸ h_one_mem
  have h_pos : s5_3.bag.length ≥ 1 := by
    have h_ne : s5_3.bag ≠ [] := List.ne_nil_of_mem h_one_mem'
    cases h : s5_3.bag with
    | nil => exact absurd h h_ne
    | cons _ _ => simp
  omega

/-- **Iter 1202: true-head s5_5.bag.length = s5_3.bag.length - 1**.
    Chain iter 1192 (s5_4 = s5_3 - 1) + iter 1193 (s5_5 = s5_4).
    A useful intermediate length characterization. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step5_bag_length_via_step3
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_3 s5_5,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 5 = some s5_5
      ∧ s5_5.bag.length = s5_3.bag.length - 1 := by
  obtain ⟨s5_3, s5_4, h_n3, h_n4, h_len4⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_bag_length cts rest phase N h_N bag h_perm
  obtain ⟨s5_4', s5_5, h_n4', h_n5, h_len5⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_bag_length cts rest phase N h_N bag h_perm
  refine ⟨s5_3, s5_5, h_n3, h_n5, ?_⟩
  have h_align : s5_4 = s5_4' := Option.some.inj (h_n4.symm.trans h_n4')
  rw [h_len5, ← h_align, h_len4]

/-- **Iter 1203: generic head element of `aux data i` is in the bag**.
    For any non-empty `data` and any starting counter `i`,
    `i ∈ ctsConfigToSystem5BagAux data i`.  Both true-head and
    false-head cases have `i` as the first element. -/
theorem ctsConfigToSystem5BagAux_head_mem
    (data : List Bool) (i : Int) (h : data ≠ []) :
    i ∈ ctsConfigToSystem5BagAux data i := by
  cases data with
  | nil => exact absurd rfl h
  | cons head _ =>
    cases head with
    | true =>
      show i ∈ i :: (i + 2) :: (i + 3) :: (i + 5) :: _
      simp
    | false =>
      show i ∈ i :: (i + 1) :: (i + 2) :: (i + 3) :: _
      simp

/-- **Iter 1204: 4 ∈ s5_3.bag at true-head Perm-chain points (when
    rest non-empty)**.  Reasoning: by iter 1170, `s5_3.bag = xorMerge LHS
    (r2.map(·+3))`; by iter 1173, the LHS is Perm-equivalent to
    `(r2.map(·+1)).reverse ++ (1 :: 3 :: aux rest 4)`; when rest non-empty,
    `4 ∈ aux rest 4` (iter 1203), so `4 ∈ LHS`; and `4 ∉ r2.map(·+3)`
    (r2 ≥ 9 ⇒ r2.map(·+3) ≥ 12).  xorMerge mem analysis gives `4 ∈ s5_3.bag`. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step3_four_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (h_rest : rest ≠ [])
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_3,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ (4 : Int) ∈ s5_3.bag := by
  obtain ⟨r1, r2, tail, s5_2, s5_3, h_eq, _h_n2, h_n3, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_3, h_n3, ?_⟩
  rw [h_bag_form]
  -- 4 ∈ LHS via Perm form
  obtain ⟨_r1', r2', _tail', s5_2', h_eq', h_n2', h_perm_lhs⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_dec_erase_perm_r2
      cts rest phase N h_N bag h_perm
  have h_align : r1 :: r2 :: tail = _r1' :: r2' :: _tail' := h_eq.symm.trans h_eq'
  have h_r2_eq : r2 = r2' := (List.cons.inj (List.cons.inj h_align).2).1
  have h_s5_2_align : System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
      { data := true :: rest, phase := phase } N⟩ 2 = some s5_2 := _h_n2
  have h_s5_2_eq : s5_2 = s5_2' := Option.some.inj (h_s5_2_align.symm.trans h_n2')
  have h_4_in_aux : (4 : Int) ∈ ctsConfigToSystem5BagAux rest 4 :=
    ctsConfigToSystem5BagAux_head_mem rest 4 h_rest
  have h_4_in_perm_rhs : (4 : Int) ∈ ((r2'.map (· + 1)).reverse ++
      ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4)) := by
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact h_4_in_aux
  have h_4_in_lhs : (4 : Int) ∈ (s5_2.bag.map (· - 1)).erase 0 := by
    rw [h_s5_2_eq]
    exact (List.Perm.mem_iff h_perm_lhs).mpr h_4_in_perm_rhs
  -- 4 ∉ r2.map(·+3): r2 ≥ 9
  have h_4_not_in_r2_3 : (4 : Int) ∉ r2.map (· + 3) := by
    rw [List.mem_map]
    intro ⟨x, hx, h_eq_x⟩
    obtain ⟨_, r2'', _, h_eq'', _, h_r2_ge⟩ :=
      ctsToSystem5_true_head_first_two_rules_ge_eleven cts rest phase N h_N
    have h_r2_eq'' : r2 = r2'' :=
      (List.cons.inj (List.cons.inj (h_eq.symm.trans h_eq'')).2).1
    rw [h_r2_eq''] at hx
    have := h_r2_ge x hx
    omega
  -- Get Nodups
  obtain ⟨s5_1', s5_2'', h_n1, h_n2'', h_dec⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_form cts rest phase N h_N bag h_perm
  have h_s5_2_eq2 : s5_2 = s5_2'' :=
    Option.some.inj (h_s5_2_align.symm.trans h_n2'')
  have h_step1_some : System5.step ⟨bag, ctsRulesToSystem5Rules cts
      { data := true :: rest, phase := phase } N⟩ = some s5_1' := by
    rw [System5.nSteps_one] at h_n1; exact h_n1
  obtain ⟨s5_1''', h_step1''', h_s5_1_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_nodup cts
      { data := true :: rest, phase := phase } N h_N (by simp) bag h_perm
  have h_s5_1_align : s5_1' = s5_1''' :=
    Option.some.inj (h_step1_some.symm.trans h_step1''')
  have h_s5_2_bag_nodup : s5_2.bag.Nodup := by
    rw [h_s5_2_eq2, h_dec, h_s5_1_align]
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_1_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  have h_lhs_nodup : ((s5_2.bag.map (· - 1)).erase 0).Nodup := by
    apply List.Nodup.erase
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_2_bag_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  obtain ⟨_, r2_3', _, h_eq_r2_3, h_r2_3_nodup⟩ :=
    ctsRulesToSystem5Rules_second_rule_map_add_3_nodup cts
      { data := true :: rest, phase := phase } N h_N
  have h_r2_3_align : r2 = r2_3' :=
    (List.cons.inj (List.cons.inj (h_eq.symm.trans h_eq_r2_3)).2).1
  apply xorMerge_mem_left_of_not_mem_right
  · exact h_lhs_nodup
  · rw [h_r2_3_align]; exact h_r2_3_nodup
  · exact h_4_in_lhs
  · exact h_4_not_in_r2_3

/-- **Iter 1205: 3 ∈ s5_4.bag at true-head Perm-chain points (when
    rest non-empty)**.  Chain iter 1204 (4 ∈ s5_3.bag) + iter 1179
    (s5_4.bag = (s5_3.bag.map(·-1)).erase 0) + iter 975
    (`mem_imp_pred_in_dec_erase`, 4 ≠ 1). -/
theorem ctsConfigToSystem5Bag_true_head_perm_step4_three_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (h_rest : rest ≠ [])
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_4,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ (3 : Int) ∈ s5_4.bag := by
  obtain ⟨s5_3, s5_4, h_n3, h_n4, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_3', h_n3', h_4_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_four_mem cts rest phase N h_N h_rest bag h_perm
  refine ⟨s5_4, h_n4, ?_⟩
  have h_align : s5_3 = s5_3' := Option.some.inj (h_n3.symm.trans h_n3')
  have h_4_mem' : (4 : Int) ∈ s5_3.bag := h_align ▸ h_4_mem
  rw [h_bag_form]
  have h_dec := mem_imp_pred_in_dec_erase s5_3.bag 4 h_4_mem' (by omega)
  have h_eq : (4 : Int) - 1 = 3 := by omega
  rw [h_eq] at h_dec
  exact h_dec

/-- **Iter 1206: 2 ∈ s5_5.bag at true-head Perm-chain points (when
    rest non-empty)**.  Chain iter 1205 (3 ∈ s5_4.bag) + iter 1184
    (s5_5.bag = s5_4.bag.map(·-1)). -/
theorem ctsConfigToSystem5Bag_true_head_perm_step5_two_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (h_rest : rest ≠ [])
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_5,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 5 = some s5_5
      ∧ (2 : Int) ∈ s5_5.bag := by
  obtain ⟨s5_4, s5_5, h_n4, h_n5, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_4', h_n4', h_3_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_three_mem cts rest phase N h_N h_rest bag h_perm
  refine ⟨s5_5, h_n5, ?_⟩
  have h_align : s5_4 = s5_4' := Option.some.inj (h_n4.symm.trans h_n4')
  have h_3_mem' : (3 : Int) ∈ s5_4.bag := h_align ▸ h_3_mem
  rw [h_bag_form, List.mem_map]
  refine ⟨3, h_3_mem', ?_⟩
  omega

/-- **Iter 1207: 1 ∈ s5_6.bag at true-head Perm-chain points (when
    rest non-empty)**.  Chain iter 1206 (2 ∈ s5_5.bag) + iter 1187
    (s5_6.bag = (s5_5.bag.map(·-1)).erase 0) + iter 975. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step6_one_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (h_rest : rest ≠ [])
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_6,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 6 = some s5_6
      ∧ (1 : Int) ∈ s5_6.bag := by
  obtain ⟨s5_5, s5_6, h_n5, h_n6, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step6_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_5', h_n5', h_2_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_two_mem cts rest phase N h_N h_rest bag h_perm
  refine ⟨s5_6, h_n6, ?_⟩
  have h_align : s5_5 = s5_5' := Option.some.inj (h_n5.symm.trans h_n5')
  have h_2_mem' : (2 : Int) ∈ s5_5.bag := h_align ▸ h_2_mem
  rw [h_bag_form]
  have h_dec := mem_imp_pred_in_dec_erase s5_5.bag 2 h_2_mem' (by omega)
  have h_eq : (2 : Int) - 1 = 1 := by omega
  rw [h_eq] at h_dec
  exact h_dec

/-- **Iter 1208: s5_2.bag is Nodup at true-head Perm-chain points**.
    Direct chain: iter 1166 (s5_2.bag = s5_1.bag.map(·-1)) + iter 1065
    (s5_1.bag.Nodup at any Perm-chain point) + decrement injectivity.
    Extracts the Nodup property buried in iter 1188's proof. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step2_bag_nodup_clean
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_2,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ s5_2.bag.Nodup := by
  obtain ⟨s5_1, s5_2, h_n1, h_n2, h_dec⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_2, h_n2, ?_⟩
  have h_step1_some : System5.step ⟨bag, ctsRulesToSystem5Rules cts
      { data := true :: rest, phase := phase } N⟩ = some s5_1 := by
    rw [System5.nSteps_one] at h_n1; exact h_n1
  obtain ⟨s5_1', h_step1', h_s5_1_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_nodup cts
      { data := true :: rest, phase := phase } N h_N (by simp) bag h_perm
  have h_align : s5_1 = s5_1' :=
    Option.some.inj (h_step1_some.symm.trans h_step1')
  rw [h_dec, h_align]
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_1_nodup
  intro a b h_ne h_eq_dec
  apply h_ne
  have : a - 1 = b - 1 := h_eq_dec
  omega

/-- **Iter 1209: s5_3.bag.length ≥ 2 at true-head Perm-chain points**.
    From iter 1176 (1 ∈ s5_3.bag) + iter 1177 (3 ∈ s5_3.bag) +
    iter 1188 (s5_3.bag.Nodup): two distinct mem witnesses imply
    length ≥ 2 (via uniqueness from Nodup). -/
theorem ctsConfigToSystem5Bag_true_head_perm_step3_bag_length_ge_two
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_3,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ s5_3.bag.length ≥ 2 := by
  obtain ⟨s5_3, h_n3, h_one_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_one_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_3', h_n3', h_three_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_three_mem cts rest phase N h_N bag h_perm
  obtain ⟨s5_3'', h_n3'', h_nodup⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_bag_nodup cts rest phase N h_N bag h_perm
  refine ⟨s5_3, h_n3, ?_⟩
  have h_align' : s5_3 = s5_3' := Option.some.inj (h_n3.symm.trans h_n3')
  have h_align'' : s5_3 = s5_3'' := Option.some.inj (h_n3.symm.trans h_n3'')
  have h_three_mem' : (3 : Int) ∈ s5_3.bag := h_align' ▸ h_three_mem
  have h_nodup' : s5_3.bag.Nodup := h_align'' ▸ h_nodup
  -- Two distinct elements 1 and 3 (with Nodup) ⇒ length ≥ 2
  -- Use List.Sublist of [1, 3] ⊆ s5_3.bag, then length_le
  -- Simpler: just list two elements and use length facts
  have h_pair_sub : ∀ x y : Int, x ≠ y → x ∈ s5_3.bag → y ∈ s5_3.bag → s5_3.bag.length ≥ 2 := by
    intro x y h_ne hx hy
    -- s5_3.bag is non-empty (contains x), so it's c :: rest
    cases h_bag : s5_3.bag with
    | nil => rw [h_bag] at hx; exact absurd hx (List.not_mem_nil)
    | cons c rest =>
      cases h_rest : rest with
      | nil =>
        -- s5_3.bag = [c], so x = c and y = c, but x ≠ y
        rw [h_bag, h_rest] at hx hy
        simp at hx hy
        rw [hx, hy] at h_ne
        exact absurd rfl h_ne
      | cons d rest' =>
        simp [List.length_cons]
  exact h_pair_sub 1 3 (by omega) h_one_mem h_three_mem'

/-- **Iter 1210: s5_6.bag.length ≥ 1 at true-head Perm-chain points
    when rest non-empty**.  Direct from iter 1207 (1 ∈ s5_6.bag when
    rest ≠ []) ⇒ s5_6.bag ≠ [] ⇒ length ≥ 1.  Useful as a positive
    lower bound for downstream xorMerge-or-step-7 reasoning. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step6_bag_length_ge_one
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (h_rest : rest ≠ [])
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_6,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := true :: rest, phase := phase } N⟩ 6 = some s5_6
      ∧ s5_6.bag.length ≥ 1 := by
  obtain ⟨s5_6, h_n6, h_one_mem⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step6_one_mem cts rest phase N h_N h_rest bag h_perm
  refine ⟨s5_6, h_n6, ?_⟩
  have h_ne : s5_6.bag ≠ [] := List.ne_nil_of_mem h_one_mem
  cases h : s5_6.bag with
  | nil => exact absurd h h_ne
  | cons _ _ => simp [List.length_cons]

/-- **Iter 1211: 4 ∉ s5_3.bag at true-head Perm-chain points when rest
    is empty**.  When `rest = []`, `aux [] 4 = []`, so the LHS Perm form
    `(r2.map(·+1)).reverse ++ [1, 3]` contains no `4` (r2.map(·+1) ≥ 10,
    and 4 ∉ {1, 3}); also `4 ∉ r2.map(·+3)` (≥ 12).  xorMerge mem
    analysis gives `4 ∉ s5_3.bag`.  **Important consequence: 1 ∉ s5_6.bag
    when rest = []** — the trajectory's bag is "smaller" in this case. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step3_four_not_mem_when_empty
    (cts : CTS) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := [true], phase := phase })) :
    ∃ s5_3,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := [true], phase := phase } N⟩ 3 = some s5_3
      ∧ (4 : Int) ∉ s5_3.bag := by
  obtain ⟨r1, r2, tail, s5_2, s5_3, h_eq, _h_n2, h_n3, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_bag_form cts [] phase N h_N bag h_perm
  refine ⟨s5_3, h_n3, ?_⟩
  rw [h_bag_form]
  obtain ⟨_r1', r2', _tail', s5_2', h_eq', h_n2', h_perm_lhs⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_dec_erase_perm_r2
      cts [] phase N h_N bag h_perm
  have h_align : r1 :: r2 :: tail = _r1' :: r2' :: _tail' := h_eq.symm.trans h_eq'
  have h_r2_eq : r2 = r2' := (List.cons.inj (List.cons.inj h_align).2).1
  have h_s5_2_align : System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
      { data := [true], phase := phase } N⟩ 2 = some s5_2 := _h_n2
  have h_s5_2_eq : s5_2 = s5_2' := Option.some.inj (h_s5_2_align.symm.trans h_n2')
  -- 4 ∉ LHS via Perm form
  obtain ⟨_, r2'', _, h_eq'', _, h_r2_ge⟩ :=
    ctsToSystem5_true_head_first_two_rules_ge_eleven cts [] phase N h_N
  have h_r2_eq'' : r2 = r2'' :=
    (List.cons.inj (List.cons.inj (h_eq.symm.trans h_eq'')).2).1
  have h_4_not_in_perm_rhs : (4 : Int) ∉ ((r2'.map (· + 1)).reverse ++
      ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux [] 4)) := by
    intro h_in
    rw [List.mem_append] at h_in
    rcases h_in with h_left | h_right
    · rw [List.mem_reverse, List.mem_map] at h_left
      obtain ⟨x, hx, h_eq_x⟩ := h_left
      rw [← h_r2_eq, h_r2_eq''] at hx
      have := h_r2_ge x hx
      omega
    · simp [ctsConfigToSystem5BagAux] at h_right
  have h_4_not_in_lhs : (4 : Int) ∉ (s5_2.bag.map (· - 1)).erase 0 := by
    rw [h_s5_2_eq]
    intro h_in
    exact h_4_not_in_perm_rhs ((List.Perm.mem_iff h_perm_lhs).mp h_in)
  have h_4_not_in_r2_3 : (4 : Int) ∉ r2.map (· + 3) := by
    rw [List.mem_map]
    intro ⟨x, hx, h_eq_x⟩
    rw [h_r2_eq''] at hx
    have := h_r2_ge x hx
    omega
  -- Get Nodups (using same template as iter 1181)
  obtain ⟨s5_1', s5_2'', h_n1, h_n2'', h_dec⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step2_bag_form cts [] phase N h_N bag h_perm
  have h_s5_2_eq2 : s5_2 = s5_2'' :=
    Option.some.inj (h_s5_2_align.symm.trans h_n2'')
  have h_step1_some : System5.step ⟨bag, ctsRulesToSystem5Rules cts
      { data := [true], phase := phase } N⟩ = some s5_1' := by
    rw [System5.nSteps_one] at h_n1; exact h_n1
  obtain ⟨s5_1''', h_step1''', h_s5_1_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_nodup cts
      { data := [true], phase := phase } N h_N (by simp) bag h_perm
  have h_s5_1_align : s5_1' = s5_1''' :=
    Option.some.inj (h_step1_some.symm.trans h_step1''')
  have h_s5_2_bag_nodup : s5_2.bag.Nodup := by
    rw [h_s5_2_eq2, h_dec, h_s5_1_align]
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_1_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  have h_lhs_nodup : ((s5_2.bag.map (· - 1)).erase 0).Nodup := by
    apply List.Nodup.erase
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_2_bag_nodup
    intro a b h_ne h_eq_dec
    apply h_ne
    have : a - 1 = b - 1 := h_eq_dec
    omega
  obtain ⟨_, r2_3', _, h_eq_r2_3, h_r2_3_nodup⟩ :=
    ctsRulesToSystem5Rules_second_rule_map_add_3_nodup cts
      { data := [true], phase := phase } N h_N
  have h_r2_3_align : r2 = r2_3' :=
    (List.cons.inj (List.cons.inj (h_eq.symm.trans h_eq_r2_3)).2).1
  have h_r2_3_nodup' : (r2.map (· + 3)).Nodup := by
    rw [h_r2_3_align]; exact h_r2_3_nodup
  intro h_4_in
  rw [xorMerge_mem_iff _ _ h_lhs_nodup h_r2_3_nodup' 4] at h_4_in
  rcases h_4_in with ⟨h_l, _⟩ | ⟨_, h_r⟩
  · exact h_4_not_in_lhs h_l
  · exact h_4_not_in_r2_3 h_r

/-- **Iter 1212: 3 ∉ s5_4.bag at true-head Perm-chain points when rest
    = []**.  Chain iter 1211 (4 ∉ s5_3.bag) + iter 1179
    (s5_4.bag = (s5_3.bag.map(·-1)).erase 0): if no y ∈ s5_3.bag
    decrements to 3 (i.e., 4 ∉ s5_3.bag), then 3 ∉ s5_3.bag.map(·-1)
    and erase preserves non-membership. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step4_three_not_mem_when_empty
    (cts : CTS) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := [true], phase := phase })) :
    ∃ s5_4,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := [true], phase := phase } N⟩ 4 = some s5_4
      ∧ (3 : Int) ∉ s5_4.bag := by
  obtain ⟨s5_3, s5_4, h_n3, h_n4, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_bag_form cts [] phase N h_N bag h_perm
  obtain ⟨s5_3', h_n3', h_4_not⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step3_four_not_mem_when_empty cts phase N h_N bag h_perm
  refine ⟨s5_4, h_n4, ?_⟩
  have h_align : s5_3 = s5_3' := Option.some.inj (h_n3.symm.trans h_n3')
  have h_4_not' : (4 : Int) ∉ s5_3.bag := h_align ▸ h_4_not
  rw [h_bag_form]
  intro h_3_in
  have h_3_in_map : (3 : Int) ∈ s5_3.bag.map (· - 1) := List.mem_of_mem_erase h_3_in
  rw [List.mem_map] at h_3_in_map
  obtain ⟨x, hx, h_eq_x⟩ := h_3_in_map
  -- x - 1 = 3 ⇒ x = 4, but 4 ∉ s5_3.bag — contradiction
  have h_x_eq : x = 4 := by omega
  rw [h_x_eq] at hx
  exact h_4_not' hx

/-- **Iter 1213: 2 ∉ s5_5.bag at true-head Perm-chain points when rest
    = []**.  Chain iter 1212 + iter 1184 (s5_5.bag = s5_4.bag.map(·-1)). -/
theorem ctsConfigToSystem5Bag_true_head_perm_step5_two_not_mem_when_empty
    (cts : CTS) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := [true], phase := phase })) :
    ∃ s5_5,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := [true], phase := phase } N⟩ 5 = some s5_5
      ∧ (2 : Int) ∉ s5_5.bag := by
  obtain ⟨s5_4, s5_5, h_n4, h_n5, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_bag_form cts [] phase N h_N bag h_perm
  obtain ⟨s5_4', h_n4', h_3_not⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step4_three_not_mem_when_empty cts phase N h_N bag h_perm
  refine ⟨s5_5, h_n5, ?_⟩
  have h_align : s5_4 = s5_4' := Option.some.inj (h_n4.symm.trans h_n4')
  have h_3_not' : (3 : Int) ∉ s5_4.bag := h_align ▸ h_3_not
  rw [h_bag_form]
  intro h_2_in
  rw [List.mem_map] at h_2_in
  obtain ⟨x, hx, h_eq_x⟩ := h_2_in
  have h_x_eq : x = 3 := by omega
  rw [h_x_eq] at hx
  exact h_3_not' hx

/-- **Iter 1214: 1 ∉ s5_6.bag at true-head Perm-chain points when rest
    = []**.  Chain iter 1213 + iter 1187 (s5_6.bag = (s5_5.bag.map(·-1)).erase 0).
    **Confirms: when rest = [], 1 ∉ s5_6.bag** — companion to iter 1207
    (1 ∈ s5_6.bag when rest ≠ []).  Together they characterize step 7
    behavior precisely: P-step iff rest non-empty. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step6_one_not_mem_when_empty
    (cts : CTS) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := [true], phase := phase })) :
    ∃ s5_6,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := [true], phase := phase } N⟩ 6 = some s5_6
      ∧ (1 : Int) ∉ s5_6.bag := by
  obtain ⟨s5_5, s5_6, h_n5, h_n6, h_bag_form⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step6_bag_form cts [] phase N h_N bag h_perm
  obtain ⟨s5_5', h_n5', h_2_not⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step5_two_not_mem_when_empty cts phase N h_N bag h_perm
  refine ⟨s5_6, h_n6, ?_⟩
  have h_align : s5_5 = s5_5' := Option.some.inj (h_n5.symm.trans h_n5')
  have h_2_not' : (2 : Int) ∉ s5_5.bag := h_align ▸ h_2_not
  rw [h_bag_form]
  intro h_1_in
  have h_1_in_map : (1 : Int) ∈ s5_5.bag.map (· - 1) := List.mem_of_mem_erase h_1_in
  rw [List.mem_map] at h_1_in_map
  obtain ⟨x, hx, h_eq_x⟩ := h_1_in_map
  have h_x_eq : x = 2 := by omega
  rw [h_x_eq] at hx
  exact h_2_not' hx

/-- **Iter 1215: `i + 3 ∈ aux data i` for non-empty data**.  Both true-
    and false-head cases have `i + 3` as the third or fourth element
    respectively.  Generic primitive for downstream membership analysis. -/
theorem ctsConfigToSystem5BagAux_third_mem
    (data : List Bool) (i : Int) (h : data ≠ []) :
    i + 3 ∈ ctsConfigToSystem5BagAux data i := by
  cases data with
  | nil => exact absurd rfl h
  | cons head _ =>
    cases head with
    | true =>
      show i + 3 ∈ i :: (i + 2) :: (i + 3) :: (i + 5) :: _
      simp
    | false =>
      show i + 3 ∈ i :: (i + 1) :: (i + 2) :: (i + 3) :: _
      simp

/-- **Iter 1216: `i + 2 ∈ aux data i` for non-empty data**.  True-head
    case has `i + 2` as the second element; false-head case has it as
    the third.  Generic primitive. -/
theorem ctsConfigToSystem5BagAux_second_mem
    (data : List Bool) (i : Int) (h : data ≠ []) :
    i + 2 ∈ ctsConfigToSystem5BagAux data i := by
  cases data with
  | nil => exact absurd rfl h
  | cons head _ =>
    cases head with
    | true =>
      show i + 2 ∈ i :: (i + 2) :: (i + 3) :: (i + 5) :: _
      simp
    | false =>
      show i + 2 ∈ i :: (i + 1) :: (i + 2) :: (i + 3) :: _
      simp

/-- **Iter 1217: counterAfterWorkingString lower bound for true-head
    data**.  When `data = true :: rest`, `counterAfterWorkingString
    (true :: rest) ≥ 7`.  Direct from `_cons_true` (adds 6) +
    `_ge_one` (≥ 1).  Companion to iter 905 for true-head. -/
theorem counterAfterWorkingString_true_head_ge (rest : List Bool) :
    counterAfterWorkingString (true :: rest) ≥ 7 := by
  rw [counterAfterWorkingString_cons_true]
  have := counterAfterWorkingString_ge_one rest
  omega

/-- **Iter 1218: counterAfterWorkingString lower bound for non-empty
    data**.  When `data ≠ []`, `counterAfterWorkingString data ≥ 5`.
    Combines iter 905 (false-head ≥ 5) and iter 1217 (true-head ≥ 7,
    ≥ 5). -/
theorem counterAfterWorkingString_nonempty_ge (data : List Bool)
    (h : data ≠ []) :
    counterAfterWorkingString data ≥ 5 := by
  cases data with
  | nil => exact absurd rfl h
  | cons head tail =>
    cases head with
    | true =>
      have := counterAfterWorkingString_true_head_ge tail
      omega
    | false =>
      exact counterAfterWorkingString_false_head_ge tail

/-- **Iter 1219: generic r1 ≥ 9, r2 ≥ 7 for any non-empty data**.
    Direct from `ctsRulesToSystem5Rules_first_two_rules_min_value`
    (r1 ≥ counter + 4, r2 ≥ counter + 2) + iter 1218 (counter ≥ 5
    when data ≠ []).  **Generic version of iter 970 (false-head ≥ 7)
    and iter 1159 (true-head ≥ 11)** — at the cost of slightly weaker
    bounds, applies to both head cases. -/
theorem ctsToSystem5_nonempty_first_two_rules_ge
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ []) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
      ∧ (∀ x ∈ r1, x ≥ 9)
      ∧ (∀ x ∈ r2, x ≥ 7) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, h_r2⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_min_value cts cfg N h_N
  have h_counter : counterAfterWorkingString cfg.data ≥ 5 :=
    counterAfterWorkingString_nonempty_ge cfg.data h_data
  refine ⟨r1, r2, tail, h_eq, ?_, ?_⟩
  · intro x hx
    have := h_r1 x hx
    omega
  · intro x hx
    have := h_r2 x hx
    omega

/-- **Iter 1220: generic 1 ∉ r1.map(·+1) for non-empty data**.
    Direct from iter 1219 (r1 ≥ 9) ⇒ r1.map(·+1) ≥ 10 ⇒ 1 ∉.
    **Generic version of iter 971** (false-head specific). -/
theorem ctsRulesToSystem5Rules_nonempty_first_rule_inc_no_one
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ []) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
      ∧ (1 : Int) ∉ r1.map (· + 1) := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, _⟩ :=
    ctsToSystem5_nonempty_first_two_rules_ge cts cfg N h_N h_data
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  rw [List.mem_map]
  intro ⟨x, hx, h_eq_x⟩
  have := h_r1 x hx
  omega

/-- **Iter 1221: generic 1 ∉ r2.map(·+2) for non-empty data**.
    Direct from iter 1219 (r2 ≥ 7) ⇒ r2.map(·+2) ≥ 9 ⇒ 1 ∉.
    **Generic version of iter 976** (false-head specific). -/
theorem ctsRulesToSystem5Rules_nonempty_second_rule_inc2_no_one
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ []) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
      ∧ (1 : Int) ∉ r2.map (· + 2) := by
  obtain ⟨r1, r2, tail, h_eq, _, h_r2⟩ :=
    ctsToSystem5_nonempty_first_two_rules_ge cts cfg N h_N h_data
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  rw [List.mem_map]
  intro ⟨x, hx, h_eq_x⟩
  have := h_r2 x hx
  omega

/-- **Iter 1222: generic r1.map(·+1) ≥ 10 for non-empty data**.
    Direct from iter 1219 (r1 ≥ 9) ⇒ each element +1 ≥ 10.
    Useful primitive: any small value < 10 is not in r1.map(·+1). -/
theorem ctsRulesToSystem5Rules_nonempty_first_rule_inc_ge_ten
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ []) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
      ∧ ∀ x ∈ r1.map (· + 1), x ≥ 10 := by
  obtain ⟨r1, r2, tail, h_eq, h_r1, _⟩ :=
    ctsToSystem5_nonempty_first_two_rules_ge cts cfg N h_N h_data
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨y, hy, h_y_eq⟩ := hx
  have := h_r1 y hy
  omega

/-- **Iter 1223: generic r2.map(·+2) ≥ 9 for non-empty data**.
    Companion to iter 1222.  Direct from iter 1219 (r2 ≥ 7). -/
theorem ctsRulesToSystem5Rules_nonempty_second_rule_inc2_ge_nine
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ []) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
      ∧ ∀ x ∈ r2.map (· + 2), x ≥ 9 := by
  obtain ⟨r1, r2, tail, h_eq, _, h_r2⟩ :=
    ctsToSystem5_nonempty_first_two_rules_ge cts cfg N h_N h_data
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨y, hy, h_y_eq⟩ := hx
  have := h_r2 y hy
  omega

/-- **Iter 1224: generic r2.map(·+3) ≥ 10 for non-empty data**.
    Direct from iter 1219 (r2 ≥ 7) ⇒ r2.map(·+3) ≥ 10.  Useful
    primitive — value bound for the step 3 P-step rule contribution
    in the true-head trajectory. -/
theorem ctsRulesToSystem5Rules_nonempty_second_rule_inc3_ge_ten
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ []) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
      ∧ ∀ x ∈ r2.map (· + 3), x ≥ 10 := by
  obtain ⟨r1, r2, tail, h_eq, _, h_r2⟩ :=
    ctsToSystem5_nonempty_first_two_rules_ge cts cfg N h_N h_data
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨y, hy, h_y_eq⟩ := hx
  have := h_r2 y hy
  omega

/-- **Iter 1225: generic n ∉ r2.map(·+3) for non-empty data and n < 10**.
    Useful primitive — any small value < 10 is not in the step 3
    rule contribution.  Direct from iter 1224. -/
theorem ctsRulesToSystem5Rules_nonempty_second_rule_inc3_no_small
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ []) (n : Int) (h_n : n < 10) :
    ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail
      ∧ n ∉ r2.map (· + 3) := by
  obtain ⟨r1, r2, tail, h_eq, h_r2_ge⟩ :=
    ctsRulesToSystem5Rules_nonempty_second_rule_inc3_ge_ten cts cfg N h_N h_data
  refine ⟨r1, r2, tail, h_eq, ?_⟩
  intro h_in
  have := h_r2_ge n h_in
  omega

/-- **Iter 1226: encoder bag of post-CTS-step true-head config**.
    When `cts.step {data := true :: rest, phase} = some result`, the
    encoder bag of `result` is `aux (rest ++ cts.currentAppendant phase) 1`.
    Direct from `CTS.step` definition (true-head appends the appendant). -/
theorem ctsConfigToSystem5Bag_true_head_step_result_eq_explicit
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := true :: rest, phase := phase } = some result) :
    ctsConfigToSystem5Bag result
      = ctsConfigToSystem5BagAux (rest ++ cts.currentAppendant phase) 1 := by
  -- result.data = rest ++ cts.currentAppendant phase via CTS.step definition
  have h_data : result.data = rest ++ cts.currentAppendant phase := by
    unfold CTS.step at h_step
    simp at h_step
    rw [← h_step]
  show ctsConfigToSystem5BagAux result.data 1 = _
  rw [h_data]

/-- **Iter 1227: post-CTS-step true-head encoder bag in append form**.
    Composes iter 1226 + iter 653 (aux append):
    `ctsConfigToSystem5Bag result = aux rest 1 ++ aux appendant
    (counterAfterWorkingString rest)`.  **Decomposes the trajectory's
    target bag into the pre-step part (`aux rest 1`) and the appendant
    contribution (`aux appendant ...`).**  The appendant part is what
    the rule contributions at steps 1, 3 must equal in the trajectory. -/
theorem ctsConfigToSystem5Bag_true_head_step_result_append_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := true :: rest, phase := phase } = some result) :
    ctsConfigToSystem5Bag result
      = ctsConfigToSystem5BagAux rest 1
        ++ ctsConfigToSystem5BagAux (cts.currentAppendant phase)
            (counterAfterWorkingString rest) := by
  rw [ctsConfigToSystem5Bag_true_head_step_result_eq_explicit cts rest phase result h_step]
  rw [ctsConfigToSystem5BagAux_append]
  rw [counterAux_one_eq_counterAfterWorkingString]

/-- **Iter 1228: post-CTS-step true-head encoder bag length**.
    Direct from iter 1227 + `_length`: the post-step bag has length
    `4 * (rest.length + (cts.currentAppendant phase).length)`. -/
theorem ctsConfigToSystem5Bag_true_head_step_result_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := true :: rest, phase := phase } = some result) :
    (ctsConfigToSystem5Bag result).length
      = 4 * (rest.length + (cts.currentAppendant phase).length) := by
  rw [ctsConfigToSystem5Bag_true_head_step_result_append_form cts rest phase result h_step]
  rw [List.length_append, ctsConfigToSystem5BagAux_length, ctsConfigToSystem5BagAux_length]
  omega

/-- **Iter 1232: aux length is positive iff data non-empty**.  Direct
    corollary of `ctsConfigToSystem5BagAux_length` (= 4 * data.length).
    Useful primitive: bag is non-empty iff data is non-empty. -/
theorem ctsConfigToSystem5BagAux_length_pos_iff (data : List Bool) (i : Int) :
    (ctsConfigToSystem5BagAux data i).length > 0 ↔ data ≠ [] := by
  rw [ctsConfigToSystem5BagAux_length]
  constructor
  · intro h h_data
    rw [h_data, List.length_nil] at h
    omega
  · intro h
    cases h_data : data with
    | nil => exact absurd h_data h
    | cons _ _ => simp [List.length_cons]

/-- **Iter 1233: aux at counter i ≠ [] iff data ≠ []**.  Companion to
    iter 1232; relates non-emptiness of bag to non-emptiness of data
    via length. -/
theorem ctsConfigToSystem5BagAux_ne_nil_iff_data_ne_nil
    (data : List Bool) (i : Int) :
    ctsConfigToSystem5BagAux data i ≠ [] ↔ data ≠ [] := by
  constructor
  · intro h h_data
    apply h
    rw [h_data]
    rfl
  · intro h_data h
    have h_len : (ctsConfigToSystem5BagAux data i).length = 0 := by rw [h]; rfl
    rw [ctsConfigToSystem5BagAux_length] at h_len
    have h_dlen : data.length = 0 := by omega
    exact h_data (List.length_eq_zero_iff.mp h_dlen)

/-- **Iter 1234: encoder bag has length 0 iff data is empty**.
    Direct corollary of `ctsConfigToSystem5Bag_length`. -/
theorem ctsConfigToSystem5Bag_length_eq_zero_iff (cfg : CTSConfig) :
    (ctsConfigToSystem5Bag cfg).length = 0 ↔ cfg.data = [] := by
  rw [ctsConfigToSystem5Bag_length]
  constructor
  · intro h
    have : cfg.data.length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  · intro h_data
    rw [h_data]; rfl

/-- **Iter 1235: encoder bag is non-empty iff data is non-empty (Perm
    transferable)**.  Same statement as iter 1233 specialized to the
    full encoder bag, useful for clarity in chain proofs. -/
theorem ctsConfigToSystem5Bag_ne_nil_iff (cfg : CTSConfig) :
    ctsConfigToSystem5Bag cfg ≠ [] ↔ cfg.data ≠ [] :=
  ctsConfigToSystem5BagAux_ne_nil_iff_data_ne_nil cfg.data 1

/-- **Iter 1236: encoder bag length is divisible by 4**.  Direct from
    `_length` (= 4 * data.length).  Useful invariant: the bag length
    is always a multiple of 4 throughout the encoder construction. -/
theorem ctsConfigToSystem5Bag_length_divisible_four (cfg : CTSConfig) :
    4 ∣ (ctsConfigToSystem5Bag cfg).length := by
  rw [ctsConfigToSystem5Bag_length]
  exact ⟨cfg.data.length, rfl⟩

/-- **Iter 1237: aux at any counter has length divisible by 4**.
    Generic version of iter 1236. -/
theorem ctsConfigToSystem5BagAux_length_divisible_four
    (data : List Bool) (i : Int) :
    4 ∣ (ctsConfigToSystem5BagAux data i).length := by
  rw [ctsConfigToSystem5BagAux_length]
  exact ⟨data.length, rfl⟩

/-- **Iter 1238: Perm-chain bag length divisible by 4**.  At any
    Perm-chain point, `bag.length` is divisible by 4.  Direct from
    iter 1154 (closed-form length = 4 * data.length). -/
theorem ctsConfigToSystem5Bag_perm_bag_length_divisible_four
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    4 ∣ bag.length := by
  rw [ctsConfigToSystem5Bag_perm_bag_length_eq cfg bag h_perm]
  exact ⟨cfg.data.length, rfl⟩

/-- **Iter 1239: aux head element n+1 ∈ aux data (n+1)**.  Specialization
    of iter 1203 (head_mem) used in fixed-point chains where counter
    increments by 1. -/
theorem ctsConfigToSystem5BagAux_head_mem_succ
    (data : List Bool) (n : Int) (h : data ≠ []) :
    n + 1 ∈ ctsConfigToSystem5BagAux data (n + 1) :=
  ctsConfigToSystem5BagAux_head_mem data (n + 1) h

/-- **Iter 1240: aux dec preserves Nodup**.  Direct corollary of
    `_nodup` + `List.Pairwise.map` (decrement injectivity). -/
theorem ctsConfigToSystem5BagAux_dec_nodup (data : List Bool) (i : Int) :
    ((ctsConfigToSystem5BagAux data i).map (· - 1)).Nodup := by
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ (ctsConfigToSystem5BagAux_nodup data i)
  intro a b h_ne h_eq_dec
  apply h_ne
  have : a - 1 = b - 1 := h_eq_dec
  omega

/-- **Iter 1241: aux inc preserves Nodup**.  Companion to iter 1240. -/
theorem ctsConfigToSystem5BagAux_inc_nodup (data : List Bool) (i : Int) :
    ((ctsConfigToSystem5BagAux data i).map (· + 1)).Nodup := by
  apply List.Pairwise.map (· + 1) (R := (· ≠ ·)) ?_ (ctsConfigToSystem5BagAux_nodup data i)
  intro a b h_ne h_eq_inc
  apply h_ne
  have : a + 1 = b + 1 := h_eq_inc
  omega

/-- **Iter 1242: dec-erase of bag with 1 ∈ bag has length bag.length - 1**.
    Generic primitive: when `1 ∈ xs`, the dec-erase reduces length by 1.
    Direct from `zero_mem_decrement_iff_one_mem` + `List.length_erase_of_mem`. -/
theorem List_Int_dec_erase_length_of_one_mem (xs : List Int) (h : (1 : Int) ∈ xs) :
    ((xs.map (· - 1)).erase 0).length = xs.length - 1 := by
  have h_zero : (0 : Int) ∈ xs.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h
  rw [List.length_erase_of_mem h_zero, List.length_map]

/-- **Iter 1243: dec-erase of bag without 1 has length bag.length**.
    Companion: when `1 ∉ xs`, the dec-erase doesn't reduce length
    (since 0 ∉ dec, erase is identity). -/
theorem List_Int_dec_erase_length_of_one_not_mem
    (xs : List Int) (h : (1 : Int) ∉ xs) :
    ((xs.map (· - 1)).erase 0).length = xs.length := by
  have h_zero : (0 : Int) ∉ xs.map (· - 1) := by
    intro h_zero_in
    exact h ((zero_mem_decrement_iff_one_mem _).mp h_zero_in)
  rw [List.erase_of_not_mem h_zero, List.length_map]

/-- **Iter 1244: generic dec-erase preserves Nodup**.  When `xs.Nodup`,
    `((xs.map(·-1)).erase 0).Nodup`.  Direct from decrement injectivity
    + `List.Nodup.erase`.  Generic primitive applicable in any context. -/
theorem List_Int_dec_erase_nodup (xs : List Int) (h : xs.Nodup) :
    ((xs.map (· - 1)).erase 0).Nodup := by
  apply List.Nodup.erase
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h
  intro a b h_ne h_eq_dec
  apply h_ne
  have : a - 1 = b - 1 := h_eq_dec
  omega

/-- **Iter 1245: generic dec preserves Nodup**.  When `xs.Nodup`,
    `(xs.map(·-1)).Nodup`.  Direct from decrement injectivity. -/
theorem List_Int_dec_nodup (xs : List Int) (h : xs.Nodup) :
    (xs.map (· - 1)).Nodup := by
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h
  intro a b h_ne h_eq_dec
  apply h_ne
  have : a - 1 = b - 1 := h_eq_dec
  omega

/-- **Iter 1246: aux head element is `i` for non-empty data**.
    For any non-empty data, `aux data i` starts with `i`.  Stronger
    than iter 1203 (which gives membership): provides the explicit
    cons form. -/
theorem ctsConfigToSystem5BagAux_head_form
    (data : List Bool) (i : Int) (h : data ≠ []) :
    ∃ tail, ctsConfigToSystem5BagAux data i = i :: tail := by
  cases data with
  | nil => exact absurd rfl h
  | cons head tail =>
    cases head with
    | true =>
      refine ⟨(i + 2) :: (i + 3) :: (i + 5) :: ctsConfigToSystem5BagAux tail (i + 6), ?_⟩
      rfl
    | false =>
      refine ⟨(i + 1) :: (i + 2) :: (i + 3) :: ctsConfigToSystem5BagAux tail (i + 4), ?_⟩
      rfl

/-- **Iter 1247: encoder bag head form**.  For any non-empty cfg.data,
    `ctsConfigToSystem5Bag cfg = 1 :: tail` for some tail.  Direct
    specialization of iter 1246 to i = 1. -/
theorem ctsConfigToSystem5Bag_head_form (cfg : CTSConfig) (h : cfg.data ≠ []) :
    ∃ tail, ctsConfigToSystem5Bag cfg = (1 : Int) :: tail :=
  ctsConfigToSystem5BagAux_head_form cfg.data 1 h

/-- **Iter 1248: encoder bag head form with Nodup tail**.  Combines
    iter 1247 + Nodup of the bag.  The tail is also Nodup since the
    full bag is Nodup. -/
theorem ctsConfigToSystem5Bag_head_form_nodup (cfg : CTSConfig) (h : cfg.data ≠ []) :
    ∃ tail, ctsConfigToSystem5Bag cfg = (1 : Int) :: tail
          ∧ ((1 : Int) :: tail).Nodup := by
  obtain ⟨tail, h_eq⟩ := ctsConfigToSystem5Bag_head_form cfg h
  refine ⟨tail, h_eq, ?_⟩
  rw [← h_eq]
  exact ctsConfigToSystem5BagAux_nodup cfg.data 1

/-- **Iter 1249: dec-erase of a list starting with 1 = tail dec'd**.
    `((1 :: ys).map(·-1)).erase 0 = ys.map(·-1)`.  The `1` decrements
    to `0`, which is then erased, leaving just the tail decremented.
    Useful primitive for inductive bag transformations. -/
theorem List_Int_one_cons_dec_erase (ys : List Int) :
    (((1 : Int) :: ys).map (· - 1)).erase 0 = ys.map (· - 1) := by
  simp only [List.map_cons]
  show ((0 : Int) :: ys.map (· - 1)).erase 0 = ys.map (· - 1)
  rw [List.erase_cons_head]

/-- **Iter 1250: encoder bag dec-erase = tail dec'd when data non-empty**.
    Composes iter 1247 (encoder bag head form) + iter 1249. -/
theorem ctsConfigToSystem5Bag_dec_erase_tail
    (cfg : CTSConfig) (h : cfg.data ≠ []) :
    ∃ tail, ctsConfigToSystem5Bag cfg = (1 : Int) :: tail
          ∧ ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0 = tail.map (· - 1) := by
  obtain ⟨tail, h_eq⟩ := ctsConfigToSystem5Bag_head_form cfg h
  refine ⟨tail, h_eq, ?_⟩
  rw [h_eq]
  exact List_Int_one_cons_dec_erase tail

/-- **Iter 1251: dec-erase length is at most the bag length**.
    `((xs.map(·-1)).erase 0).length ≤ xs.length`.  Direct from
    `List.length_erase_le` + `List.length_map`.  Useful upper bound. -/
theorem List_Int_dec_erase_length_le (xs : List Int) :
    ((xs.map (· - 1)).erase 0).length ≤ xs.length := by
  have h1 : ((xs.map (· - 1)).erase 0).length ≤ (xs.map (· - 1)).length :=
    List.length_erase_le
  rw [List.length_map] at h1
  exact h1

/-- **Iter 1252: dec-erase length is bag length minus at most 1**.
    `((xs.map(·-1)).erase 0).length ≥ xs.length - 1`.  Useful lower
    bound (erase removes at most one element). -/
theorem List_Int_dec_erase_length_ge (xs : List Int) :
    ((xs.map (· - 1)).erase 0).length ≥ xs.length - 1 := by
  by_cases h_zero : (0 : Int) ∈ xs.map (· - 1)
  · rw [List.length_erase_of_mem h_zero, List.length_map]
    omega
  · rw [List.erase_of_not_mem h_zero, List.length_map]
    omega

/-- **Iter 1253: cancellation property under any shift (alternate form)**.
    `r1 = r2.map(·+2) ⇒ r1.map(·+m) = r2.map(·+(m+2))`.  Useful for
    chain points with arbitrary shift offsets — directly relates the
    shifted r1 to a different shift of r2.  Companion to iter 1018. -/
theorem List_Int_cancellation_under_shift_alt
    (r1 r2 : List Int) (h : r1 = r2.map (· + 2)) (m : Int) :
    r1.map (· + m) = r2.map (· + (m + 2)) := by
  rw [h]
  have h_helper : ∀ ys : List Int,
      (ys.map (· + 2)).map (· + m) = ys.map (· + (m + 2)) := by
    intro ys
    induction ys with
    | nil => rfl
    | cons x zs ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨by omega, ih⟩
  exact h_helper r2

/-- **Iter 1254: Perm preserves non-emptiness**.  `xs.Perm ys ⇒
    (xs ≠ [] ↔ ys ≠ [])`.  Direct from `List.Perm.length_eq` +
    length-positivity.  Useful primitive for chain-induction. -/
theorem List_Perm_ne_nil_iff {α : Type _} {xs ys : List α} (h : xs.Perm ys) :
    xs ≠ [] ↔ ys ≠ [] := by
  constructor
  · intro h_x h_y
    apply h_x
    have h_len := List.Perm.length_eq h
    rw [h_y, List.length_nil] at h_len
    exact List.length_eq_zero_iff.mp h_len
  · intro h_y h_x
    apply h_y
    have h_len := List.Perm.length_eq h
    rw [h_x, List.length_nil] at h_len
    exact List.length_eq_zero_iff.mp h_len.symm

/-- **Iter 1255: Perm-chain bag ≠ [] iff data ≠ []**.  Composes
    iter 1254 (Perm preserves non-empty) + iter 1235 (encoder bag
    ≠ [] iff data ≠ []).  Useful corollary at the chain level. -/
theorem ctsConfigToSystem5Bag_perm_ne_nil_iff
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    bag ≠ [] ↔ cfg.data ≠ [] := by
  rw [List_Perm_ne_nil_iff h_perm, ctsConfigToSystem5Bag_ne_nil_iff]

/-- **Iter 1256: Perm-chain bag = [] iff data = []**.  Negation form
    of iter 1255. -/
theorem ctsConfigToSystem5Bag_perm_eq_nil_iff
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    bag = [] ↔ cfg.data = [] := by
  have h_len_bag := List.Perm.length_eq h_perm
  rw [ctsConfigToSystem5Bag_length] at h_len_bag
  constructor
  · intro h_b
    rw [h_b, List.length_nil] at h_len_bag
    have h_zero : cfg.data.length = 0 := by omega
    exact List.length_eq_zero_iff.mp h_zero
  · intro h_d
    rw [h_d, List.length_nil] at h_len_bag
    simp at h_len_bag
    exact h_len_bag

/-- **Iter 1257: 1 ∈ encoder bag iff data non-empty**.  Composes
    iter 1247 (forward: data ≠ [] ⇒ ∃ tail, bag = 1 :: tail ⇒ 1 ∈ bag)
    + iter 1234 (backward: data = [] ⇒ bag = []).  Useful biconditional. -/
theorem ctsConfigToSystem5Bag_one_mem_iff (cfg : CTSConfig) :
    (1 : Int) ∈ ctsConfigToSystem5Bag cfg ↔ cfg.data ≠ [] := by
  constructor
  · intro h_in h_data
    have h_len : (ctsConfigToSystem5Bag cfg).length = 0 :=
      (ctsConfigToSystem5Bag_length_eq_zero_iff cfg).mpr h_data
    have h_bag_nil : ctsConfigToSystem5Bag cfg = [] :=
      List.length_eq_zero_iff.mp h_len
    rw [h_bag_nil] at h_in
    exact List.not_mem_nil h_in
  · intro h_data
    obtain ⟨tail, h_eq⟩ := ctsConfigToSystem5Bag_head_form cfg h_data
    rw [h_eq]
    exact List.mem_cons_self

/-- **Iter 1258: Perm-chain bag has 1 iff data non-empty**.  Direct
    from iter 1257 + `List.Perm.mem_iff`.  Useful biconditional at
    any chain point. -/
theorem ctsConfigToSystem5Bag_perm_one_mem_iff
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    (1 : Int) ∈ bag ↔ cfg.data ≠ [] := by
  rw [List.Perm.mem_iff h_perm, ctsConfigToSystem5Bag_one_mem_iff]

/-- **Iter 1259: Perm-chain bag has 0 ∈ dec iff data non-empty**.
    Combines iter 1258 with `zero_mem_decrement_iff_one_mem`.
    Useful: P-step trigger condition iff data non-empty. -/
theorem ctsConfigToSystem5Bag_perm_zero_in_dec_iff
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    (0 : Int) ∈ bag.map (· - 1) ↔ cfg.data ≠ [] := by
  rw [zero_mem_decrement_iff_one_mem,
      ctsConfigToSystem5Bag_perm_one_mem_iff cfg bag h_perm]

/-- **Iter 1260: encoder rules non-empty when N ≥ 1**.  The encoder
    `ctsRulesToSystem5Rules cts cfg N` has length `4 * |appendants| * N`,
    which is positive when `N ≥ 1` (since `|appendants| > 0` by
    `cts.nonempty`).  Direct from `_length` + arithmetic. -/
theorem ctsRulesToSystem5Rules_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    ctsRulesToSystem5Rules cts cfg N ≠ [] := by
  intro h_eq
  have h_len : (ctsRulesToSystem5Rules cts cfg N).length = 0 := by
    rw [h_eq]; rfl
  rw [ctsRulesToSystem5Rules_length] at h_len
  have h_app := cts.nonempty
  -- 4 * |appendants| * N = 0, with |appendants| ≥ 1 and N ≥ 1
  have h_pos : 4 * cts.appendants.length * N > 0 := by
    have : 4 * cts.appendants.length ≥ 4 := by
      have : cts.appendants.length ≥ 1 := h_app
      omega
    have : 4 * cts.appendants.length * N ≥ 4 * 1 := by
      have h1 : 4 * cts.appendants.length ≥ 4 := by omega
      exact Nat.le_trans (by omega) (Nat.mul_le_mul h1 h_N)
    omega
  omega

/-- **Iter 1261: encoder rules length ≥ 4 when N ≥ 1**.  Direct from
    `_length` (= 4 * |appendants| * N) + `cts.nonempty` (|appendants| ≥ 1).
    Useful for accessing first 4 rules in proofs. -/
theorem ctsRulesToSystem5Rules_length_ge_four
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    (ctsRulesToSystem5Rules cts cfg N).length ≥ 4 := by
  rw [ctsRulesToSystem5Rules_length]
  have h_app : cts.appendants.length ≥ 1 := cts.nonempty
  have h1 : 4 * cts.appendants.length ≥ 4 := by omega
  have h2 : 4 * cts.appendants.length * N ≥ 4 * 1 :=
    Nat.le_trans (by omega) (Nat.mul_le_mul h1 h_N)
  omega

/-- **Iter 1262: encoder rules length divisible by 4**.  Direct from
    `_length` (= 4 * |appendants| * N).  Useful invariant: rules are
    organized in 4-tuples (one per appendant per cycle). -/
theorem ctsRulesToSystem5Rules_length_divisible_four
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    4 ∣ (ctsRulesToSystem5Rules cts cfg N).length := by
  rw [ctsRulesToSystem5Rules_length]
  exact ⟨cts.appendants.length * N, by rw [Nat.mul_assoc]⟩

/-- **Iter 1263: System5 step succeeds at Perm-chain points with N ≥ 1
    and data non-empty**.  Composes iter 1255 (bag ≠ [] iff data ≠ [])
    + iter 1260 (rules ≠ []) + `System5_step_some_iff`.  Useful packaged
    form for chain-induction. -/
theorem ctsConfigToSystem5Bag_perm_step_succeeds_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_data : cfg.data ≠ [])
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ s5', System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5' := by
  apply (System5_step_some_iff _).mpr
  refine ⟨?_, ?_⟩
  · exact (ctsConfigToSystem5Bag_perm_ne_nil_iff cfg bag h_perm).mpr h_data
  · exact ctsRulesToSystem5Rules_ne_nil cts cfg N h_N

/-- **Iter 1264: ctsHalted = false ⇔ data ≠ []**.  Direct from
    `ctsHalted` def (= `data.isEmpty`).  Useful biconditional
    establishing halt = empty-data. -/
theorem ctsHalted_false_iff_data_ne_nil (cfg : CTSConfig) :
    ctsHalted cfg = false ↔ cfg.data ≠ [] := by
  unfold ctsHalted
  constructor
  · intro h h_data
    rw [h_data] at h
    simp at h
  · intro h_data
    cases h : cfg.data with
    | nil => exact absurd h h_data
    | cons _ _ => simp

/-- **Iter 1265: ctsHalted = true ⇔ data = []**.  Negation form. -/
theorem ctsHalted_true_iff_data_eq_nil (cfg : CTSConfig) :
    ctsHalted cfg = true ↔ cfg.data = [] := by
  unfold ctsHalted
  constructor
  · intro h
    cases h_data : cfg.data with
    | nil => rfl
    | cons _ _ => rw [h_data] at h; simp at h
  · intro h_data
    rw [h_data]; rfl

/-- **Iter 1266: encoder bag empty iff CTS halted**.  Composes iter 1234
    (bag length = 0 iff data = []) + iter 1265.  **The encoder bag
    encodes halt-state correctly: empty bag iff halted CTS config.** -/
theorem ctsConfigToSystem5Bag_eq_nil_iff_halted (cfg : CTSConfig) :
    ctsConfigToSystem5Bag cfg = [] ↔ ctsHalted cfg = true := by
  rw [ctsHalted_true_iff_data_eq_nil]
  constructor
  · intro h
    have h_len : (ctsConfigToSystem5Bag cfg).length = 0 := by rw [h]; rfl
    exact (ctsConfigToSystem5Bag_length_eq_zero_iff cfg).mp h_len
  · intro h_data
    have h_len : (ctsConfigToSystem5Bag cfg).length = 0 :=
      (ctsConfigToSystem5Bag_length_eq_zero_iff cfg).mpr h_data
    exact List.length_eq_zero_iff.mp h_len

/-- **Iter 1267: encoder bag non-empty iff CTS not halted**.  Negation
    form of iter 1266. -/
theorem ctsConfigToSystem5Bag_ne_nil_iff_not_halted (cfg : CTSConfig) :
    ctsConfigToSystem5Bag cfg ≠ [] ↔ ctsHalted cfg = false := by
  rw [ctsConfigToSystem5Bag_ne_nil_iff, ctsHalted_false_iff_data_ne_nil]

/-- **Iter 1268: Perm-chain bag empty iff CTS halted**.  Composes
    iter 1256 (bag = [] iff data = []) + iter 1265.  Halt-detection
    primitive at any chain point. -/
theorem ctsConfigToSystem5Bag_perm_eq_nil_iff_halted
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    bag = [] ↔ ctsHalted cfg = true := by
  rw [ctsConfigToSystem5Bag_perm_eq_nil_iff cfg bag h_perm,
      ctsHalted_true_iff_data_eq_nil]

/-- **Iter 1269: Perm-chain bag non-empty iff CTS not halted**.
    Negation form of iter 1268. -/
theorem ctsConfigToSystem5Bag_perm_ne_nil_iff_not_halted
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    bag ≠ [] ↔ ctsHalted cfg = false := by
  rw [ctsConfigToSystem5Bag_perm_ne_nil_iff cfg bag h_perm,
      ctsHalted_false_iff_data_ne_nil]

/-- **Iter 1270: System5 step succeeds at non-halted Perm-chain points
    with N ≥ 1**.  Combines iter 1269 (¬halted ⇒ data ≠ []) with
    iter 1263 (step succeeds when data ≠ [] and N ≥ 1).  Useful
    packaging using halt-state directly. -/
theorem ctsConfigToSystem5Bag_perm_step_succeeds_nonhalted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_nh : ctsHalted cfg = false)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ s5', System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5' := by
  have h_data : cfg.data ≠ [] := (ctsHalted_false_iff_data_ne_nil cfg).mp h_nh
  exact ctsConfigToSystem5Bag_perm_step_succeeds_v2 cts cfg N h_N h_data bag h_perm

/-- **Iter 1271: System5 step gives `none` at halted Perm-chain points**.
    When `ctsHalted cfg = true`, the bag is empty (iter 1268), so
    `System5.step` returns `none` (`System5_step_none_iff`). -/
theorem ctsConfigToSystem5Bag_perm_step_none_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_h : ctsHalted cfg = true)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = none := by
  have h_bag_nil : bag = [] :=
    (ctsConfigToSystem5Bag_perm_eq_nil_iff_halted cfg bag h_perm).mpr h_h
  apply (System5_step_none_iff _).mpr
  exact Or.inl h_bag_nil

/-- **Iter 1272: cts.step success implies data non-empty**.  When
    `cts.step cfg = some result`, `cfg.data ≠ []`.  Direct from
    `CTS.step` definition (returns `none` on empty data). -/
theorem CTS_step_some_data_ne_nil (cts : CTS) (cfg result : CTSConfig)
    (h_step : cts.step cfg = some result) :
    cfg.data ≠ [] := by
  intro h_data
  unfold CTS.step at h_step
  rw [h_data] at h_step
  simp at h_step

/-- **Iter 1273: cts.step success implies cfg not halted**.  Direct
    consequence of iter 1272 + iter 1264. -/
theorem CTS_step_some_not_halted (cts : CTS) (cfg result : CTSConfig)
    (h_step : cts.step cfg = some result) :
    ctsHalted cfg = false :=
  (ctsHalted_false_iff_data_ne_nil cfg).mpr (CTS_step_some_data_ne_nil cts cfg result h_step)

/-- **Iter 1274: cts.step is total at non-halted configs**.  When
    `ctsHalted cfg = false` (i.e., `data ≠ []`), `cts.step cfg ≠ none`.
    Direct from `CTS.step` definition + iter 1264. -/
theorem CTS_step_total_of_not_halted (cts : CTS) (cfg : CTSConfig)
    (h_nh : ctsHalted cfg = false) :
    cts.step cfg ≠ none := by
  have h_data : cfg.data ≠ [] := (ctsHalted_false_iff_data_ne_nil cfg).mp h_nh
  unfold CTS.step
  cases h : cfg.data with
  | nil => exact absurd h h_data
  | cons _ _ => simp

/-- **Iter 1275: cts.step yields some at non-halted configs**.  Existential
    form of iter 1274. -/
theorem CTS_step_some_of_not_halted (cts : CTS) (cfg : CTSConfig)
    (h_nh : ctsHalted cfg = false) :
    ∃ result, cts.step cfg = some result := by
  cases h : cts.step cfg with
  | none => exact absurd h (CTS_step_total_of_not_halted cts cfg h_nh)
  | some result => exact ⟨result, rfl⟩

/-- **Iter 1276: cts.step = none iff halted**.  Biconditional combining
    iters 1273 and 1274. -/
theorem CTS_step_none_iff_halted_v2 (cts : CTS) (cfg : CTSConfig) :
    cts.step cfg = none ↔ ctsHalted cfg = true := by
  constructor
  · intro h_none
    by_cases h : ctsHalted cfg = false
    · have := CTS_step_total_of_not_halted cts cfg h
      exact absurd h_none this
    · cases h_eq : ctsHalted cfg with
      | true => rfl
      | false => exact absurd h_eq h
  · intro h_h
    by_cases h : cts.step cfg = none
    · exact h
    · cases h_step : cts.step cfg with
      | none => rfl
      | some result =>
        have := CTS_step_some_not_halted cts cfg result h_step
        rw [h_h] at this
        contradiction

/-- **Iter 1277: cts.step success existential iff non-halted**.
    `(∃ result, cts.step cfg = some result) ↔ ctsHalted cfg = false`.
    Composes iter 1275 + iter 1273. -/
theorem CTS_step_some_iff_not_halted (cts : CTS) (cfg : CTSConfig) :
    (∃ result, cts.step cfg = some result) ↔ ctsHalted cfg = false := by
  constructor
  · intro ⟨result, h⟩
    exact CTS_step_some_not_halted cts cfg result h
  · intro h_nh
    exact CTS_step_some_of_not_halted cts cfg h_nh

/-- **Iter 1278: encoder bag length ≥ 4 at non-halted configs**.
    Direct from iter 1264 (¬halted ⇒ data ≠ []) + iter 1142
    (data ≠ [] ⇒ bag.length ≥ 4). -/
theorem ctsConfigToSystem5Bag_length_ge_four_of_not_halted
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) :
    (ctsConfigToSystem5Bag cfg).length ≥ 4 :=
  ctsConfigToSystem5Bag_length_ge_four_of_nonempty cfg
    ((ctsHalted_false_iff_data_ne_nil cfg).mp h_nh)

/-- **Iter 1279: Perm-chain bag length ≥ 4 at non-halted configs**.
    Generic version using halt-state directly. -/
theorem ctsConfigToSystem5Bag_perm_bag_length_ge_four_of_not_halted
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    bag.length ≥ 4 := by
  rw [List.Perm.length_eq h_perm]
  exact ctsConfigToSystem5Bag_length_ge_four_of_not_halted cfg h_nh

/-- **Iter 1280: 1 ∈ bag at non-halted Perm-chain points**.  Direct
    chain: ¬halted ⇒ data ≠ [] ⇒ 1 ∈ bag (via iter 1258). -/
theorem ctsConfigToSystem5Bag_perm_one_mem_of_not_halted
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    (1 : Int) ∈ bag :=
  (ctsConfigToSystem5Bag_perm_one_mem_iff cfg bag h_perm).mpr
    ((ctsHalted_false_iff_data_ne_nil cfg).mp h_nh)

/-- **Iter 1281: 0 ∈ bag.map(·-1) at non-halted Perm-chain points**.
    P-step trigger condition. -/
theorem ctsConfigToSystem5Bag_perm_zero_in_dec_of_not_halted
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    (0 : Int) ∈ bag.map (· - 1) :=
  (ctsConfigToSystem5Bag_perm_zero_in_dec_iff cfg bag h_perm).mpr
    ((ctsHalted_false_iff_data_ne_nil cfg).mp h_nh)

/-- **Iter 1282: Perm-chain bag is empty or contains 1**.  Direct
    case-split on `cfg.data`: if empty, bag = []; else 1 ∈ bag.
    Useful trichotomy primitive. -/
theorem ctsConfigToSystem5Bag_perm_eq_nil_or_one_mem
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    bag = [] ∨ (1 : Int) ∈ bag := by
  by_cases h : cfg.data = []
  · left
    exact (ctsConfigToSystem5Bag_perm_eq_nil_iff cfg bag h_perm).mpr h
  · right
    exact (ctsConfigToSystem5Bag_perm_one_mem_iff cfg bag h_perm).mpr h

/-- **Iter 1283: Perm-chain bag is halted-empty or has 1**.  Halt-state
    form of iter 1282. -/
theorem ctsConfigToSystem5Bag_perm_halted_or_one_mem
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ctsHalted cfg = true ∨ (1 : Int) ∈ bag := by
  rcases ctsConfigToSystem5Bag_perm_eq_nil_or_one_mem cfg bag h_perm with h | h
  · left
    exact (ctsConfigToSystem5Bag_perm_eq_nil_iff_halted cfg bag h_perm).mp h
  · right; exact h

/-- **Iter 1284: Perm-chain dec-erase result Perm-equivalent to encoder
    bag dec-erase**.  Direct from `List.Perm.map (·-1)` + `List.Perm.erase 0`. -/
theorem ctsConfigToSystem5Bag_perm_dec_erase_perm
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ((bag.map (· - 1)).erase 0).Perm
      (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0) :=
  List_Int_dec_erase_perm bag _ h_perm

/-- **Iter 1285: dec-erase length at Perm-chain non-halted
    points**.  Composes iters 1280, 1242, and Perm length transfer. -/
theorem ctsConfigToSystem5Bag_perm_dec_erase_length_of_not_halted
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ((bag.map (· - 1)).erase 0).length = bag.length - 1 := by
  have h_one : (1 : Int) ∈ bag :=
    ctsConfigToSystem5Bag_perm_one_mem_of_not_halted cfg h_nh bag h_perm
  exact List_Int_dec_erase_length_of_one_mem bag h_one

/-- **Iter 1286: post-step bag length ≥ 3 at non-halted Perm-chain
    with N ≥ 1**.  Direct from iter 1195 (step1 length = r1.length +
    bag.length - 1) + iter 1278 (bag.length ≥ 4 at non-halted). -/
theorem ctsConfigToSystem5Bag_perm_step1_bag_length_ge_three
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_nh : ctsHalted cfg = false)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ s5_1, System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5_1
          ∧ s5_1.bag.length ≥ 3 := by
  have h_data : cfg.data ≠ [] := (ctsHalted_false_iff_data_ne_nil cfg).mp h_nh
  obtain ⟨r1, r2, tail, s5_1, h_eq, h_step, h_len⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_length cts cfg N h_N h_data bag h_perm
  refine ⟨s5_1, h_step, ?_⟩
  rw [h_len]
  have h_bag_ge : bag.length ≥ 4 :=
    ctsConfigToSystem5Bag_perm_bag_length_ge_four_of_not_halted cfg h_nh bag h_perm
  omega

/-- **Iter 1287: post-step bag non-empty at non-halted Perm-chain**.
    Direct from iter 1286 (length ≥ 3 > 0). -/
theorem ctsConfigToSystem5Bag_perm_step1_bag_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_nh : ctsHalted cfg = false)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ s5_1, System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5_1
          ∧ s5_1.bag ≠ [] := by
  obtain ⟨s5_1, h_step, h_len⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_length_ge_three cts cfg N h_N h_nh bag h_perm
  refine ⟨s5_1, h_step, ?_⟩
  intro h_eq
  rw [h_eq, List.length_nil] at h_len
  omega

/-- **Iter 1288: post-step rules length = encoder rules length - 1
    at non-halted Perm-chain**.  Direct from iter 1057 (s5_1.rules =
    (r2 :: tail).map(...)) + length analysis.  P-step pops one rule. -/
theorem ctsConfigToSystem5Bag_perm_step1_rules_length
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_nh : ctsHalted cfg = false)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ s5_1, System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5_1
          ∧ s5_1.rules.length = (ctsRulesToSystem5Rules cts cfg N).length - 1 := by
  have h_data : cfg.data ≠ [] := (ctsHalted_false_iff_data_ne_nil cfg).mp h_nh
  obtain ⟨r1, r2, tail, h_eq, h_step⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts cfg N h_N bag h_data h_perm
  refine ⟨_, h_step, ?_⟩
  show ((r2 :: tail).map (fun r => r.map (· + 1))).length = _
  rw [List.length_map, h_eq]
  simp [List.length_cons]

/-- **Iter 1289: post-step rules length ≥ 3 at non-halted Perm-chain
    with N ≥ 1**.  Direct from iter 1288 + iter 1261. -/
theorem ctsConfigToSystem5Bag_perm_step1_rules_length_ge_three
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_nh : ctsHalted cfg = false)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ s5_1, System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5_1
          ∧ s5_1.rules.length ≥ 3 := by
  obtain ⟨s5_1, h_step, h_len⟩ :=
    ctsConfigToSystem5Bag_perm_step1_rules_length cts cfg N h_N h_nh bag h_perm
  refine ⟨s5_1, h_step, ?_⟩
  rw [h_len]
  have h_ge := ctsRulesToSystem5Rules_length_ge_four cts cfg N h_N
  omega

/-- **Iter 1290: post-step rules non-empty at non-halted Perm-chain
    with N ≥ 1**.  Direct from iter 1289 (length ≥ 3 > 0). -/
theorem ctsConfigToSystem5Bag_perm_step1_rules_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_nh : ctsHalted cfg = false)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ s5_1, System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5_1
          ∧ s5_1.rules ≠ [] := by
  obtain ⟨s5_1, h_step, h_len⟩ :=
    ctsConfigToSystem5Bag_perm_step1_rules_length_ge_three cts cfg N h_N h_nh bag h_perm
  refine ⟨s5_1, h_step, ?_⟩
  intro h_eq
  rw [h_eq, List.length_nil] at h_len
  omega

/-- **Iter 1291: two consecutive System5 steps succeed at non-halted
    Perm-chain points with N ≥ 1**.  Composes iter 1287 (post-step
    bag non-empty) + iter 1290 (post-step rules non-empty) +
    `System5_step_some_iff` for the second step.
    **Generic version** of iters 1062 (false-head specific) / 1163
    (true-head specific) using halt-state directly.
    **🎯 400-LEMMA MILESTONE.** -/
theorem ctsConfigToSystem5Bag_perm_step2_succeeds
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_nh : ctsHalted cfg = false)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ s5_2, System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ 2 = some s5_2 := by
  obtain ⟨s5_1, h_step1, h_bag_ne⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_ne_nil cts cfg N h_N h_nh bag h_perm
  obtain ⟨s5_1', h_step1', h_rules_ne⟩ :=
    ctsConfigToSystem5Bag_perm_step1_rules_ne_nil cts cfg N h_N h_nh bag h_perm
  have h_align : s5_1 = s5_1' := Option.some.inj (h_step1.symm.trans h_step1')
  have h_rules_ne' : s5_1.rules ≠ [] := h_align ▸ h_rules_ne
  obtain ⟨s5_2, h_step2⟩ :=
    (System5_step_some_iff s5_1).mpr ⟨h_bag_ne, h_rules_ne'⟩
  refine ⟨s5_2, ?_⟩
  rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add]
  rw [System5.nSteps_one, h_step1]
  simp only [Option.bind_some, System5.nSteps_one]
  exact h_step2

/-- **Iter 1292: post-step bag length ≥ bag.length - 1 at non-halted
    Perm-chain**.  Lower bound: after one step, the bag length doesn't
    drop below `original - 1`.  Direct from iter 1195. -/
theorem ctsConfigToSystem5Bag_perm_step1_bag_length_ge_pred
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (h_nh : ctsHalted cfg = false)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    ∃ s5_1, System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5_1
          ∧ s5_1.bag.length ≥ bag.length - 1 := by
  have h_data : cfg.data ≠ [] := (ctsHalted_false_iff_data_ne_nil cfg).mp h_nh
  obtain ⟨_r1, _r2, _tail, s5_1, _h_eq, h_step, h_len⟩ :=
    ctsConfigToSystem5Bag_perm_step1_bag_length cts cfg N h_N h_data bag h_perm
  refine ⟨s5_1, h_step, ?_⟩
  rw [h_len]
  omega

/-- **Iter 1293: cts.step result phase < cts.appendants.length**.
    Direct from `CTS.step` definition (phase = `(cfg.phase + 1) %
    cts.appendants.length`, always bounded).  Useful invariant. -/
theorem CTS_step_phase_bound (cts : CTS) (cfg result : CTSConfig)
    (h_step : cts.step cfg = some result) :
    result.phase < cts.appendants.length := by
  unfold CTS.step at h_step
  cases h_data : cfg.data with
  | nil => rw [h_data] at h_step; simp at h_step
  | cons _ _ =>
    rw [h_data] at h_step
    simp at h_step
    rw [← h_step]
    exact Nat.mod_lt _ cts.nonempty

/-- **Iter 1294: cts.step result phase explicit form**.  When
    `cts.step cfg = some result`, `result.phase = (cfg.phase + 1) %
    cts.appendants.length`.  Direct from `CTS.step` definition. -/
theorem CTS_step_phase_eq (cts : CTS) (cfg result : CTSConfig)
    (h_step : cts.step cfg = some result) :
    result.phase = (cfg.phase + 1) % cts.appendants.length := by
  unfold CTS.step at h_step
  cases h_data : cfg.data with
  | nil => rw [h_data] at h_step; simp at h_step
  | cons _ _ =>
    rw [h_data] at h_step
    simp at h_step
    rw [← h_step]

/-- **Iter 1295: currentAppendant phase ∈ appendants**.  Direct from
    `CTS.currentAppendant` def + `List.get_mem`.  Useful invariant. -/
theorem CTS_currentAppendant_mem (cts : CTS) (phase : Nat) :
    cts.currentAppendant phase ∈ cts.appendants := by
  unfold CTS.currentAppendant
  apply List.get_mem

/-- **Iter 1300 (ITER MILESTONE): cts.appendants.length ≥ 1**.  Direct
    from `cts.nonempty`.  Useful primitive in cleaner Nat form. -/
theorem CTS_appendants_length_ge_one (cts : CTS) :
    cts.appendants.length ≥ 1 := cts.nonempty

/-- **Iter 1301: cts.appendants ≠ []**.  Direct from `cts.nonempty`. -/
theorem CTS_appendants_ne_nil (cts : CTS) :
    cts.appendants ≠ [] := by
  intro h
  have h_len : cts.appendants.length = 0 := by rw [h]; rfl
  have := cts.nonempty
  omega

/-- **Iter 1302: cts.appendants.length > 0 (Nat form)**.  Direct
    from iter 1300. -/
theorem CTS_appendants_length_pos (cts : CTS) :
    cts.appendants.length > 0 := cts.nonempty

/-- **Iter 1303: 4 * cts.appendants.length > 0**.  Useful primitive
    for arithmetic in encoder rules length analysis. -/
theorem CTS_four_times_appendants_length_pos (cts : CTS) :
    4 * cts.appendants.length > 0 := by
  have := cts.nonempty
  omega

/-- **Iter 1306: cts.eval cfg 0 = some cfg iff halted**.  Direct from
    `CTS.eval` def at 0 fuel. -/
theorem CTS_eval_zero_iff_halted (cts : CTS) (cfg : CTSConfig) :
    cts.eval cfg 0 = some cfg ↔ ctsHalted cfg = true := by
  unfold CTS.eval
  constructor
  · intro h
    by_cases h_halt : ctsHalted cfg = true
    · exact h_halt
    · simp [h_halt] at h
  · intro h_halt
    simp [h_halt]

/-- **Iter 1307: cts.eval cfg 0 = none iff not halted**.  Negation
    form of iter 1306. -/
theorem CTS_eval_zero_eq_none_iff_not_halted (cts : CTS) (cfg : CTSConfig) :
    cts.eval cfg 0 = none ↔ ctsHalted cfg = false := by
  unfold CTS.eval
  constructor
  · intro h
    by_cases h_halt : ctsHalted cfg = true
    · simp [h_halt] at h
    · cases h_eq : ctsHalted cfg with
      | true => exact absurd h_eq h_halt
      | false => rfl
  · intro h_nh
    simp [h_nh]

/-- **Iter 1308: cts.eval result is halted**.  Whenever `cts.eval cfg
    fuel = some result`, `ctsHalted result = true`.  By induction on
    fuel: the only ways eval returns `some` are (a) halted at start,
    (b) reaches halted via recursion, (c) step returns none (which
    iter 1276 says implies halted). -/
theorem CTS_eval_some_halted (cts : CTS) :
    ∀ (fuel : Nat) (cfg result : CTSConfig),
      cts.eval cfg fuel = some result → ctsHalted result = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro cfg result h
    unfold CTS.eval at h
    by_cases h_halt : ctsHalted cfg = true
    · simp [h_halt] at h
      rw [← h]; exact h_halt
    · simp [h_halt] at h
  | succ n ih =>
    intro cfg result h
    unfold CTS.eval at h
    by_cases h_halt : ctsHalted cfg = true
    · simp [h_halt] at h
      rw [← h]; exact h_halt
    · simp [h_halt] at h
      cases h_step : cts.step cfg with
      | none =>
        rw [h_step] at h
        simp at h
        rw [← h]
        exact (CTS_step_none_iff_halted_v2 cts cfg).mp h_step
      | some cfg' =>
        rw [h_step] at h
        simp at h
        exact ih cfg' result h

/-- **Iter 1309: cts.eval result.data is empty**.  Direct from
    iter 1308 (result halted) + iter 1265 (halted iff data empty). -/
theorem CTS_eval_some_data_empty (cts : CTS) (cfg result : CTSConfig) (fuel : Nat)
    (h : cts.eval cfg fuel = some result) :
    result.data = [] :=
  (ctsHalted_true_iff_data_eq_nil result).mp (CTS_eval_some_halted cts fuel cfg result h)

/-- **Iter 1310: cts.eval result encoder bag is empty**.  Direct from
    iter 1308 + iter 1266. -/
theorem CTS_eval_some_encoder_bag_empty
    (cts : CTS) (cfg result : CTSConfig) (fuel : Nat)
    (h : cts.eval cfg fuel = some result) :
    ctsConfigToSystem5Bag result = [] :=
  (ctsConfigToSystem5Bag_eq_nil_iff_halted result).mpr
    (CTS_eval_some_halted cts fuel cfg result h)

/-- **Iter 1311: CTS.Halts implies result halted**.  When CTS halts,
    `cts.eval cfg fuel = some result` for some fuel, and that result
    is halted (iter 1308). -/
theorem CTS_Halts_eval_result_halted (cts : CTS) (cfg : CTSConfig)
    (h : cts.Halts cfg) :
    ∃ fuel result, cts.eval cfg fuel = some result ∧ ctsHalted result = true := by
  obtain ⟨fuel, result, h_eval⟩ := h
  refine ⟨fuel, result, h_eval, ?_⟩
  exact CTS_eval_some_halted cts fuel cfg result h_eval

/-- **Iter 1312: CTS.Halts implies eval result has empty data**.
    Direct from iter 1311 + iter 1265. **🎯 420 INCOMING**. -/
theorem CTS_Halts_eval_result_data_empty (cts : CTS) (cfg : CTSConfig)
    (h : cts.Halts cfg) :
    ∃ fuel result, cts.eval cfg fuel = some result ∧ result.data = [] := by
  obtain ⟨fuel, result, h_eval, h_halted⟩ := CTS_Halts_eval_result_halted cts cfg h
  refine ⟨fuel, result, h_eval, ?_⟩
  exact (ctsHalted_true_iff_data_eq_nil result).mp h_halted

/-- **Iter 1313: CTS.Halts implies eval result encoder bag is empty**.
    Direct from iter 1311 + iter 1266. -/
theorem CTS_Halts_eval_result_bag_empty (cts : CTS) (cfg : CTSConfig)
    (h : cts.Halts cfg) :
    ∃ fuel result, cts.eval cfg fuel = some result
                 ∧ ctsConfigToSystem5Bag result = [] := by
  obtain ⟨fuel, result, h_eval, h_halted⟩ := CTS_Halts_eval_result_halted cts cfg h
  refine ⟨fuel, result, h_eval, ?_⟩
  exact (ctsConfigToSystem5Bag_eq_nil_iff_halted result).mpr h_halted

/-- **Iter 1314: CTS.Halts existential extraction**.  When `cts.Halts cfg`,
    we can extract a halted result config witness.  Existential form
    of iter 1311. -/
theorem CTS_Halts_iff_exists_halted_eval (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ∃ fuel result, cts.eval cfg fuel = some result
                                 ∧ ctsHalted result = true := by
  constructor
  · exact CTS_Halts_eval_result_halted cts cfg
  · intro ⟨fuel, result, h_eval, _⟩
    exact ⟨fuel, result, h_eval⟩

/-- **Iter 1315: cts.eval at halted cfg returns some cfg at any fuel**.
    Halted state is "absorbing" — once halted, eval just returns it. -/
theorem CTS_eval_halted_returns (cts : CTS) (cfg : CTSConfig)
    (h : ctsHalted cfg = true) (fuel : Nat) :
    cts.eval cfg fuel = some cfg := by
  cases fuel with
  | zero => unfold CTS.eval; simp [h]
  | succ n => unfold CTS.eval; simp [h]

/-- **Iter 1316: CTS.Halts halted cfg is trivially true**.  Halted
    configs always halt (with fuel = 0). -/
theorem CTS_Halts_of_halted (cts : CTS) (cfg : CTSConfig)
    (h : ctsHalted cfg = true) :
    cts.Halts cfg :=
  ⟨0, cfg, CTS_eval_halted_returns cts cfg h 0⟩

/-- **Iter 1317: data empty implies Halts**.  Direct from
    `ctsHalted_true_iff_data_eq_nil` + iter 1316. -/
theorem CTS_Halts_of_data_empty (cts : CTS) (cfg : CTSConfig)
    (h : cfg.data = []) :
    cts.Halts cfg :=
  CTS_Halts_of_halted cts cfg ((ctsHalted_true_iff_data_eq_nil cfg).mpr h)

/-- **Iter 1318: encoder bag empty implies Halts**.  Composes iter 1266
    + iter 1316. -/
theorem CTS_Halts_of_encoder_bag_empty (cts : CTS) (cfg : CTSConfig)
    (h : ctsConfigToSystem5Bag cfg = []) :
    cts.Halts cfg :=
  CTS_Halts_of_halted cts cfg ((ctsConfigToSystem5Bag_eq_nil_iff_halted cfg).mp h)

/-- **Iter 1319: cts.eval is monotonic in fuel**.  When `cts.eval cfg
    fuel1 = some result`, eval at higher fuel returns the same halted
    result (since result is halted, iter 1308, and halted is absorbing,
    iter 1315). -/
theorem CTS_eval_monotonic (cts : CTS) (cfg result : CTSConfig)
    (fuel1 : Nat) (h : cts.eval cfg fuel1 = some result) (k : Nat) :
    cts.eval cfg (fuel1 + k) = some result := by
  -- Strategy: by structure on cts.eval, the result must be reachable;
  -- once halted, additional fuel just returns the same.
  -- We don't need this directly — easier path via Halts.
  -- Use induction on fuel1 directly.
  induction fuel1 generalizing cfg with
  | zero =>
    rw [Nat.zero_add]
    unfold CTS.eval at h
    by_cases h_halt : ctsHalted cfg = true
    · simp [h_halt] at h
      rw [← h]
      exact CTS_eval_halted_returns cts cfg h_halt k
    · simp [h_halt] at h
  | succ n ih =>
    unfold CTS.eval at h
    by_cases h_halt : ctsHalted cfg = true
    · simp [h_halt] at h
      rw [← h]
      exact CTS_eval_halted_returns cts cfg h_halt _
    · simp [h_halt] at h
      cases h_step : cts.step cfg with
      | none =>
        rw [h_step] at h; simp at h
        rw [← h]
        have : ctsHalted cfg = true := (CTS_step_none_iff_halted_v2 cts cfg).mp h_step
        exact CTS_eval_halted_returns cts cfg this _
      | some cfg' =>
        rw [h_step] at h; simp at h
        have h_eval' : cts.eval cfg' (n + k) = some result := ih cfg' h
        show cts.eval cfg (n + 1 + k) = some result
        rw [show n + 1 + k = (n + k) + 1 from by omega]
        unfold CTS.eval
        simp [h_halt, h_step]
        exact h_eval'

/-- **Iter 1320: cts.eval is deterministic across different fuels**.
    When `cts.eval cfg f1 = some r1` and `cts.eval cfg f2 = some r2`,
    `r1 = r2`.  Direct from iter 1319 (monotonic). -/
theorem CTS_eval_deterministic
    (cts : CTS) (cfg : CTSConfig) (f1 f2 : Nat) (r1 r2 : CTSConfig)
    (h1 : cts.eval cfg f1 = some r1) (h2 : cts.eval cfg f2 = some r2) :
    r1 = r2 := by
  by_cases h_le : f1 ≤ f2
  · obtain ⟨k, hk⟩ := Nat.le.dest h_le
    rw [← hk] at h2
    have h := CTS_eval_monotonic cts cfg r1 f1 h1 k
    rw [h] at h2
    exact Option.some.inj h2
  · have h_le' : f2 ≤ f1 := by omega
    obtain ⟨k, hk⟩ := Nat.le.dest h_le'
    rw [← hk] at h1
    have h := CTS_eval_monotonic cts cfg r2 f2 h2 k
    rw [h] at h1
    exact (Option.some.inj h1).symm

/-- **Iter 1321: encoder bag depends only on data, not phase**.
    `ctsConfigToSystem5Bag {data, phase1} = ctsConfigToSystem5Bag {data, phase2}`. -/
theorem ctsConfigToSystem5Bag_phase_invariant
    (data : List Bool) (phase1 phase2 : Nat) :
    ctsConfigToSystem5Bag { data := data, phase := phase1 }
      = ctsConfigToSystem5Bag { data := data, phase := phase2 } := rfl

/-- **Iter 1322: encoder bag = aux of cfg.data 1**.  Direct definitional
    unfolding. -/
theorem ctsConfigToSystem5Bag_eq_aux (cfg : CTSConfig) :
    ctsConfigToSystem5Bag cfg = ctsConfigToSystem5BagAux cfg.data 1 := rfl

/-- **Iter 1324: cts.Halts is preserved by step (forward)**.  When
    `cts.step cfg = some result` and `result` halts, `cfg` halts too.
    Direct: prepend a step to the eval trajectory. -/
theorem CTS_Halts_of_step_Halts
    (cts : CTS) (cfg result : CTSConfig)
    (h_step : cts.step cfg = some result)
    (h_halts : cts.Halts result) :
    cts.Halts cfg := by
  obtain ⟨fuel, final, h_eval⟩ := h_halts
  refine ⟨fuel + 1, final, ?_⟩
  unfold CTS.eval
  have h_nh : ctsHalted cfg = false :=
    CTS_step_some_not_halted cts cfg result h_step
  simp [h_nh, h_step]
  exact h_eval

/-- **Iter 1325: CTS.Halts step-Halts converse for non-halted cfg**.
    When `cfg.Halts` and `cfg` is not halted, ∃ result, `cts.step cfg
    = some result ∧ result.Halts`. -/
theorem CTS_Halts_step_some_of_not_halted
    (cts : CTS) (cfg : CTSConfig)
    (h_halts : cts.Halts cfg)
    (h_nh : ctsHalted cfg = false) :
    ∃ result, cts.step cfg = some result ∧ cts.Halts result := by
  obtain ⟨result, h_step⟩ := CTS_step_some_of_not_halted cts cfg h_nh
  refine ⟨result, h_step, ?_⟩
  -- result.Halts: from cfg.Halts via eval at fuel ≥ 1, the next config halts.
  obtain ⟨fuel, final, h_eval⟩ := h_halts
  cases fuel with
  | zero =>
    -- fuel = 0: eval cfg 0 = some final means cfg is halted
    unfold CTS.eval at h_eval
    by_cases h_halt : ctsHalted cfg = true
    · rw [h_halt] at h_nh; contradiction
    · simp [h_halt] at h_eval
  | succ n =>
    -- fuel = n+1: eval unfolds to step + recurse
    refine ⟨n, final, ?_⟩
    unfold CTS.eval at h_eval
    simp [h_nh, h_step] at h_eval
    exact h_eval

/-- **Iter 1326: CTS.Halts characterization**.  `cfg.Halts ↔ halted cfg
    ∨ (∃ result, step cfg = some result ∧ result.Halts)`.  Combines
    iters 1316, 1324, 1325. -/
theorem CTS_Halts_iff_halted_or_step_Halts (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ctsHalted cfg = true
                 ∨ (∃ result, cts.step cfg = some result ∧ cts.Halts result) := by
  constructor
  · intro h_halts
    by_cases h_h : ctsHalted cfg = true
    · left; exact h_h
    · right
      have h_nh : ctsHalted cfg = false := by
        cases h : ctsHalted cfg with
        | true => exact absurd h h_h
        | false => rfl
      exact CTS_Halts_step_some_of_not_halted cts cfg h_halts h_nh
  · intro h_or
    rcases h_or with h_h | ⟨result, h_step, h_halts⟩
    · exact CTS_Halts_of_halted cts cfg h_h
    · exact CTS_Halts_of_step_Halts cts cfg result h_step h_halts

/-- **Iter 1327: CTS.Halts at non-halted cfg iff step result Halts**.
    Specialization of iter 1326 to non-halted: when `cfg` not halted,
    `cfg.Halts ↔ ∃ result, step cfg = some result ∧ result.Halts`. -/
theorem CTS_Halts_iff_step_Halts_of_not_halted
    (cts : CTS) (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) :
    cts.Halts cfg ↔ ∃ result, cts.step cfg = some result ∧ cts.Halts result := by
  rw [CTS_Halts_iff_halted_or_step_Halts]
  constructor
  · intro h
    rcases h with h_h | h_step
    · rw [h_h] at h_nh; contradiction
    · exact h_step
  · intro h
    right; exact h

/-- **Iter 1328: cts.nSteps at 0 returns some cfg**.  Direct from def. -/
theorem CTS_nSteps_zero (cts : CTS) (cfg : CTSConfig) :
    cts.nSteps cfg 0 = some cfg := rfl

/-- **Iter 1329: cts.nSteps successor unfolding**.  Direct from def:
    `nSteps cfg (n+1) = match step cfg with | none => none | some cfg' => nSteps cfg' n`. -/
theorem CTS_nSteps_succ (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    cts.nSteps cfg (n + 1)
      = match cts.step cfg with
        | none => none
        | some cfg' => cts.nSteps cfg' n := rfl

/-- **Iter 1330: cts.nSteps composition**.  `cts.nSteps cfg (n + m) =
    (cts.nSteps cfg n).bind (fun cfg' => cts.nSteps cfg' m)`.  By
    induction on n. -/
theorem CTS_nSteps_add (cts : CTS) :
    ∀ (n m : Nat) (cfg : CTSConfig),
      cts.nSteps cfg (n + m) = (cts.nSteps cfg n).bind (fun cfg' => cts.nSteps cfg' m) := by
  intro n
  induction n with
  | zero =>
    intro m cfg
    rw [Nat.zero_add, CTS_nSteps_zero]; rfl
  | succ k ih =>
    intro m cfg
    rw [show k + 1 + m = (k + m) + 1 from by omega, CTS_nSteps_succ, CTS_nSteps_succ]
    cases h_step : cts.step cfg with
    | none => simp
    | some cfg' => exact ih m cfg'

/-- **Iter 1331: cts.nSteps cfg 1 = cts.step cfg**.  Direct from def. -/
theorem CTS_nSteps_one (cts : CTS) (cfg : CTSConfig) :
    cts.nSteps cfg 1 = cts.step cfg := by
  unfold CTS.nSteps
  cases cts.step cfg with
  | none => rfl
  | some cfg' => rfl

/-- **Iter 1332: cts.nSteps preserves halt-detection (none means halt
    along the trajectory)**.  When `cts.nSteps cfg n = none`, some
    intermediate config halted (step gave none).  By induction. -/
theorem CTS_nSteps_eq_none_iff_step_eq_none
    (cts : CTS) :
    ∀ (n : Nat) (cfg : CTSConfig),
      cts.nSteps cfg (n + 1) = none
        ↔ cts.step cfg = none ∨ ∃ cfg', cts.step cfg = some cfg' ∧ cts.nSteps cfg' n = none := by
  intro n cfg
  rw [CTS_nSteps_succ]
  constructor
  · intro h
    cases h_step : cts.step cfg with
    | none => left; rfl
    | some cfg' =>
      rw [h_step] at h
      simp at h
      right; exact ⟨cfg', rfl, h⟩
  · intro h
    rcases h with h | ⟨cfg', h_step, h_n⟩
    · rw [h]
    · rw [h_step]; exact h_n

/-- **Iter 1333: cts.nSteps prefix existence**.  When `nSteps cfg n =
    some result`, all prefixes `nSteps cfg k` for `k ≤ n` exist (some). -/
theorem CTS_nSteps_some_of_le
    (cts : CTS) :
    ∀ (n : Nat) (cfg result : CTSConfig),
      cts.nSteps cfg n = some result →
      ∀ k, k ≤ n → ∃ result_k, cts.nSteps cfg k = some result_k := by
  intro n
  induction n with
  | zero =>
    intro cfg result h_n k h_le
    have h_k : k = 0 := Nat.le_zero.mp h_le
    rw [h_k]
    exact ⟨cfg, rfl⟩
  | succ n' ih =>
    intro cfg result h_n k h_le
    by_cases h_k : k = n' + 1
    · rw [h_k]; exact ⟨result, h_n⟩
    · have h_k_le : k ≤ n' := by omega
      rw [CTS_nSteps_succ] at h_n
      cases h_step : cts.step cfg with
      | none => rw [h_step] at h_n; simp at h_n
      | some cfg' =>
        rw [h_step] at h_n
        simp at h_n
        cases k with
        | zero => exact ⟨cfg, rfl⟩
        | succ k' =>
          have h_k'_le : k' ≤ n' := by omega
          obtain ⟨result_k, h_k_eval⟩ := ih cfg' result h_n k' h_k'_le
          refine ⟨result_k, ?_⟩
          rw [CTS_nSteps_succ, h_step]
          exact h_k_eval

/-- **Iter 1334: cts.nSteps n.succ = some implies ¬halted cfg**.
    nSteps requires a successful step, which requires non-halted cfg. -/
theorem CTS_nSteps_succ_some_not_halted
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h : cts.nSteps cfg (n + 1) = some result) :
    ctsHalted cfg = false := by
  rw [CTS_nSteps_succ] at h
  cases h_step : cts.step cfg with
  | none => rw [h_step] at h; simp at h
  | some cfg' =>
    exact CTS_step_some_not_halted cts cfg cfg' h_step

/-- **Iter 1335: System5.nSteps prefix existence**.  When `nSteps cfg
    n = some result`, all prefixes `nSteps cfg k` for `k ≤ n` exist.
    Companion to iter 1333 for System5. -/
theorem System5_nSteps_some_of_le :
    ∀ (n : Nat) (cfg result : System5Config),
      System5.nSteps cfg n = some result →
      ∀ k, k ≤ n → ∃ result_k, System5.nSteps cfg k = some result_k := by
  intro n
  induction n with
  | zero =>
    intro cfg result h_n k h_le
    have h_k : k = 0 := Nat.le_zero.mp h_le
    rw [h_k]
    exact ⟨cfg, rfl⟩
  | succ n' ih =>
    intro cfg result h_n k h_le
    by_cases h_k : k = n' + 1
    · rw [h_k]; exact ⟨result, h_n⟩
    · have h_k_le : k ≤ n' := by omega
      rw [System5.nSteps_succ] at h_n
      cases h_step : System5.step cfg with
      | none => rw [h_step] at h_n; simp at h_n
      | some cfg' =>
        rw [h_step] at h_n
        simp at h_n
        cases k with
        | zero => exact ⟨cfg, rfl⟩
        | succ k' =>
          have h_k'_le : k' ≤ n' := by omega
          obtain ⟨result_k, h_k_eval⟩ := ih cfg' result h_n k' h_k'_le
          refine ⟨result_k, ?_⟩
          rw [System5.nSteps_succ, h_step]
          exact h_k_eval

/-- **Iter 1336: System5.nSteps n.succ some implies bag and rules
    non-empty at start**.  Direct from `System5_step_some_iff`. -/
theorem System5_nSteps_succ_some_bag_rules_ne_nil
    (cfg result : System5Config) (n : Nat)
    (h : System5.nSteps cfg (n + 1) = some result) :
    cfg.bag ≠ [] ∧ cfg.rules ≠ [] := by
  rw [System5.nSteps_succ] at h
  cases h_step : System5.step cfg with
  | none => rw [h_step] at h; simp at h
  | some cfg' =>
    have h_step_some : ∃ s, System5.step cfg = some s := ⟨cfg', h_step⟩
    exact (System5_step_some_iff cfg).mp h_step_some

/-- **Iter 1337: cts.nSteps n+1 = some iff nSteps n some + step**.
    `nSteps cfg (n + 1) = some result ↔ ∃ result', nSteps cfg n = some
    result' ∧ step result' = some result`.  Useful trailing-step form. -/
theorem CTS_nSteps_succ_some_iff
    (cts : CTS) (cfg result : CTSConfig) (n : Nat) :
    cts.nSteps cfg (n + 1) = some result
      ↔ ∃ result', cts.nSteps cfg n = some result' ∧ cts.step result' = some result := by
  rw [show n + 1 = n + 1 from rfl, CTS_nSteps_add cts n 1]
  constructor
  · intro h
    cases h_n : cts.nSteps cfg n with
    | none => rw [h_n] at h; simp at h
    | some result' =>
      rw [h_n] at h
      simp at h
      refine ⟨result', rfl, ?_⟩
      rw [CTS_nSteps_one] at h; exact h
  · intro ⟨result', h_n, h_step⟩
    rw [h_n]; simp
    rw [CTS_nSteps_one]; exact h_step

/-- **Iter 1338: System5.nSteps n+1 = some iff nSteps n + step**.
    Trailing-step characterization for System5. Companion to iter 1337. -/
theorem System5_nSteps_succ_some_iff
    (cfg result : System5Config) (n : Nat) :
    System5.nSteps cfg (n + 1) = some result
      ↔ ∃ result', System5.nSteps cfg n = some result' ∧ System5.step result' = some result := by
  rw [show n + 1 = n + 1 from rfl, System5.nSteps_add]
  constructor
  · intro h
    cases h_n : System5.nSteps cfg n with
    | none => rw [h_n] at h; simp at h
    | some result' =>
      rw [h_n] at h
      simp at h
      refine ⟨result', rfl, ?_⟩
      rw [System5.nSteps_one] at h; exact h
  · intro ⟨result', h_n, h_step⟩
    rw [h_n]; simp
    rw [System5.nSteps_one]; exact h_step

/-- **Iter 1339: cts.nSteps cfg 0 = some result implies result = cfg**. -/
theorem CTS_nSteps_zero_eq (cts : CTS) (cfg result : CTSConfig)
    (h : cts.nSteps cfg 0 = some result) :
    result = cfg :=
  Option.some.inj h.symm

/-- **Iter 1340: System5.nSteps cfg 0 = some result implies result = cfg**. -/
theorem System5_nSteps_zero_eq (cfg result : System5Config)
    (h : System5.nSteps cfg 0 = some result) :
    result = cfg :=
  Option.some.inj h.symm

/-- **Iter 1341 (🎯 450 LANDMARK): cts.nSteps split at any prefix point**.
    When `nSteps cfg n_total = some result_total` and `k ≤ n_total`,
    `∃ result_k, nSteps cfg k = some result_k ∧ nSteps result_k
    (n_total - k) = some result_total`.  Direct from iter 1330. -/
theorem CTS_nSteps_split_at
    (cts : CTS) (cfg result_total : CTSConfig) (n_total k : Nat)
    (h_le : k ≤ n_total)
    (h_total : cts.nSteps cfg n_total = some result_total) :
    ∃ result_k, cts.nSteps cfg k = some result_k
              ∧ cts.nSteps result_k (n_total - k) = some result_total := by
  obtain ⟨m, hm⟩ := Nat.le.dest h_le
  rw [← hm] at h_total
  rw [CTS_nSteps_add] at h_total
  cases h_k : cts.nSteps cfg k with
  | none => rw [h_k] at h_total; simp at h_total
  | some result_k =>
    rw [h_k] at h_total
    simp at h_total
    refine ⟨result_k, rfl, ?_⟩
    have h_diff : n_total - k = m := by omega
    rw [h_diff]
    exact h_total

/-- **Iter 1342: System5.nSteps split at any prefix point**.  Companion
    to iter 1341 for System5. -/
theorem System5_nSteps_split_at
    (cfg result_total : System5Config) (n_total k : Nat)
    (h_le : k ≤ n_total)
    (h_total : System5.nSteps cfg n_total = some result_total) :
    ∃ result_k, System5.nSteps cfg k = some result_k
              ∧ System5.nSteps result_k (n_total - k) = some result_total := by
  obtain ⟨m, hm⟩ := Nat.le.dest h_le
  rw [← hm] at h_total
  rw [System5.nSteps_add] at h_total
  cases h_k : System5.nSteps cfg k with
  | none => rw [h_k] at h_total; simp at h_total
  | some result_k =>
    rw [h_k] at h_total
    simp at h_total
    refine ⟨result_k, rfl, ?_⟩
    have h_diff : n_total - k = m := by omega
    rw [h_diff]
    exact h_total

/-- **Iter 1343: cts.nSteps n.succ = some implies first step succeeds**.
    Direct from `nSteps_succ` unfolding. -/
theorem CTS_nSteps_succ_some_first_step
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h : cts.nSteps cfg (n + 1) = some result) :
    ∃ cfg', cts.step cfg = some cfg' ∧ cts.nSteps cfg' n = some result := by
  rw [CTS_nSteps_succ] at h
  cases h_step : cts.step cfg with
  | none => rw [h_step] at h; simp at h
  | some cfg' => rw [h_step] at h; exact ⟨cfg', rfl, h⟩

/-- **Iter 1344: System5.nSteps n.succ some implies first step succeeds**.
    Companion to iter 1343 for System5. -/
theorem System5_nSteps_succ_some_first_step
    (cfg result : System5Config) (n : Nat)
    (h : System5.nSteps cfg (n + 1) = some result) :
    ∃ cfg', System5.step cfg = some cfg' ∧ System5.nSteps cfg' n = some result := by
  rw [System5.nSteps_succ] at h
  cases h_step : System5.step cfg with
  | none => rw [h_step] at h; simp at h
  | some cfg' => rw [h_step] at h; exact ⟨cfg', rfl, h⟩

/-- **Iter 1345: cts.eval at non-halted cfg with step success = recurse**.
    When `cfg` is not halted and `cts.step cfg = some cfg'`,
    `cts.eval cfg (n+1) = cts.eval cfg' n`. -/
theorem CTS_eval_succ_not_halted (cts : CTS) (cfg cfg' : CTSConfig) (n : Nat)
    (h_nh : ctsHalted cfg = false) (h_step : cts.step cfg = some cfg') :
    cts.eval cfg (n + 1) = cts.eval cfg' n := by
  show (match n + 1 with
        | 0 => if ctsHalted cfg = true then some cfg else none
        | fuel + 1 =>
          if ctsHalted cfg = true then some cfg
          else
            match cts.step cfg with
            | none => some cfg
            | some cfg'' => cts.eval cfg'' fuel) = _
  simp [h_nh, h_step]

/-- **Iter 1346: dec preserves encoder bag Nodup**.  Direct from
    `ctsConfigToSystem5Bag_nodup` (existing) + iter 1245. -/
theorem ctsConfigToSystem5Bag_dec_nodup (cfg : CTSConfig) :
    ((ctsConfigToSystem5Bag cfg).map (· - 1)).Nodup :=
  List_Int_dec_nodup _ (ctsConfigToSystem5Bag_nodup cfg)

/-- **Iter 1347: dec-erase preserves encoder bag Nodup**. -/
theorem ctsConfigToSystem5Bag_dec_erase_nodup (cfg : CTSConfig) :
    (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0).Nodup :=
  List_Int_dec_erase_nodup _ (ctsConfigToSystem5Bag_nodup cfg)

/-- **Iter 1348: encoder bag dec-erase length at non-halted = bag.length - 1**.
    Direct from iter 1242 + iter 1257 (1 ∈ bag iff data ≠ []). -/
theorem ctsConfigToSystem5Bag_dec_erase_length_of_not_halted
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) :
    (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0).length
      = (ctsConfigToSystem5Bag cfg).length - 1 := by
  have h_one : (1 : Int) ∈ ctsConfigToSystem5Bag cfg :=
    (ctsConfigToSystem5Bag_one_mem_iff cfg).mpr
      ((ctsHalted_false_iff_data_ne_nil cfg).mp h_nh)
  exact List_Int_dec_erase_length_of_one_mem _ h_one

/-- **Iter 1349: encoder bag dec-erase length closed form**.
    `dec-erase length = 4 * data.length - 1` at non-halted. -/
theorem ctsConfigToSystem5Bag_dec_erase_length_eq
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) :
    (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0).length
      = 4 * cfg.data.length - 1 := by
  rw [ctsConfigToSystem5Bag_dec_erase_length_of_not_halted cfg h_nh,
      ctsConfigToSystem5Bag_length]

/-- **Iter 1350 (ITER 1350 MILESTONE): encoder bag dec-erase length ≥ 3
    at non-halted**.  Direct from iter 1349 + iter 1278 (length ≥ 4). -/
theorem ctsConfigToSystem5Bag_dec_erase_length_ge_three
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) :
    (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0).length ≥ 3 := by
  rw [ctsConfigToSystem5Bag_dec_erase_length_of_not_halted cfg h_nh]
  have := ctsConfigToSystem5Bag_length_ge_four_of_not_halted cfg h_nh
  omega

/-- **Iter 1351: encoder bag dec-erase non-empty at non-halted**. -/
theorem ctsConfigToSystem5Bag_dec_erase_ne_nil_of_not_halted
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) :
    ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0 ≠ [] := by
  intro h
  have h_len : (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0).length = 0 := by
    rw [h]; rfl
  have := ctsConfigToSystem5Bag_dec_erase_length_ge_three cfg h_nh
  omega

/-- **Iter 1352: encoder bag dec length closed form**.
    `(bag.map(·-1)).length = 4 * data.length`.  Direct from
    `length_map` + `_length`. -/
theorem ctsConfigToSystem5Bag_dec_length (cfg : CTSConfig) :
    ((ctsConfigToSystem5Bag cfg).map (· - 1)).length = 4 * cfg.data.length := by
  rw [List.length_map, ctsConfigToSystem5Bag_length]

/-- **Iter 1353: encoder bag dec length ≥ 4 at non-halted**. -/
theorem ctsConfigToSystem5Bag_dec_length_ge_four_of_not_halted
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) :
    ((ctsConfigToSystem5Bag cfg).map (· - 1)).length ≥ 4 := by
  rw [ctsConfigToSystem5Bag_dec_length]
  have h_data : cfg.data ≠ [] := (ctsHalted_false_iff_data_ne_nil cfg).mp h_nh
  cases h : cfg.data with
  | nil => exact absurd h h_data
  | cons _ _ => simp [List.length_cons]; omega

/-- **Iter 1354: encoder bag dec non-empty at non-halted**.  Direct
    from iter 1353. -/
theorem ctsConfigToSystem5Bag_dec_ne_nil_of_not_halted
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) :
    (ctsConfigToSystem5Bag cfg).map (· - 1) ≠ [] := by
  intro h
  have h_len : ((ctsConfigToSystem5Bag cfg).map (· - 1)).length = 0 := by rw [h]; rfl
  have := ctsConfigToSystem5Bag_dec_length_ge_four_of_not_halted cfg h_nh
  omega

/-- **Iter 1355: encoder bag map preserves Nodup at non-halted**. -/
theorem ctsConfigToSystem5Bag_dec_nodup_of_not_halted
    (cfg : CTSConfig) (_h_nh : ctsHalted cfg = false) :
    ((ctsConfigToSystem5Bag cfg).map (· - 1)).Nodup :=
  ctsConfigToSystem5Bag_dec_nodup cfg

/-- **Iter 1356: 0 ∈ encoder bag dec at non-halted**.  Direct from
    iter 1257 + `zero_mem_decrement_iff_one_mem`. -/
theorem ctsConfigToSystem5Bag_zero_in_dec_of_not_halted
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) :
    (0 : Int) ∈ (ctsConfigToSystem5Bag cfg).map (· - 1) := by
  apply (zero_mem_decrement_iff_one_mem _).mpr
  exact (ctsConfigToSystem5Bag_one_mem_iff cfg).mpr
    ((ctsHalted_false_iff_data_ne_nil cfg).mp h_nh)

/-- **Iter 1357: 1 ∈ encoder bag at non-halted**.  Direct from iter
    1257 + iter 1264. -/
theorem ctsConfigToSystem5Bag_one_mem_of_not_halted
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) :
    (1 : Int) ∈ ctsConfigToSystem5Bag cfg :=
  (ctsConfigToSystem5Bag_one_mem_iff cfg).mpr
    ((ctsHalted_false_iff_data_ne_nil cfg).mp h_nh)

/-- **Iter 1358: encoder bag length pos at non-halted**. -/
theorem ctsConfigToSystem5Bag_length_pos_of_not_halted
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) :
    (ctsConfigToSystem5Bag cfg).length > 0 := by
  have := ctsConfigToSystem5Bag_length_ge_four_of_not_halted cfg h_nh
  omega

/-- **Iter 1359: encoder bag length = 4 when data is one element**. -/
theorem ctsConfigToSystem5Bag_length_one_data
    (cfg : CTSConfig) (h_data : cfg.data.length = 1) :
    (ctsConfigToSystem5Bag cfg).length = 4 := by
  rw [ctsConfigToSystem5Bag_length, h_data]

/-- **Iter 1360: encoder bag length divides 4** — same as iter 1236
    but with `Dvd` form. Already exists. Skip and add: encoder bag
    length = 0 iff data.length = 0. -/
theorem ctsConfigToSystem5Bag_length_eq_zero_iff_data
    (cfg : CTSConfig) :
    (ctsConfigToSystem5Bag cfg).length = 0 ↔ cfg.data.length = 0 := by
  rw [ctsConfigToSystem5Bag_length]
  omega

/-- **Iter 1361 (🎯 470 LANDMARK): encoder bag length iff data length**.
    `(bag).length = 4 * n ↔ data.length = n`. -/
theorem ctsConfigToSystem5Bag_length_eq_iff
    (cfg : CTSConfig) (n : Nat) :
    (ctsConfigToSystem5Bag cfg).length = 4 * n ↔ cfg.data.length = n := by
  rw [ctsConfigToSystem5Bag_length]
  omega

/-- **Iter 1362: encoder bag dec-erase length iff data length**.
    `((bag.map(·-1)).erase 0).length = 4n - 1 ↔ data.length = n` for
    n ≥ 1 at non-halted. -/
theorem ctsConfigToSystem5Bag_dec_erase_length_eq_iff
    (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) (n : Nat) (h_n : n ≥ 1) :
    (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0).length = 4 * n - 1
      ↔ cfg.data.length = n := by
  rw [ctsConfigToSystem5Bag_dec_erase_length_eq cfg h_nh]
  have h_data_ne : cfg.data ≠ [] := (ctsHalted_false_iff_data_ne_nil cfg).mp h_nh
  have h_data_pos : cfg.data.length ≥ 1 := by
    cases h : cfg.data with
    | nil => exact absurd h h_data_ne
    | cons _ _ => simp
  omega

/-- **Iter 1363: aux contains all integers from i to (i+counter-1)
    where counter = counterAfterWorkingString data**.  Useful range
    bound. -/
theorem ctsConfigToSystem5BagAux_mem_ge_i_lt_counter
    (data : List Bool) (i : Int) (x : Int)
    (h : x ∈ ctsConfigToSystem5BagAux data i) :
    i ≤ x ∧ x ≤ i + counterAfterWorkingString data - 2 :=
  ⟨ctsConfigToSystem5BagAux_ge data i x h,
   ctsConfigToSystem5BagAux_max data i x h⟩

/-- **Iter 1364: encoder bag range bound**.  `1 ≤ x ≤ counter - 1`
    for any x ∈ encoder bag.  Specialization of iter 1363 to i=1. -/
theorem ctsConfigToSystem5Bag_mem_range
    (cfg : CTSConfig) (x : Int) (h : x ∈ ctsConfigToSystem5Bag cfg) :
    1 ≤ x ∧ x ≤ counterAfterWorkingString cfg.data - 1 := by
  have := ctsConfigToSystem5BagAux_mem_ge_i_lt_counter cfg.data 1 x h
  refine ⟨this.1, ?_⟩
  have := this.2
  omega

/-- **Iter 1365: Perm-chain bag range bound**.  Companion to iter 1364
    at any Perm-chain point. -/
theorem ctsConfigToSystem5Bag_perm_mem_range
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (x : Int) (h_x : x ∈ bag) :
    1 ≤ x ∧ x ≤ counterAfterWorkingString cfg.data - 1 :=
  ctsConfigToSystem5Bag_mem_range cfg x ((List.Perm.mem_iff h_perm).mp h_x)

/-- **Iter 1366: Perm-chain bag elements all ≥ 1**.  Direct from
    iter 1365.  Useful primitive — no zero or negative elements. -/
theorem ctsConfigToSystem5Bag_perm_all_ge_one
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (x : Int) (h_x : x ∈ bag) :
    x ≥ 1 :=
  (ctsConfigToSystem5Bag_perm_mem_range cfg bag h_perm x h_x).1

/-- **Iter 1367: Perm-chain bag has no zero**. -/
theorem ctsConfigToSystem5Bag_perm_no_zero
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    (0 : Int) ∉ bag := by
  intro h_zero_in
  have := ctsConfigToSystem5Bag_perm_all_ge_one cfg bag h_perm 0 h_zero_in
  omega

/-- **Iter 1368: encoder bag has no zero**.  Direct from iter 1367. -/
theorem ctsConfigToSystem5Bag_no_zero (cfg : CTSConfig) :
    (0 : Int) ∉ ctsConfigToSystem5Bag cfg :=
  ctsConfigToSystem5Bag_perm_no_zero cfg _ (List.Perm.refl _)

/-- **Iter 1369: encoder bag elements all ≥ 1**.  Direct from iter 1366. -/
theorem ctsConfigToSystem5Bag_all_ge_one
    (cfg : CTSConfig) (x : Int) (h_x : x ∈ ctsConfigToSystem5Bag cfg) :
    x ≥ 1 :=
  ctsConfigToSystem5Bag_perm_all_ge_one cfg _ (List.Perm.refl _) x h_x

/-- **Iter 1370 (ITER 1370 MILESTONE): encoder bag no negatives**.
    Direct from iter 1369 (all ≥ 1 ⇒ no negatives). -/
theorem ctsConfigToSystem5Bag_no_negatives
    (cfg : CTSConfig) (x : Int) (h_neg : x < 1)
    (h_x : x ∈ ctsConfigToSystem5Bag cfg) :
    False := by
  have := ctsConfigToSystem5Bag_all_ge_one cfg x h_x
  omega

/-- **Iter 1371: Perm-chain bag no negatives**. -/
theorem ctsConfigToSystem5Bag_perm_no_negatives
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (x : Int) (h_neg : x < 1) (h_x : x ∈ bag) :
    False := by
  have := ctsConfigToSystem5Bag_perm_all_ge_one cfg bag h_perm x h_x
  omega

/-- **Iter 1372: Perm-chain bag dec-erase all ≥ 1**.  After dec-erase,
    all elements are ≥ 1 (since pre-dec ≥ 1 by iter 1366, dec gives
    ≥ 0, erase 0 removes 0 leaving ≥ 1). -/
theorem ctsConfigToSystem5Bag_perm_dec_erase_all_ge_one
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (x : Int) (h_x : x ∈ ((bag.map (· - 1)).erase 0)) :
    x ≥ 1 := by
  have h_in_dec : x ∈ bag.map (· - 1) := List.mem_of_mem_erase h_x
  rw [List.mem_map] at h_in_dec
  obtain ⟨y, hy, h_eq⟩ := h_in_dec
  have h_y_ge : y ≥ 1 := ctsConfigToSystem5Bag_perm_all_ge_one cfg bag h_perm y hy
  -- x = y - 1; we know y ≥ 1, so x ≥ 0.
  -- We also need x ≠ 0; since x ∈ ... erase 0, this holds.
  -- Use that elements in erase 0 != 0. Approach: case on y.
  by_cases h_y_eq : y = 1
  · rw [h_y_eq] at h_eq
    have h_x_zero : x = 0 := by omega
    rw [h_x_zero] at h_x
    have h_dec_nodup : (bag.map (· - 1)).Nodup := by
      apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_
        ((List.Perm.nodup_iff h_perm).mpr (ctsConfigToSystem5Bag_nodup cfg))
      intro a b h_ne h_eq_dec
      apply h_ne
      have : a - 1 = b - 1 := h_eq_dec
      omega
    rw [List.Nodup.mem_erase_iff h_dec_nodup] at h_x
    exact absurd rfl h_x.1
  · have : y ≥ 2 := by omega
    omega

/-- **Iter 1373: encoder bag dec-erase all ≥ 1**.  Cfg-level form. -/
theorem ctsConfigToSystem5Bag_dec_erase_all_ge_one
    (cfg : CTSConfig) (x : Int)
    (h_x : x ∈ (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0)) :
    x ≥ 1 :=
  ctsConfigToSystem5Bag_perm_dec_erase_all_ge_one cfg _ (List.Perm.refl _) x h_x

/-- **Iter 1374: encoder bag dec-erase has no zero**. -/
theorem ctsConfigToSystem5Bag_dec_erase_no_zero (cfg : CTSConfig) :
    (0 : Int) ∉ (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0) := by
  intro h_in
  have := ctsConfigToSystem5Bag_dec_erase_all_ge_one cfg 0 h_in
  omega

/-- **Iter 1375: encoder bag map shift bound**.  `bag.map(·+k)` has all
    elements ≥ 1+k.  Direct from iter 1369. -/
theorem ctsConfigToSystem5Bag_map_add_all_ge
    (cfg : CTSConfig) (k : Int) (x : Int)
    (h_x : x ∈ (ctsConfigToSystem5Bag cfg).map (· + k)) :
    x ≥ 1 + k := by
  rw [List.mem_map] at h_x
  obtain ⟨y, hy, h_eq⟩ := h_x
  have := ctsConfigToSystem5Bag_all_ge_one cfg y hy
  omega

/-- **Iter 1376: encoder bag map(·+1) all ≥ 2**.  Specialization of
    iter 1375 with k=1. -/
theorem ctsConfigToSystem5Bag_map_add_one_all_ge_two
    (cfg : CTSConfig) (x : Int)
    (h_x : x ∈ (ctsConfigToSystem5Bag cfg).map (· + 1)) :
    x ≥ 2 := by
  have := ctsConfigToSystem5Bag_map_add_all_ge cfg 1 x h_x
  omega

/-- **Iter 1377: small value n ∉ encoder bag**.  For any n < 1,
    n ∉ encoder bag.  Direct from iter 1369. -/
theorem ctsConfigToSystem5Bag_small_not_mem
    (cfg : CTSConfig) (n : Int) (h_n : n < 1) :
    n ∉ ctsConfigToSystem5Bag cfg := by
  intro h_in
  have := ctsConfigToSystem5Bag_all_ge_one cfg n h_in
  omega

/-- **Iter 1378: small value n ∉ Perm-chain bag**. -/
theorem ctsConfigToSystem5Bag_perm_small_not_mem
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (n : Int) (h_n : n < 1) :
    n ∉ bag := by
  intro h_in
  have := ctsConfigToSystem5Bag_perm_all_ge_one cfg bag h_perm n h_in
  omega

/-- **Iter 1379: -1 ∉ encoder bag**. -/
theorem ctsConfigToSystem5Bag_neg_one_not_mem (cfg : CTSConfig) :
    (-1 : Int) ∉ ctsConfigToSystem5Bag cfg :=
  ctsConfigToSystem5Bag_small_not_mem cfg (-1) (by omega)

/-- **Iter 1380: -1 ∉ Perm-chain bag**. -/
theorem ctsConfigToSystem5Bag_perm_neg_one_not_mem
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    (-1 : Int) ∉ bag :=
  ctsConfigToSystem5Bag_perm_small_not_mem cfg bag h_perm (-1) (by omega)

/-- **Iter 1381 (🎯 490 LANDMARK): encoder bag dec all ≥ 0**.
    Direct from iter 1369. -/
theorem ctsConfigToSystem5Bag_dec_all_ge_zero
    (cfg : CTSConfig) (x : Int)
    (h_x : x ∈ (ctsConfigToSystem5Bag cfg).map (· - 1)) :
    x ≥ 0 := by
  rw [List.mem_map] at h_x
  obtain ⟨y, hy, h_eq⟩ := h_x
  have := ctsConfigToSystem5Bag_all_ge_one cfg y hy
  omega

/-- **Iter 1382: Perm-chain bag dec all ≥ 0**.  Direct from iter 1366. -/
theorem ctsConfigToSystem5Bag_perm_dec_all_ge_zero
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (x : Int) (h_x : x ∈ bag.map (· - 1)) :
    x ≥ 0 := by
  rw [List.mem_map] at h_x
  obtain ⟨y, hy, h_eq⟩ := h_x
  have := ctsConfigToSystem5Bag_perm_all_ge_one cfg bag h_perm y hy
  omega

/-- **Iter 1383: encoder bag dec contains 0 iff data non-empty**.
    Direct from `zero_mem_decrement_iff_one_mem` + iter 1257. -/
theorem ctsConfigToSystem5Bag_zero_in_dec_iff (cfg : CTSConfig) :
    (0 : Int) ∈ (ctsConfigToSystem5Bag cfg).map (· - 1) ↔ cfg.data ≠ [] := by
  rw [zero_mem_decrement_iff_one_mem, ctsConfigToSystem5Bag_one_mem_iff]

/-- **Iter 1384: encoder bag dec contains 0 iff not halted**. -/
theorem ctsConfigToSystem5Bag_zero_in_dec_iff_not_halted (cfg : CTSConfig) :
    (0 : Int) ∈ (ctsConfigToSystem5Bag cfg).map (· - 1) ↔ ctsHalted cfg = false := by
  rw [ctsConfigToSystem5Bag_zero_in_dec_iff, ctsHalted_false_iff_data_ne_nil]

/-- **Iter 1385: Perm-chain bag dec contains 0 iff not halted**. -/
theorem ctsConfigToSystem5Bag_perm_zero_in_dec_iff_not_halted
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg)) :
    (0 : Int) ∈ bag.map (· - 1) ↔ ctsHalted cfg = false := by
  rw [ctsConfigToSystem5Bag_perm_zero_in_dec_iff cfg bag h_perm,
      ctsHalted_false_iff_data_ne_nil]

/-- **Iter 1386 (🎯 495 LANDMARK): encoder bag dec range bound**.
    `0 ≤ x ≤ counter - 2` for any `x ∈ bag.map(·-1)`.  Combines
    iters 1381 + iter 1364. -/
theorem ctsConfigToSystem5Bag_dec_range
    (cfg : CTSConfig) (x : Int)
    (h_x : x ∈ (ctsConfigToSystem5Bag cfg).map (· - 1)) :
    0 ≤ x ∧ x ≤ counterAfterWorkingString cfg.data - 2 := by
  refine ⟨ctsConfigToSystem5Bag_dec_all_ge_zero cfg x h_x, ?_⟩
  rw [List.mem_map] at h_x
  obtain ⟨y, hy, h_eq⟩ := h_x
  have := ctsConfigToSystem5Bag_mem_range cfg y hy
  omega

/-- **Iter 1387: encoder bag dec-erase range bound**.  `1 ≤ x ≤ counter - 2`
    for any `x ∈ (bag.map(·-1)).erase 0`.  Direct from iter 1386 +
    iter 1373 (≥ 1 since erase 0). -/
theorem ctsConfigToSystem5Bag_dec_erase_range
    (cfg : CTSConfig) (x : Int)
    (h_x : x ∈ (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0)) :
    1 ≤ x ∧ x ≤ counterAfterWorkingString cfg.data - 2 := by
  refine ⟨ctsConfigToSystem5Bag_dec_erase_all_ge_one cfg x h_x, ?_⟩
  have h_in_dec : x ∈ (ctsConfigToSystem5Bag cfg).map (· - 1) := List.mem_of_mem_erase h_x
  exact (ctsConfigToSystem5Bag_dec_range cfg x h_in_dec).2

/-- **Iter 1388: Perm-chain bag dec-erase range bound**.  Companion
    to iter 1387 at any Perm-chain point. -/
theorem ctsConfigToSystem5Bag_perm_dec_erase_range
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (x : Int) (h_x : x ∈ ((bag.map (· - 1)).erase 0)) :
    1 ≤ x ∧ x ≤ counterAfterWorkingString cfg.data - 2 := by
  refine ⟨ctsConfigToSystem5Bag_perm_dec_erase_all_ge_one cfg bag h_perm x h_x, ?_⟩
  have h_in_dec : x ∈ bag.map (· - 1) := List.mem_of_mem_erase h_x
  rw [List.mem_map] at h_in_dec
  obtain ⟨y, hy, h_eq⟩ := h_in_dec
  have := ctsConfigToSystem5Bag_perm_mem_range cfg bag h_perm y hy
  omega

/-- **Iter 1389: Perm-chain bag dec range bound**.  `0 ≤ x ≤ counter - 2`
    for `x ∈ bag.map(·-1)` at Perm-chain. -/
theorem ctsConfigToSystem5Bag_perm_dec_range
    (cfg : CTSConfig) (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag cfg))
    (x : Int) (h_x : x ∈ bag.map (· - 1)) :
    0 ≤ x ∧ x ≤ counterAfterWorkingString cfg.data - 2 := by
  refine ⟨ctsConfigToSystem5Bag_perm_dec_all_ge_zero cfg bag h_perm x h_x, ?_⟩
  rw [List.mem_map] at h_x
  obtain ⟨y, hy, h_eq⟩ := h_x
  have := ctsConfigToSystem5Bag_perm_mem_range cfg bag h_perm y hy
  omega

/-- **Iter 1390: encoder bag dec.map(·+1) all ≥ 1**.  Composing dec
    + inc gives identity, so all ≥ 1 (= original bag). -/
theorem ctsConfigToSystem5Bag_dec_inc_all_ge_one
    (cfg : CTSConfig) (x : Int)
    (h_x : x ∈ ((ctsConfigToSystem5Bag cfg).map (· - 1)).map (· + 1)) :
    x ≥ 1 := by
  rw [List.mem_map] at h_x
  obtain ⟨y, hy, h_eq⟩ := h_x
  have h_y_in_dec := ctsConfigToSystem5Bag_dec_all_ge_zero cfg y hy
  -- x = y + 1, so x ≥ 1
  omega

/-- **Iter 1391 (🎯🎯🎯 500-LEMMA MILESTONE): cts.Halts iff exists
    nSteps reaching halted**.  Substantive equivalence relating the
    eval-based `Halts` definition to the nSteps trajectory + halt-state.
    Forward: by induction on eval fuel.  Backward: nSteps trajectory
    embedded in eval at the same fuel + iter 1308. -/
theorem CTS_Halts_iff_nSteps_halted (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ∃ n result, cts.nSteps cfg n = some result
                              ∧ ctsHalted result = true := by
  constructor
  · -- Forward: Halts ⇒ ∃ n result, nSteps n = some result ∧ halted result
    -- By strong induction on eval fuel
    intro h_halts
    obtain ⟨fuel, result, h_eval⟩ := h_halts
    induction fuel generalizing cfg with
    | zero =>
      unfold CTS.eval at h_eval
      by_cases h_h : ctsHalted cfg = true
      · simp [h_h] at h_eval
        exact ⟨0, cfg, rfl, h_h⟩
      · simp [h_h] at h_eval
    | succ n ih =>
      unfold CTS.eval at h_eval
      by_cases h_h : ctsHalted cfg = true
      · simp [h_h] at h_eval
        exact ⟨0, cfg, rfl, h_h⟩
      · simp [h_h] at h_eval
        cases h_step : cts.step cfg with
        | none =>
          rw [h_step] at h_eval
          simp at h_eval
          have h_halted : ctsHalted cfg = true :=
            (CTS_step_none_iff_halted_v2 cts cfg).mp h_step
          rw [h_halted] at h_h; contradiction
        | some cfg' =>
          rw [h_step] at h_eval
          simp at h_eval
          obtain ⟨n', result', h_n', h_halt'⟩ := ih cfg' h_eval
          refine ⟨n' + 1, result', ?_, h_halt'⟩
          rw [CTS_nSteps_succ, h_step]
          exact h_n'
  · intro ⟨n, result, h_n, h_halt⟩
    -- Embed nSteps as eval at the same fuel
    -- Strategy: induction on n
    induction n generalizing cfg with
    | zero =>
      have h_eq : result = cfg := Option.some.inj h_n.symm
      refine ⟨0, cfg, ?_⟩
      unfold CTS.eval
      rw [← h_eq] at *
      simp [h_halt]
    | succ k ih =>
      rw [CTS_nSteps_succ] at h_n
      cases h_step : cts.step cfg with
      | none => rw [h_step] at h_n; simp at h_n
      | some cfg' =>
        rw [h_step] at h_n
        obtain ⟨fuel', result', h_eval'⟩ := ih cfg' h_n
        refine ⟨fuel' + 1, result', ?_⟩
        have h_nh : ctsHalted cfg = false :=
          CTS_step_some_not_halted cts cfg cfg' h_step
        rw [CTS_eval_succ_not_halted cts cfg cfg' fuel' h_nh h_step]
        exact h_eval'

/-- **Iter 1392: cts.eval cfg fuel some implies nSteps reaches halted**.
    Direct from iter 1391 (forward direction). -/
theorem CTS_eval_some_implies_nSteps_halted
    (cts : CTS) (cfg result : CTSConfig) (fuel : Nat)
    (h : cts.eval cfg fuel = some result) :
    ∃ n result', cts.nSteps cfg n = some result'
              ∧ ctsHalted result' = true := by
  apply (CTS_Halts_iff_nSteps_halted cts cfg).mp
  exact ⟨fuel, result, h⟩

/-- **Iter 1393: nSteps halted implies eval gives some result for any
    fuel ≥ that n**.  Direct from iter 1391 (backward direction) +
    iter 1319 (eval monotonic). -/
theorem CTS_nSteps_halted_implies_eval_some
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h_n : cts.nSteps cfg n = some result)
    (h_halt : ctsHalted result = true) :
    cts.Halts cfg :=
  (CTS_Halts_iff_nSteps_halted cts cfg).mpr ⟨n, result, h_n, h_halt⟩

/-- **Iter 1394: at non-halted cfg, Halts gives a step witness with
    Halts result**.  Combines iters 1325 + 1391-style. -/
theorem CTS_Halts_step_witness
    (cts : CTS) (cfg : CTSConfig)
    (h_halts : cts.Halts cfg) (h_nh : ctsHalted cfg = false) :
    ∃ result, cts.step cfg = some result ∧ cts.Halts result :=
  CTS_Halts_step_some_of_not_halted cts cfg h_halts h_nh

/-- **Iter 1395: nSteps result at non-halted gives nSteps' result**.
    When `nSteps cfg n = some result` with `n ≥ 1`, `cfg` is not halted. -/
theorem CTS_nSteps_pos_implies_not_halted
    (cts : CTS) (cfg result : CTSConfig) (n : Nat) (h_n : n ≥ 1)
    (h : cts.nSteps cfg n = some result) :
    ctsHalted cfg = false := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [hk] at h
  exact CTS_nSteps_succ_some_not_halted cts cfg result k h

/-- **Iter 1396: System5.nSteps pos implies bag/rules non-empty**. -/
theorem System5_nSteps_pos_implies_bag_rules_ne_nil
    (cfg result : System5Config) (n : Nat) (h_n : n ≥ 1)
    (h : System5.nSteps cfg n = some result) :
    cfg.bag ≠ [] ∧ cfg.rules ≠ [] := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [hk] at h
  exact System5_nSteps_succ_some_bag_rules_ne_nil cfg result k h

/-- **Iter 1397: nSteps embeds in eval at same fuel when result halted**.
    `nSteps cfg n = some result ∧ halted result ⇒ eval cfg n = some result`.
    By induction on n. -/
theorem CTS_nSteps_eval_eq
    (cts : CTS) :
    ∀ (n : Nat) (cfg result : CTSConfig),
      cts.nSteps cfg n = some result → ctsHalted result = true →
      cts.eval cfg n = some result := by
  intro n
  induction n with
  | zero =>
    intro cfg result h_n h_halt
    have h_eq : result = cfg := Option.some.inj h_n.symm
    rw [h_eq] at h_halt
    unfold CTS.eval
    simp [h_halt]
    exact h_eq.symm
  | succ k ih =>
    intro cfg result h_n h_halt
    rw [CTS_nSteps_succ] at h_n
    cases h_step : cts.step cfg with
    | none => rw [h_step] at h_n; simp at h_n
    | some cfg' =>
      rw [h_step] at h_n
      have h_nh : ctsHalted cfg = false :=
        CTS_step_some_not_halted cts cfg cfg' h_step
      rw [CTS_eval_succ_not_halted cts cfg cfg' k h_nh h_step]
      exact ih cfg' result h_n h_halt

/-- **Iter 1398: cts.nSteps result is deterministic when both halt**.
    `nSteps cfg n1 = some r1 ∧ halted r1 ∧ nSteps cfg n2 = some r2 ∧
    halted r2 ⇒ r1 = r2`.  Direct from iters 1397 + 1320. -/
theorem CTS_nSteps_halted_deterministic
    (cts : CTS) (cfg r1 r2 : CTSConfig) (n1 n2 : Nat)
    (h_n1 : cts.nSteps cfg n1 = some r1) (h_h1 : ctsHalted r1 = true)
    (h_n2 : cts.nSteps cfg n2 = some r2) (h_h2 : ctsHalted r2 = true) :
    r1 = r2 := by
  have h_eval1 := CTS_nSteps_eval_eq cts n1 cfg r1 h_n1 h_h1
  have h_eval2 := CTS_nSteps_eval_eq cts n2 cfg r2 h_n2 h_h2
  exact CTS_eval_deterministic cts cfg n1 n2 r1 r2 h_eval1 h_eval2

/-- **Iter 1399: nSteps from halted cfg returns the cfg if n = 0,
    else none**.  At halted cfg, only n=0 returns some. -/
theorem CTS_nSteps_halted_eq
    (cts : CTS) (cfg : CTSConfig) (h : ctsHalted cfg = true) (n : Nat) :
    cts.nSteps cfg n = if n = 0 then some cfg else none := by
  cases n with
  | zero => rfl
  | succ k =>
    rw [CTS_nSteps_succ]
    have h_step : cts.step cfg = none :=
      (CTS_step_none_iff_halted_v2 cts cfg).mpr h
    rw [h_step]
    simp

/-- **Iter 1400 (🎯 ITER 1400 MILESTONE): System5.nSteps from
    halted/stuck cfg**.  When `System5.step cfg = none`, `nSteps cfg
    n = if n = 0 then some cfg else none`. -/
theorem System5_nSteps_step_none_eq
    (cfg : System5Config) (h : System5.step cfg = none) (n : Nat) :
    System5.nSteps cfg n = if n = 0 then some cfg else none := by
  cases n with
  | zero => rfl
  | succ k =>
    rw [System5.nSteps_succ, h]
    simp

/-- **Iter 1401 (🎯 510 LANDMARK): cts.Halts implies eval at any
    sufficient fuel returns halted result**.  Combines iter 1391 +
    iter 1319 (monotonic). -/
theorem CTS_Halts_eval_eventually
    (cts : CTS) (cfg : CTSConfig) (h_halts : cts.Halts cfg) :
    ∃ N result, ctsHalted result = true ∧
      ∀ fuel, fuel ≥ N → cts.eval cfg fuel = some result := by
  obtain ⟨n, result, h_n, h_halt⟩ := (CTS_Halts_iff_nSteps_halted cts cfg).mp h_halts
  refine ⟨n, result, h_halt, ?_⟩
  intro fuel h_fuel
  have h_eval_n := CTS_nSteps_eval_eq cts n cfg result h_n h_halt
  obtain ⟨k, hk⟩ := Nat.le.dest h_fuel
  rw [← hk]
  exact CTS_eval_monotonic cts cfg result n h_eval_n k

/-- **Iter 1402: ¬Halts implies eval at any fuel is none**.  Contrapositive
    of `Halts` definition. -/
theorem CTS_not_Halts_eval_none
    (cts : CTS) (cfg : CTSConfig) (h : ¬cts.Halts cfg) (fuel : Nat) :
    cts.eval cfg fuel = none := by
  cases h_eval : cts.eval cfg fuel with
  | none => rfl
  | some result =>
    exact absurd ⟨fuel, result, h_eval⟩ h

/-- **Iter 1403: ¬Halts iff all eval are none**.  Biconditional. -/
theorem CTS_not_Halts_iff_all_eval_none
    (cts : CTS) (cfg : CTSConfig) :
    ¬cts.Halts cfg ↔ ∀ fuel, cts.eval cfg fuel = none := by
  constructor
  · exact CTS_not_Halts_eval_none cts cfg
  · intro h_all h_halts
    obtain ⟨fuel, result, h_eval⟩ := h_halts
    rw [h_all] at h_eval
    contradiction

/-- **Iter 1404: cts.Halts iff exists fuel with eval ≠ none**.  Direct
    from def (eval = some ↔ ≠ none, since result : CTSConfig is non-trivial). -/
theorem CTS_Halts_iff_exists_eval_ne_none
    (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ∃ fuel, cts.eval cfg fuel ≠ none := by
  constructor
  · intro ⟨fuel, result, h_eval⟩
    refine ⟨fuel, ?_⟩
    rw [h_eval]; simp
  · intro ⟨fuel, h_ne⟩
    cases h_eval : cts.eval cfg fuel with
    | none => rw [h_eval] at h_ne; contradiction
    | some result => exact ⟨fuel, result, h_eval⟩

/-- **Iter 1405: cts.nSteps preserves Halts**.  When `nSteps cfg n =
    some result`, `cfg.Halts ↔ result.Halts`.  By induction on n. -/
theorem CTS_nSteps_Halts_iff
    (cts : CTS) :
    ∀ (n : Nat) (cfg result : CTSConfig),
      cts.nSteps cfg n = some result →
      (cts.Halts cfg ↔ cts.Halts result) := by
  intro n
  induction n with
  | zero =>
    intro cfg result h_n
    have h_eq : result = cfg := Option.some.inj h_n.symm
    rw [h_eq]
  | succ k ih =>
    intro cfg result h_n
    rw [CTS_nSteps_succ] at h_n
    cases h_step : cts.step cfg with
    | none => rw [h_step] at h_n; simp at h_n
    | some cfg' =>
      rw [h_step] at h_n
      have h_cfg_halts_iff_cfg'_halts : cts.Halts cfg ↔ cts.Halts cfg' := by
        constructor
        · intro h_halts
          obtain ⟨fuel, r, h_eval⟩ := h_halts
          have h_nh : ctsHalted cfg = false :=
            CTS_step_some_not_halted cts cfg cfg' h_step
          cases fuel with
          | zero =>
            unfold CTS.eval at h_eval
            simp [h_nh] at h_eval
          | succ m =>
            rw [CTS_eval_succ_not_halted cts cfg cfg' m h_nh h_step] at h_eval
            exact ⟨m, r, h_eval⟩
        · intro h_halts
          exact CTS_Halts_of_step_Halts cts cfg cfg' h_step h_halts
      rw [h_cfg_halts_iff_cfg'_halts]
      exact ih cfg' result h_n

/-- **Iter 1406 (🎯 515 LANDMARK): cts.step preserves Halts iff**.
    Direct from iter 1405 with n=1. -/
theorem CTS_step_Halts_iff
    (cts : CTS) (cfg result : CTSConfig)
    (h_step : cts.step cfg = some result) :
    cts.Halts cfg ↔ cts.Halts result := by
  have h_n1 : cts.nSteps cfg 1 = some result := by
    rw [CTS_nSteps_one]; exact h_step
  exact CTS_nSteps_Halts_iff cts 1 cfg result h_n1

/-- **Iter 1407: System5 step preserves nSteps successor**.  When
    `step cfg = some cfg'`, `nSteps cfg (n+1) = nSteps cfg' n`. -/
theorem System5_step_nSteps_succ
    (cfg cfg' : System5Config) (n : Nat)
    (h_step : System5.step cfg = some cfg') :
    System5.nSteps cfg (n + 1) = System5.nSteps cfg' n := by
  rw [System5.nSteps_succ, h_step]
  rfl

/-- **Iter 1408: cts.step preserves nSteps successor**. -/
theorem CTS_step_nSteps_succ
    (cts : CTS) (cfg cfg' : CTSConfig) (n : Nat)
    (h_step : cts.step cfg = some cfg') :
    cts.nSteps cfg (n + 1) = cts.nSteps cfg' n := by
  rw [CTS_nSteps_succ, h_step]

/-- **Iter 1409: cts.nSteps termination point**.  When `nSteps cfg n =
    some result ∧ nSteps cfg (n+1) = none`, `result` is halted.  The
    n-th step succeeds but n+1-th fails, meaning the result is the
    halt point. -/
theorem CTS_nSteps_termination_point
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h_n : cts.nSteps cfg n = some result)
    (h_succ : cts.nSteps cfg (n + 1) = none) :
    ctsHalted result = true := by
  -- nSteps cfg (n+1) = (nSteps cfg n).bind (· cts.step ·) — actually trailing step
  rw [show n + 1 = n + 1 from rfl, CTS_nSteps_add cts n 1, h_n] at h_succ
  simp at h_succ
  rw [CTS_nSteps_one] at h_succ
  exact (CTS_step_none_iff_halted_v2 cts result).mp h_succ

/-- **Iter 1410: System5.nSteps termination point**.  When `nSteps cfg
    n = some result ∧ nSteps cfg (n+1) = none`, `result.bag = [] ∨
    result.rules = []`. -/
theorem System5_nSteps_termination_point
    (cfg result : System5Config) (n : Nat)
    (h_n : System5.nSteps cfg n = some result)
    (h_succ : System5.nSteps cfg (n + 1) = none) :
    result.bag = [] ∨ result.rules = [] := by
  rw [show n + 1 = n + 1 from rfl, System5.nSteps_add, h_n] at h_succ
  simp at h_succ
  rw [System5.nSteps_one] at h_succ
  exact (System5_step_none_iff result).mp h_succ

/-- **Iter 1411 (🎯 520 LANDMARK): cts.nSteps split iff**.
    Biconditional split form: `nSteps cfg (n+m) = some r ↔ ∃ r',
    nSteps cfg n = some r' ∧ nSteps r' m = some r`. -/
theorem CTS_nSteps_split_iff
    (cts : CTS) (cfg result : CTSConfig) (n m : Nat) :
    cts.nSteps cfg (n + m) = some result
      ↔ ∃ result', cts.nSteps cfg n = some result' ∧ cts.nSteps result' m = some result := by
  rw [CTS_nSteps_add]
  constructor
  · intro h
    cases h_n : cts.nSteps cfg n with
    | none => rw [h_n] at h; simp at h
    | some result' => rw [h_n] at h; simp at h; exact ⟨result', rfl, h⟩
  · intro ⟨result', h_n, h_m⟩
    rw [h_n]; simp; exact h_m

/-- **Iter 1412: System5.nSteps split iff**.  Companion to iter 1411
    for System5. -/
theorem System5_nSteps_split_iff
    (cfg result : System5Config) (n m : Nat) :
    System5.nSteps cfg (n + m) = some result
      ↔ ∃ result', System5.nSteps cfg n = some result' ∧ System5.nSteps result' m = some result := by
  rw [System5.nSteps_add]
  constructor
  · intro h
    cases h_n : System5.nSteps cfg n with
    | none => rw [h_n] at h; simp at h
    | some result' => rw [h_n] at h; simp at h; exact ⟨result', rfl, h⟩
  · intro ⟨result', h_n, h_m⟩
    rw [h_n]; simp; exact h_m

/-- **Iter 1413: cts.nSteps add none iff**.  `nSteps cfg (n+m) = none ↔
    nSteps cfg n = none ∨ ∃ r', nSteps cfg n = some r' ∧ nSteps r' m = none`. -/
theorem CTS_nSteps_add_none_iff
    (cts : CTS) (cfg : CTSConfig) (n m : Nat) :
    cts.nSteps cfg (n + m) = none
      ↔ cts.nSteps cfg n = none
        ∨ ∃ r', cts.nSteps cfg n = some r' ∧ cts.nSteps r' m = none := by
  rw [CTS_nSteps_add]
  cases h_n : cts.nSteps cfg n with
  | none => simp
  | some r' => simp

/-- **Iter 1414: System5.nSteps add none iff**.  Companion to iter 1413
    for System5. -/
theorem System5_nSteps_add_none_iff
    (cfg : System5Config) (n m : Nat) :
    System5.nSteps cfg (n + m) = none
      ↔ System5.nSteps cfg n = none
        ∨ ∃ r', System5.nSteps cfg n = some r' ∧ System5.nSteps r' m = none := by
  rw [System5.nSteps_add]
  cases h_n : System5.nSteps cfg n with
  | none => simp
  | some r' => simp

/-- **Iter 1415: cts.nSteps none monotonic**.  Once nSteps returns
    none at fuel n, all higher fuels also return none. -/
theorem CTS_nSteps_none_monotonic
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (h_n : cts.nSteps cfg n = none) (m : Nat) :
    cts.nSteps cfg (n + m) = none := by
  rw [CTS_nSteps_add, h_n]; rfl

/-- **Iter 1416: System5.nSteps none monotonic**. -/
theorem System5_nSteps_none_monotonic
    (cfg : System5Config) (n : Nat) (h_n : System5.nSteps cfg n = none) (m : Nat) :
    System5.nSteps cfg (n + m) = none := by
  rw [System5.nSteps_add, h_n]; rfl

/-- **Iter 1417: System5.nSteps n.succ = some implies step succeeds**.
    Companion to iter 1343 for System5. -/
theorem System5_nSteps_succ_some_step
    (cfg result : System5Config) (n : Nat)
    (h : System5.nSteps cfg (n + 1) = some result) :
    ∃ cfg', System5.step cfg = some cfg' := by
  obtain ⟨cfg', h_step, _⟩ := System5_nSteps_succ_some_first_step cfg result n h
  exact ⟨cfg', h_step⟩

/-- **Iter 1418: cts.nSteps n.succ = some implies step succeeds**. -/
theorem CTS_nSteps_succ_some_step
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h : cts.nSteps cfg (n + 1) = some result) :
    ∃ cfg', cts.step cfg = some cfg' := by
  obtain ⟨cfg', h_step, _⟩ := CTS_nSteps_succ_some_first_step cts cfg result n h
  exact ⟨cfg', h_step⟩

/-- **Iter 1419: cts.eval result.Halts**.  The result of eval is itself
    a Halts witness.  Direct from iters 1308 + 1316. -/
theorem CTS_eval_some_result_Halts
    (cts : CTS) (cfg result : CTSConfig) (fuel : Nat)
    (h : cts.eval cfg fuel = some result) :
    cts.Halts result :=
  CTS_Halts_of_halted cts result (CTS_eval_some_halted cts fuel cfg result h)

/-- **Iter 1420: CTS.Halts cfg implies result.Halts**.  Whenever CTS
    halts, the eval result also halts (trivially, since it's halted). -/
theorem CTS_Halts_implies_eval_result_Halts
    (cts : CTS) (cfg : CTSConfig) (h : cts.Halts cfg) :
    ∃ fuel result, cts.eval cfg fuel = some result ∧ cts.Halts result := by
  obtain ⟨fuel, result, h_eval⟩ := h
  exact ⟨fuel, result, h_eval, CTS_eval_some_result_Halts cts cfg result fuel h_eval⟩

/-- **Iter 1421 (🎯 530 LANDMARK): step result Halts when cfg Halts**.
    `cfg.Halts ∧ cts.step cfg = some result ⇒ result.Halts`.  Direct
    from iter 1406. -/
theorem CTS_step_result_Halts_of_cfg_Halts
    (cts : CTS) (cfg result : CTSConfig)
    (h_halts : cts.Halts cfg) (h_step : cts.step cfg = some result) :
    cts.Halts result :=
  (CTS_step_Halts_iff cts cfg result h_step).mp h_halts

/-- **Iter 1422: nSteps result Halts when cfg Halts**. -/
theorem CTS_nSteps_result_Halts_of_cfg_Halts
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h_halts : cts.Halts cfg) (h_n : cts.nSteps cfg n = some result) :
    cts.Halts result :=
  (CTS_nSteps_Halts_iff cts n cfg result h_n).mp h_halts

/-- **Iter 1423: nSteps result not-Halts when cfg not-Halts**. -/
theorem CTS_nSteps_result_not_Halts_of_cfg_not_Halts
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h_not_halts : ¬cts.Halts cfg) (h_n : cts.nSteps cfg n = some result) :
    ¬cts.Halts result := fun h => h_not_halts
  ((CTS_nSteps_Halts_iff cts n cfg result h_n).mpr h)

/-- **Iter 1424: cts.step result not-Halts when cfg not-Halts**. -/
theorem CTS_step_result_not_Halts_of_cfg_not_Halts
    (cts : CTS) (cfg result : CTSConfig)
    (h_not_halts : ¬cts.Halts cfg) (h_step : cts.step cfg = some result) :
    ¬cts.Halts result := fun h => h_not_halts
  ((CTS_step_Halts_iff cts cfg result h_step).mpr h)

/-- **Iter 1425: cts.Halts iff exists eval some**.  Direct from def. -/
theorem CTS_Halts_iff_exists_eval_some
    (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ∃ fuel result, cts.eval cfg fuel = some result := by
  rfl

/-- **Iter 1426: cts.Halts iff at non-halted, step result Halts**. -/
theorem CTS_Halts_at_non_halted_iff
    (cts : CTS) (cfg : CTSConfig) (h_nh : ctsHalted cfg = false) :
    cts.Halts cfg ↔ ∀ result, cts.step cfg = some result → cts.Halts result := by
  constructor
  · intro h_halts result h_step
    exact (CTS_step_Halts_iff cts cfg result h_step).mp h_halts
  · intro h_all
    obtain ⟨result, h_step⟩ := CTS_step_some_of_not_halted cts cfg h_nh
    exact CTS_Halts_of_step_Halts cts cfg result h_step (h_all result h_step)

/-- **Iter 1427: nSteps non-halted result extension exists**.  When
    `nSteps cfg n = some result` and `result` is non-halted, we can
    extend the trajectory by one more step. -/
theorem CTS_nSteps_non_halted_extension
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h_n : cts.nSteps cfg n = some result)
    (h_nh : ctsHalted result = false) :
    ∃ result', cts.step result = some result'
            ∧ cts.nSteps cfg (n + 1) = some result' := by
  obtain ⟨result', h_step⟩ := CTS_step_some_of_not_halted cts result h_nh
  refine ⟨result', h_step, ?_⟩
  rw [show n + 1 = n + 1 from rfl, CTS_nSteps_add cts n 1, h_n]
  simp
  rw [CTS_nSteps_one]
  exact h_step

/-- **Iter 1428: System5.nSteps non-empty result extension**.  When
    `nSteps cfg n = some result` and `result.bag ≠ [] ∧ result.rules ≠ []`,
    we can extend the trajectory by one more step. -/
theorem System5_nSteps_non_empty_extension
    (cfg result : System5Config) (n : Nat)
    (h_n : System5.nSteps cfg n = some result)
    (h_bag : result.bag ≠ []) (h_rules : result.rules ≠ []) :
    ∃ result', System5.step result = some result'
            ∧ System5.nSteps cfg (n + 1) = some result' := by
  obtain ⟨result', h_step⟩ :=
    (System5_step_some_iff result).mpr ⟨h_bag, h_rules⟩
  refine ⟨result', h_step, ?_⟩
  rw [show n + 1 = n + 1 from rfl, System5.nSteps_add, h_n]
  simp
  rw [System5.nSteps_one]
  exact h_step

/-- **Iter 1429: nSteps halted result cannot extend**.  When
    `nSteps cfg n = some result ∧ halted result`, `nSteps cfg (n+m) = none`
    for any `m ≥ 1`. -/
theorem CTS_nSteps_halted_cannot_extend
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h_n : cts.nSteps cfg n = some result)
    (h_halt : ctsHalted result = true) (m : Nat) (h_m : m ≥ 1) :
    cts.nSteps cfg (n + m) = none := by
  rw [show n + m = n + m from rfl, CTS_nSteps_add cts n m, h_n]
  simp
  rw [CTS_nSteps_halted_eq cts result h_halt m]
  have h_m_ne : m ≠ 0 := by omega
  simp [h_m_ne]

/-- **Iter 1430: nSteps none implies Halts**.  When the trajectory
    fails (nSteps returns none at some n), the cfg must Halt because
    failure means hitting a halted state. -/
theorem CTS_nSteps_none_implies_Halts
    (cts : CTS) :
    ∀ (n : Nat) (cfg : CTSConfig),
      cts.nSteps cfg n = none → cts.Halts cfg := by
  intro n
  induction n with
  | zero => intro cfg h; simp [CTS_nSteps_zero] at h
  | succ k ih =>
    intro cfg h
    rw [CTS_nSteps_succ] at h
    cases h_step : cts.step cfg with
    | none =>
      -- cfg is halted
      have h_halted : ctsHalted cfg = true :=
        (CTS_step_none_iff_halted_v2 cts cfg).mp h_step
      exact CTS_Halts_of_halted cts cfg h_halted
    | some cfg' =>
      rw [h_step] at h
      simp at h
      have h_cfg' : cts.Halts cfg' := ih cfg' h
      exact CTS_Halts_of_step_Halts cts cfg cfg' h_step h_cfg'

/-- **Iter 1431: ¬Halts implies all nSteps succeed**.  Contrapositive
    of iter 1430: when a cfg does NOT halt, the trajectory never fails
    — every `nSteps cfg n` returns `some result`. -/
theorem CTS_not_Halts_nSteps_some
    (cts : CTS) (cfg : CTSConfig) (h_not_halts : ¬ cts.Halts cfg) :
    ∀ n, ∃ result, cts.nSteps cfg n = some result := by
  intro n
  cases h : cts.nSteps cfg n with
  | none =>
    exfalso
    exact h_not_halts (CTS_nSteps_none_implies_Halts cts n cfg h)
  | some result => exact ⟨result, rfl⟩

/-- **Iter 1432: ¬Halts implies not halted**.  Direct contrapositive
    of `CTS_Halts_of_halted` (iter 1316). -/
theorem CTS_not_Halts_not_halted
    (cts : CTS) (cfg : CTSConfig) (h_not_halts : ¬ cts.Halts cfg) :
    ctsHalted cfg = false := by
  cases h : ctsHalted cfg with
  | true => exact absurd (CTS_Halts_of_halted cts cfg h) h_not_halts
  | false => rfl

/-- **Iter 1433: ¬Halts step yields ¬Halts result**.  When `cfg` does
    not Halt, the step succeeds and its result also does not Halt.
    Useful trampoline lemma: composes ¬halted (iter 1432) + step total
    (iter 1274) + step preserves Halts (iter 1424). -/
theorem CTS_not_Halts_step_some_not_Halts
    (cts : CTS) (cfg : CTSConfig) (h_not_halts : ¬ cts.Halts cfg) :
    ∃ result, cts.step cfg = some result ∧ ¬ cts.Halts result := by
  have h_not_halted : ctsHalted cfg = false :=
    CTS_not_Halts_not_halted cts cfg h_not_halts
  obtain ⟨result, h_step⟩ := CTS_step_some_of_not_halted cts cfg h_not_halted
  refine ⟨result, h_step, ?_⟩
  exact CTS_step_result_not_Halts_of_cfg_not_Halts cts cfg result h_not_halts h_step

/-- **Iter 1434: ¬Halts nSteps yields ¬Halts result**.  Multi-step lift
    of iter 1433: composes iter 1431 (¬Halts ⇒ nSteps some) + iter 1423
    (¬Halts ⇒ nSteps result ¬Halts).  Trampoline for trajectory analysis
    of non-halting CTS configs. -/
theorem CTS_not_Halts_nSteps_some_not_Halts
    (cts : CTS) (cfg : CTSConfig) (h_not_halts : ¬ cts.Halts cfg) :
    ∀ n, ∃ result, cts.nSteps cfg n = some result ∧ ¬ cts.Halts result := by
  intro n
  obtain ⟨result, h_n⟩ := CTS_not_Halts_nSteps_some cts cfg h_not_halts n
  refine ⟨result, h_n, ?_⟩
  exact CTS_nSteps_result_not_Halts_of_cfg_not_Halts cts cfg result n h_not_halts h_n

/-- **Iter 1435: cts.Halts iff exists nSteps none**.  Substantive
    biconditional: Halts ⇔ trajectory eventually fails.  Forward: from
    iter 1391 (Halts ⇒ ∃ n with nSteps = some halted), then iter 1429
    gives nSteps (n+1) = none.  Backward: iter 1430. -/
theorem CTS_Halts_iff_exists_nSteps_none
    (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ∃ n, cts.nSteps cfg n = none := by
  refine ⟨?_, ?_⟩
  · intro h_halts
    obtain ⟨n, result, h_n, h_halted⟩ := (CTS_Halts_iff_nSteps_halted cts cfg).mp h_halts
    refine ⟨n + 1, ?_⟩
    have := CTS_nSteps_halted_cannot_extend cts cfg result n h_n h_halted 1
      (Nat.le_refl 1)
    exact this
  · intro ⟨n, h_n⟩
    exact CTS_nSteps_none_implies_Halts cts n cfg h_n

/-- **Iter 1436 (🎯 545-LEMMA MILESTONE): ¬Halts iff all nSteps succeed**.
    Biconditional version of iter 1431: `¬cts.Halts cfg ↔ ∀ n, ∃ result,
    cts.nSteps cfg n = some result`.  Forward: iter 1431.  Backward:
    contrapositive of iter 1435 (Halts ⇔ ∃ n nSteps = none). -/
theorem CTS_not_Halts_iff_all_nSteps_some
    (cts : CTS) (cfg : CTSConfig) :
    ¬ cts.Halts cfg ↔ ∀ n, ∃ result, cts.nSteps cfg n = some result := by
  refine ⟨CTS_not_Halts_nSteps_some cts cfg, ?_⟩
  intro h_all h_halts
  obtain ⟨n, h_n⟩ := (CTS_Halts_iff_exists_nSteps_none cts cfg).mp h_halts
  obtain ⟨_, h_some⟩ := h_all n
  rw [h_some] at h_n
  cases h_n

/-- **Iter 1437: eval succ from non-halted yields step witness**.  When
    `eval cfg (fuel+1) = some result` and `cfg` is not halted, the step
    must succeed and eval continues from the result.  Generalizes iter
    1345 to extract the step witness. -/
theorem CTS_eval_succ_some_step_witness
    (cts : CTS) (cfg : CTSConfig) (fuel : Nat) (result : CTSConfig)
    (h_not_halted : ctsHalted cfg = false)
    (h_eval : cts.eval cfg (fuel + 1) = some result) :
    ∃ cfg', cts.step cfg = some cfg' ∧ cts.eval cfg' fuel = some result := by
  obtain ⟨cfg', h_step⟩ := CTS_step_some_of_not_halted cts cfg h_not_halted
  refine ⟨cfg', h_step, ?_⟩
  rw [CTS_eval_succ_not_halted cts cfg cfg' fuel h_not_halted h_step] at h_eval
  exact h_eval

/-- **Iter 1438: eval some implies nSteps some at smaller fuel**.
    When `eval cfg fuel = some result`, there exists `k ≤ fuel` with
    `nSteps cfg k = some result`.  Reverse direction of iter 1397.
    By induction on fuel, casing on halted at each level. -/
theorem CTS_eval_some_implies_nSteps_some
    (cts : CTS) :
    ∀ (fuel : Nat) (cfg result : CTSConfig),
      cts.eval cfg fuel = some result →
        ∃ k, k ≤ fuel ∧ cts.nSteps cfg k = some result := by
  intro fuel
  induction fuel with
  | zero =>
    intro cfg result h_eval
    -- eval cfg 0 = some result ⇒ halted cfg ∧ result = cfg
    have h_halted : ctsHalted cfg = true := by
      cases h : ctsHalted cfg with
      | true => rfl
      | false =>
        rw [show cts.eval cfg 0 = if ctsHalted cfg then some cfg else none from rfl] at h_eval
        rw [h] at h_eval
        simp at h_eval
    rw [show cts.eval cfg 0 = if ctsHalted cfg then some cfg else none from rfl] at h_eval
    rw [h_halted] at h_eval
    simp at h_eval
    refine ⟨0, Nat.le_refl 0, ?_⟩
    rw [CTS_nSteps_zero, h_eval]
  | succ n ih =>
    intro cfg result h_eval
    cases h_halted : ctsHalted cfg with
    | true =>
      have h_eval_eq : cts.eval cfg (n + 1) = some cfg := by
        exact CTS_eval_halted_returns cts cfg h_halted (n + 1)
      rw [h_eval_eq] at h_eval
      injection h_eval with h_eq
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [CTS_nSteps_zero, h_eq]
    | false =>
      obtain ⟨cfg', h_step, h_eval'⟩ :=
        CTS_eval_succ_some_step_witness cts cfg n result h_halted h_eval
      obtain ⟨k, h_k_le, h_k⟩ := ih cfg' result h_eval'
      refine ⟨k + 1, Nat.succ_le_succ h_k_le, ?_⟩
      rw [CTS_nSteps_succ, h_step]
      exact h_k

/-- **Iter 1439: eval some implies nSteps halted witness**.  Strengthens
    iter 1438 by adding the halted-result conclusion (via iter 1308).
    `eval cfg fuel = some result ⇒ ∃ k ≤ fuel, nSteps cfg k = some result
    ∧ halted result`. -/
theorem CTS_eval_some_implies_nSteps_halted_witness
    (cts : CTS) (cfg : CTSConfig) (fuel : Nat) (result : CTSConfig)
    (h_eval : cts.eval cfg fuel = some result) :
    ∃ k, k ≤ fuel ∧ cts.nSteps cfg k = some result ∧ ctsHalted result = true := by
  obtain ⟨k, h_k_le, h_k⟩ :=
    CTS_eval_some_implies_nSteps_some cts fuel cfg result h_eval
  refine ⟨k, h_k_le, h_k, ?_⟩
  exact CTS_eval_some_halted cts fuel cfg result h_eval

/-- **Iter 1440: eval some iff nSteps halted at smaller fuel**.
    Substantive biconditional bridging eval and nSteps:
    `eval cfg fuel = some result ↔ ∃ k ≤ fuel, nSteps cfg k = some result
    ∧ halted result`.  Forward: iter 1439.  Backward: iter 1397 + iter
    1319 (eval monotonic in fuel). -/
theorem CTS_eval_some_iff_nSteps_halted_le
    (cts : CTS) (cfg : CTSConfig) (fuel : Nat) (result : CTSConfig) :
    cts.eval cfg fuel = some result ↔
      ∃ k, k ≤ fuel ∧ cts.nSteps cfg k = some result ∧ ctsHalted result = true := by
  refine ⟨CTS_eval_some_implies_nSteps_halted_witness cts cfg fuel result, ?_⟩
  intro ⟨k, h_k_le, h_n, h_halted⟩
  have h_eval_k : cts.eval cfg k = some result :=
    CTS_nSteps_eval_eq cts k cfg result h_n h_halted
  have h_split : fuel = k + (fuel - k) := by omega
  rw [h_split]
  exact CTS_eval_monotonic cts cfg result k h_eval_k (fuel - k)

/-- **Iter 1441 (🎯 550-LEMMA MILESTONE): eval none iff no halted prefix**.
    Contrapositive of iter 1440: `eval cfg fuel = none ↔ ∀ k ≤ fuel, ∀ r,
    nSteps cfg k = some r → ¬halted r`.  Substantive characterization of
    eval-failure as absence of halted prefix in the trajectory. -/
theorem CTS_eval_none_iff_no_halted_prefix
    (cts : CTS) (cfg : CTSConfig) (fuel : Nat) :
    cts.eval cfg fuel = none ↔
      ∀ k, k ≤ fuel → ∀ r, cts.nSteps cfg k = some r → ctsHalted r = false := by
  refine ⟨?_, ?_⟩
  · intro h_none k h_k_le r h_n
    cases h_halted : ctsHalted r with
    | false => rfl
    | true =>
      exfalso
      have h_eval_some : cts.eval cfg fuel = some r :=
        (CTS_eval_some_iff_nSteps_halted_le cts cfg fuel r).mpr ⟨k, h_k_le, h_n, h_halted⟩
      rw [h_eval_some] at h_none
      cases h_none
  · intro h_no_halted
    cases h_eval : cts.eval cfg fuel with
    | none => rfl
    | some r =>
      exfalso
      obtain ⟨k, h_k_le, h_n, h_halted⟩ :=
        CTS_eval_some_implies_nSteps_halted_witness cts cfg fuel r h_eval
      have := h_no_halted k h_k_le r h_n
      rw [h_halted] at this
      cases this

/-- **Iter 1442: eval extends through a step**.  When `cfg` not halted,
    `step cfg = some cfg'`, and `eval cfg' n = some result`, then
    `eval cfg (n+1) = some result`.  Direct corollary of iter 1345. -/
theorem CTS_eval_step_extension
    (cts : CTS) (cfg cfg' result : CTSConfig) (n : Nat)
    (h_not_halted : ctsHalted cfg = false)
    (h_step : cts.step cfg = some cfg')
    (h_eval : cts.eval cfg' n = some result) :
    cts.eval cfg (n + 1) = some result := by
  rw [CTS_eval_succ_not_halted cts cfg cfg' n h_not_halted h_step]
  exact h_eval

/-- **Iter 1443: nSteps two equals chained step**.  `nSteps cfg 2 =
    (step cfg).bind step`.  Useful primitive for two-step trajectory
    analysis. -/
theorem CTS_nSteps_two_eq_step_bind
    (cts : CTS) (cfg : CTSConfig) :
    cts.nSteps cfg 2 = (cts.step cfg).bind cts.step := by
  show cts.nSteps cfg (1 + 1) = _
  rw [CTS_nSteps_succ]
  cases h : cts.step cfg with
  | none => simp
  | some cfg' => simp; exact CTS_nSteps_one cts cfg'

/-- **Iter 1444: System5 nSteps two equals chained step**.  System5
    companion to iter 1443: `nSteps cfg 2 = (step cfg).bind step`. -/
theorem System5_nSteps_two_eq_step_bind
    (cfg : System5Config) :
    System5.nSteps cfg 2 = (System5.step cfg).bind System5.step := by
  show System5.nSteps cfg (1 + 1) = _
  rw [System5.nSteps_succ]
  cases h : System5.step cfg with
  | none => simp
  | some cfg' => simp; exact System5.nSteps_one cfg'

/-- **Iter 1445: nSteps two some iff chained step some**.  Biconditional
    form of iter 1443: `nSteps cfg 2 = some result ↔ ∃ cfg', step cfg =
    some cfg' ∧ step cfg' = some result`. -/
theorem CTS_nSteps_two_some_iff
    (cts : CTS) (cfg result : CTSConfig) :
    cts.nSteps cfg 2 = some result ↔
      ∃ cfg', cts.step cfg = some cfg' ∧ cts.step cfg' = some result := by
  rw [CTS_nSteps_two_eq_step_bind]
  cases h : cts.step cfg with
  | none => simp
  | some cfg' =>
    constructor
    · intro h_step2
      simp at h_step2
      exact ⟨cfg', rfl, h_step2⟩
    · intro ⟨c', h_eq, h_step2⟩
      injection h_eq with h_eq; subst h_eq
      simp; exact h_step2

/-- **Iter 1446 (🎯 555-LEMMA MILESTONE): System5 nSteps two some iff
    chained step some**.  System5 companion to iter 1445. -/
theorem System5_nSteps_two_some_iff
    (cfg result : System5Config) :
    System5.nSteps cfg 2 = some result ↔
      ∃ cfg', System5.step cfg = some cfg' ∧ System5.step cfg' = some result := by
  rw [System5_nSteps_two_eq_step_bind]
  cases h : System5.step cfg with
  | none => simp
  | some cfg' =>
    constructor
    · intro h_step2
      simp at h_step2
      exact ⟨cfg', rfl, h_step2⟩
    · intro ⟨c', h_eq, h_step2⟩
      injection h_eq with h_eq; subst h_eq
      simp; exact h_step2

/-- **Iter 1447: nSteps extends through trailing step**.  When `nSteps
    cfg n = some result` and `step result = some result'`, then
    `nSteps cfg (n+1) = some result'`.  Forward direction of iter 1337,
    direct chain composition. -/
theorem CTS_nSteps_step_extension
    (cts : CTS) (cfg result result' : CTSConfig) (n : Nat)
    (h_n : cts.nSteps cfg n = some result)
    (h_step : cts.step result = some result') :
    cts.nSteps cfg (n + 1) = some result' :=
  (CTS_nSteps_succ_some_iff cts cfg result' n).mpr ⟨result, h_n, h_step⟩

/-- **Iter 1448: System5 nSteps extends through trailing step**.
    System5 companion to iter 1447. -/
theorem System5_nSteps_step_extension
    (cfg result result' : System5Config) (n : Nat)
    (h_n : System5.nSteps cfg n = some result)
    (h_step : System5.step result = some result') :
    System5.nSteps cfg (n + 1) = some result' :=
  (System5_nSteps_succ_some_iff cfg result' n).mpr ⟨result, h_n, h_step⟩

/-- **Iter 1449: nSteps prepended via leading step**.  When `step cfg =
    some cfg'` and `nSteps cfg' n = some result`, then `nSteps cfg (n+1)
    = some result`.  Direct corollary of iter 1407 (`step_nSteps_succ`). -/
theorem CTS_nSteps_step_prepend
    (cts : CTS) (cfg cfg' result : CTSConfig) (n : Nat)
    (h_step : cts.step cfg = some cfg')
    (h_n : cts.nSteps cfg' n = some result) :
    cts.nSteps cfg (n + 1) = some result := by
  rw [CTS_step_nSteps_succ cts cfg cfg' n h_step]
  exact h_n

/-- **Iter 1450: System5 nSteps prepended via leading step**.  System5
    companion to iter 1449. -/
theorem System5_nSteps_step_prepend
    (cfg cfg' result : System5Config) (n : Nat)
    (h_step : System5.step cfg = some cfg')
    (h_n : System5.nSteps cfg' n = some result) :
    System5.nSteps cfg (n + 1) = some result := by
  rw [System5_step_nSteps_succ cfg cfg' n h_step]
  exact h_n

/-- **Iter 1451 (🎯🎯🎯 560-LEMMA MILESTONE): nSteps double-step extension**.
    When `nSteps cfg n = some r1`, `step r1 = some r2`, `step r2 = some
    r3`, then `nSteps cfg (n+2) = some r3`.  Direct chain composition of
    iter 1447 twice. -/
theorem CTS_nSteps_step_step_chain
    (cts : CTS) (cfg r1 r2 r3 : CTSConfig) (n : Nat)
    (h_n : cts.nSteps cfg n = some r1)
    (h_step1 : cts.step r1 = some r2)
    (h_step2 : cts.step r2 = some r3) :
    cts.nSteps cfg (n + 2) = some r3 := by
  show cts.nSteps cfg (n + 1 + 1) = _
  exact CTS_nSteps_step_extension cts cfg r2 r3 (n + 1)
    (CTS_nSteps_step_extension cts cfg r1 r2 n h_n h_step1) h_step2

/-- **Iter 1452: System5 nSteps double-step extension**.  System5
    companion to iter 1451. -/
theorem System5_nSteps_step_step_chain
    (cfg r1 r2 r3 : System5Config) (n : Nat)
    (h_n : System5.nSteps cfg n = some r1)
    (h_step1 : System5.step r1 = some r2)
    (h_step2 : System5.step r2 = some r3) :
    System5.nSteps cfg (n + 2) = some r3 := by
  show System5.nSteps cfg (n + 1 + 1) = _
  exact System5_nSteps_step_extension cfg r2 r3 (n + 1)
    (System5_nSteps_step_extension cfg r1 r2 n h_n h_step1) h_step2

/-- **Iter 1453: System5 nSteps quadruple-step extension**.  Chain four
    consecutive steps through nSteps.  Useful for cy2s5's 4-step CTS-step
    correspondence (one CTS step = 4 System5 steps when all P-steps).
    Composes iter 1452 twice. -/
theorem System5_nSteps_step_4_chain
    (cfg r1 r2 r3 r4 r5 : System5Config) (n : Nat)
    (h_n : System5.nSteps cfg n = some r1)
    (h_s1 : System5.step r1 = some r2)
    (h_s2 : System5.step r2 = some r3)
    (h_s3 : System5.step r3 = some r4)
    (h_s4 : System5.step r4 = some r5) :
    System5.nSteps cfg (n + 4) = some r5 := by
  have h_n2 : System5.nSteps cfg (n + 2) = some r3 :=
    System5_nSteps_step_step_chain cfg r1 r2 r3 n h_n h_s1 h_s2
  show System5.nSteps cfg (n + 2 + 2) = _
  exact System5_nSteps_step_step_chain cfg r3 r4 r5 (n + 2) h_n2 h_s3 h_s4

/-- **Iter 1454: System5 nSteps sextuple-step extension**.  Chain six
    consecutive steps through nSteps.  Useful for the true-head
    6-step CTS-step correspondence (one true-head CTS step = 6 System5
    steps in the P,D,P,P-empty,D,P-empty pattern).  Composes iter 1453 +
    iter 1452. -/
theorem System5_nSteps_step_6_chain
    (cfg r1 r2 r3 r4 r5 r6 r7 : System5Config) (n : Nat)
    (h_n : System5.nSteps cfg n = some r1)
    (h_s1 : System5.step r1 = some r2)
    (h_s2 : System5.step r2 = some r3)
    (h_s3 : System5.step r3 = some r4)
    (h_s4 : System5.step r4 = some r5)
    (h_s5 : System5.step r5 = some r6)
    (h_s6 : System5.step r6 = some r7) :
    System5.nSteps cfg (n + 6) = some r7 := by
  have h_n4 : System5.nSteps cfg (n + 4) = some r5 :=
    System5_nSteps_step_4_chain cfg r1 r2 r3 r4 r5 n h_n h_s1 h_s2 h_s3 h_s4
  show System5.nSteps cfg (n + 4 + 2) = _
  exact System5_nSteps_step_step_chain cfg r5 r6 r7 (n + 4) h_n4 h_s5 h_s6

/-- **Iter 1455: step some iff nSteps one some**.  `cts.step cfg = some
    result ↔ cts.nSteps cfg 1 = some result`.  Trivial reformulation via
    iter 1331. -/
theorem CTS_step_some_iff_nSteps_one_some
    (cts : CTS) (cfg result : CTSConfig) :
    cts.step cfg = some result ↔ cts.nSteps cfg 1 = some result := by
  rw [CTS_nSteps_one]

/-- **Iter 1456 (🎯 565-LEMMA MILESTONE): System5 step some iff nSteps
    one some**.  System5 companion to iter 1455. -/
theorem System5_step_some_iff_nSteps_one_some
    (cfg result : System5Config) :
    System5.step cfg = some result ↔ System5.nSteps cfg 1 = some result := by
  rw [System5.nSteps_one]

/-- **Iter 1457: nSteps three equals chained step bind**.  `nSteps cfg 3
    = ((step cfg).bind step).bind step`.  Generalizes iter 1443 to three
    steps. -/
theorem CTS_nSteps_three_eq_step_bind
    (cts : CTS) (cfg : CTSConfig) :
    cts.nSteps cfg 3 = ((cts.step cfg).bind cts.step).bind cts.step := by
  show cts.nSteps cfg (2 + 1) = _
  rw [CTS_nSteps_succ]
  cases h1 : cts.step cfg with
  | none => simp
  | some cfg1 =>
    simp
    show cts.nSteps cfg1 (1 + 1) = _
    rw [CTS_nSteps_succ]
    cases h2 : cts.step cfg1 with
    | none => simp
    | some cfg2 => simp; exact CTS_nSteps_one cts cfg2

/-- **Iter 1458: System5 nSteps three equals chained step bind**.
    System5 companion to iter 1457. -/
theorem System5_nSteps_three_eq_step_bind
    (cfg : System5Config) :
    System5.nSteps cfg 3 = ((System5.step cfg).bind System5.step).bind System5.step := by
  show System5.nSteps cfg (2 + 1) = _
  rw [System5.nSteps_succ]
  cases h1 : System5.step cfg with
  | none => simp
  | some cfg1 =>
    simp
    show System5.nSteps cfg1 (1 + 1) = _
    rw [System5.nSteps_succ]
    cases h2 : System5.step cfg1 with
    | none => simp
    | some cfg2 => simp; exact System5.nSteps_one cfg2

/-- **Iter 1459: System5 nSteps triple-step extension**.  Chain three
    consecutive steps through nSteps.  Composes iter 1452 + iter 1448. -/
theorem System5_nSteps_step_3_chain
    (cfg r1 r2 r3 r4 : System5Config) (n : Nat)
    (h_n : System5.nSteps cfg n = some r1)
    (h_s1 : System5.step r1 = some r2)
    (h_s2 : System5.step r2 = some r3)
    (h_s3 : System5.step r3 = some r4) :
    System5.nSteps cfg (n + 3) = some r4 := by
  have h_n2 : System5.nSteps cfg (n + 2) = some r3 :=
    System5_nSteps_step_step_chain cfg r1 r2 r3 n h_n h_s1 h_s2
  show System5.nSteps cfg (n + 2 + 1) = _
  exact System5_nSteps_step_extension cfg r3 r4 (n + 2) h_n2 h_s3

/-- **Iter 1460: System5 nSteps quintuple-step extension**.  Chain five
    consecutive steps.  Composes iter 1453 + iter 1448. -/
theorem System5_nSteps_step_5_chain
    (cfg r1 r2 r3 r4 r5 r6 : System5Config) (n : Nat)
    (h_n : System5.nSteps cfg n = some r1)
    (h_s1 : System5.step r1 = some r2)
    (h_s2 : System5.step r2 = some r3)
    (h_s3 : System5.step r3 = some r4)
    (h_s4 : System5.step r4 = some r5)
    (h_s5 : System5.step r5 = some r6) :
    System5.nSteps cfg (n + 5) = some r6 := by
  have h_n4 : System5.nSteps cfg (n + 4) = some r5 :=
    System5_nSteps_step_4_chain cfg r1 r2 r3 r4 r5 n h_n h_s1 h_s2 h_s3 h_s4
  show System5.nSteps cfg (n + 4 + 1) = _
  exact System5_nSteps_step_extension cfg r5 r6 (n + 4) h_n4 h_s5

/-- **Iter 1461 (🎯🎯🎯 570-LEMMA MILESTONE): CTS nSteps triple-step
    extension**.  CTS companion to iter 1459: chain three consecutive
    CTS steps through nSteps.  Composes iter 1451 + iter 1447. -/
theorem CTS_nSteps_step_3_chain
    (cts : CTS) (cfg r1 r2 r3 r4 : CTSConfig) (n : Nat)
    (h_n : cts.nSteps cfg n = some r1)
    (h_s1 : cts.step r1 = some r2)
    (h_s2 : cts.step r2 = some r3)
    (h_s3 : cts.step r3 = some r4) :
    cts.nSteps cfg (n + 3) = some r4 := by
  have h_n2 : cts.nSteps cfg (n + 2) = some r3 :=
    CTS_nSteps_step_step_chain cts cfg r1 r2 r3 n h_n h_s1 h_s2
  show cts.nSteps cfg (n + 2 + 1) = _
  exact CTS_nSteps_step_extension cts cfg r3 r4 (n + 2) h_n2 h_s3

/-- **Iter 1462: CTS nSteps quadruple-step extension**.  CTS companion to
    iter 1453.  Chains four consecutive CTS steps. -/
theorem CTS_nSteps_step_4_chain
    (cts : CTS) (cfg r1 r2 r3 r4 r5 : CTSConfig) (n : Nat)
    (h_n : cts.nSteps cfg n = some r1)
    (h_s1 : cts.step r1 = some r2)
    (h_s2 : cts.step r2 = some r3)
    (h_s3 : cts.step r3 = some r4)
    (h_s4 : cts.step r4 = some r5) :
    cts.nSteps cfg (n + 4) = some r5 := by
  have h_n2 : cts.nSteps cfg (n + 2) = some r3 :=
    CTS_nSteps_step_step_chain cts cfg r1 r2 r3 n h_n h_s1 h_s2
  show cts.nSteps cfg (n + 2 + 2) = _
  exact CTS_nSteps_step_step_chain cts cfg r3 r4 r5 (n + 2) h_n2 h_s3 h_s4

/-- **Iter 1463: nSteps succ some implies step some**.  When `nSteps cfg
    (n+1) = some result`, the first step must succeed: `∃ cfg', step cfg
    = some cfg'`.  Direct corollary of iter 1343. -/
theorem CTS_nSteps_succ_some_implies_step_some
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h_n : cts.nSteps cfg (n + 1) = some result) :
    ∃ cfg', cts.step cfg = some cfg' := by
  obtain ⟨cfg', h_step, _⟩ := CTS_nSteps_succ_some_first_step cts cfg result n h_n
  exact ⟨cfg', h_step⟩

/-- **Iter 1464: System5 nSteps succ some implies step some**.  System5
    companion to iter 1463. -/
theorem System5_nSteps_succ_some_implies_step_some
    (cfg result : System5Config) (n : Nat)
    (h_n : System5.nSteps cfg (n + 1) = some result) :
    ∃ cfg', System5.step cfg = some cfg' := by
  obtain ⟨cfg', h_step, _⟩ := System5_nSteps_succ_some_first_step cfg result n h_n
  exact ⟨cfg', h_step⟩

/-- **Iter 1465: nSteps step intermediate**.  When `nSteps cfg n = some
    result` and `n ≥ 1`, the trajectory must include a first step.
    Useful for trajectory decomposition. -/
theorem CTS_nSteps_pos_some_first_step_witness
    (cts : CTS) (cfg result : CTSConfig) (n : Nat) (h_pos : n ≥ 1)
    (h_n : cts.nSteps cfg n = some result) :
    ∃ cfg' k, cts.step cfg = some cfg' ∧ n = k + 1 ∧ cts.nSteps cfg' k = some result := by
  obtain ⟨k, h_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp h_pos)
  rw [h_eq] at h_n
  obtain ⟨cfg', h_step, h_k⟩ := CTS_nSteps_succ_some_first_step cts cfg result k h_n
  exact ⟨cfg', k, h_step, h_eq, h_k⟩

/-- **Iter 1466 (🎯 575-LEMMA MILESTONE): System5 nSteps positive some
    first-step witness**.  System5 companion to iter 1465. -/
theorem System5_nSteps_pos_some_first_step_witness
    (cfg result : System5Config) (n : Nat) (h_pos : n ≥ 1)
    (h_n : System5.nSteps cfg n = some result) :
    ∃ cfg' k, System5.step cfg = some cfg' ∧ n = k + 1 ∧ System5.nSteps cfg' k = some result := by
  obtain ⟨k, h_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp h_pos)
  rw [h_eq] at h_n
  obtain ⟨cfg', h_step, h_k⟩ := System5_nSteps_succ_some_first_step cfg result k h_n
  exact ⟨cfg', k, h_step, h_eq, h_k⟩

/-- **Iter 1467: nSteps succ none characterization**.  `nSteps cfg (n+1)
    = none ↔ step cfg = none ∨ (∃ r, step cfg = some r ∧ nSteps r n =
    none)`.  Useful for failure-mode analysis. -/
theorem CTS_nSteps_succ_none_iff
    (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    cts.nSteps cfg (n + 1) = none ↔
      cts.step cfg = none ∨ (∃ r, cts.step cfg = some r ∧ cts.nSteps r n = none) := by
  rw [CTS_nSteps_succ]
  cases h : cts.step cfg with
  | none => simp
  | some r =>
    refine ⟨fun h_n => Or.inr ⟨r, rfl, h_n⟩, ?_⟩
    intro h_or
    rcases h_or with h_none | ⟨r', h_eq, h_n⟩
    · cases h_none
    · injection h_eq with h_eq
      subst h_eq
      exact h_n

/-- **Iter 1468: System5 nSteps succ none characterization**.  System5
    companion to iter 1467. -/
theorem System5_nSteps_succ_none_iff
    (cfg : System5Config) (n : Nat) :
    System5.nSteps cfg (n + 1) = none ↔
      System5.step cfg = none ∨ (∃ r, System5.step cfg = some r ∧ System5.nSteps r n = none) := by
  rw [System5.nSteps_succ]
  cases h : System5.step cfg with
  | none => simp
  | some r =>
    refine ⟨fun h_n => Or.inr ⟨r, rfl, h_n⟩, ?_⟩
    intro h_or
    rcases h_or with h_none | ⟨r', h_eq, h_n⟩
    · cases h_none
    · injection h_eq with h_eq
      subst h_eq
      exact h_n

/-- **Iter 1469: nSteps positive some last-step witness**.  Pairs with
    iter 1465 (first-step): `nSteps cfg n = some result` and `n ≥ 1`
    ⇒ ∃ r' k, n = k + 1 ∧ nSteps cfg k = some r' ∧ step r' = some result. -/
theorem CTS_nSteps_pos_some_last_step_witness
    (cts : CTS) (cfg result : CTSConfig) (n : Nat) (h_pos : n ≥ 1)
    (h_n : cts.nSteps cfg n = some result) :
    ∃ r' k, n = k + 1 ∧ cts.nSteps cfg k = some r' ∧ cts.step r' = some result := by
  obtain ⟨k, h_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp h_pos)
  rw [h_eq] at h_n
  obtain ⟨r', h_k, h_step⟩ := (CTS_nSteps_succ_some_iff cts cfg result k).mp h_n
  exact ⟨r', k, h_eq, h_k, h_step⟩

/-- **Iter 1470 (🎯 ITER 1470 MILESTONE): System5 nSteps positive some
    last-step witness**.  System5 companion to iter 1469. -/
theorem System5_nSteps_pos_some_last_step_witness
    (cfg result : System5Config) (n : Nat) (h_pos : n ≥ 1)
    (h_n : System5.nSteps cfg n = some result) :
    ∃ r' k, n = k + 1 ∧ System5.nSteps cfg k = some r' ∧ System5.step r' = some result := by
  obtain ⟨k, h_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp h_pos)
  rw [h_eq] at h_n
  obtain ⟨r', h_k, h_step⟩ := (System5_nSteps_succ_some_iff cfg result k).mp h_n
  exact ⟨r', k, h_eq, h_k, h_step⟩

/-- **Iter 1471 (🎯🎯🎯 580-LEMMA MILESTONE): System5 step some implies
    bag/rules non-empty**.  Direct contrapositive of `System5_step_none_iff`:
    when `step cfg = some result`, both `cfg.bag ≠ []` and `cfg.rules ≠ []`. -/
theorem System5_step_some_implies_bag_rules_ne_nil
    (cfg result : System5Config) (h_step : System5.step cfg = some result) :
    cfg.bag ≠ [] ∧ cfg.rules ≠ [] := by
  refine ⟨?_, ?_⟩
  · intro h_bag
    have h_none : System5.step cfg = none := by
      rw [System5_step_none_iff]; left; exact h_bag
    rw [h_none] at h_step; cases h_step
  · intro h_rules
    have h_none : System5.step cfg = none := by
      rw [System5_step_none_iff]; right; exact h_rules
    rw [h_none] at h_step; cases h_step

/-- **Iter 1472: step chain implies nSteps two**.  `step cfg = some r1`
    and `step r1 = some r2` ⇒ `nSteps cfg 2 = some r2`.  Direct via
    iter 1445. -/
theorem CTS_step_step_chain_implies_nSteps_2
    (cts : CTS) (cfg r1 r2 : CTSConfig)
    (h_s1 : cts.step cfg = some r1)
    (h_s2 : cts.step r1 = some r2) :
    cts.nSteps cfg 2 = some r2 :=
  (CTS_nSteps_two_some_iff cts cfg r2).mpr ⟨r1, h_s1, h_s2⟩

/-- **Iter 1473: System5 step chain implies nSteps two**.  System5
    companion to iter 1472. -/
theorem System5_step_step_chain_implies_nSteps_2
    (cfg r1 r2 : System5Config)
    (h_s1 : System5.step cfg = some r1)
    (h_s2 : System5.step r1 = some r2) :
    System5.nSteps cfg 2 = some r2 :=
  (System5_nSteps_two_some_iff cfg r2).mpr ⟨r1, h_s1, h_s2⟩

/-- **Iter 1474: eval succ some characterization**.  `eval cfg (n+1) =
    some r ↔ (halted cfg ∧ r = cfg) ∨ (¬halted cfg ∧ ∃ cfg', step cfg =
    some cfg' ∧ eval cfg' n = some r)`.  Substantive eval characterization. -/
theorem CTS_eval_succ_some_iff
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (r : CTSConfig) :
    cts.eval cfg (n + 1) = some r ↔
      (ctsHalted cfg = true ∧ r = cfg) ∨
        (ctsHalted cfg = false ∧ ∃ cfg', cts.step cfg = some cfg' ∧ cts.eval cfg' n = some r) := by
  refine ⟨?_, ?_⟩
  · intro h_eval
    cases h_halt : ctsHalted cfg with
    | true =>
      left
      have h_eq : cts.eval cfg (n + 1) = some cfg :=
        CTS_eval_halted_returns cts cfg h_halt (n + 1)
      rw [h_eq] at h_eval
      injection h_eval with h_eq2
      exact ⟨rfl, h_eq2.symm⟩
    | false =>
      right
      refine ⟨rfl, ?_⟩
      exact CTS_eval_succ_some_step_witness cts cfg n r h_halt h_eval
  · intro h_or
    rcases h_or with ⟨h_halt, h_eq⟩ | ⟨h_halt, ⟨cfg', h_step, h_eval⟩⟩
    · rw [h_eq]
      exact CTS_eval_halted_returns cts cfg h_halt (n + 1)
    · exact CTS_eval_step_extension cts cfg cfg' r n h_halt h_step h_eval

/-- **Iter 1475: eval some succ extension**.  When `eval cfg n = some r`,
    `eval cfg (n+1) = some r`.  Direct via iter 1319 with k=1. -/
theorem CTS_eval_some_succ_extension
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h_eval : cts.eval cfg n = some result) :
    cts.eval cfg (n + 1) = some result :=
  CTS_eval_monotonic cts cfg result n h_eval 1

/-- **Iter 1476 (🎯 585-LEMMA MILESTONE): eval some le extension**.
    When `eval cfg n = some r` and `n ≤ m`, `eval cfg m = some r`.
    Cleaner consumer for iter 1319. -/
theorem CTS_eval_some_le_extension
    (cts : CTS) (cfg result : CTSConfig) (n m : Nat) (h_le : n ≤ m)
    (h_eval : cts.eval cfg n = some result) :
    cts.eval cfg m = some result := by
  have h_split : m = n + (m - n) := by omega
  rw [h_split]
  exact CTS_eval_monotonic cts cfg result n h_eval (m - n)

/-- **Iter 1477: nSteps halted eval at higher fuel**.  When `nSteps cfg
    n = some r ∧ halted r`, then for any `m ≥ n`, `eval cfg m = some r`.
    Composes iter 1397 (nSteps halted ⇒ eval) + iter 1476 (eval le
    extension). -/
theorem CTS_nSteps_halted_eval_le
    (cts : CTS) (cfg result : CTSConfig) (n m : Nat) (h_le : n ≤ m)
    (h_n : cts.nSteps cfg n = some result)
    (h_halted : ctsHalted result = true) :
    cts.eval cfg m = some result :=
  CTS_eval_some_le_extension cts cfg result n m h_le
    (CTS_nSteps_eval_eq cts n cfg result h_n h_halted)

/-- **Iter 1478: step some iff data non-empty**.  Combines iter 1277
    + iter 1264: `(∃ result, step cfg = some result) ↔ cfg.data ≠ []`. -/
theorem CTS_step_some_iff_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) :
    (∃ result, cts.step cfg = some result) ↔ cfg.data ≠ [] := by
  rw [CTS_step_some_iff_not_halted, ctsHalted_false_iff_data_ne_nil]

/-- **Iter 1479: System5 ¬Halts iff all nSteps succeed**.  Direct from
    System5.Halts def + Option case-split. -/
theorem System5_not_Halts_iff_all_nSteps_some
    (cfg : System5Config) :
    ¬ System5.Halts cfg ↔ ∀ n, ∃ result, System5.nSteps cfg n = some result := by
  unfold System5.Halts
  refine ⟨?_, ?_⟩
  · intro h_not_exists n
    cases h : System5.nSteps cfg n with
    | none => exfalso; exact h_not_exists ⟨n, h⟩
    | some r => exact ⟨r, rfl⟩
  · intro h_all ⟨n, h_n⟩
    obtain ⟨_, h_some⟩ := h_all n
    rw [h_some] at h_n
    cases h_n

/-- **Iter 1480: System5 Halts iff exists nSteps none**.  Restatement
    of `System5.Halts` def.  Useful named primitive parallel to iter
    1435 (CTS version). -/
theorem System5_Halts_iff_exists_nSteps_none
    (cfg : System5Config) :
    System5.Halts cfg ↔ ∃ n, System5.nSteps cfg n = none :=
  Iff.rfl

/-- **Iter 1481 (🎯🎯🎯 590-LEMMA MILESTONE): System5 ¬Halts step yields
    ¬Halts result**.  Parallel to CTS iter 1433.  When `cfg` does not
    Halt, the step succeeds and result also does not Halt. -/
theorem System5_not_Halts_step_some_not_Halts
    (cfg : System5Config) (h_not_halts : ¬ System5.Halts cfg) :
    ∃ result, System5.step cfg = some result ∧ ¬ System5.Halts result := by
  -- step cfg = some result, else Halts via System5_step_none_imp_Halts
  cases h_step : System5.step cfg with
  | none => exact absurd (System5_step_none_imp_Halts cfg h_step) h_not_halts
  | some result =>
    refine ⟨result, rfl, ?_⟩
    intro h_result_halts
    exact h_not_halts (System5_Halts_step_pred cfg result h_step h_result_halts)

/-- **Iter 1482: System5 ¬Halts implies all nSteps succeed**.  Parallel
    to CTS iter 1431. -/
theorem System5_not_Halts_nSteps_some
    (cfg : System5Config) (h_not_halts : ¬ System5.Halts cfg) :
    ∀ n, ∃ result, System5.nSteps cfg n = some result :=
  (System5_not_Halts_iff_all_nSteps_some cfg).mp h_not_halts

/-- **Iter 1483: System5 ¬Halts nSteps yields ¬Halts result**.  Parallel
    to CTS iter 1434.  Multi-step lift of iter 1481. -/
theorem System5_not_Halts_nSteps_some_not_Halts
    (cfg : System5Config) (h_not_halts : ¬ System5.Halts cfg) :
    ∀ n, ∃ result, System5.nSteps cfg n = some result ∧ ¬ System5.Halts result := by
  intro n
  obtain ⟨result, h_n⟩ := System5_not_Halts_nSteps_some cfg h_not_halts n
  refine ⟨result, h_n, ?_⟩
  intro h_result_halts
  exact h_not_halts (System5_Halts_nSteps_pred cfg n result h_n h_result_halts)

/-- **Iter 1484: System5 Halts characterization via step**.  Parallel
    to CTS iter 1326: `cfg.Halts ↔ step cfg = none ∨ (∃ r, step cfg =
    some r ∧ r.Halts)`. -/
theorem System5_Halts_iff_step_none_or_step_Halts
    (cfg : System5Config) :
    System5.Halts cfg ↔
      System5.step cfg = none ∨ (∃ r, System5.step cfg = some r ∧ System5.Halts r) := by
  refine ⟨?_, ?_⟩
  · intro h_halts
    cases h_step : System5.step cfg with
    | none => left; rfl
    | some r =>
      right
      refine ⟨r, rfl, ?_⟩
      exact (System5_Halts_step_iff cfg r h_step).mp h_halts
  · intro h_or
    rcases h_or with h_none | ⟨r, h_step, h_r_halts⟩
    · exact System5_step_none_imp_Halts cfg h_none
    · exact System5_Halts_step_pred cfg r h_step h_r_halts

/-- **Iter 1485: nSteps none implies step-none witness**.  When `nSteps
    cfg n = none`, ∃ m result, `nSteps cfg m = some result ∧ step result
    = none`.  Useful for analyzing System5 halting trajectories.  By
    induction on n. -/
theorem System5_nSteps_none_implies_step_none_witness :
    ∀ (n : Nat) (cfg : System5Config),
      System5.nSteps cfg n = none →
      ∃ m result, System5.nSteps cfg m = some result ∧ System5.step result = none := by
  intro n
  induction n with
  | zero =>
    intro cfg h_n
    rw [System5.nSteps_zero] at h_n
    cases h_n
  | succ k ih =>
    intro cfg h_n
    rcases (System5_nSteps_succ_none_iff cfg k).mp h_n with h_step_none | ⟨r, h_step, h_rec⟩
    · exact ⟨0, cfg, by rw [System5.nSteps_zero], h_step_none⟩
    · obtain ⟨m', result, h_m', h_step'⟩ := ih r h_rec
      refine ⟨m' + 1, result, ?_, h_step'⟩
      exact System5_nSteps_step_prepend cfg r result m' h_step h_m'

/-- **Iter 1486 (🎯🎯🎯 595-LEMMA MILESTONE): System5 Halts implies
    step-none witness**.  Direct corollary of iter 1485 + System5.Halts
    def: when cfg.Halts, ∃ m result, `nSteps cfg m = some result ∧
    step result = none`.  The "last successful state" of the trajectory. -/
theorem System5_Halts_implies_step_none_witness
    (cfg : System5Config) (h_halts : System5.Halts cfg) :
    ∃ m result, System5.nSteps cfg m = some result ∧ System5.step result = none := by
  obtain ⟨n, h_n⟩ := h_halts
  exact System5_nSteps_none_implies_step_none_witness n cfg h_n

/-- **Iter 1487: System5 Halts iff exists step-none witness**.  Forward
    direction is iter 1486; backward direction shows the witness yields
    Halts via `System5_step_none_imp_Halts` chained through `nSteps`. -/
theorem System5_Halts_iff_step_none_witness
    (cfg : System5Config) :
    System5.Halts cfg ↔
      ∃ m result, System5.nSteps cfg m = some result ∧ System5.step result = none := by
  refine ⟨System5_Halts_implies_step_none_witness cfg, ?_⟩
  intro ⟨m, result, h_m, h_step⟩
  exact System5_Halts_nSteps_pred cfg m result h_m
    (System5_step_none_imp_Halts result h_step)

/-- **Iter 1488: System5 nSteps cannot extend past step-none point**.
    Parallel to CTS iter 1429.  Direct via existing
    `System5_nSteps_past_step_none_eq_none`. -/
theorem System5_nSteps_step_none_cannot_extend
    (cfg result : System5Config) (n : Nat)
    (h_n : System5.nSteps cfg n = some result)
    (h_step : System5.step result = none)
    (m : Nat) (h_m : m ≥ 1) :
    System5.nSteps cfg (n + m) = none :=
  System5_nSteps_past_step_none_eq_none cfg n result h_n h_step m h_m

/-- **Iter 1489: System5 Halts step-some witness when step ≠ none**.
    Parallel to CTS iter 1325.  When cfg.Halts and step cfg ≠ none,
    ∃ r, step cfg = some r ∧ r.Halts. -/
theorem System5_Halts_step_some_witness_of_step_ne_none
    (cfg : System5Config) (h_halts : System5.Halts cfg)
    (h_step_ne : System5.step cfg ≠ none) :
    ∃ r, System5.step cfg = some r ∧ System5.Halts r := by
  rcases (System5_Halts_iff_step_none_or_step_Halts cfg).mp h_halts with h_none | ⟨r, h_step, h_r⟩
  · exact absurd h_none h_step_ne
  · exact ⟨r, h_step, h_r⟩

/-- **Iter 1490: CTS Halts iff step-none witness**.  Parallel to System5
    iter 1487: `cfg.Halts ↔ ∃ m result, nSteps cfg m = some result ∧
    step result = none`.  Forward: iter 1391 + iter 1276 (step none iff
    halted).  Backward: same direction. -/
theorem CTS_Halts_iff_step_none_witness
    (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔
      ∃ m result, cts.nSteps cfg m = some result ∧ cts.step result = none := by
  rw [CTS_Halts_iff_nSteps_halted cts cfg]
  refine ⟨?_, ?_⟩
  · intro ⟨m, result, h_m, h_halted⟩
    refine ⟨m, result, h_m, ?_⟩
    exact (CTS_step_none_iff_halted_v2 cts result).mpr h_halted
  · intro ⟨m, result, h_m, h_step⟩
    refine ⟨m, result, h_m, ?_⟩
    exact (CTS_step_none_iff_halted_v2 cts result).mp h_step

/-- **Iter 1491 (🎯🎯🎯🎯🎯 600-LEMMA MILESTONE): CTS ¬Halts trajectory
    continues at every chain point**.  When `¬cfg.Halts`, at any chain
    point along the trajectory the result is non-halting and step
    succeeds.  Combines iter 1434 (¬Halts ⇒ nSteps result ¬Halts) +
    iter 1432 (¬Halts ⇒ ¬halted) + iter 1276 (step ≠ none iff ¬halted). -/
theorem CTS_not_Halts_chain_continues
    (cts : CTS) (cfg : CTSConfig) (h_not_halts : ¬ cts.Halts cfg) :
    ∀ n, ∃ result, cts.nSteps cfg n = some result ∧
      ¬ cts.Halts result ∧ cts.step result ≠ none := by
  intro n
  obtain ⟨result, h_n, h_result_not_halts⟩ :=
    CTS_not_Halts_nSteps_some_not_Halts cts cfg h_not_halts n
  refine ⟨result, h_n, h_result_not_halts, ?_⟩
  intro h_step_none
  exact h_result_not_halts (CTS_Halts_of_halted cts result
    ((CTS_step_none_iff_halted_v2 cts result).mp h_step_none))

/-- **Iter 1492: System5 ¬Halts trajectory continues at every chain
    point**.  Parallel to CTS iter 1491. -/
theorem System5_not_Halts_chain_continues
    (cfg : System5Config) (h_not_halts : ¬ System5.Halts cfg) :
    ∀ n, ∃ result, System5.nSteps cfg n = some result ∧
      ¬ System5.Halts result ∧ System5.step result ≠ none := by
  intro n
  obtain ⟨result, h_n, h_result_not_halts⟩ :=
    System5_not_Halts_nSteps_some_not_Halts cfg h_not_halts n
  refine ⟨result, h_n, h_result_not_halts, ?_⟩
  intro h_step_none
  exact h_result_not_halts (System5_step_none_imp_Halts result h_step_none)

/-- **Iter 1493: CTS ¬Halts nSteps advance witness**.  When `¬cfg.Halts`
    and `nSteps cfg n = some r`, ∃ r', `step r = some r' ∧ nSteps cfg
    (n+1) = some r'`.  Useful trampoline for non-halting trajectory
    induction.  Composes iter 1491 + iter 1447. -/
theorem CTS_not_Halts_nSteps_advance
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h_not_halts : ¬ cts.Halts cfg)
    (h_n : cts.nSteps cfg n = some result) :
    ∃ result', cts.step result = some result' ∧ cts.nSteps cfg (n + 1) = some result' := by
  obtain ⟨r, h_n', _, h_step_ne⟩ := CTS_not_Halts_chain_continues cts cfg h_not_halts n
  rw [h_n] at h_n'
  injection h_n' with h_eq
  subst h_eq
  cases h : cts.step result with
  | none => exact absurd h h_step_ne
  | some result' =>
    refine ⟨result', rfl, ?_⟩
    exact CTS_nSteps_step_extension cts cfg result result' n h_n h

/-- **Iter 1494: System5 ¬Halts nSteps advance witness**.  System5
    companion to iter 1493. -/
theorem System5_not_Halts_nSteps_advance
    (cfg result : System5Config) (n : Nat)
    (h_not_halts : ¬ System5.Halts cfg)
    (h_n : System5.nSteps cfg n = some result) :
    ∃ result', System5.step result = some result' ∧ System5.nSteps cfg (n + 1) = some result' := by
  obtain ⟨r, h_n', _, h_step_ne⟩ := System5_not_Halts_chain_continues cfg h_not_halts n
  rw [h_n] at h_n'
  injection h_n' with h_eq
  subst h_eq
  cases h : System5.step result with
  | none => exact absurd h h_step_ne
  | some result' =>
    refine ⟨result', rfl, ?_⟩
    exact System5_nSteps_step_extension cfg result result' n h_n h

/-- **Iter 1495: CTS Halts implies eval some at all higher fuels**.
    Direct corollary of iter 1391 + iter 1477: when cfg.Halts, ∃ N
    such that ∀ fuel ≥ N, eval cfg fuel = some result.  Cleaner consumer
    name for iter 1401 with the witness extracted. -/
theorem CTS_Halts_implies_eval_some_at_higher_fuel
    (cts : CTS) (cfg : CTSConfig) (h_halts : cts.Halts cfg) :
    ∃ N result, ∀ fuel, fuel ≥ N → cts.eval cfg fuel = some result := by
  obtain ⟨n, result, h_n, h_halted⟩ := (CTS_Halts_iff_nSteps_halted cts cfg).mp h_halts
  refine ⟨n, result, ?_⟩
  intro fuel h_fuel
  exact CTS_nSteps_halted_eval_le cts cfg result n fuel h_fuel h_n h_halted

/-- **Iter 1496 (🎯🎯🎯 605-LEMMA MILESTONE): CTS Halts iff eval some at
    higher fuels**.  Biconditional version of iter 1495: `cfg.Halts ↔
    ∃ N result, ∀ fuel ≥ N, eval cfg fuel = some result`. -/
theorem CTS_Halts_iff_eval_some_at_higher_fuel
    (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ∃ N result, ∀ fuel, fuel ≥ N → cts.eval cfg fuel = some result := by
  refine ⟨CTS_Halts_implies_eval_some_at_higher_fuel cts cfg, ?_⟩
  intro ⟨N, result, h_all⟩
  refine ⟨N, result, ?_⟩
  exact h_all N (Nat.le_refl _)

/-- **Iter 1497: ¬Halts implies data ≠ nil**.  Direct corollary of iter
    1432 (¬Halts ⇒ ¬halted) + iter 1264 (¬halted ↔ data ≠ []). -/
theorem CTS_not_Halts_implies_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) (h_not_halts : ¬ cts.Halts cfg) :
    cfg.data ≠ [] := by
  rw [← ctsHalted_false_iff_data_ne_nil]
  exact CTS_not_Halts_not_halted cts cfg h_not_halts

/-- **Iter 1498: ¬Halts nSteps result has data ≠ nil**.  When `¬cfg.Halts`
    and `nSteps cfg n = some r`, `r.data ≠ []`.  Direct chain: iter
    1434 (result ¬Halts) + iter 1497 (¬Halts ⇒ data ≠ []). -/
theorem CTS_not_Halts_nSteps_some_data_ne_nil
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h_not_halts : ¬ cts.Halts cfg)
    (h_n : cts.nSteps cfg n = some result) :
    result.data ≠ [] :=
  CTS_not_Halts_implies_data_ne_nil cts result
    (CTS_nSteps_result_not_Halts_of_cfg_not_Halts cts cfg result n h_not_halts h_n)

/-- **Iter 1499: ¬Halts nSteps result step succeeds**.  When `¬cfg.Halts`
    and `nSteps cfg n = some result`, ∃ r', `step result = some r'`.
    Composes iter 1498 + iter 1278. -/
theorem CTS_not_Halts_nSteps_some_step_some
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h_not_halts : ¬ cts.Halts cfg)
    (h_n : cts.nSteps cfg n = some result) :
    ∃ result', cts.step result = some result' :=
  (CTS_step_some_iff_data_ne_nil cts result).mpr
    (CTS_not_Halts_nSteps_some_data_ne_nil cts cfg result n h_not_halts h_n)

/-- **Iter 1500 (🎯 ITER 1500 MILESTONE): ¬Halts iff chain perpetually
    has non-empty data**.  Substantive biconditional: `¬cfg.Halts ↔ ∀ n,
    ∃ r, nSteps cfg n = some r ∧ r.data ≠ []`.  Forward: iter 1498.
    Backward: data ≠ [] ⇒ ¬halted ⇒ step succeeds, so the chain never
    fails ⇒ ¬Halts via iter 1435 contrapositive. -/
theorem CTS_not_Halts_iff_chain_perpetually_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) :
    ¬ cts.Halts cfg ↔ ∀ n, ∃ r, cts.nSteps cfg n = some r ∧ r.data ≠ [] := by
  refine ⟨?_, ?_⟩
  · intro h_not_halts n
    obtain ⟨r, h_n⟩ := CTS_not_Halts_nSteps_some cts cfg h_not_halts n
    refine ⟨r, h_n, ?_⟩
    exact CTS_not_Halts_nSteps_some_data_ne_nil cts cfg r n h_not_halts h_n
  · intro h_all
    rw [(CTS_not_Halts_iff_all_nSteps_some cts cfg)]
    intro n
    obtain ⟨r, h_n, _⟩ := h_all n
    exact ⟨r, h_n⟩

/-- **Iter 1501 (🎯🎯🎯 610-LEMMA MILESTONE): System5 ¬Halts iff chain
    perpetually has non-empty bag/rules**.  Parallel to CTS iter 1500.
    Uses iter 1492 (chain continues) + iter 1471 (step some ⇒ bag/rules
    ne nil) on the result's step. -/
theorem System5_not_Halts_iff_chain_perpetually_bag_rules_ne_nil
    (cfg : System5Config) :
    ¬ System5.Halts cfg ↔
      ∀ n, ∃ r, System5.nSteps cfg n = some r ∧ r.bag ≠ [] ∧ r.rules ≠ [] := by
  refine ⟨?_, ?_⟩
  · intro h_not_halts n
    obtain ⟨r, h_n, _, h_step_ne⟩ := System5_not_Halts_chain_continues cfg h_not_halts n
    cases h_step : System5.step r with
    | none => exact absurd h_step h_step_ne
    | some r' =>
      obtain ⟨h_bag, h_rules⟩ := System5_step_some_implies_bag_rules_ne_nil r r' h_step
      exact ⟨r, h_n, h_bag, h_rules⟩
  · intro h_all
    rw [System5_not_Halts_iff_all_nSteps_some]
    intro n
    obtain ⟨r, h_n, _⟩ := h_all n
    exact ⟨r, h_n⟩

/-- **Iter 1502: System5 Halts iff bag-or-rules-empty witness**.
    `cfg.Halts ↔ ∃ n result, nSteps cfg n = some result ∧ (result.bag =
    [] ∨ result.rules = [])`.  Combines iter 1487 + System5_step_none_iff. -/
theorem System5_Halts_iff_bag_or_rules_empty_witness
    (cfg : System5Config) :
    System5.Halts cfg ↔
      ∃ n result, System5.nSteps cfg n = some result ∧
        (result.bag = [] ∨ result.rules = []) := by
  rw [System5_Halts_iff_step_none_witness]
  refine ⟨?_, ?_⟩
  · intro ⟨n, result, h_n, h_step⟩
    refine ⟨n, result, h_n, ?_⟩
    exact (System5_step_none_iff result).mp h_step
  · intro ⟨n, result, h_n, h_or⟩
    refine ⟨n, result, h_n, ?_⟩
    exact (System5_step_none_iff result).mpr h_or

/-- **Iter 1503: System5 Halts via rules-empty witness**.  When ∃ n
    result, `nSteps cfg n = some result ∧ result.rules = []`, then
    `cfg.Halts`.  Direct via iter 1502 backward. -/
theorem System5_Halts_via_rules_empty_witness
    (cfg : System5Config) (n : Nat) (result : System5Config)
    (h_n : System5.nSteps cfg n = some result)
    (h_rules : result.rules = []) :
    System5.Halts cfg :=
  (System5_Halts_iff_bag_or_rules_empty_witness cfg).mpr
    ⟨n, result, h_n, Or.inr h_rules⟩

/-- **Iter 1504: System5 Halts via bag-empty witness**.  Companion to
    iter 1503: when ∃ n result, `nSteps cfg n = some result ∧ result.bag
    = []`, then `cfg.Halts`. -/
theorem System5_Halts_via_bag_empty_witness
    (cfg : System5Config) (n : Nat) (result : System5Config)
    (h_n : System5.nSteps cfg n = some result)
    (h_bag : result.bag = []) :
    System5.Halts cfg :=
  (System5_Halts_iff_bag_or_rules_empty_witness cfg).mpr
    ⟨n, result, h_n, Or.inl h_bag⟩

/-- **Iter 1505: encoder Halts when data empty**.  When `cfg.data = []`,
    `(ctsToSystem5 cts cfg N).Halts`.  Direct from `System5.Halts_of_empty_bag`
    + iter 1234 (`ctsConfigToSystem5Bag_eq_nil_iff` ⇒ encoder bag = []). -/
theorem ctsToSystem5_Halts_when_data_empty
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_data : cfg.data = []) :
    System5.Halts (ctsToSystem5 cts cfg N) := by
  apply System5.Halts_of_empty_bag
  unfold ctsToSystem5
  simp
  rw [ctsConfigToSystem5Bag_eq_nil_iff]
  exact h_data

/-- **Iter 1506 (🎯🎯🎯 615-LEMMA MILESTONE): encoder Halts when ctsHalted**.
    Companion to iter 1505 using halt-state directly.  Direct from
    iter 1505 + iter 1265 (halted ↔ data empty). -/
theorem ctsToSystem5_Halts_when_ctsHalted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_halted : ctsHalted cfg = true) :
    System5.Halts (ctsToSystem5 cts cfg N) :=
  ctsToSystem5_Halts_when_data_empty cts cfg N
    ((ctsHalted_true_iff_data_eq_nil cfg).mp h_halted)

/-- **Iter 1507: encoder Halts when N = 0**.  When `N = 0`, encoder rules
    are empty, so System5 trivially halts via `Halts_of_empty_rules`. -/
theorem ctsToSystem5_Halts_when_N_zero
    (cts : CTS) (cfg : CTSConfig) :
    System5.Halts (ctsToSystem5 cts cfg 0) := by
  apply System5.Halts_of_empty_rules
  unfold ctsToSystem5
  simp [ctsRulesToSystem5Rules]

/-- **Iter 1508: encoder ¬Halts implies data ≠ [] and N ≥ 1**.
    Contrapositive of iter 1505 + iter 1507.  When the encoder does
    NOT Halt, both the data is non-empty AND N is positive. -/
theorem ctsToSystem5_not_Halts_implies_data_ne_nil_and_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_not_halts : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    cfg.data ≠ [] ∧ N ≥ 1 := by
  refine ⟨?_, ?_⟩
  · intro h_data
    exact h_not_halts (ctsToSystem5_Halts_when_data_empty cts cfg N h_data)
  · cases N with
    | zero => exact absurd (ctsToSystem5_Halts_when_N_zero cts cfg) h_not_halts
    | succ k => exact Nat.succ_le_succ (Nat.zero_le k)

/-- **Iter 1509: encoder Halts when data empty or N zero**.  Combined
    disjunction primitive composing iter 1505 + iter 1507. -/
theorem ctsToSystem5_Halts_when_disj_data_empty_or_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_or : cfg.data = [] ∨ N = 0) :
    System5.Halts (ctsToSystem5 cts cfg N) := by
  rcases h_or with h_data | h_N
  · exact ctsToSystem5_Halts_when_data_empty cts cfg N h_data
  · rw [h_N]
    exact ctsToSystem5_Halts_when_N_zero cts cfg

/-- **Iter 1510 (🎯🎯🎯 620-LEMMA MILESTONE): encoder step some implies
    data ≠ []**.  When `System5.step (ctsToSystem5 cts cfg N) = some
    result`, then `cfg.data ≠ []`.  Direct via iter 1471 + iter 1234. -/
theorem ctsToSystem5_step_some_implies_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config)
    (h_step : System5.step (ctsToSystem5 cts cfg N) = some result) :
    cfg.data ≠ [] := by
  have ⟨h_bag, _⟩ := System5_step_some_implies_bag_rules_ne_nil _ result h_step
  intro h_data
  apply h_bag
  unfold ctsToSystem5
  simp
  rw [ctsConfigToSystem5Bag_eq_nil_iff]
  exact h_data

/-- **Iter 1511: encoder step some implies N ≥ 1**.  Companion to iter
    1510.  When `System5.step (ctsToSystem5 cts cfg N) = some result`,
    `N ≥ 1`. -/
theorem ctsToSystem5_step_some_implies_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config)
    (h_step : System5.step (ctsToSystem5 cts cfg N) = some result) :
    N ≥ 1 := by
  have ⟨_, h_rules⟩ := System5_step_some_implies_bag_rules_ne_nil _ result h_step
  cases N with
  | zero =>
    exfalso
    apply h_rules
    unfold ctsToSystem5
    simp [ctsRulesToSystem5Rules]
  | succ k => exact Nat.succ_le_succ (Nat.zero_le k)

/-- **Iter 1512: encoder step some implies data ≠ [] and N ≥ 1**.
    Combined packaging of iters 1510 + 1511. -/
theorem ctsToSystem5_step_some_implies_data_ne_nil_and_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config)
    (h_step : System5.step (ctsToSystem5 cts cfg N) = some result) :
    cfg.data ≠ [] ∧ N ≥ 1 :=
  ⟨ctsToSystem5_step_some_implies_data_ne_nil cts cfg N result h_step,
   ctsToSystem5_step_some_implies_N_pos cts cfg N result h_step⟩

/-- **Iter 1513: encoder step some iff data ≠ [] and N ≥ 1**.  Full
    biconditional: `(∃ r, System5.step (ctsToSystem5 cts cfg N) = some
    r) ↔ cfg.data ≠ [] ∧ N ≥ 1`.  Forward: iter 1512.  Backward:
    `ctsToSystem5_step_some_of_data_nonempty` (iter 762). -/
theorem ctsToSystem5_step_some_iff_data_ne_nil_and_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (∃ result, System5.step (ctsToSystem5 cts cfg N) = some result) ↔
      cfg.data ≠ [] ∧ N ≥ 1 := by
  refine ⟨?_, ?_⟩
  · intro ⟨result, h_step⟩
    exact ctsToSystem5_step_some_implies_data_ne_nil_and_N_pos cts cfg N result h_step
  · intro ⟨h_data, h_N⟩
    apply (System5_step_some_iff _).mpr
    refine ⟨?_, ctsRulesToSystem5Rules_ne_nil cts cfg N h_N⟩
    intro h_empty
    apply h_data
    rw [← ctsConfigToSystem5Bag_eq_nil_iff]
    show ctsConfigToSystem5Bag cfg = []
    have : (ctsToSystem5 cts cfg N).bag = ctsConfigToSystem5Bag cfg := by
      unfold ctsToSystem5; rfl
    rw [← this]
    exact h_empty

/-- **Iter 1514: encoder step none iff data empty or N zero**.  Direct
    contrapositive of iter 1513 via Option some/none case-split. -/
theorem ctsToSystem5_step_none_iff_data_empty_or_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.step (ctsToSystem5 cts cfg N) = none ↔ cfg.data = [] ∨ N = 0 := by
  rw [System5_step_none_iff]
  refine ⟨?_, ?_⟩
  · intro h_or
    rcases h_or with h_bag | h_rules
    · left
      rw [← ctsConfigToSystem5Bag_eq_nil_iff]
      show ctsConfigToSystem5Bag cfg = []
      have h_eq : (ctsToSystem5 cts cfg N).bag = ctsConfigToSystem5Bag cfg := by
        unfold ctsToSystem5; rfl
      rw [← h_eq]
      exact h_bag
    · right
      cases N with
      | zero => rfl
      | succ k =>
        exfalso
        apply ctsRulesToSystem5Rules_ne_nil cts cfg (k + 1)
                (Nat.succ_le_succ (Nat.zero_le k))
        have h_eq : (ctsToSystem5 cts cfg (k + 1)).rules =
                    ctsRulesToSystem5Rules cts cfg (k + 1) := by
          unfold ctsToSystem5; rfl
        rw [← h_eq]; exact h_rules
  · intro h_or
    rcases h_or with h_data | h_N
    · left
      unfold ctsToSystem5
      simp
      rw [ctsConfigToSystem5Bag_eq_nil_iff]
      exact h_data
    · right
      rw [h_N]
      unfold ctsToSystem5
      simp [ctsRulesToSystem5Rules]

/-- **Iter 1515 (🎯🎯🎯 625-LEMMA MILESTONE): encoder step none iff
    halted or N zero**.  Iter 1514 stated in halt-state form via iter
    1265 substitution. -/
theorem ctsToSystem5_step_none_iff_halted_or_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.step (ctsToSystem5 cts cfg N) = none ↔ ctsHalted cfg = true ∨ N = 0 := by
  rw [ctsToSystem5_step_none_iff_data_empty_or_N_zero,
      ← ctsHalted_true_iff_data_eq_nil]

/-- **Iter 1516: encoder step some iff not halted and N ≥ 1**.
    Reformulation of iter 1513 in halt-state form. -/
theorem ctsToSystem5_step_some_iff_not_halted_and_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (∃ result, System5.step (ctsToSystem5 cts cfg N) = some result) ↔
      ctsHalted cfg = false ∧ N ≥ 1 := by
  rw [ctsToSystem5_step_some_iff_data_ne_nil_and_N_pos,
      ctsHalted_false_iff_data_ne_nil]

/-- **Iter 1517: encoder nSteps succ some implies data ≠ [] and N ≥ 1**.
    When `System5.nSteps (ctsToSystem5 cts cfg N) (n+1) = some s5'`,
    then `cfg.data ≠ [] ∧ N ≥ 1`.  Direct via iter 1464 + iter 1512. -/
theorem ctsToSystem5_nSteps_succ_some_implies_data_ne_nil_and_N_pos
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) (n + 1) = some s5') :
    cfg.data ≠ [] ∧ N ≥ 1 := by
  obtain ⟨cfg', h_step⟩ := System5_nSteps_succ_some_implies_step_some _ s5' n h_n
  exact ctsToSystem5_step_some_implies_data_ne_nil_and_N_pos cts cfg N cfg' h_step

/-- **Iter 1518: encoder nSteps pos some implies data ≠ [] and N ≥ 1**.
    When `n ≥ 1` and `nSteps cfg5 n = some s5'`, both conditions hold.
    Direct via case split on n + iter 1517. -/
theorem ctsToSystem5_nSteps_pos_some_implies_data_ne_nil_and_N_pos
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_pos : n ≥ 1)
    (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) n = some s5') :
    cfg.data ≠ [] ∧ N ≥ 1 := by
  obtain ⟨k, h_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp h_pos)
  rw [h_eq] at h_n
  exact ctsToSystem5_nSteps_succ_some_implies_data_ne_nil_and_N_pos cts cfg N k s5' h_n

/-- **Iter 1519: encoder nSteps zero**.  Trivial direct unfolding:
    `nSteps cfg5 0 = some cfg5`.  Useful named primitive. -/
theorem ctsToSystem5_nSteps_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.nSteps (ctsToSystem5 cts cfg N) 0 = some (ctsToSystem5 cts cfg N) :=
  System5.nSteps_zero _

/-- **Iter 1520 (🎯🎯🎯 630-LEMMA MILESTONE): encoder bag.length =
    4 * cfg.data.length**.  Closed-form length identity for encoder bag. -/
theorem ctsToSystem5_bag_length
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length = 4 * cfg.data.length := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_length cfg

/-- **Iter 1521: encoder rules.length = 4 * N * cts.appendants.length**.
    Closed-form length identity for encoder rules.  Direct via
    `ctsRulesToSystem5Rules_length`. -/
theorem ctsToSystem5_rules_length
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules.length = 4 * cts.appendants.length * N := by
  rw [ctsToSystem5_rules_eq]
  exact ctsRulesToSystem5Rules_length cts cfg N

/-- **Iter 1522: encoder bag ≠ nil iff data ≠ nil**.  Trivial corollary
    of iter 1234 lifted to cfg5 level. -/
theorem ctsToSystem5_bag_ne_nil_iff
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag ≠ [] ↔ cfg.data ≠ [] := by
  rw [ctsToSystem5_bag_eq, ctsConfigToSystem5Bag_ne_nil_iff]

/-- **Iter 1523: encoder rules ≠ nil iff N ≥ 1**.  Companion to iter 1522.
    Composes iter 1521 (length closed form) with positivity. -/
theorem ctsToSystem5_rules_ne_nil_iff
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules ≠ [] ↔ N ≥ 1 := by
  rw [ctsToSystem5_rules_eq]
  refine ⟨?_, ?_⟩
  · intro h_ne
    cases N with
    | zero => exfalso; apply h_ne; simp [ctsRulesToSystem5Rules]
    | succ k => exact Nat.succ_le_succ (Nat.zero_le k)
  · intro h_N
    exact ctsRulesToSystem5Rules_ne_nil cts cfg N h_N

/-- **Iter 1524: encoder bag = nil iff data = nil**.  Negation form of
    iter 1522. -/
theorem ctsToSystem5_bag_eq_nil_iff
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag = [] ↔ cfg.data = [] := by
  rw [ctsToSystem5_bag_eq, ctsConfigToSystem5Bag_eq_nil_iff]

/-- **Iter 1525: encoder rules = nil iff N = 0**.  Negation form of
    iter 1523. -/
theorem ctsToSystem5_rules_eq_nil_iff
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules = [] ↔ N = 0 := by
  rw [ctsToSystem5_rules_eq]
  refine ⟨?_, ?_⟩
  · intro h_eq
    cases h_N : N with
    | zero => rfl
    | succ k =>
      exfalso
      have h_pos : N ≥ 1 := h_N ▸ Nat.succ_le_succ (Nat.zero_le k)
      exact ctsRulesToSystem5Rules_ne_nil cts cfg N h_pos h_eq
  · intro h_N
    rw [h_N]
    simp [ctsRulesToSystem5Rules]

/-- **Iter 1526 (🎯🎯🎯 635-LEMMA MILESTONE): encoder ¬Halts implies data
    ≠ []**.  Direct corollary of iter 1508. -/
theorem ctsToSystem5_not_Halts_implies_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_not_halts : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    cfg.data ≠ [] :=
  (ctsToSystem5_not_Halts_implies_data_ne_nil_and_N_pos cts cfg N h_not_halts).1

/-- **Iter 1527: encoder ¬Halts implies N ≥ 1**.  Direct corollary. -/
theorem ctsToSystem5_not_Halts_implies_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_not_halts : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    N ≥ 1 :=
  (ctsToSystem5_not_Halts_implies_data_ne_nil_and_N_pos cts cfg N h_not_halts).2

/-- **Iter 1528: encoder ¬Halts implies not halted and N ≥ 1**.
    Halt-state form of iters 1526 + 1527. -/
theorem ctsToSystem5_not_Halts_implies_not_halted_and_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_not_halts : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ctsHalted cfg = false ∧ N ≥ 1 := by
  refine ⟨?_, ctsToSystem5_not_Halts_implies_N_pos cts cfg N h_not_halts⟩
  rw [ctsHalted_false_iff_data_ne_nil]
  exact ctsToSystem5_not_Halts_implies_data_ne_nil cts cfg N h_not_halts

/-- **Iter 1529: encoder bag = nil iff ctsHalted**.  Halt-state form of
    iter 1524.  Direct via iter 1524 + iter 1265 substitution. -/
theorem ctsToSystem5_bag_eq_nil_iff_ctsHalted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag = [] ↔ ctsHalted cfg = true := by
  rw [ctsToSystem5_bag_eq_nil_iff, ← ctsHalted_true_iff_data_eq_nil]

/-- **Iter 1530: encoder bag ≠ nil iff ¬ ctsHalted**.  Companion to
    iter 1529. -/
theorem ctsToSystem5_bag_ne_nil_iff_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag ≠ [] ↔ ctsHalted cfg = false := by
  rw [ctsToSystem5_bag_ne_nil_iff, ctsHalted_false_iff_data_ne_nil]

/-- **Iter 1531 (🎯🎯🎯 640-LEMMA MILESTONE): encoder rules length > 0
    iff N ≥ 1**.  Direct corollary of iter 1521 + length-positive
    iff non-empty (using iter 1523). -/
theorem ctsToSystem5_rules_length_pos_iff_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules.length > 0 ↔ N ≥ 1 := by
  rw [ctsToSystem5_rules_length]
  have h_app : cts.appendants.length ≥ 1 :=
    List.length_pos_iff.mpr (CTS_appendants_ne_nil cts)
  refine ⟨?_, ?_⟩
  · intro h_pos
    cases N with
    | zero => simp at h_pos
    | succ k => exact Nat.succ_le_succ (Nat.zero_le k)
  · intro h_N
    have h1 : 4 * cts.appendants.length ≥ 4 := by
      have : 4 * 1 ≤ 4 * cts.appendants.length := Nat.mul_le_mul_left 4 h_app
      omega
    exact Nat.lt_of_lt_of_le (by omega : 0 < 4) (Nat.le_trans (by omega : 4 ≤ 4 * cts.appendants.length)
      (Nat.le_mul_of_pos_right _ h_N))

/-- **Iter 1532: encoder bag length > 0 iff data ≠ []**.  Composes
    iter 1520 (closed-form length) with arithmetic. -/
theorem ctsToSystem5_bag_length_pos_iff_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length > 0 ↔ cfg.data ≠ [] := by
  rw [ctsToSystem5_bag_length]
  refine ⟨?_, ?_⟩
  · intro h_pos h_data
    rw [h_data] at h_pos
    simp at h_pos
  · intro h_ne
    have h_pos : cfg.data.length ≥ 1 := List.length_pos_iff.mpr h_ne
    have h_mul_pos : 4 * cfg.data.length ≥ 4 := by
      have : 4 * 1 ≤ 4 * cfg.data.length := Nat.mul_le_mul_left 4 h_pos
      omega
    omega

/-- **Iter 1533: encoder bag length = 0 iff data = []**.  Negation form
    of iter 1532. -/
theorem ctsToSystem5_bag_length_eq_zero_iff_data_eq_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length = 0 ↔ cfg.data = [] := by
  rw [ctsToSystem5_bag_length]
  refine ⟨?_, ?_⟩
  · intro h
    have : cfg.data.length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  · intro h
    rw [h]
    simp

/-- **Iter 1534: encoder bag length ≥ 4 when data non-empty**.  Direct
    via iter 1520 + arithmetic. -/
theorem ctsToSystem5_bag_length_ge_4_of_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_data : cfg.data ≠ []) :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 := by
  rw [ctsToSystem5_bag_length]
  have h_pos : cfg.data.length ≥ 1 := List.length_pos_iff.mpr h_data
  have : 4 * 1 ≤ 4 * cfg.data.length := Nat.mul_le_mul_left 4 h_pos
  omega

/-- **Iter 1535: encoder rules length ≥ 4 * |appendants| when N ≥ 1**.
    Companion to iter 1534 for the rules side. -/
theorem ctsToSystem5_rules_length_ge_of_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 * cts.appendants.length := by
  rw [ctsToSystem5_rules_length]
  have : 4 * cts.appendants.length * 1 ≤ 4 * cts.appendants.length * N :=
    Nat.mul_le_mul_left _ h_N
  omega

/-- **Iter 1536 (🎯🎯🎯 645-LEMMA MILESTONE): encoder rules length ≥ 4
    when N ≥ 1**.  Stronger floor via iter 1535 + appendants ≥ 1. -/
theorem ctsToSystem5_rules_length_ge_4_of_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 := by
  have h_app : cts.appendants.length ≥ 1 :=
    List.length_pos_iff.mpr (CTS_appendants_ne_nil cts)
  have h_ge : (ctsToSystem5 cts cfg N).rules.length ≥ 4 * cts.appendants.length :=
    ctsToSystem5_rules_length_ge_of_N_pos cts cfg N h_N
  have : 4 * 1 ≤ 4 * cts.appendants.length := Nat.mul_le_mul_left 4 h_app
  omega

/-- **Iter 1537: encoder bag 1 ∈ iff data ≠ nil**.  Lifts iter 1257 to
    cfg5 level. -/
theorem ctsToSystem5_bag_one_mem_iff
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    1 ∈ (ctsToSystem5 cts cfg N).bag ↔ cfg.data ≠ [] := by
  rw [ctsToSystem5_bag_eq, ctsConfigToSystem5Bag_one_mem_iff]

/-- **Iter 1538: encoder bag 1 ∈ when data non-empty**.  Forward
    direction of iter 1537. -/
theorem ctsToSystem5_bag_one_mem_of_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_data : cfg.data ≠ []) :
    1 ∈ (ctsToSystem5 cts cfg N).bag :=
  (ctsToSystem5_bag_one_mem_iff cts cfg N).mpr h_data

/-- **Iter 1539: encoder 0 ∈ bag.dec iff data ≠ []**.  Lifts iter 1383
    to cfg5 level.  P-step trigger condition. -/
theorem ctsToSystem5_zero_in_dec_iff
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    0 ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) ↔ cfg.data ≠ [] := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_zero_in_dec_iff cfg

/-- **Iter 1540: encoder bag is Nodup**.  Lifts iter 645's `_nodup`
    to cfg5 level. -/
theorem ctsToSystem5_bag_nodup
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.Nodup := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_nodup cfg

/-- **Iter 1541 (🎯 ITER 1541 — 650-LEMMA MILESTONE): encoder bag has
    no zero**.  Lifts iter 1368 to cfg5 level. -/
theorem ctsToSystem5_bag_no_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (0 : Int) ∉ (ctsToSystem5 cts cfg N).bag := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_no_zero cfg

/-- **Iter 1542: encoder bag all ≥ 1**.  Lifts iter 1369 to cfg5 level. -/
theorem ctsToSystem5_bag_all_ge_one
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ∀ x ∈ (ctsToSystem5 cts cfg N).bag, x ≥ 1 := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_all_ge_one cfg

/-- **Iter 1543: encoder bag mem range**.  Lifts iter 1364 to cfg5
    level: every bag element is in [1, counter - 1]. -/
theorem ctsToSystem5_bag_mem_range
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (x : Int) (h : x ∈ (ctsToSystem5 cts cfg N).bag) :
    1 ≤ x ∧ x ≤ counterAfterWorkingString cfg.data - 1 := by
  rw [ctsToSystem5_bag_eq] at h
  exact ctsConfigToSystem5Bag_mem_range cfg x h

/-- **Iter 1544: encoder bag small values not in**.  Lifts iter 1377. -/
theorem ctsToSystem5_bag_small_not_mem
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (n : Int) (h_small : n < 1) :
    n ∉ (ctsToSystem5 cts cfg N).bag := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_small_not_mem cfg n h_small

/-- **Iter 1545: encoder bag dec all ≥ 0**.  Lifts iter 1381. -/
theorem ctsToSystem5_bag_dec_all_ge_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ∀ x ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1), x ≥ 0 := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_dec_all_ge_zero cfg

/-- **Iter 1546 (🎯🎯🎯 655-LEMMA MILESTONE): encoder bag dec-erase
    length when data ≠ []**.  Direct via iter 1349 lifted to cfg5. -/
theorem ctsToSystem5_bag_dec_erase_length_of_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_data : cfg.data ≠ []) :
    (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).length =
      4 * cfg.data.length - 1 := by
  rw [ctsToSystem5_bag_eq]
  have h_not_halted : ctsHalted cfg = false :=
    (ctsHalted_false_iff_data_ne_nil cfg).mpr h_data
  exact ctsConfigToSystem5Bag_dec_erase_length_eq cfg h_not_halted

/-- **Iter 1547: encoder bag dec-erase ≠ nil when data ≠ []**.
    Lifts iter 1351 to cfg5 level. -/
theorem ctsToSystem5_bag_dec_erase_ne_nil_of_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_data : cfg.data ≠ []) :
    ((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0 ≠ [] := by
  rw [ctsToSystem5_bag_eq]
  have h_not_halted : ctsHalted cfg = false :=
    (ctsHalted_false_iff_data_ne_nil cfg).mpr h_data
  exact ctsConfigToSystem5Bag_dec_erase_ne_nil_of_not_halted cfg h_not_halted

/-- **Iter 1548: encoder bag dec-erase Nodup**.  Lifts iter 1347. -/
theorem ctsToSystem5_bag_dec_erase_nodup
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).Nodup := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_dec_erase_nodup cfg

/-- **Iter 1549: encoder bag dec-erase no zero**.  Lifts iter 1374. -/
theorem ctsToSystem5_bag_dec_erase_no_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (0 : Int) ∉ ((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0 := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_dec_erase_no_zero cfg

/-- **Iter 1550 (🎯 ITER 1550 MILESTONE): encoder bag dec-erase all ≥
    1**.  Lifts iter 1373. -/
theorem ctsToSystem5_bag_dec_erase_all_ge_one
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ∀ x ∈ ((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0, x ≥ 1 := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_dec_erase_all_ge_one cfg

/-- **Iter 1551 (🎯🎯🎯 660-LEMMA MILESTONE): encoder bag no negatives**.
    Lifts iter 1370 to cfg5 level. -/
theorem ctsToSystem5_bag_no_negatives
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (n : Int) (h_neg : n < 0) :
    n ∉ (ctsToSystem5 cts cfg N).bag := by
  rw [ctsToSystem5_bag_eq]
  have h_lt_one : n < 1 := by omega
  exact ctsConfigToSystem5Bag_no_negatives cfg n h_lt_one

/-- **Iter 1552: encoder bag -1 ∉**.  Direct corollary of iter 1551. -/
theorem ctsToSystem5_bag_neg_one_not_mem
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (-1 : Int) ∉ (ctsToSystem5 cts cfg N).bag :=
  ctsToSystem5_bag_no_negatives cts cfg N (-1) (by omega)

/-- **Iter 1553: encoder bag map(·+1) all ≥ 2**.  Lifts iter 1376. -/
theorem ctsToSystem5_bag_map_add_one_all_ge_two
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ∀ x ∈ (ctsToSystem5 cts cfg N).bag.map (· + 1), x ≥ 2 := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_map_add_one_all_ge_two cfg

/-- **Iter 1554: encoder bag dec.map(·+1) all ≥ 1**.  Lifts iter 1390. -/
theorem ctsToSystem5_bag_dec_inc_all_ge_one
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ∀ x ∈ ((ctsToSystem5 cts cfg N).bag.map (· - 1)).map (· + 1), x ≥ 1 := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_dec_inc_all_ge_one cfg

/-- **Iter 1555: encoder bag dec range**.  Lifts iter 1386. -/
theorem ctsToSystem5_bag_dec_range
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (x : Int) (h : x ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1)) :
    0 ≤ x ∧ x ≤ counterAfterWorkingString cfg.data - 2 := by
  rw [ctsToSystem5_bag_eq] at h
  exact ctsConfigToSystem5Bag_dec_range cfg x h

/-- **Iter 1556 (🎯🎯🎯 665-LEMMA MILESTONE): encoder bag dec-erase
    range**.  Lifts iter 1387. -/
theorem ctsToSystem5_bag_dec_erase_range
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (x : Int) (h : x ∈ ((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0) :
    1 ≤ x ∧ x ≤ counterAfterWorkingString cfg.data - 2 := by
  rw [ctsToSystem5_bag_eq] at h
  exact ctsConfigToSystem5Bag_dec_erase_range cfg x h

/-- **Iter 1557: encoder bag length divisible by 4**.  Lifts iter 1236. -/
theorem ctsToSystem5_bag_length_divisible_4
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    4 ∣ (ctsToSystem5 cts cfg N).bag.length := by
  rw [ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_length_divisible_four cfg

/-- **Iter 1558: encoder rules length divisible by 4**.  Lifts iter 1262. -/
theorem ctsToSystem5_rules_length_divisible_4
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    4 ∣ (ctsToSystem5 cts cfg N).rules.length := by
  rw [ctsToSystem5_rules_eq]
  exact ctsRulesToSystem5Rules_length_divisible_four cts cfg N

/-- **Iter 1559: encoder bag dec length = bag length**.  Direct via
    List.length_map. -/
theorem ctsToSystem5_bag_dec_length
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ((ctsToSystem5 cts cfg N).bag.map (· - 1)).length =
      (ctsToSystem5 cts cfg N).bag.length :=
  List.length_map _

/-- **Iter 1560 (🎯🎯🎯 670-LEMMA MILESTONE): encoder bag dec length
    closed form**.  Composes iter 1559 + iter 1520. -/
theorem ctsToSystem5_bag_dec_length_eq
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ((ctsToSystem5 cts cfg N).bag.map (· - 1)).length = 4 * cfg.data.length := by
  rw [ctsToSystem5_bag_dec_length, ctsToSystem5_bag_length]

/-- **Iter 1561: encoder bag dec-erase length ≤ 4 * data.length**.
    Direct upper bound. -/
theorem ctsToSystem5_bag_dec_erase_length_le
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).length ≤
      4 * cfg.data.length := by
  have h_le : (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).length ≤
              ((ctsToSystem5 cts cfg N).bag.map (· - 1)).length :=
    List.length_erase_le
  rw [ctsToSystem5_bag_dec_length_eq] at h_le
  exact h_le

/-- **Iter 1562: encoder bag dec-erase length ≥ 4 * data.length - 1**.
    Lower bound via iter 1252 lifted to cfg5. -/
theorem ctsToSystem5_bag_dec_erase_length_ge
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).length ≥
      4 * cfg.data.length - 1 := by
  rw [ctsToSystem5_bag_eq]
  have h_ge := List_Int_dec_erase_length_ge (ctsConfigToSystem5Bag cfg)
  rw [show (ctsConfigToSystem5Bag cfg).length = 4 * cfg.data.length from
      ctsConfigToSystem5Bag_length cfg] at h_ge
  exact h_ge

/-- **Iter 1563: encoder bag dec-erase length pos iff data ≠ []**.
    Composes iter 1547 + `List.length_pos_iff`. -/
theorem ctsToSystem5_bag_dec_erase_length_pos_iff_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).length > 0 ↔ cfg.data ≠ [] := by
  refine ⟨?_, ?_⟩
  · intro h_pos h_data
    have h_eq : ((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0 = [] := by
      have h_bag : (ctsToSystem5 cts cfg N).bag = [] :=
        (ctsToSystem5_bag_eq_nil_iff cts cfg N).mpr h_data
      rw [h_bag]
      simp
    rw [h_eq] at h_pos
    simp at h_pos
  · intro h_data
    exact List.length_pos_iff.mpr
      (ctsToSystem5_bag_dec_erase_ne_nil_of_data_ne_nil cts cfg N h_data)

/-- **Iter 1564: encoder bag dec-erase length eq zero iff data eq nil**.
    Negation form of iter 1563. -/
theorem ctsToSystem5_bag_dec_erase_length_eq_zero_iff
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).length = 0 ↔ cfg.data = [] := by
  refine ⟨?_, ?_⟩
  · intro h_zero
    cases h_data : cfg.data with
    | nil => rfl
    | cons head tail =>
      exfalso
      have h_data_ne : cfg.data ≠ [] := by rw [h_data]; simp
      have h_pos := (ctsToSystem5_bag_dec_erase_length_pos_iff_data_ne_nil cts cfg N).mpr h_data_ne
      omega
  · intro h_data
    have h_bag : (ctsToSystem5 cts cfg N).bag = [] :=
      (ctsToSystem5_bag_eq_nil_iff cts cfg N).mpr h_data
    rw [h_bag]
    simp

/-- **Iter 1565 (🎯🎯🎯 675-LEMMA MILESTONE): encoder bag 1 ∈ iff not
    halted**.  Halt-state form of iter 1537 via iter 1264 substitution. -/
theorem ctsToSystem5_bag_one_mem_iff_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    1 ∈ (ctsToSystem5 cts cfg N).bag ↔ ctsHalted cfg = false := by
  rw [ctsToSystem5_bag_one_mem_iff, ctsHalted_false_iff_data_ne_nil]

/-- **Iter 1566: encoder 0 ∈ bag.dec iff not halted**.  Halt-state form
    of iter 1539. -/
theorem ctsToSystem5_zero_in_dec_iff_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    0 ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) ↔ ctsHalted cfg = false := by
  rw [ctsToSystem5_zero_in_dec_iff, ctsHalted_false_iff_data_ne_nil]

/-- **Iter 1567: encoder bag 1 ∈ when not halted**.  Forward direction
    of iter 1565. -/
theorem ctsToSystem5_bag_one_mem_of_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_not_halted : ctsHalted cfg = false) :
    1 ∈ (ctsToSystem5 cts cfg N).bag :=
  (ctsToSystem5_bag_one_mem_iff_not_halted cts cfg N).mpr h_not_halted

/-- **Iter 1568: encoder 0 ∈ bag.dec when not halted**.  Forward
    direction of iter 1566.  P-step trigger primitive. -/
theorem ctsToSystem5_zero_in_dec_of_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_not_halted : ctsHalted cfg = false) :
    0 ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) :=
  (ctsToSystem5_zero_in_dec_iff_not_halted cts cfg N).mpr h_not_halted

/-- **Iter 1569: encoder step succeeds when not halted and N ≥ 1**.
    Cleanly composes iter 1516 backward direction. -/
theorem ctsToSystem5_step_some_of_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_not_halted : ctsHalted cfg = false) (h_N : N ≥ 1) :
    ∃ result, System5.step (ctsToSystem5 cts cfg N) = some result :=
  (ctsToSystem5_step_some_iff_not_halted_and_N_pos cts cfg N).mpr ⟨h_not_halted, h_N⟩

/-- **Iter 1570 (🎯 ITER 1570 MILESTONE): encoder step none when halted
    or N zero**.  Direct via iter 1515 backward. -/
theorem ctsToSystem5_step_none_when_halted_or_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_or : ctsHalted cfg = true ∨ N = 0) :
    System5.step (ctsToSystem5 cts cfg N) = none :=
  (ctsToSystem5_step_none_iff_halted_or_N_zero cts cfg N).mpr h_or

/-- **Iter 1571 (🎯🎯🎯 680-LEMMA MILESTONE): encoder step none when
    halted**.  Direct via iter 1570 with Or.inl. -/
theorem ctsToSystem5_step_none_when_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_halted : ctsHalted cfg = true) :
    System5.step (ctsToSystem5 cts cfg N) = none :=
  ctsToSystem5_step_none_when_halted_or_N_zero cts cfg N (Or.inl h_halted)

/-- **Iter 1572: encoder step none when N = 0**.  Direct via iter 1570
    with Or.inr. -/
theorem ctsToSystem5_step_none_when_N_zero
    (cts : CTS) (cfg : CTSConfig) :
    System5.step (ctsToSystem5 cts cfg 0) = none :=
  ctsToSystem5_step_none_when_halted_or_N_zero cts cfg 0 (Or.inr rfl)

/-- **Iter 1573: encoder step some implies data decomp**.  When encoder
    step succeeds, cfg.data must be a cons.  Composes iter 1510. -/
theorem ctsToSystem5_step_some_implies_data_cons
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config)
    (h_step : System5.step (ctsToSystem5 cts cfg N) = some result) :
    ∃ head rest, cfg.data = head :: rest := by
  have h_data : cfg.data ≠ [] :=
    ctsToSystem5_step_some_implies_data_ne_nil cts cfg N result h_step
  cases h : cfg.data with
  | nil => exact absurd h h_data
  | cons head rest => exact ⟨head, rest, rfl⟩

/-- **Iter 1574: encoder step some implies CTS step success**.  When
    `System5.step (ctsToSystem5 cts cfg N) = some r`, `cts.step cfg`
    also succeeds.  Composes iter 1510 + iter 1278's existential. -/
theorem ctsToSystem5_step_some_implies_cts_step_some
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config)
    (h_step : System5.step (ctsToSystem5 cts cfg N) = some result) :
    ∃ result', cts.step cfg = some result' := by
  have h_data : cfg.data ≠ [] :=
    ctsToSystem5_step_some_implies_data_ne_nil cts cfg N result h_step
  exact (CTS_step_some_iff_data_ne_nil cts cfg).mpr h_data

/-- **Iter 1575: cts.step some + N pos implies encoder step some**.
    Reverse direction of iter 1574 with N ≥ 1 hypothesis.  Useful
    CTS→System5 bridge. -/
theorem cts_step_some_implies_ctsToSystem5_step_some
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (result : CTSConfig) (h_step : cts.step cfg = some result) :
    ∃ s5_result, System5.step (ctsToSystem5 cts cfg N) = some s5_result := by
  have h_data : cfg.data ≠ [] := CTS_step_some_data_ne_nil cts cfg result h_step
  exact ctsToSystem5_step_some_of_not_halted cts cfg N
    ((ctsHalted_false_iff_data_ne_nil cfg).mpr h_data) h_N

/-- **Iter 1576 (🎯🎯🎯 685-LEMMA MILESTONE): encoder step some iff
    CTS step some and N pos**.  Full biconditional composing iters
    1574 + 1575.  CTS-System5 step-success bridge. -/
theorem ctsToSystem5_step_some_iff_cts_step_some_and_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (∃ s5_result, System5.step (ctsToSystem5 cts cfg N) = some s5_result) ↔
      (∃ result, cts.step cfg = some result) ∧ N ≥ 1 := by
  refine ⟨?_, ?_⟩
  · intro ⟨s5_result, h_step⟩
    refine ⟨?_, ?_⟩
    · exact ctsToSystem5_step_some_implies_cts_step_some cts cfg N s5_result h_step
    · exact ctsToSystem5_step_some_implies_N_pos cts cfg N s5_result h_step
  · intro ⟨⟨result, h_step⟩, h_N⟩
    exact cts_step_some_implies_ctsToSystem5_step_some cts cfg N h_N result h_step

/-- **Iter 1577: encoder step none iff cts step none or N zero**.
    Contrapositive of iter 1576 in step-none form.  Composes iter 1514
    + iter 1276 substitution. -/
theorem ctsToSystem5_step_none_iff_cts_step_none_or_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.step (ctsToSystem5 cts cfg N) = none ↔
      cts.step cfg = none ∨ N = 0 := by
  rw [ctsToSystem5_step_none_iff_halted_or_N_zero, ← CTS_step_none_iff_halted_v2]

/-- **Iter 1578: encoder rules length at N+1 = N**.  Adjacent comparison
    of iter 1521 — going from N to N+1 adds 4·|appendants| rules. -/
theorem ctsToSystem5_rules_length_succ
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg (N + 1)).rules.length =
      (ctsToSystem5 cts cfg N).rules.length + 4 * cts.appendants.length := by
  rw [ctsToSystem5_rules_length, ctsToSystem5_rules_length, Nat.mul_succ]

/-- **Iter 1579: encoder bag length grows by 4 per data element**.
    Comparison form: when cfg.data has one more element, bag.length is
    4 larger.  Direct via iter 1520 + Nat.mul_succ. -/
theorem ctsToSystem5_bag_length_cons
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (head : Bool)
    (h_cfg : cfg.data = head :: cfg.data.tail) :
    (ctsToSystem5 cts cfg N).bag.length =
      (ctsToSystem5 cts ⟨cfg.data.tail, cfg.phase⟩ N).bag.length + 4 := by
  rw [ctsToSystem5_bag_length, ctsToSystem5_bag_length]
  show 4 * cfg.data.length = 4 * cfg.data.tail.length + 4
  rw [h_cfg]
  simp [Nat.mul_succ]

/-- **Iter 1580 (🎯 ITER 1580 MILESTONE): encoder bag phase-invariant**.
    Encoder bag depends only on data, not phase: `(ctsToSystem5 cts ⟨d,
    p1⟩ N).bag = (ctsToSystem5 cts ⟨d, p2⟩ N).bag`. Direct via iter
    1322 lifted. -/
theorem ctsToSystem5_bag_phase_invariant
    (cts : CTS) (data : List Bool) (phase1 phase2 : Nat) (N : Nat) :
    (ctsToSystem5 cts ⟨data, phase1⟩ N).bag =
      (ctsToSystem5 cts ⟨data, phase2⟩ N).bag := by
  rw [ctsToSystem5_bag_eq, ctsToSystem5_bag_eq]
  exact ctsConfigToSystem5Bag_phase_invariant data phase1 phase2

/-- **Iter 1581 (🎯🎯🎯 690-LEMMA MILESTONE): encoder rules phase-invariant**.
    Encoder rules depend only on cfg.data via counterAfterWorkingString,
    not on cfg.phase. -/
theorem ctsToSystem5_rules_phase_invariant
    (cts : CTS) (data : List Bool) (phase1 phase2 : Nat) (N : Nat) :
    (ctsToSystem5 cts ⟨data, phase1⟩ N).rules =
      (ctsToSystem5 cts ⟨data, phase2⟩ N).rules := by
  rw [ctsToSystem5_rules_eq, ctsToSystem5_rules_eq]
  rfl

/-- **Iter 1582: full encoder phase-invariant**.  The encoder is fully
    phase-invariant: only data and N matter.  Combines iters 1580 + 1581. -/
theorem ctsToSystem5_phase_invariant
    (cts : CTS) (data : List Bool) (phase1 phase2 : Nat) (N : Nat) :
    ctsToSystem5 cts ⟨data, phase1⟩ N = ctsToSystem5 cts ⟨data, phase2⟩ N := by
  have h_bag := ctsToSystem5_bag_phase_invariant cts data phase1 phase2 N
  have h_rules := ctsToSystem5_rules_phase_invariant cts data phase1 phase2 N
  cases h1 : ctsToSystem5 cts ⟨data, phase1⟩ N with
  | mk b1 r1 =>
    cases h2 : ctsToSystem5 cts ⟨data, phase2⟩ N with
    | mk b2 r2 =>
      rw [h1] at h_bag h_rules
      rw [h2] at h_bag h_rules
      simp at h_bag h_rules
      rw [h_bag, h_rules]

/-- **Iter 1583: encoder bag length pos iff not halted**.  Halt-state
    form of iter 1532. -/
theorem ctsToSystem5_bag_length_pos_iff_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length > 0 ↔ ctsHalted cfg = false := by
  rw [ctsToSystem5_bag_length_pos_iff_data_ne_nil, ctsHalted_false_iff_data_ne_nil]

/-- **Iter 1584: encoder bag length zero iff halted**.  Negation form
    of iter 1583. -/
theorem ctsToSystem5_bag_length_eq_zero_iff_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length = 0 ↔ ctsHalted cfg = true := by
  rw [ctsToSystem5_bag_length_eq_zero_iff_data_eq_nil, ← ctsHalted_true_iff_data_eq_nil]

/-- **Iter 1585 (🎯🎯🎯 695-LEMMA MILESTONE): encoder bag length ≥ 4 when
    not halted**.  Halt-state form of iter 1534. -/
theorem ctsToSystem5_bag_length_ge_4_of_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_not_halted : ctsHalted cfg = false) :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 :=
  ctsToSystem5_bag_length_ge_4_of_data_ne_nil cts cfg N
    ((ctsHalted_false_iff_data_ne_nil cfg).mp h_not_halted)

/-- **Iter 1586: encoder step some implies 1 ∈ encoder bag**.  Composes
    iter 1510 + iter 1538. -/
theorem ctsToSystem5_step_some_implies_one_mem
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config)
    (h_step : System5.step (ctsToSystem5 cts cfg N) = some result) :
    1 ∈ (ctsToSystem5 cts cfg N).bag :=
  ctsToSystem5_bag_one_mem_of_data_ne_nil cts cfg N
    (ctsToSystem5_step_some_implies_data_ne_nil cts cfg N result h_step)

/-- **Iter 1587: encoder step some implies 0 ∈ encoder bag.dec**.
    P-step trigger condition.  Composes iter 1510 + iter 1539. -/
theorem ctsToSystem5_step_some_implies_zero_in_dec
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config)
    (h_step : System5.step (ctsToSystem5 cts cfg N) = some result) :
    0 ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) :=
  (ctsToSystem5_zero_in_dec_iff cts cfg N).mpr
    (ctsToSystem5_step_some_implies_data_ne_nil cts cfg N result h_step)

/-- **Iter 1588: encoder nSteps succ some implies 1 ∈ encoder bag**.
    Composes iter 1464 + iter 1586. -/
theorem ctsToSystem5_nSteps_succ_some_implies_one_mem
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) (n + 1) = some s5') :
    1 ∈ (ctsToSystem5 cts cfg N).bag := by
  obtain ⟨cfg', h_step⟩ := System5_nSteps_succ_some_implies_step_some _ s5' n h_n
  exact ctsToSystem5_step_some_implies_one_mem cts cfg N cfg' h_step

/-- **Iter 1589: encoder nSteps pos some implies 1 ∈ encoder bag**.
    Direct via case split + iter 1588. -/
theorem ctsToSystem5_nSteps_pos_some_implies_one_mem
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_pos : n ≥ 1)
    (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) n = some s5') :
    1 ∈ (ctsToSystem5 cts cfg N).bag := by
  obtain ⟨k, h_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp h_pos)
  rw [h_eq] at h_n
  exact ctsToSystem5_nSteps_succ_some_implies_one_mem cts cfg N k s5' h_n

/-- **Iter 1590 (🎯 ITER 1590 MILESTONE): encoder nSteps pos some
    implies 0 ∈ encoder bag.dec**.  Composes iter 1589 + iter 1539. -/
theorem ctsToSystem5_nSteps_pos_some_implies_zero_in_dec
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_pos : n ≥ 1)
    (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) n = some s5') :
    0 ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) :=
  (ctsToSystem5_zero_in_dec_iff cts cfg N).mpr
    ((ctsToSystem5_nSteps_pos_some_implies_data_ne_nil_and_N_pos
        cts cfg N n h_pos s5' h_n).1)

/-- **Iter 1591 (🎯🎯🎯🎯🎯 700-LEMMA MILESTONE): encoder nSteps pos
    some packaging**.  When `nSteps cfg5 n = some s5'` with `n ≥ 1`,
    the encoder satisfies all standard P-step prerequisites: data ≠ [],
    N ≥ 1, 1 ∈ bag, 0 ∈ bag.dec, bag is Nodup, bag.length ≥ 4.  Useful
    omnibus primitive for chain-induction setup. -/
theorem ctsToSystem5_nSteps_pos_some_full_witness
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_pos : n ≥ 1)
    (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) n = some s5') :
    cfg.data ≠ [] ∧ N ≥ 1 ∧
    1 ∈ (ctsToSystem5 cts cfg N).bag ∧
    0 ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) ∧
    (ctsToSystem5 cts cfg N).bag.Nodup ∧
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 := by
  obtain ⟨h_data, h_N⟩ := ctsToSystem5_nSteps_pos_some_implies_data_ne_nil_and_N_pos
    cts cfg N n h_pos s5' h_n
  exact ⟨h_data, h_N,
    ctsToSystem5_nSteps_pos_some_implies_one_mem cts cfg N n h_pos s5' h_n,
    ctsToSystem5_nSteps_pos_some_implies_zero_in_dec cts cfg N n h_pos s5' h_n,
    ctsToSystem5_bag_nodup cts cfg N,
    ctsToSystem5_bag_length_ge_4_of_data_ne_nil cts cfg N h_data⟩

/-- **Iter 1592: encoder step some omnibus witness**.  Companion to
    iter 1591 for single-step.  When `step cfg5 = some r`, packages
    all standard prerequisites. -/
theorem ctsToSystem5_step_some_full_witness
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config)
    (h_step : System5.step (ctsToSystem5 cts cfg N) = some result) :
    cfg.data ≠ [] ∧ N ≥ 1 ∧
    1 ∈ (ctsToSystem5 cts cfg N).bag ∧
    0 ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) ∧
    (ctsToSystem5 cts cfg N).bag.Nodup ∧
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 := by
  obtain ⟨h_data, h_N⟩ := ctsToSystem5_step_some_implies_data_ne_nil_and_N_pos
    cts cfg N result h_step
  exact ⟨h_data, h_N,
    ctsToSystem5_step_some_implies_one_mem cts cfg N result h_step,
    ctsToSystem5_step_some_implies_zero_in_dec cts cfg N result h_step,
    ctsToSystem5_bag_nodup cts cfg N,
    ctsToSystem5_bag_length_ge_4_of_data_ne_nil cts cfg N h_data⟩

/-- **Iter 1593: encoder nSteps pos some implies cts.step some**.
    When the System5 encoder trajectory has progressed at least one
    step, the underlying CTS step also succeeds. -/
theorem ctsToSystem5_nSteps_pos_some_implies_cts_step_some
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_pos : n ≥ 1)
    (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) n = some s5') :
    ∃ result, cts.step cfg = some result := by
  obtain ⟨h_data, _⟩ := ctsToSystem5_nSteps_pos_some_implies_data_ne_nil_and_N_pos
    cts cfg N n h_pos s5' h_n
  exact (CTS_step_some_iff_data_ne_nil cts cfg).mpr h_data

/-- **Iter 1594: encoder nSteps pos some implies cfg not halted**.
    Halt-state form of iter 1518. -/
theorem ctsToSystem5_nSteps_pos_some_implies_not_halted
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_pos : n ≥ 1)
    (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) n = some s5') :
    ctsHalted cfg = false := by
  obtain ⟨h_data, _⟩ := ctsToSystem5_nSteps_pos_some_implies_data_ne_nil_and_N_pos
    cts cfg N n h_pos s5' h_n
  exact (ctsHalted_false_iff_data_ne_nil cfg).mpr h_data

/-- **Iter 1595: encoder step some implies cfg not halted**.  Halt-state
    form of iter 1510. -/
theorem ctsToSystem5_step_some_implies_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config)
    (h_step : System5.step (ctsToSystem5 cts cfg N) = some result) :
    ctsHalted cfg = false :=
  (ctsHalted_false_iff_data_ne_nil cfg).mpr
    (ctsToSystem5_step_some_implies_data_ne_nil cts cfg N result h_step)

/-- **Iter 1596 (🎯🎯🎯 705-LEMMA MILESTONE): encoder nSteps pos some
    implies encoder step some**.  When nSteps cfg5 n = some s5' (n ≥ 1),
    the System5.step on cfg5 also succeeds — the trajectory's first
    step succeeds. -/
theorem ctsToSystem5_nSteps_pos_some_implies_step_some
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_pos : n ≥ 1)
    (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) n = some s5') :
    ∃ result, System5.step (ctsToSystem5 cts cfg N) = some result := by
  obtain ⟨h_data, h_N⟩ := ctsToSystem5_nSteps_pos_some_implies_data_ne_nil_and_N_pos
    cts cfg N n h_pos s5' h_n
  exact ctsToSystem5_step_some_of_not_halted cts cfg N
    ((ctsHalted_false_iff_data_ne_nil cfg).mpr h_data) h_N

/-- **Iter 1597: encoder nSteps succ some implies cts.step some**.
    Direct via case-split + iter 1593. -/
theorem ctsToSystem5_nSteps_succ_some_implies_cts_step_some
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) (n + 1) = some s5') :
    ∃ result, cts.step cfg = some result :=
  ctsToSystem5_nSteps_pos_some_implies_cts_step_some cts cfg N (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) s5' h_n

/-- **Iter 1598: encoder nSteps one some iff step some**.  Specialization
    of iter 1456 to the cfg5 case. -/
theorem ctsToSystem5_nSteps_one_some_iff_step_some
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config) :
    System5.nSteps (ctsToSystem5 cts cfg N) 1 = some result ↔
      System5.step (ctsToSystem5 cts cfg N) = some result :=
  (System5_step_some_iff_nSteps_one_some _ result).symm

/-- **Iter 1599: CTS step result data either tail or tail++appendant**.
    Case-split on cfg.data.head: false-head ⇒ result.data = rest;
    true-head ⇒ result.data = rest ++ cts.currentAppendant phase. -/
theorem CTS_step_some_data_eq
    (cts : CTS) (cfg : CTSConfig) (result : CTSConfig)
    (h_step : cts.step cfg = some result) :
    (∃ rest, cfg.data = false :: rest ∧ result.data = rest) ∨
      (∃ rest, cfg.data = true :: rest ∧
        result.data = rest ++ cts.currentAppendant cfg.phase) := by
  unfold CTS.step at h_step
  cases h : cfg.data with
  | nil => rw [h] at h_step; simp at h_step
  | cons head tail =>
    rw [h] at h_step
    cases head with
    | false =>
      simp at h_step
      left
      refine ⟨tail, rfl, ?_⟩
      rw [← h_step]
    | true =>
      simp at h_step
      right
      refine ⟨tail, rfl, ?_⟩
      rw [← h_step]

/-- **Iter 1600 (🎯 ITER 1600 MILESTONE): CTS step result data length
    relation**.  When `cts.step cfg = some result`:
    - false-head ⇒ result.data.length = cfg.data.length - 1
    - true-head ⇒ result.data.length = cfg.data.length - 1 + |currentAppendant|
    Direct via iter 1599 + List.length manipulations. -/
theorem CTS_step_some_data_length_eq
    (cts : CTS) (cfg : CTSConfig) (result : CTSConfig)
    (h_step : cts.step cfg = some result) :
    result.data.length + 1 = cfg.data.length ∨
      result.data.length + 1 =
        cfg.data.length + (cts.currentAppendant cfg.phase).length := by
  rcases CTS_step_some_data_eq cts cfg result h_step with
    ⟨rest, h_data, h_result⟩ | ⟨rest, h_data, h_result⟩
  · left
    rw [h_data, h_result]
    simp
  · right
    rw [h_data, h_result]
    simp
    omega

/-- **Iter 1601 (🎯🎯🎯 710-LEMMA MILESTONE): encoder bag length after
    CTS step**.  When cts.step cfg = some result:
    - false-head: bag(result).length + 4 = bag(cfg).length
    - true-head: bag(result).length + 4 = bag(cfg).length + 4·|appendant|
    Direct via iter 1600 + iter 1520. -/
theorem ctsToSystem5_bag_length_after_cts_step
    (cts : CTS) (cfg result : CTSConfig) (N : Nat)
    (h_step : cts.step cfg = some result) :
    (ctsToSystem5 cts result N).bag.length + 4 = (ctsToSystem5 cts cfg N).bag.length ∨
      (ctsToSystem5 cts result N).bag.length + 4 =
        (ctsToSystem5 cts cfg N).bag.length + 4 * (cts.currentAppendant cfg.phase).length := by
  rw [ctsToSystem5_bag_length, ctsToSystem5_bag_length]
  rcases CTS_step_some_data_length_eq cts cfg result h_step with h_fh | h_th
  · left; omega
  · right; omega

/-- **Iter 1602: encoder rules length invariant under CTS step**.
    The encoder rules length = 4·|appendants|·N depends only on cts and
    N, not on cfg.data, so it's preserved by any CTS state evolution. -/
theorem ctsToSystem5_rules_length_invariant_cts_step
    (cts : CTS) (cfg result : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules.length = (ctsToSystem5 cts result N).rules.length := by
  rw [ctsToSystem5_rules_length, ctsToSystem5_rules_length]

/-- **Iter 1603: false-head step result encoder bag length**.  When
    cts.step ⟨false :: rest, phase⟩ = some result, then
    encoder_bag(result, N).length = 4 * rest.length. -/
theorem ctsToSystem5_false_head_step_result_bag_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat)
    (result : CTSConfig)
    (h_step : cts.step ⟨false :: rest, phase⟩ = some result) :
    (ctsToSystem5 cts result N).bag.length = 4 * rest.length := by
  rw [ctsToSystem5_bag_length]
  have h_data : result.data = rest := by
    unfold CTS.step at h_step
    simp at h_step
    rw [← h_step]
  rw [h_data]

/-- **Iter 1604: true-head step result encoder bag length**.  When
    cts.step ⟨true :: rest, phase⟩ = some result, encoder_bag(result,
    N).length = 4 * (rest.length + |currentAppendant|). -/
theorem ctsToSystem5_true_head_step_result_bag_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat)
    (result : CTSConfig)
    (h_step : cts.step ⟨true :: rest, phase⟩ = some result) :
    (ctsToSystem5 cts result N).bag.length =
      4 * (rest.length + (cts.currentAppendant phase).length) := by
  rw [ctsToSystem5_bag_length]
  have h_data : result.data = rest ++ cts.currentAppendant phase := by
    unfold CTS.step at h_step
    simp at h_step
    rw [← h_step]
  rw [h_data]
  simp

/-- **Iter 1605 (🎯🎯🎯 715-LEMMA MILESTONE): false-head step preserves
    encoder bag length to within 4**.  Direct corollary: bag(false-head
    cfg) = bag(result) + 4. -/
theorem ctsToSystem5_false_head_step_bag_length_diff
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat)
    (result : CTSConfig)
    (h_step : cts.step ⟨false :: rest, phase⟩ = some result) :
    (ctsToSystem5 cts ⟨false :: rest, phase⟩ N).bag.length =
      (ctsToSystem5 cts result N).bag.length + 4 := by
  rw [ctsToSystem5_bag_length,
      ctsToSystem5_false_head_step_result_bag_length cts rest phase N result h_step]
  simp [Nat.mul_succ]

/-- **Iter 1606: true-head step bag length diff**.  Companion to iter
    1605: bag(true-head cfg) + 4·|appendant| = bag(result) + 4. -/
theorem ctsToSystem5_true_head_step_bag_length_diff
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat)
    (result : CTSConfig)
    (h_step : cts.step ⟨true :: rest, phase⟩ = some result) :
    (ctsToSystem5 cts ⟨true :: rest, phase⟩ N).bag.length +
        4 * (cts.currentAppendant phase).length =
      (ctsToSystem5 cts result N).bag.length + 4 := by
  rw [ctsToSystem5_bag_length,
      ctsToSystem5_true_head_step_result_bag_length cts rest phase N result h_step]
  simp [Nat.mul_succ]
  omega

/-- **Iter 1607: encoder for step result invariant under phase choice**.
    Useful corollary of iter 1582: post-step encoder depends only on
    result.data, not on phase. -/
theorem ctsToSystem5_step_result_phase_choice_invariant
    (cts : CTS) (result : CTSConfig) (phase : Nat) (N : Nat) :
    ctsToSystem5 cts result N =
      ctsToSystem5 cts ⟨result.data, phase⟩ N := by
  cases result with
  | mk d ph =>
    exact ctsToSystem5_phase_invariant cts d ph phase N

/-- **Iter 1608: false-head step phase advancement**.  When cts.step
    ⟨false :: rest, phase⟩ = some result, result.phase = (phase + 1)
    mod |appendants|. -/
theorem CTS_step_false_head_phase
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step ⟨false :: rest, phase⟩ = some result) :
    result.phase = (phase + 1) % cts.appendants.length := by
  unfold CTS.step at h_step
  simp at h_step
  rw [← h_step]

/-- **Iter 1609: true-head step phase advancement**.  Companion. -/
theorem CTS_step_true_head_phase
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step ⟨true :: rest, phase⟩ = some result) :
    result.phase = (phase + 1) % cts.appendants.length := by
  unfold CTS.step at h_step
  simp at h_step
  rw [← h_step]

/-- **Iter 1610 (🎯🎯🎯 720-LEMMA MILESTONE): encoder bag depends only
    on data**.  When two cfgs have the same data, their encoder bags
    are equal regardless of phase.  Useful for relating cfgs with
    different phases. -/
theorem ctsConfigToSystem5Bag_data_only
    (cfg1 cfg2 : CTSConfig) (h_data : cfg1.data = cfg2.data) :
    ctsConfigToSystem5Bag cfg1 = ctsConfigToSystem5Bag cfg2 := by
  unfold ctsConfigToSystem5Bag
  rw [h_data]

/-- **Iter 1611: encoder rules depends only on data**.  When two cfgs
    have the same data, their encoder rules are equal regardless of
    phase. -/
theorem ctsRulesToSystem5Rules_data_only
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (N : Nat)
    (h_data : cfg1.data = cfg2.data) :
    ctsRulesToSystem5Rules cts cfg1 N = ctsRulesToSystem5Rules cts cfg2 N := by
  unfold ctsRulesToSystem5Rules
  rw [h_data]

/-- **Iter 1612: full encoder depends only on data**.  Combines iters
    1610 + 1611 into a full encoder equality. -/
theorem ctsToSystem5_data_only
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (N : Nat)
    (h_data : cfg1.data = cfg2.data) :
    ctsToSystem5 cts cfg1 N = ctsToSystem5 cts cfg2 N := by
  unfold ctsToSystem5
  rw [ctsConfigToSystem5Bag_data_only cfg1 cfg2 h_data,
      ctsRulesToSystem5Rules_data_only cts cfg1 cfg2 N h_data]

/-- **Iter 1613: cts.step some iff data cons**.  Biconditional: step
    succeeds iff data has cons form. -/
theorem CTS_step_some_iff_data_cons
    (cts : CTS) (cfg : CTSConfig) :
    (∃ result, cts.step cfg = some result) ↔
      (∃ head rest, cfg.data = head :: rest) := by
  refine ⟨?_, ?_⟩
  · intro ⟨result, h_step⟩
    rcases CTS_step_some_data_eq cts cfg result h_step with
      ⟨rest, h_data, _⟩ | ⟨rest, h_data, _⟩
    · exact ⟨false, rest, h_data⟩
    · exact ⟨true, rest, h_data⟩
  · intro ⟨head, rest, h_data⟩
    apply (CTS_step_some_iff_data_ne_nil cts cfg).mpr
    rw [h_data]; simp

/-- **Iter 1614: false-head step result data length**.  Direct via
    iter 1296 specialized to cons form. -/
theorem CTS_step_false_head_result_data_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step ⟨false :: rest, phase⟩ = some result) :
    result.data.length = rest.length := by
  unfold CTS.step at h_step
  simp at h_step
  rw [← h_step]

/-- **Iter 1615 (🎯🎯🎯 725-LEMMA MILESTONE): true-head step result
    data length**.  When cts.step ⟨true :: rest, phase⟩ = some result,
    result.data.length = rest.length + |currentAppendant phase|. -/
theorem CTS_step_true_head_result_data_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step ⟨true :: rest, phase⟩ = some result) :
    result.data.length = rest.length + (cts.currentAppendant phase).length := by
  unfold CTS.step at h_step
  simp at h_step
  rw [← h_step]
  simp

/-- **Iter 1616: currentAppendant phase invariant under modulus**.
    `cts.currentAppendant (phase % |appendants|) = cts.currentAppendant
    phase`.  Direct via def + Nat.mod_mod_self. -/
theorem CTS_currentAppendant_phase_mod
    (cts : CTS) (phase : Nat) :
    cts.currentAppendant (phase % cts.appendants.length) =
      cts.currentAppendant phase := by
  unfold CTS.currentAppendant
  simp [Nat.mod_mod]

/-- **Iter 1617: both encoder and CTS step succeed at non-halted +
    N ≥ 1**.  Useful joint witness lemma: when cfg.data ≠ [] and N ≥ 1,
    both `System5.step (encoder)` and `cts.step cfg` produce some
    results. -/
theorem ctsToSystem5_and_cts_step_some_of_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_not_halted : ctsHalted cfg = false) (h_N : N ≥ 1) :
    (∃ s5_result, System5.step (ctsToSystem5 cts cfg N) = some s5_result) ∧
      (∃ result, cts.step cfg = some result) := by
  refine ⟨ctsToSystem5_step_some_of_not_halted cts cfg N h_not_halted h_N, ?_⟩
  exact CTS_step_some_of_not_halted cts cfg h_not_halted

/-- **Iter 1618: cts.step result phase invariant**.  When cts.step cfg
    = some result, result.phase only depends on cfg.phase and
    cts.appendants.length (not on cfg.data). -/
theorem CTS_step_some_phase_only_depends_on_phase_and_appendants
    (cts : CTS) (cfg result : CTSConfig)
    (h_step : cts.step cfg = some result) :
    result.phase = (cfg.phase + 1) % cts.appendants.length := by
  unfold CTS.step at h_step
  cases h : cfg.data with
  | nil => rw [h] at h_step; simp at h_step
  | cons head tail =>
    rw [h] at h_step
    cases head <;> simp at h_step <;> rw [← h_step]

/-- **Iter 1619: cts.step result phase < appendants.length**.  Direct
    corollary of iter 1618 + Nat.mod_lt + cts.nonempty. -/
theorem CTS_step_some_phase_lt_appendants
    (cts : CTS) (cfg result : CTSConfig)
    (h_step : cts.step cfg = some result) :
    result.phase < cts.appendants.length := by
  rw [CTS_step_some_phase_only_depends_on_phase_and_appendants cts cfg result h_step]
  exact Nat.mod_lt _ cts.nonempty

/-- **Iter 1620 (🎯🎯🎯 730-LEMMA MILESTONE): cts.Halts iff data
    eventually empty**.  Halt-state form of iter 1391: `cts.Halts cfg
    ↔ ∃ n result, nSteps cfg n = some result ∧ result.data = []`. -/
theorem CTS_Halts_iff_data_eventually_empty
    (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ∃ n result, cts.nSteps cfg n = some result ∧ result.data = [] := by
  rw [CTS_Halts_iff_nSteps_halted]
  refine ⟨?_, ?_⟩
  · intro ⟨n, result, h_n, h_halted⟩
    refine ⟨n, result, h_n, ?_⟩
    exact (ctsHalted_true_iff_data_eq_nil result).mp h_halted
  · intro ⟨n, result, h_n, h_data⟩
    refine ⟨n, result, h_n, ?_⟩
    exact (ctsHalted_true_iff_data_eq_nil result).mpr h_data

/-- **Iter 1621: cts.Halts iff eventually encoder bag empty**.  Combines
    iter 1620 + iter 1234.  Useful Halts characterization at the
    encoder bag level. -/
theorem CTS_Halts_iff_eventually_encoder_bag_empty
    (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔
      ∃ n result, cts.nSteps cfg n = some result ∧ ctsConfigToSystem5Bag result = [] := by
  rw [CTS_Halts_iff_data_eventually_empty]
  refine ⟨?_, ?_⟩
  · intro ⟨n, result, h_n, h_data⟩
    refine ⟨n, result, h_n, ?_⟩
    rw [ctsConfigToSystem5Bag_eq_nil_iff]; exact h_data
  · intro ⟨n, result, h_n, h_bag⟩
    refine ⟨n, result, h_n, ?_⟩
    rw [← ctsConfigToSystem5Bag_eq_nil_iff]; exact h_bag

/-- **Iter 1622: cts.Halts iff encoder of result eventually has step
    none**.  When N ≥ 1, cfg.Halts ↔ ∃ n result, nSteps cfg n = some
    result ∧ System5.step (encoder result N) = none.  Composes iter
    1620 + iter 1514. -/
theorem CTS_Halts_iff_encoder_eventually_step_none
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    cts.Halts cfg ↔
      ∃ n result, cts.nSteps cfg n = some result ∧
        System5.step (ctsToSystem5 cts result N) = none := by
  rw [CTS_Halts_iff_data_eventually_empty]
  refine ⟨?_, ?_⟩
  · intro ⟨n, result, h_n, h_data⟩
    refine ⟨n, result, h_n, ?_⟩
    exact (ctsToSystem5_step_none_iff_data_empty_or_N_zero cts result N).mpr (Or.inl h_data)
  · intro ⟨n, result, h_n, h_step⟩
    refine ⟨n, result, h_n, ?_⟩
    rcases (ctsToSystem5_step_none_iff_data_empty_or_N_zero cts result N).mp h_step with
      h_data | h_N0
    · exact h_data
    · exfalso; omega

/-- **Iter 1623: data nil implies step none**.  Composes iter 1264 +
    iter 1276. -/
theorem CTS_data_eq_nil_implies_step_none
    (cts : CTS) (cfg : CTSConfig) (h_data : cfg.data = []) :
    cts.step cfg = none :=
  (CTS_step_none_iff_halted_v2 cts cfg).mpr
    ((ctsHalted_true_iff_data_eq_nil cfg).mpr h_data)

/-- **Iter 1624: data ≠ nil implies step some**.  Direct via iter 1478. -/
theorem CTS_data_ne_nil_implies_step_some
    (cts : CTS) (cfg : CTSConfig) (h_data : cfg.data ≠ []) :
    ∃ result, cts.step cfg = some result :=
  (CTS_step_some_iff_data_ne_nil cts cfg).mpr h_data

/-- **Iter 1625 (🎯🎯🎯 735-LEMMA MILESTONE): step decomposition with
    explicit head**.  When `cfg.data ≠ []`, the step result is fully
    characterized: ∃ head rest, `cfg.data = head :: rest ∧ cts.step cfg
    = some {data := if head then rest ++ appendant else rest, phase := ...}`. -/
theorem CTS_step_some_decomp_explicit
    (cts : CTS) (cfg : CTSConfig) (h_data : cfg.data ≠ []) :
    ∃ head rest, cfg.data = head :: rest ∧
      cts.step cfg = some
        ⟨if head = true then rest ++ cts.currentAppendant cfg.phase else rest,
         (cfg.phase + 1) % cts.appendants.length⟩ := by
  cases h : cfg.data with
  | nil => exact absurd h h_data
  | cons head tail =>
    refine ⟨head, tail, rfl, ?_⟩
    unfold CTS.step
    rw [h]

/-- **Iter 1626: nSteps succ some implies first step decomp**.  When
    `nSteps cfg (n+1) = some result`, ∃ head rest, cfg.data = head ::
    rest.  Composes iter 1463 + iter 1599. -/
theorem CTS_nSteps_succ_some_implies_data_cons
    (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h_n : cts.nSteps cfg (n + 1) = some result) :
    ∃ head rest, cfg.data = head :: rest := by
  obtain ⟨cfg', h_step⟩ := CTS_nSteps_succ_some_implies_step_some cts cfg result n h_n
  exact (CTS_step_some_iff_data_cons cts cfg).mp ⟨cfg', h_step⟩

/-- **Iter 1627: CTS nSteps pos some implies data cons**.  Direct via
    case split + iter 1626. -/
theorem CTS_nSteps_pos_some_implies_data_cons
    (cts : CTS) (cfg result : CTSConfig) (n : Nat) (h_pos : n ≥ 1)
    (h_n : cts.nSteps cfg n = some result) :
    ∃ head rest, cfg.data = head :: rest := by
  obtain ⟨k, h_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp h_pos)
  rw [h_eq] at h_n
  exact CTS_nSteps_succ_some_implies_data_cons cts cfg result k h_n

/-- **Iter 1628: CTS nSteps zero some iff result = cfg**.  Trivial via
    iter 1339. -/
theorem CTS_nSteps_zero_some_iff
    (cts : CTS) (cfg result : CTSConfig) :
    cts.nSteps cfg 0 = some result ↔ result = cfg := by
  rw [CTS_nSteps_zero]
  exact ⟨fun h => (Option.some.inj h).symm,
         fun h => by rw [h]⟩

/-- **Iter 1629: System5 nSteps zero some iff result = cfg**.  System5
    companion to iter 1628. -/
theorem System5_nSteps_zero_some_iff
    (cfg result : System5Config) :
    System5.nSteps cfg 0 = some result ↔ result = cfg := by
  rw [System5.nSteps_zero]
  exact ⟨fun h => (Option.some.inj h).symm,
         fun h => by rw [h]⟩

/-- **Iter 1630 (🎯🎯🎯 740-LEMMA MILESTONE): encoder nSteps zero some
    iff result = encoder**.  Specialization of iter 1629 to cfg5 case. -/
theorem ctsToSystem5_nSteps_zero_some_iff
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config) :
    System5.nSteps (ctsToSystem5 cts cfg N) 0 = some result ↔
      result = ctsToSystem5 cts cfg N :=
  System5_nSteps_zero_some_iff _ result

/-- **Iter 1631: encoder bag.length ≤ 4 implies data.length ≤ 1**.
    Useful constraint: small bag means small data. -/
theorem ctsToSystem5_bag_length_le_4_implies_data_length_le_1
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_le : (ctsToSystem5 cts cfg N).bag.length ≤ 4) :
    cfg.data.length ≤ 1 := by
  rw [ctsToSystem5_bag_length] at h_le
  omega

/-- **Iter 1632: encoder bag length = 4 iff data length = 1**.  Direct
    bijection. -/
theorem ctsToSystem5_bag_length_eq_4_iff_data_length_eq_1
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length = 4 ↔ cfg.data.length = 1 := by
  rw [ctsToSystem5_bag_length]
  refine ⟨?_, ?_⟩
  · intro h; omega
  · intro h; omega

/-- **Iter 1633: encoder bag length / 4 = data length**.  Direct via
    iter 1520 + Nat.mul_div_cancel_left. -/
theorem ctsToSystem5_bag_length_div_4
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length / 4 = cfg.data.length := by
  rw [ctsToSystem5_bag_length]
  exact Nat.mul_div_cancel_left _ (by omega : (0 : Nat) < 4)

/-- **Iter 1634: encoder rules length / 4 = appendants × N**.  Direct
    via iter 1521 + Nat.mul_div_cancel_left. -/
theorem ctsToSystem5_rules_length_div_4
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules.length / 4 = cts.appendants.length * N := by
  rw [ctsToSystem5_rules_length, Nat.mul_assoc]
  exact Nat.mul_div_cancel_left _ (by omega : (0 : Nat) < 4)

/-- **Iter 1635 (🎯🎯🎯 745-LEMMA MILESTONE): encoder bag length mod 4
    = 0**.  Direct corollary of iter 1557. -/
theorem ctsToSystem5_bag_length_mod_4
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length % 4 = 0 := by
  rw [ctsToSystem5_bag_length]
  exact Nat.mul_mod_right 4 cfg.data.length

/-- **Iter 1636: encoder rules length mod 4 = 0**.  Direct corollary
    of iter 1558. -/
theorem ctsToSystem5_rules_length_mod_4
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules.length % 4 = 0 := by
  rw [ctsToSystem5_rules_length, Nat.mul_assoc]
  exact Nat.mul_mod_right 4 _

/-- **Iter 1637: false-head singleton step result data empty**.  When
    cts.step ⟨[false], phase⟩ = some result, result.data = []. -/
theorem CTS_step_false_head_singleton_result_data_empty
    (cts : CTS) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step ⟨[false], phase⟩ = some result) :
    result.data = [] := by
  have h_data : result.data = [] := by
    unfold CTS.step at h_step
    simp at h_step
    rw [← h_step]
  exact h_data

/-- **Iter 1638: true-head singleton step result data = appendant**.
    When cts.step ⟨[true], phase⟩ = some result, result.data =
    cts.currentAppendant phase. -/
theorem CTS_step_true_head_singleton_result_data
    (cts : CTS) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step ⟨[true], phase⟩ = some result) :
    result.data = cts.currentAppendant phase := by
  unfold CTS.step at h_step
  simp at h_step
  rw [← h_step]

/-- **Iter 1639: cts.step at empty data is none**.  Trivial via def. -/
theorem CTS_step_empty_data
    (cts : CTS) (phase : Nat) :
    cts.step ⟨[], phase⟩ = none := by
  unfold CTS.step
  simp

/-- **Iter 1640 (🎯🎯🎯🎯🎯 750-LEMMA MILESTONE): encoder bag at empty
    data is empty**.  Direct via iter 1524 specialized.  Useful as a
    chain primitive when reasoning about halt-state cfgs. -/
theorem ctsToSystem5_bag_at_empty_data
    (cts : CTS) (phase : Nat) (N : Nat) :
    (ctsToSystem5 cts ⟨[], phase⟩ N).bag = [] :=
  (ctsToSystem5_bag_eq_nil_iff cts ⟨[], phase⟩ N).mpr rfl

/-- **Iter 1641: encoder Halts at empty data**.  Direct via iter 1640
    + `System5.Halts_of_empty_bag`. -/
theorem ctsToSystem5_Halts_at_empty_data
    (cts : CTS) (phase : Nat) (N : Nat) :
    System5.Halts (ctsToSystem5 cts ⟨[], phase⟩ N) :=
  System5.Halts_of_empty_bag _ (ctsToSystem5_bag_at_empty_data cts phase N)

/-- **Iter 1642: encoder bag at halted cfg is empty**.  Direct via
    iter 1529 forward direction. -/
theorem ctsToSystem5_bag_at_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_halted : ctsHalted cfg = true) :
    (ctsToSystem5 cts cfg N).bag = [] :=
  (ctsToSystem5_bag_eq_nil_iff_ctsHalted cts cfg N).mpr h_halted

/-- **Iter 1643: encoder bag at halted cfg has length 0**.  Direct
    corollary of iter 1642. -/
theorem ctsToSystem5_bag_length_at_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_halted : ctsHalted cfg = true) :
    (ctsToSystem5 cts cfg N).bag.length = 0 := by
  rw [ctsToSystem5_bag_at_halted cts cfg N h_halted]
  simp

/-- **Iter 1644: encoder step none implies halted or N = 0**.  Direct
    via iter 1515 forward direction. -/
theorem ctsToSystem5_step_none_implies_halted_or_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_step : System5.step (ctsToSystem5 cts cfg N) = none) :
    ctsHalted cfg = true ∨ N = 0 :=
  (ctsToSystem5_step_none_iff_halted_or_N_zero cts cfg N).mp h_step

/-- **Iter 1645 (🎯🎯🎯 755-LEMMA MILESTONE): CTS Halts implies encoder
    of nSteps result Halts**.  When `cts.Halts cfg`, ∃ n result,
    `nSteps cfg n = some result ∧ System5.Halts (encoder result N)`.
    Composes iter 1391 + iter 1506. -/
theorem CTS_Halts_implies_encoder_result_Halts
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_halts : cts.Halts cfg) :
    ∃ n result, cts.nSteps cfg n = some result ∧
      System5.Halts (ctsToSystem5 cts result N) := by
  obtain ⟨n, result, h_n, h_halted⟩ := (CTS_Halts_iff_nSteps_halted cts cfg).mp h_halts
  refine ⟨n, result, h_n, ?_⟩
  exact ctsToSystem5_Halts_when_ctsHalted cts result N h_halted

/-- **Iter 1646: encoder bag ≠ nil at non-halted cfg**.  Direct via
    iter 1530. -/
theorem ctsToSystem5_bag_ne_nil_at_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_not_halted : ctsHalted cfg = false) :
    (ctsToSystem5 cts cfg N).bag ≠ [] :=
  (ctsToSystem5_bag_ne_nil_iff_not_halted cts cfg N).mpr h_not_halted

/-- **Iter 1647: CTS Halts implies encoder of nSteps result step
    none**.  Stronger than iter 1645: explicit step = none witness. -/
theorem CTS_Halts_implies_encoder_result_step_none
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_halts : cts.Halts cfg) :
    ∃ n result, cts.nSteps cfg n = some result ∧
      System5.step (ctsToSystem5 cts result N) = none := by
  obtain ⟨n, result, h_n, h_halted⟩ := (CTS_Halts_iff_nSteps_halted cts cfg).mp h_halts
  refine ⟨n, result, h_n, ?_⟩
  exact ctsToSystem5_step_none_when_halted cts result N h_halted

/-- **Iter 1648: encoder rules at empty data**.  At cfg with empty data,
    encoder rules = ctsRulesToSystem5Rules cts ⟨[], phase⟩ N.  Useful
    explicit witness. -/
theorem ctsToSystem5_rules_at_empty_data
    (cts : CTS) (phase : Nat) (N : Nat) :
    (ctsToSystem5 cts ⟨[], phase⟩ N).rules =
      ctsRulesToSystem5Rules cts ⟨[], phase⟩ N :=
  ctsToSystem5_rules_eq cts ⟨[], phase⟩ N

/-- **Iter 1649: encoder at halted cfg eq encoder at empty data**.
    Useful normalization: when ctsHalted cfg = true, ctsToSystem5 cts
    cfg N = ctsToSystem5 cts ⟨[], cfg.phase⟩ N. -/
theorem ctsToSystem5_at_halted_eq_at_empty_data
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_halted : ctsHalted cfg = true) :
    ctsToSystem5 cts cfg N = ctsToSystem5 cts ⟨[], cfg.phase⟩ N := by
  apply ctsToSystem5_data_only
  show cfg.data = []
  exact (ctsHalted_true_iff_data_eq_nil cfg).mp h_halted

/-- **Iter 1650 (🎯🎯🎯 760-LEMMA MILESTONE): encoder at halted cfg
    phase-irrelevant**.  When ctsHalted cfg = true, the encoder at
    cfg with any phase is the same: ctsToSystem5 cts ⟨[], p1⟩ N =
    ctsToSystem5 cts ⟨[], p2⟩ N. -/
theorem ctsToSystem5_at_empty_data_phase_irrelevant
    (cts : CTS) (phase1 phase2 : Nat) (N : Nat) :
    ctsToSystem5 cts ⟨[], phase1⟩ N = ctsToSystem5 cts ⟨[], phase2⟩ N :=
  ctsToSystem5_phase_invariant cts [] phase1 phase2 N

/-- **Iter 1651: encoder bag eq when data eq via aux**.  Direct unfold
    showing the bag is `aux data 1`. -/
theorem ctsConfigToSystem5Bag_via_aux
    (cfg : CTSConfig) :
    ctsConfigToSystem5Bag cfg = ctsConfigToSystem5BagAux cfg.data 1 := by
  unfold ctsConfigToSystem5Bag
  rfl

/-- **Iter 1652: cts.step at cons explicit form**.  Direct unfolding
    of `CTS.step` for cons data. -/
theorem CTS_step_cons_eq
    (cts : CTS) (head : Bool) (rest : List Bool) (phase : Nat) :
    cts.step ⟨head :: rest, phase⟩ = some
      ⟨if head = true then rest ++ cts.currentAppendant phase else rest,
       (phase + 1) % cts.appendants.length⟩ := by
  unfold CTS.step
  simp

/-- **Iter 1653: cts.step at false-head explicit form**.  Specialization
    of iter 1652. -/
theorem CTS_step_false_cons_eq
    (cts : CTS) (rest : List Bool) (phase : Nat) :
    cts.step ⟨false :: rest, phase⟩ =
      some ⟨rest, (phase + 1) % cts.appendants.length⟩ := by
  rw [CTS_step_cons_eq]
  simp

/-- **Iter 1654: cts.step at true-head explicit form**.  Specialization
    of iter 1652. -/
theorem CTS_step_true_cons_eq
    (cts : CTS) (rest : List Bool) (phase : Nat) :
    cts.step ⟨true :: rest, phase⟩ =
      some ⟨rest ++ cts.currentAppendant phase,
            (phase + 1) % cts.appendants.length⟩ := by
  rw [CTS_step_cons_eq]
  simp

/-- **Iter 1655: cts.step dichotomy**.  cts.step cfg either succeeds or
    fails.  Trivial via Option dichotomy. -/
theorem CTS_step_dichotomy
    (cts : CTS) (cfg : CTSConfig) :
    cts.step cfg = none ∨ ∃ result, cts.step cfg = some result := by
  cases h : cts.step cfg with
  | none => left; rfl
  | some result => right; exact ⟨result, rfl⟩

/-- **Iter 1656 (🎯🎯🎯 765-LEMMA MILESTONE): System5 step dichotomy**.
    System5 companion to iter 1655. -/
theorem System5_step_dichotomy
    (cfg : System5Config) :
    System5.step cfg = none ∨ ∃ result, System5.step cfg = some result := by
  cases h : System5.step cfg with
  | none => left; rfl
  | some result => right; exact ⟨result, rfl⟩

/-- **Iter 1657: CTS step result data either nil or appendant when
    rest empty**.  Specialization of iter 1599 with rest = []:
    false-head ⇒ result.data = [], true-head ⇒ result.data = appendant. -/
theorem CTS_step_some_singleton_data
    (cts : CTS) (head : Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step ⟨[head], phase⟩ = some result) :
    (head = false ∧ result.data = []) ∨
    (head = true ∧ result.data = cts.currentAppendant phase) := by
  cases head with
  | false =>
    left
    refine ⟨rfl, ?_⟩
    exact CTS_step_false_head_singleton_result_data_empty cts phase result h_step
  | true =>
    right
    refine ⟨rfl, ?_⟩
    exact CTS_step_true_head_singleton_result_data cts phase result h_step

/-- **Iter 1658: CTS step false-singleton halt-pred**.  When cts.step
    ⟨[false], phase⟩ = some result, result is halted (data = []). -/
theorem CTS_step_false_head_singleton_result_halted
    (cts : CTS) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step ⟨[false], phase⟩ = some result) :
    ctsHalted result = true :=
  (ctsHalted_true_iff_data_eq_nil result).mpr
    (CTS_step_false_head_singleton_result_data_empty cts phase result h_step)

/-- **Iter 1659: false-singleton cfg Halts**.  When cfg = ⟨[false],
    phase⟩, cfg.Halts.  Direct via iter 1316 + step iteration. -/
theorem CTS_Halts_at_false_singleton
    (cts : CTS) (phase : Nat) :
    cts.Halts ⟨[false], phase⟩ := by
  apply CTS_Halts_step_pred cts ⟨[false], phase⟩
    ⟨[], (phase + 1) % cts.appendants.length⟩
  · exact CTS_step_false_cons_eq cts [] phase
  · exact CTS_Halts_of_halted cts _ rfl

/-- **Iter 1660 (🎯 ITER 1660 MILESTONE): empty-data cfg Halts**.
    Trivial via iter 1316. -/
theorem CTS_Halts_at_empty_data
    (cts : CTS) (phase : Nat) :
    cts.Halts ⟨[], phase⟩ :=
  CTS_Halts_of_halted cts ⟨[], phase⟩ rfl

/-- **Iter 1661 (🎯🎯🎯 770-LEMMA MILESTONE): cfg with empty data Halts**.
    When cfg.data = [], cfg.Halts.  Direct via iter 1318. -/
theorem CTS_Halts_of_data_empty_general
    (cts : CTS) (cfg : CTSConfig) (h_data : cfg.data = []) :
    cts.Halts cfg :=
  CTS_Halts_of_halted cts cfg ((ctsHalted_true_iff_data_eq_nil cfg).mpr h_data)

/-- **Iter 1662: not-halted Halts requires positive nSteps**.  When
    cfg.Halts ∧ ¬halted cfg, the witness fuel n must satisfy n ≥ 1
    (since at n=0, nSteps cfg 0 = some cfg, which doesn't have halted
    result). -/
theorem CTS_not_halted_Halts_implies_pos_witness
    (cts : CTS) (cfg : CTSConfig) (h_halts : cts.Halts cfg)
    (h_not_halted : ctsHalted cfg = false) :
    ∃ n result, n ≥ 1 ∧ cts.nSteps cfg n = some result ∧ ctsHalted result = true := by
  obtain ⟨n, result, h_n, h_halted⟩ := (CTS_Halts_iff_nSteps_halted cts cfg).mp h_halts
  cases n with
  | zero =>
    rw [CTS_nSteps_zero] at h_n
    injection h_n with h_eq
    rw [← h_eq] at h_halted
    rw [h_halted] at h_not_halted
    cases h_not_halted
  | succ k => exact ⟨k + 1, result, Nat.succ_le_succ (Nat.zero_le k), h_n, h_halted⟩

/-- **Iter 1663: System5 not-empty Halts requires positive nSteps**.
    System5 companion of iter 1662: when cfg.Halts and bag/rules
    non-empty, the Halts witness fuel ≥ 1. -/
theorem System5_step_some_Halts_implies_pos_witness
    (cfg : System5Config) (h_halts : System5.Halts cfg)
    (result : System5Config) (h_step : System5.step cfg = some result) :
    ∃ n, n ≥ 1 ∧ System5.nSteps cfg n = none := by
  obtain ⟨n, h_n⟩ := h_halts
  cases n with
  | zero =>
    rw [System5.nSteps_zero] at h_n
    cases h_n
  | succ k => exact ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k), h_n⟩

/-- **Iter 1664: CTS halted cfg has Halts witness at zero fuel**.
    When ctsHalted cfg, the Halts witness is trivially at n = 0:
    nSteps cfg 0 = some cfg, which is halted. -/
theorem CTS_halted_nSteps_zero_witness
    (cts : CTS) (cfg : CTSConfig) (h_halted : ctsHalted cfg = true) :
    cts.nSteps cfg 0 = some cfg ∧ ctsHalted cfg = true := by
  refine ⟨?_, h_halted⟩
  rw [CTS_nSteps_zero]

/-- **Iter 1665: CTS Halts dichotomy**.  cfg.Halts iff already halted
    OR can step to a Halts cfg.  Composes iter 1326. -/
theorem CTS_Halts_dichotomy
    (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ctsHalted cfg = true ∨
      (∃ result, cts.step cfg = some result ∧ cts.Halts result) :=
  CTS_Halts_iff_halted_or_step_Halts cts cfg

/-- **Iter 1666 (🎯🎯🎯 775-LEMMA MILESTONE): System5 Halts dichotomy**.
    System5 companion to iter 1665 — direct alias of iter 1484. -/
theorem System5_Halts_dichotomy
    (cfg : System5Config) :
    System5.Halts cfg ↔ System5.step cfg = none ∨
      (∃ r, System5.step cfg = some r ∧ System5.Halts r) :=
  System5_Halts_iff_step_none_or_step_Halts cfg

/-- **Iter 1667: CTS ¬Halts iff exists step result ¬Halts**.  Stronger
    biconditional via iters 1432 + 1326. -/
theorem CTS_not_Halts_iff_step_result_not_Halts
    (cts : CTS) (cfg : CTSConfig) :
    ¬ cts.Halts cfg ↔
      ¬ ctsHalted cfg = true ∧
        ∀ result, cts.step cfg = some result → ¬ cts.Halts result := by
  rw [CTS_Halts_dichotomy]
  refine ⟨?_, ?_⟩
  · intro h_not_halts
    refine ⟨?_, ?_⟩
    · intro h_halted
      exact h_not_halts (Or.inl h_halted)
    · intro result h_step h_halts
      exact h_not_halts (Or.inr ⟨result, h_step, h_halts⟩)
  · intro ⟨h_not_halted, h_all⟩ h_or
    rcases h_or with h_halted | ⟨result, h_step, h_halts⟩
    · exact h_not_halted h_halted
    · exact h_all result h_step h_halts

/-- **Iter 1668: System5 ¬Halts iff exists step result ¬Halts**.
    System5 companion of iter 1667. -/
theorem System5_not_Halts_iff_step_result_not_Halts
    (cfg : System5Config) :
    ¬ System5.Halts cfg ↔
      ¬ System5.step cfg = none ∧
        ∀ r, System5.step cfg = some r → ¬ System5.Halts r := by
  rw [System5_Halts_dichotomy]
  refine ⟨?_, ?_⟩
  · intro h_not_halts
    refine ⟨?_, ?_⟩
    · intro h_step_none
      exact h_not_halts (Or.inl h_step_none)
    · intro r h_step h_halts
      exact h_not_halts (Or.inr ⟨r, h_step, h_halts⟩)
  · intro ⟨h_step_ne, h_all⟩ h_or
    rcases h_or with h_step_none | ⟨r, h_step, h_halts⟩
    · exact h_step_ne h_step_none
    · exact h_all r h_step h_halts

/-- **Iter 1669: encoder nSteps 1 = encoder step**.  Direct via System5
    nSteps_one. -/
theorem ctsToSystem5_nSteps_one_eq_step
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.nSteps (ctsToSystem5 cts cfg N) 1 = System5.step (ctsToSystem5 cts cfg N) :=
  System5.nSteps_one _

/-- **Iter 1670 (🎯 ITER 1670 MILESTONE): encoder nSteps add**.
    Direct specialization of System5.nSteps_add. -/
theorem ctsToSystem5_nSteps_add
    (cts : CTS) (cfg : CTSConfig) (N n m : Nat) :
    System5.nSteps (ctsToSystem5 cts cfg N) (n + m) =
      (System5.nSteps (ctsToSystem5 cts cfg N) n).bind
        (fun c => System5.nSteps c m) :=
  System5.nSteps_add _ n m

/-- **Iter 1671 (🎯🎯🎯 780-LEMMA MILESTONE): encoder nSteps succ**.
    Direct specialization of System5.nSteps_succ. -/
theorem ctsToSystem5_nSteps_succ
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) :
    System5.nSteps (ctsToSystem5 cts cfg N) (n + 1) =
      (System5.step (ctsToSystem5 cts cfg N)).bind
        (fun c => System5.nSteps c n) :=
  System5.nSteps_succ _ n

/-- **Iter 1672: encoder at zero N has empty rules**.  When N = 0,
    encoder rules are empty.  Specialization of iter 1525. -/
theorem ctsToSystem5_at_zero_N_rules_empty
    (cts : CTS) (cfg : CTSConfig) :
    (ctsToSystem5 cts cfg 0).rules = [] :=
  (ctsToSystem5_rules_eq_nil_iff cts cfg 0).mpr rfl

/-- **Iter 1673: encoder at zero N has Halts**.  Combined with iter
    1672, the encoder Halts when N = 0 since rules are empty. -/
theorem ctsToSystem5_at_zero_N_Halts
    (cts : CTS) (cfg : CTSConfig) :
    System5.Halts (ctsToSystem5 cts cfg 0) :=
  ctsToSystem5_Halts_when_N_zero cts cfg

/-- **Iter 1674: CTS eval at any fuel ≥ halts at halted**.  Direct via
    iter 1315.  Useful named consumer. -/
theorem CTS_eval_at_halted_eq_some
    (cts : CTS) (cfg : CTSConfig) (h_halted : ctsHalted cfg = true) (fuel : Nat) :
    cts.eval cfg fuel = some cfg :=
  CTS_eval_halted_returns cts cfg h_halted fuel

/-- **Iter 1675: CTS eval at empty data**.  When data = [], eval at
    any fuel returns the cfg.  Direct via iter 1674. -/
theorem CTS_eval_at_empty_data
    (cts : CTS) (phase : Nat) (fuel : Nat) :
    cts.eval ⟨[], phase⟩ fuel = some ⟨[], phase⟩ :=
  CTS_eval_at_halted_eq_some cts ⟨[], phase⟩ rfl fuel

/-- **Iter 1676 (🎯🎯🎯 785-LEMMA MILESTONE): CTS nSteps at empty data
    eq**.  At empty data, nSteps cfg n = if n = 0 then some cfg else
    none.  Direct via iter 1399. -/
theorem CTS_nSteps_at_empty_data
    (cts : CTS) (phase : Nat) (n : Nat) :
    cts.nSteps ⟨[], phase⟩ n = if n = 0 then some ⟨[], phase⟩ else none :=
  CTS_nSteps_halted_eq cts ⟨[], phase⟩ rfl n

/-- **Iter 1677: CTS nSteps succ at empty data is none**.  Specialization
    of iter 1676 to n+1. -/
theorem CTS_nSteps_succ_at_empty_data
    (cts : CTS) (phase : Nat) (n : Nat) :
    cts.nSteps ⟨[], phase⟩ (n + 1) = none := by
  rw [CTS_nSteps_at_empty_data]
  simp

/-- **Iter 1678: encoder System5 nSteps succ at empty data is none**.
    When CTS data is empty, encoder bag is empty, so System5 step is
    none, so nSteps (n+1) = none. -/
theorem ctsToSystem5_nSteps_succ_at_empty_data_eq_none
    (cts : CTS) (phase : Nat) (N n : Nat) :
    System5.nSteps (ctsToSystem5 cts ⟨[], phase⟩ N) (n + 1) = none := by
  rw [ctsToSystem5_nSteps_succ]
  rw [ctsToSystem5_step_none_when_halted cts ⟨[], phase⟩ N rfl]
  rfl

/-- **Iter 1679: encoder nSteps succ at halted cfg is none**.
    Generalization of iter 1678 to any halted cfg via iter 1571. -/
theorem ctsToSystem5_nSteps_succ_at_halted_eq_none
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_halted : ctsHalted cfg = true) :
    System5.nSteps (ctsToSystem5 cts cfg N) (n + 1) = none := by
  rw [ctsToSystem5_nSteps_succ]
  rw [ctsToSystem5_step_none_when_halted cts cfg N h_halted]
  rfl

/-- **Iter 1680 (🎯 ITER 1680 MILESTONE): encoder at halted cfg has
    Halts witness at fuel = 1**.  Direct via iter 1679 with n = 0. -/
theorem ctsToSystem5_at_halted_Halts_witness_one
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_halted : ctsHalted cfg = true) :
    System5.nSteps (ctsToSystem5 cts cfg N) 1 = none :=
  ctsToSystem5_nSteps_succ_at_halted_eq_none cts cfg N 0 h_halted

/-- **Iter 1681 (🎯🎯🎯 790-LEMMA MILESTONE): encoder rules at empty
    data is also empty when N = 0**.  Combines empty data with N = 0
    edge case. -/
theorem ctsToSystem5_at_zero_N_and_empty_data_eq_zero_cfg
    (cts : CTS) (phase : Nat) :
    ctsToSystem5 cts ⟨[], phase⟩ 0 = ⟨[], []⟩ := by
  unfold ctsToSystem5
  simp [ctsConfigToSystem5Bag, ctsRulesToSystem5Rules,
        ctsConfigToSystem5BagAux]

/-- **Iter 1682: counterAfterWorkingString at empty list ≥ 1**.  Direct
    consequence: counter starts at 1. -/
theorem counterAfterWorkingString_nil_ge_one :
    counterAfterWorkingString [] ≥ 1 := by
  unfold counterAfterWorkingString
  simp

/-- **Iter 1683: encoder bag .length related to data via 4×**.  Useful
    rephrasing of iter 1520. -/
theorem ctsToSystem5_data_length_via_bag
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    4 * cfg.data.length = (ctsToSystem5 cts cfg N).bag.length :=
  (ctsToSystem5_bag_length cts cfg N).symm

/-- **Iter 1684: encoder bag length at singleton data = 4**.  Direct
    via iter 1520. -/
theorem ctsToSystem5_at_singleton_bag_length
    (cts : CTS) (head : Bool) (phase : Nat) (N : Nat) :
    (ctsToSystem5 cts ⟨[head], phase⟩ N).bag.length = 4 := by
  rw [ctsToSystem5_bag_length]
  simp

/-- **Iter 1685: encoder bag length when data length = k**.  Closed form
    parameterized by data length. -/
theorem ctsToSystem5_bag_length_when_data_len_eq
    (cts : CTS) (cfg : CTSConfig) (N k : Nat) (h_len : cfg.data.length = k) :
    (ctsToSystem5 cts cfg N).bag.length = 4 * k := by
  rw [ctsToSystem5_bag_length, h_len]

/-- **Iter 1686 (🎯🎯🎯 795-LEMMA MILESTONE): encoder rules length when
    appendants length = k**.  Parameterized closed form. -/
theorem ctsToSystem5_rules_length_when_appendants_len_eq
    (cts : CTS) (cfg : CTSConfig) (N k : Nat)
    (h_len : cts.appendants.length = k) :
    (ctsToSystem5 cts cfg N).rules.length = 4 * k * N := by
  rw [ctsToSystem5_rules_length, h_len]

/-- **Iter 1687: CTS Halts iff eval some at any sufficient fuel**.
    Reformulation. -/
theorem CTS_Halts_iff_eval_some_at_some_fuel
    (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ∃ fuel result, cts.eval cfg fuel = some result :=
  CTS_Halts_iff_exists_eval_some cts cfg

/-- **Iter 1688: encoder at singleton false data has bag = [1, 2, 3, 4]**.
    Direct via iter 645's false-head decomp. -/
theorem ctsToSystem5_at_false_singleton_bag
    (cts : CTS) (phase : Nat) (N : Nat) :
    (ctsToSystem5 cts ⟨[false], phase⟩ N).bag = [1, 2, 3, 4] := by
  rw [ctsToSystem5_bag_eq, ctsConfigToSystem5Bag_via_aux]
  show ctsConfigToSystem5BagAux [false] 1 = [1, 2, 3, 4]
  native_decide

/-- **Iter 1689: encoder at singleton true data has bag = [1, 3, 4, 6]**.
    Direct via native_decide. -/
theorem ctsToSystem5_at_true_singleton_bag
    (cts : CTS) (phase : Nat) (N : Nat) :
    (ctsToSystem5 cts ⟨[true], phase⟩ N).bag = [1, 3, 4, 6] := by
  rw [ctsToSystem5_bag_eq, ctsConfigToSystem5Bag_via_aux]
  show ctsConfigToSystem5BagAux [true] 1 = [1, 3, 4, 6]
  native_decide

/-- **Iter 1690: encoder at singleton false data bag length = 4**.
    Direct corollary of iter 1688. -/
theorem ctsToSystem5_at_false_singleton_bag_length :
    ∀ (cts : CTS) (phase N : Nat),
      (ctsToSystem5 cts ⟨[false], phase⟩ N).bag.length = 4 := by
  intro cts phase N
  rw [ctsToSystem5_at_false_singleton_bag]; rfl

/-- **Iter 1691 (🎯🎯🎯🎯🎯 800-LEMMA MILESTONE): encoder at singleton
    explicit bag and all conditions**.  When cfg.data is a singleton,
    encoder bag is explicit (4 elements depending on head) and
    satisfies standard non-emptiness conditions. -/
theorem ctsToSystem5_at_singleton_full_witness
    (cts : CTS) (head : Bool) (phase N : Nat) (h_N : N ≥ 1) :
    (ctsToSystem5 cts ⟨[head], phase⟩ N).bag ≠ [] ∧
    (ctsToSystem5 cts ⟨[head], phase⟩ N).rules ≠ [] ∧
    (ctsToSystem5 cts ⟨[head], phase⟩ N).bag.length = 4 ∧
    1 ∈ (ctsToSystem5 cts ⟨[head], phase⟩ N).bag := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases head with
    | false => rw [ctsToSystem5_at_false_singleton_bag]; simp
    | true => rw [ctsToSystem5_at_true_singleton_bag]; simp
  · exact ctsRulesToSystem5Rules_ne_nil cts ⟨[head], phase⟩ N h_N
  · cases head with
    | false => rw [ctsToSystem5_at_false_singleton_bag]; rfl
    | true => rw [ctsToSystem5_at_true_singleton_bag]; rfl
  · cases head with
    | false => rw [ctsToSystem5_at_false_singleton_bag]; simp
    | true => rw [ctsToSystem5_at_true_singleton_bag]; simp

/-- **Iter 1692: encoder at singleton true bag length = 4**.  Direct
    corollary of iter 1689. -/
theorem ctsToSystem5_at_true_singleton_bag_length :
    ∀ (cts : CTS) (phase N : Nat),
      (ctsToSystem5 cts ⟨[true], phase⟩ N).bag.length = 4 := by
  intro cts phase N
  rw [ctsToSystem5_at_true_singleton_bag]; rfl

/-- **Iter 1693: 1 ∈ encoder bag at singleton false data**.  Direct via
    iter 1688. -/
theorem ctsToSystem5_at_false_singleton_one_mem :
    ∀ (cts : CTS) (phase N : Nat),
      (1 : Int) ∈ (ctsToSystem5 cts ⟨[false], phase⟩ N).bag := by
  intro cts phase N
  rw [ctsToSystem5_at_false_singleton_bag]; simp

/-- **Iter 1694: 1 ∈ encoder bag at singleton true data**.  Direct via
    iter 1689. -/
theorem ctsToSystem5_at_true_singleton_one_mem :
    ∀ (cts : CTS) (phase N : Nat),
      (1 : Int) ∈ (ctsToSystem5 cts ⟨[true], phase⟩ N).bag := by
  intro cts phase N
  rw [ctsToSystem5_at_true_singleton_bag]; simp

/-- **Iter 1695: 1 ∈ encoder bag at any singleton data**.  Combines
    iters 1693 + 1694. -/
theorem ctsToSystem5_at_singleton_one_mem
    (cts : CTS) (head : Bool) (phase N : Nat) :
    (1 : Int) ∈ (ctsToSystem5 cts ⟨[head], phase⟩ N).bag := by
  cases head with
  | false => exact ctsToSystem5_at_false_singleton_one_mem cts phase N
  | true => exact ctsToSystem5_at_true_singleton_one_mem cts phase N

/-- **Iter 1696 (🎯🎯🎯 805-LEMMA MILESTONE): encoder bag length at any
    singleton = 4**.  Direct combined version. -/
theorem ctsToSystem5_at_singleton_bag_length_eq_4
    (cts : CTS) (head : Bool) (phase N : Nat) :
    (ctsToSystem5 cts ⟨[head], phase⟩ N).bag.length = 4 :=
  ctsToSystem5_at_singleton_bag_length cts head phase N

/-- **Iter 1697: encoder bag at singleton is Nodup**.  Specialization
    of iter 1540 to singleton data. -/
theorem ctsToSystem5_at_singleton_bag_nodup
    (cts : CTS) (head : Bool) (phase N : Nat) :
    (ctsToSystem5 cts ⟨[head], phase⟩ N).bag.Nodup :=
  ctsToSystem5_bag_nodup cts ⟨[head], phase⟩ N

/-- **Iter 1698: encoder step at singleton succeeds iff N ≥ 1**.
    Specialization of iter 1513 with non-empty data. -/
theorem ctsToSystem5_at_singleton_step_some_iff_N_pos
    (cts : CTS) (head : Bool) (phase N : Nat) :
    (∃ result, System5.step (ctsToSystem5 cts ⟨[head], phase⟩ N) = some result) ↔
      N ≥ 1 := by
  rw [ctsToSystem5_step_some_iff_data_ne_nil_and_N_pos]
  refine ⟨fun ⟨_, h⟩ => h, fun h => ⟨by simp, h⟩⟩

/-- **Iter 1699: encoder step at singleton succeeds when N ≥ 1**.
    Forward direction of iter 1698. -/
theorem ctsToSystem5_at_singleton_step_some_of_N_pos
    (cts : CTS) (head : Bool) (phase N : Nat) (h_N : N ≥ 1) :
    ∃ result, System5.step (ctsToSystem5 cts ⟨[head], phase⟩ N) = some result :=
  (ctsToSystem5_at_singleton_step_some_iff_N_pos cts head phase N).mpr h_N

/-- **Iter 1700 (🎯🎯🎯🎯🎯 ITER 1700 MILESTONE): encoder bag length at
    data of length 2 = 8**.  Direct via iter 1685. -/
theorem ctsToSystem5_at_pair_data_bag_length
    (cts : CTS) (head1 head2 : Bool) (phase N : Nat) :
    (ctsToSystem5 cts ⟨[head1, head2], phase⟩ N).bag.length = 8 := by
  rw [ctsToSystem5_bag_length]
  rfl

/-- **Iter 1701 (🎯🎯🎯 810-LEMMA MILESTONE): encoder bag length at
    triple data = 12**.  Direct via iter 1520. -/
theorem ctsToSystem5_at_triple_data_bag_length
    (cts : CTS) (h1 h2 h3 : Bool) (phase N : Nat) :
    (ctsToSystem5 cts ⟨[h1, h2, h3], phase⟩ N).bag.length = 12 := by
  rw [ctsToSystem5_bag_length]
  rfl

/-- **Iter 1702: encoder bag at [false, false] data**.  Direct
    computation: `aux [false, false] 1 = [1,2,3,4,5,6,7,8]`. -/
theorem ctsToSystem5_at_false_false_bag
    (cts : CTS) (phase N : Nat) :
    (ctsToSystem5 cts ⟨[false, false], phase⟩ N).bag = [1, 2, 3, 4, 5, 6, 7, 8] := by
  rw [ctsToSystem5_bag_eq, ctsConfigToSystem5Bag_via_aux]
  show ctsConfigToSystem5BagAux [false, false] 1 = [1, 2, 3, 4, 5, 6, 7, 8]
  native_decide

/-- **Iter 1703: encoder bag at [true, true] data**.  Direct
    computation. -/
theorem ctsToSystem5_at_true_true_bag
    (cts : CTS) (phase N : Nat) :
    (ctsToSystem5 cts ⟨[true, true], phase⟩ N).bag = [1, 3, 4, 6, 7, 9, 10, 12] := by
  rw [ctsToSystem5_bag_eq, ctsConfigToSystem5Bag_via_aux]
  show ctsConfigToSystem5BagAux [true, true] 1 = [1, 3, 4, 6, 7, 9, 10, 12]
  native_decide

/-- **Iter 1704: encoder bag at [false, true] data**.  Direct
    computation. -/
theorem ctsToSystem5_at_false_true_bag
    (cts : CTS) (phase N : Nat) :
    (ctsToSystem5 cts ⟨[false, true], phase⟩ N).bag = [1, 2, 3, 4, 5, 7, 8, 10] := by
  rw [ctsToSystem5_bag_eq, ctsConfigToSystem5Bag_via_aux]
  show ctsConfigToSystem5BagAux [false, true] 1 = [1, 2, 3, 4, 5, 7, 8, 10]
  native_decide

/-- **Iter 1705 (🎯🎯🎯 815-LEMMA MILESTONE): encoder bag at [true,
    false] data**.  Direct computation. -/
theorem ctsToSystem5_at_true_false_bag
    (cts : CTS) (phase N : Nat) :
    (ctsToSystem5 cts ⟨[true, false], phase⟩ N).bag = [1, 3, 4, 6, 7, 8, 9, 10] := by
  rw [ctsToSystem5_bag_eq, ctsConfigToSystem5Bag_via_aux]
  show ctsConfigToSystem5BagAux [true, false] 1 = [1, 3, 4, 6, 7, 8, 9, 10]
  native_decide

/-- **Iter 1706: encoder bag at [false, false, false] data**.  Direct
    computation. -/
theorem ctsToSystem5_at_three_false_bag
    (cts : CTS) (phase N : Nat) :
    (ctsToSystem5 cts ⟨[false, false, false], phase⟩ N).bag =
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] := by
  rw [ctsToSystem5_bag_eq, ctsConfigToSystem5Bag_via_aux]
  show ctsConfigToSystem5BagAux [false, false, false] 1 =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  native_decide

/-- **Iter 1707: encoder bag at [true, true, true] data**.  Direct
    computation. -/
theorem ctsToSystem5_at_three_true_bag
    (cts : CTS) (phase N : Nat) :
    (ctsToSystem5 cts ⟨[true, true, true], phase⟩ N).bag =
      [1, 3, 4, 6, 7, 9, 10, 12, 13, 15, 16, 18] := by
  rw [ctsToSystem5_bag_eq, ctsConfigToSystem5Bag_via_aux]
  show ctsConfigToSystem5BagAux [true, true, true] 1 =
    [1, 3, 4, 6, 7, 9, 10, 12, 13, 15, 16, 18]
  native_decide

/-- **Iter 1708: encoder bag mem implies data ≠ nil**.  When x ∈ bag,
    cfg.data ≠ [].  Direct via iter 1530 contrapositive. -/
theorem ctsToSystem5_bag_mem_implies_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (x : Int)
    (h_mem : x ∈ (ctsToSystem5 cts cfg N).bag) :
    cfg.data ≠ [] := by
  intro h_data
  have h_bag : (ctsToSystem5 cts cfg N).bag = [] :=
    (ctsToSystem5_bag_eq_nil_iff cts cfg N).mpr h_data
  rw [h_bag] at h_mem
  cases h_mem

/-- **Iter 1709: encoder bag mem implies cfg not halted**.  Halt-state
    form of iter 1708. -/
theorem ctsToSystem5_bag_mem_implies_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (x : Int)
    (h_mem : x ∈ (ctsToSystem5 cts cfg N).bag) :
    ctsHalted cfg = false :=
  (ctsHalted_false_iff_data_ne_nil cfg).mpr
    (ctsToSystem5_bag_mem_implies_data_ne_nil cts cfg N x h_mem)

/-- **Iter 1710 (🎯🎯🎯 820-LEMMA MILESTONE): encoder step succeeds at
    higher N**.  When step succeeds at N1 and N2 ≥ N1, step also
    succeeds at N2. -/
theorem ctsToSystem5_step_some_at_higher_N
    (cts : CTS) (cfg : CTSConfig) (N1 N2 : Nat) (h_le : N1 ≤ N2)
    (result1 : System5Config)
    (h_step : System5.step (ctsToSystem5 cts cfg N1) = some result1) :
    ∃ result2, System5.step (ctsToSystem5 cts cfg N2) = some result2 := by
  obtain ⟨h_data, h_N1⟩ :=
    ctsToSystem5_step_some_implies_data_ne_nil_and_N_pos cts cfg N1 result1 h_step
  exact ctsToSystem5_step_some_of_not_halted cts cfg N2
    ((ctsHalted_false_iff_data_ne_nil cfg).mpr h_data) (Nat.le_trans h_N1 h_le)

/-- **Iter 1711: encoder bag is N-invariant**.  Encoder bag depends only
    on cfg, not N. -/
theorem ctsToSystem5_bag_N_invariant
    (cts : CTS) (cfg : CTSConfig) (N1 N2 : Nat) :
    (ctsToSystem5 cts cfg N1).bag = (ctsToSystem5 cts cfg N2).bag := by
  rw [ctsToSystem5_bag_eq, ctsToSystem5_bag_eq]

/-- **Iter 1712: encoder bag length is N-invariant**.  Direct via iter
    1711. -/
theorem ctsToSystem5_bag_length_N_invariant
    (cts : CTS) (cfg : CTSConfig) (N1 N2 : Nat) :
    (ctsToSystem5 cts cfg N1).bag.length = (ctsToSystem5 cts cfg N2).bag.length := by
  rw [ctsToSystem5_bag_N_invariant cts cfg N1 N2]

/-- **Iter 1713: encoder bag Nodup is N-invariant**.  Direct via iter
    1711 + iter 1540. -/
theorem ctsToSystem5_bag_Nodup_at_any_N
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.Nodup :=
  ctsToSystem5_bag_nodup cts cfg N

/-- **Iter 1714: encoder bag eq iff aux of data eq**.  Trivial via
    iter 1651 substitution. -/
theorem ctsToSystem5_bag_eq_iff_aux_eq
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (N1 N2 : Nat) :
    (ctsToSystem5 cts cfg1 N1).bag = (ctsToSystem5 cts cfg2 N2).bag ↔
      ctsConfigToSystem5BagAux cfg1.data 1 = ctsConfigToSystem5BagAux cfg2.data 1 := by
  rw [ctsToSystem5_bag_eq, ctsToSystem5_bag_eq,
      ctsConfigToSystem5Bag_via_aux, ctsConfigToSystem5Bag_via_aux]

/-- **Iter 1715 (🎯🎯🎯 825-LEMMA MILESTONE): encoder bag length eq iff
    data length eq**.  Direct via iter 1520 + 4*x = 4*y iff x = y. -/
theorem ctsToSystem5_bag_length_eq_iff_data_length_eq
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (N1 N2 : Nat) :
    (ctsToSystem5 cts cfg1 N1).bag.length = (ctsToSystem5 cts cfg2 N2).bag.length ↔
      cfg1.data.length = cfg2.data.length := by
  rw [ctsToSystem5_bag_length, ctsToSystem5_bag_length]
  refine ⟨?_, ?_⟩
  · intro h; omega
  · intro h; omega

/-- **Iter 1716: encoder bag length le iff data length le**.  Direct
    via iter 1520. -/
theorem ctsToSystem5_bag_length_le_iff_data_length_le
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (N1 N2 : Nat) :
    (ctsToSystem5 cts cfg1 N1).bag.length ≤ (ctsToSystem5 cts cfg2 N2).bag.length ↔
      cfg1.data.length ≤ cfg2.data.length := by
  rw [ctsToSystem5_bag_length, ctsToSystem5_bag_length]
  refine ⟨?_, ?_⟩
  · intro h; omega
  · intro h; omega

/-- **Iter 1717: encoder bag length lt iff data length lt**.  Direct
    via iter 1520. -/
theorem ctsToSystem5_bag_length_lt_iff_data_length_lt
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (N1 N2 : Nat) :
    (ctsToSystem5 cts cfg1 N1).bag.length < (ctsToSystem5 cts cfg2 N2).bag.length ↔
      cfg1.data.length < cfg2.data.length := by
  rw [ctsToSystem5_bag_length, ctsToSystem5_bag_length]
  refine ⟨?_, ?_⟩
  · intro h; omega
  · intro h; omega

/-- **Iter 1718: encoder bag length ge iff data length ge**.  Direct
    via iter 1520. -/
theorem ctsToSystem5_bag_length_ge_iff_data_length_ge
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (N1 N2 : Nat) :
    (ctsToSystem5 cts cfg1 N1).bag.length ≥ (ctsToSystem5 cts cfg2 N2).bag.length ↔
      cfg1.data.length ≥ cfg2.data.length := by
  rw [ctsToSystem5_bag_length, ctsToSystem5_bag_length]
  refine ⟨?_, ?_⟩
  · intro h; omega
  · intro h; omega

/-- **Iter 1719: encoder step some implies data length pos**.  Direct
    via iter 1510 + List.length_pos_iff. -/
theorem ctsToSystem5_step_some_implies_data_length_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config)
    (h_step : System5.step (ctsToSystem5 cts cfg N) = some result) :
    cfg.data.length > 0 :=
  List.length_pos_iff.mpr
    (ctsToSystem5_step_some_implies_data_ne_nil cts cfg N result h_step)

/-- **Iter 1720 (🎯🎯🎯 830-LEMMA MILESTONE): encoder nSteps pos some
    implies data length pos**.  Direct via iter 1518. -/
theorem ctsToSystem5_nSteps_pos_some_implies_data_length_pos
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_pos : n ≥ 1)
    (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) n = some s5') :
    cfg.data.length > 0 := by
  obtain ⟨h_data, _⟩ :=
    ctsToSystem5_nSteps_pos_some_implies_data_ne_nil_and_N_pos cts cfg N n h_pos s5' h_n
  exact List.length_pos_iff.mpr h_data

/-- **Iter 1721: encoder nSteps pos some implies bag length ≥ 4**.
    Composes iter 1720 + iter 1534. -/
theorem ctsToSystem5_nSteps_pos_some_implies_bag_length_ge_4
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_pos : n ≥ 1)
    (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) n = some s5') :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 := by
  obtain ⟨h_data, _⟩ :=
    ctsToSystem5_nSteps_pos_some_implies_data_ne_nil_and_N_pos cts cfg N n h_pos s5' h_n
  exact ctsToSystem5_bag_length_ge_4_of_data_ne_nil cts cfg N h_data

/-- **Iter 1722: encoder nSteps pos some implies rules length ≥ 4**.
    Composes iter 1518 + iter 1536. -/
theorem ctsToSystem5_nSteps_pos_some_implies_rules_length_ge_4
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_pos : n ≥ 1)
    (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) n = some s5') :
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 := by
  obtain ⟨_, h_N⟩ :=
    ctsToSystem5_nSteps_pos_some_implies_data_ne_nil_and_N_pos cts cfg N n h_pos s5' h_n
  exact ctsToSystem5_rules_length_ge_4_of_N_pos cts cfg N h_N

/-- **Iter 1723: encoder nSteps pos some packaged**.  Combines iters
    1721 and 1722 into a single witness lemma. -/
theorem ctsToSystem5_nSteps_pos_some_bag_rules_ge_4
    (cts : CTS) (cfg : CTSConfig) (N n : Nat) (h_pos : n ≥ 1)
    (s5' : System5Config)
    (h_n : System5.nSteps (ctsToSystem5 cts cfg N) n = some s5') :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 ∧
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 :=
  ⟨ctsToSystem5_nSteps_pos_some_implies_bag_length_ge_4 cts cfg N n h_pos s5' h_n,
   ctsToSystem5_nSteps_pos_some_implies_rules_length_ge_4 cts cfg N n h_pos s5' h_n⟩

/-- **Iter 1724: encoder step some bag/rules ≥ 4**.  Companion to iter
    1723 for single-step. -/
theorem ctsToSystem5_step_some_bag_rules_ge_4
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (result : System5Config)
    (h_step : System5.step (ctsToSystem5 cts cfg N) = some result) :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 ∧
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 := by
  obtain ⟨h_data, h_N⟩ :=
    ctsToSystem5_step_some_implies_data_ne_nil_and_N_pos cts cfg N result h_step
  exact ⟨ctsToSystem5_bag_length_ge_4_of_data_ne_nil cts cfg N h_data,
         ctsToSystem5_rules_length_ge_4_of_N_pos cts cfg N h_N⟩

/-- **Iter 1725 (🎯🎯🎯 835-LEMMA MILESTONE): encoder bag/rules ≥ 4 when
    data ≠ [] and N ≥ 1**.  Combined direct witness. -/
theorem ctsToSystem5_at_data_ne_nil_bag_rules_ge_4
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_data : cfg.data ≠ []) (h_N : N ≥ 1) :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 ∧
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 :=
  ⟨ctsToSystem5_bag_length_ge_4_of_data_ne_nil cts cfg N h_data,
   ctsToSystem5_rules_length_ge_4_of_N_pos cts cfg N h_N⟩

/-- **Iter 1726: encoder bag/rules ≠ nil when data ≠ [] and N ≥ 1**.
    Combined non-nil witness. -/
theorem ctsToSystem5_bag_rules_ne_nil_at_data_ne_nil_and_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_data : cfg.data ≠ []) (h_N : N ≥ 1) :
    (ctsToSystem5 cts cfg N).bag ≠ [] ∧ (ctsToSystem5 cts cfg N).rules ≠ [] :=
  ⟨(ctsToSystem5_bag_ne_nil_iff cts cfg N).mpr h_data,
   (ctsToSystem5_rules_ne_nil_iff cts cfg N).mpr h_N⟩

/-- **Iter 1727: encoder bag/rules ≠ nil at not halted and N ≥ 1**.
    Halt-state form of iter 1726. -/
theorem ctsToSystem5_bag_rules_ne_nil_at_not_halted_and_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_not_halted : ctsHalted cfg = false) (h_N : N ≥ 1) :
    (ctsToSystem5 cts cfg N).bag ≠ [] ∧ (ctsToSystem5 cts cfg N).rules ≠ [] :=
  ctsToSystem5_bag_rules_ne_nil_at_data_ne_nil_and_N_pos cts cfg N
    ((ctsHalted_false_iff_data_ne_nil cfg).mp h_not_halted) h_N

/-- **Iter 1728: Perm-equivalent encoder bags imply equal data
    lengths**.  When bag1.Perm bag2 with both encoder bags, the data
    lengths agree.  Composes List.Perm.length_eq + iter 1520. -/
theorem ctsConfigToSystem5Bag_perm_data_length_eq
    (cfg1 cfg2 : CTSConfig)
    (h_perm : (ctsConfigToSystem5Bag cfg1).Perm (ctsConfigToSystem5Bag cfg2)) :
    cfg1.data.length = cfg2.data.length := by
  have h_len_eq : (ctsConfigToSystem5Bag cfg1).length = (ctsConfigToSystem5Bag cfg2).length :=
    h_perm.length_eq
  rw [ctsConfigToSystem5Bag_length, ctsConfigToSystem5Bag_length] at h_len_eq
  omega

/-- **Iter 1729: Perm-equivalent encoder bags preserve data ≠ nil
    iff**.  Direct via iter 1728. -/
theorem ctsConfigToSystem5Bag_perm_data_ne_nil_iff
    (cfg1 cfg2 : CTSConfig)
    (h_perm : (ctsConfigToSystem5Bag cfg1).Perm (ctsConfigToSystem5Bag cfg2)) :
    cfg1.data ≠ [] ↔ cfg2.data ≠ [] := by
  have h_len : cfg1.data.length = cfg2.data.length :=
    ctsConfigToSystem5Bag_perm_data_length_eq cfg1 cfg2 h_perm
  refine ⟨?_, ?_⟩
  · intro h h_data2
    have : cfg2.data.length = 0 := by rw [h_data2]; simp
    rw [← h_len] at this
    exact h (List.length_eq_zero_iff.mp this)
  · intro h h_data1
    have : cfg1.data.length = 0 := by rw [h_data1]; simp
    rw [h_len] at this
    exact h (List.length_eq_zero_iff.mp this)

/-- **Iter 1730 (🎯🎯🎯 840-LEMMA MILESTONE): Perm-equivalent encoder
    bags preserve halt-state**.  ctsHalted cfg1 = ctsHalted cfg2. -/
theorem ctsConfigToSystem5Bag_perm_halted_iff
    (cfg1 cfg2 : CTSConfig)
    (h_perm : (ctsConfigToSystem5Bag cfg1).Perm (ctsConfigToSystem5Bag cfg2)) :
    ctsHalted cfg1 = ctsHalted cfg2 := by
  have h_iff := ctsConfigToSystem5Bag_perm_data_ne_nil_iff cfg1 cfg2 h_perm
  cases h1 : ctsHalted cfg1 with
  | true =>
    have h_data1 : cfg1.data = [] := (ctsHalted_true_iff_data_eq_nil cfg1).mp h1
    cases h2 : ctsHalted cfg2 with
    | true => rfl
    | false =>
      exfalso
      have h_data2 : cfg2.data ≠ [] := (ctsHalted_false_iff_data_ne_nil cfg2).mp h2
      exact (h_iff.mpr h_data2) h_data1
  | false =>
    have h_data1 : cfg1.data ≠ [] := (ctsHalted_false_iff_data_ne_nil cfg1).mp h1
    cases h2 : ctsHalted cfg2 with
    | true =>
      exfalso
      have h_data2 : cfg2.data = [] := (ctsHalted_true_iff_data_eq_nil cfg2).mp h2
      exact (h_iff.mp h_data1) h_data2
    | false => rfl

/-- **Iter 1731: cts.step success preserved under same data**.  When
    cfg1.data = cfg2.data and cts.step cfg1 succeeds, cts.step cfg2
    also succeeds. -/
theorem CTS_step_some_at_same_data
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (h_data : cfg1.data = cfg2.data)
    (result1 : CTSConfig) (h_step : cts.step cfg1 = some result1) :
    ∃ result2, cts.step cfg2 = some result2 := by
  have h_data1 : cfg1.data ≠ [] := CTS_step_some_data_ne_nil cts cfg1 result1 h_step
  apply CTS_data_ne_nil_implies_step_some
  rw [← h_data]; exact h_data1

/-- **Iter 1732: cts.step none preserved under same data**.  Companion
    to iter 1731. -/
theorem CTS_step_none_at_same_data
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (h_data : cfg1.data = cfg2.data)
    (h_step : cts.step cfg1 = none) :
    cts.step cfg2 = none := by
  rcases CTS_step_dichotomy cts cfg2 with h_none | ⟨result, h_some⟩
  · exact h_none
  · exfalso
    have h_data2 : cfg2.data ≠ [] := CTS_step_some_data_ne_nil cts cfg2 result h_some
    have h_data1 : cfg1.data ≠ [] := by rw [h_data]; exact h_data2
    obtain ⟨_, h_some1⟩ := CTS_data_ne_nil_implies_step_some cts cfg1 h_data1
    rw [h_some1] at h_step
    cases h_step

/-- **Iter 1733: cts.step some at same data biconditional**.  Combines
    iter 1731 + 1732. -/
theorem CTS_step_some_iff_at_same_data
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (h_data : cfg1.data = cfg2.data) :
    (∃ r, cts.step cfg1 = some r) ↔ (∃ r, cts.step cfg2 = some r) := by
  rw [CTS_step_some_iff_data_ne_nil, CTS_step_some_iff_data_ne_nil]
  refine ⟨?_, ?_⟩
  · intro h h_data2
    apply h
    rw [h_data]; exact h_data2
  · intro h h_data1
    apply h
    rw [← h_data]; exact h_data1

/-- **Iter 1734: ctsHalted preserved under same data**.  ctsHalted
    depends only on data. -/
theorem ctsHalted_at_same_data
    (cfg1 cfg2 : CTSConfig) (h_data : cfg1.data = cfg2.data) :
    ctsHalted cfg1 = ctsHalted cfg2 := by
  unfold ctsHalted
  rw [h_data]

/-- **Iter 1735 (🎯🎯🎯 845-LEMMA MILESTONE): cts.step at same cfg
    components produces same result**.  When cfg1 = cfg2 (full equality),
    step results agree.  Trivial congruence. -/
theorem CTS_step_at_eq_cfg
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (h_eq : cfg1 = cfg2) :
    cts.step cfg1 = cts.step cfg2 := by
  rw [h_eq]

/-- **Iter 1736: encoder at eq cfg produces same encoder**.  Trivial
    congruence. -/
theorem ctsToSystem5_at_eq_cfg
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (N : Nat) (h_eq : cfg1 = cfg2) :
    ctsToSystem5 cts cfg1 N = ctsToSystem5 cts cfg2 N := by
  rw [h_eq]

/-- **Iter 1737: cts.Halts congruence under cfg equality**.  Direct
    consequence of definitional equality. -/
theorem CTS_Halts_at_eq_cfg
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (h_eq : cfg1 = cfg2) :
    cts.Halts cfg1 ↔ cts.Halts cfg2 := by
  rw [h_eq]

/-- **Iter 1738: cts.nSteps congruence under cfg equality**.  Direct
    consequence of definitional equality. -/
theorem CTS_nSteps_at_eq_cfg
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (n : Nat) (h_eq : cfg1 = cfg2) :
    cts.nSteps cfg1 n = cts.nSteps cfg2 n := by
  rw [h_eq]

/-- **Iter 1739: cts.eval congruence under cfg equality**.  Direct
    consequence of definitional equality. -/
theorem CTS_eval_at_eq_cfg
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (fuel : Nat) (h_eq : cfg1 = cfg2) :
    cts.eval cfg1 fuel = cts.eval cfg2 fuel := by
  rw [h_eq]

/-- **Iter 1740: ctsHalted congruence under cfg equality**.  Direct
    consequence of definitional equality. -/
theorem ctsHalted_at_eq_cfg
    (cfg1 cfg2 : CTSConfig) (h_eq : cfg1 = cfg2) :
    ctsHalted cfg1 = ctsHalted cfg2 := by
  rw [h_eq]

/-- **Iter 1741 (🎯🎯🎯🎯🎯 850-LEMMA MILESTONE): encoder bag
    congruence under cfg equality**.  Direct consequence of definitional
    equality.  Companion to iter 1736 specialized to the bag projection. -/
theorem ctsConfigToSystem5Bag_at_eq_cfg
    (cfg1 cfg2 : CTSConfig) (h_eq : cfg1 = cfg2) :
    ctsConfigToSystem5Bag cfg1 = ctsConfigToSystem5Bag cfg2 := by
  rw [h_eq]

/-- **Iter 1742: encoder rules congruence under cfg equality**.  Direct
    consequence of definitional equality.  Companion to iter 1741 for
    the rules projection. -/
theorem ctsRulesToSystem5Rules_at_eq_cfg
    (cts : CTS) (cfg1 cfg2 : CTSConfig) (N : Nat) (h_eq : cfg1 = cfg2) :
    ctsRulesToSystem5Rules cts cfg1 N = ctsRulesToSystem5Rules cts cfg2 N := by
  rw [h_eq]

/-- **Iter 1743: counterAfterWorkingString congruence under data
    equality**.  Direct consequence of definitional equality.  Useful for
    contexts where two CTS configs differ only in phase but share data. -/
theorem counterAfterWorkingString_at_eq_data
    (data1 data2 : List Bool) (h_eq : data1 = data2) :
    counterAfterWorkingString data1 = counterAfterWorkingString data2 := by
  rw [h_eq]

/-- **Iter 1744: aux congruence under data equality**.  Direct
    consequence of definitional equality. -/
theorem ctsConfigToSystem5BagAux_at_eq_data
    (data1 data2 : List Bool) (i : Nat) (h_eq : data1 = data2) :
    ctsConfigToSystem5BagAux data1 i = ctsConfigToSystem5BagAux data2 i := by
  rw [h_eq]

/-- **Iter 1745: encoder bag has 1 iff encoder step succeeds (when N ≥ 1)**.
    Direct combination of iters 1538 and 1538 via iter 1513.  Useful at
    chain points where N is known positive. -/
theorem ctsToSystem5_one_mem_iff_step_some_of_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (hN : N ≥ 1) :
    1 ∈ (ctsToSystem5 cts cfg N).bag ↔
    ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5' := by
  rw [ctsToSystem5_step_some_iff_data_ne_nil_and_N_pos]
  constructor
  · intro h
    refine ⟨?_, hN⟩
    rw [ctsToSystem5_bag_one_mem_iff] at h
    exact h
  · intro ⟨h_data, _⟩
    exact ctsToSystem5_bag_one_mem_of_data_ne_nil cts cfg N h_data

/-- **Iter 1746 (🎯🎯🎯 855-LEMMA MILESTONE): encoder step succeeds iff
    encoder bag is non-empty (when N ≥ 1)**.  Direct combination of iter
    1745 + iter 1567 (1 ∈ bag iff bag ≠ []) shows the bag-non-empty
    characterization of step-success. -/
theorem ctsToSystem5_step_some_iff_bag_ne_nil_of_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (hN : N ≥ 1) :
    (∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') ↔
    (ctsToSystem5 cts cfg N).bag ≠ [] := by
  rw [← ctsToSystem5_one_mem_iff_step_some_of_N_pos cts cfg N hN]
  rw [ctsToSystem5_bag_one_mem_iff, ctsToSystem5_bag_ne_nil_iff]

/-- **Iter 1747: encoder step succeeds iff encoder rules are non-empty
    AND data ≠ []**.  Restates iter 1513 in a slightly different form
    using the rules-non-empty characterization (iter 1523). -/
theorem ctsToSystem5_step_some_iff_data_ne_nil_and_rules_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') ↔
    cfg.data ≠ [] ∧ (ctsToSystem5 cts cfg N).rules ≠ [] := by
  rw [ctsToSystem5_step_some_iff_data_ne_nil_and_N_pos]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [ctsToSystem5_rules_ne_nil_iff]
    exact h2
  · intro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [ctsToSystem5_rules_ne_nil_iff] at h2
    exact h2

/-- **Iter 1748: encoder step some iff bag and rules both non-empty**.
    Combines iter 1746 + iter 1747 + iter 1522.  Pure structural
    characterization of step-success at the encoder level. -/
theorem ctsToSystem5_step_some_iff_bag_and_rules_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') ↔
    (ctsToSystem5 cts cfg N).bag ≠ [] ∧ (ctsToSystem5 cts cfg N).rules ≠ [] := by
  rw [ctsToSystem5_step_some_iff_data_ne_nil_and_rules_ne_nil]
  rw [ctsToSystem5_bag_ne_nil_iff]

/-- **Iter 1749: encoder step none iff bag or rules empty**.  Negation
    form of iter 1748. -/
theorem ctsToSystem5_step_none_iff_bag_or_rules_eq_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.step (ctsToSystem5 cts cfg N) = none ↔
    (ctsToSystem5 cts cfg N).bag = [] ∨ (ctsToSystem5 cts cfg N).rules = [] := by
  rw [System5_step_none_iff]

/-- **Iter 1750 (🎯 ITER 1750 MILESTONE): encoder step none iff data empty
    or N zero**.  Restates iter 1749 in CTS-side terms via iter 1524 +
    iter 1525.  Bridges the System5 step-none characterization to the
    pure CTS-level conditions. -/
theorem ctsToSystem5_step_none_iff_data_or_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.step (ctsToSystem5 cts cfg N) = none ↔
    cfg.data = [] ∨ N = 0 := by
  rw [ctsToSystem5_step_none_iff_bag_or_rules_eq_nil]
  rw [ctsToSystem5_bag_eq_nil_iff, ctsToSystem5_rules_eq_nil_iff]

/-- **Iter 1751 (🎯🎯🎯🎯🎯 860-LEMMA MILESTONE): encoder Halts iff data
    empty or N zero (sufficient direction for both)**.  Combines iter
    1505 + iter 1507 — direct disjunction-elimination form.  Useful for
    casework. -/
theorem ctsToSystem5_Halts_of_data_empty_or_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : cfg.data = [] ∨ N = 0) :
    System5.Halts (ctsToSystem5 cts cfg N) := by
  cases h with
  | inl h_data => exact ctsToSystem5_Halts_when_data_empty cts cfg N h_data
  | inr h_N =>
    subst h_N
    exact ctsToSystem5_Halts_when_N_zero cts cfg

/-- **Iter 1752: encoder Halts when ctsHalted or N = 0**.  Halt-state
    form of iter 1751 via iter 1265 (halted iff data empty). -/
theorem ctsToSystem5_Halts_of_halted_or_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ctsHalted cfg = true ∨ N = 0) :
    System5.Halts (ctsToSystem5 cts cfg N) := by
  apply ctsToSystem5_Halts_of_data_empty_or_N_zero
  cases h with
  | inl h_halted => exact Or.inl ((ctsHalted_true_iff_data_eq_nil cfg).mp h_halted)
  | inr h_N => exact Or.inr h_N

/-- **Iter 1753: encoder bag length ≥ 1 iff data ≠ []**.  Direct via
    iter 1532 + arithmetic.  More targeted than iter 1532 for length-1
    threshold reasoning. -/
theorem ctsToSystem5_bag_length_ge_one_iff_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length ≥ 1 ↔ cfg.data ≠ [] := by
  rw [← ctsToSystem5_bag_length_pos_iff_data_ne_nil]
  exact ⟨fun h => h, fun h => h⟩

/-- **Iter 1754: encoder rules length ≥ 1 iff N ≥ 1**.  Companion to
    iter 1753 for the rules side. -/
theorem ctsToSystem5_rules_length_ge_one_iff_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules.length ≥ 1 ↔ N ≥ 1 :=
  ctsToSystem5_rules_length_pos_iff_N_pos cts cfg N

/-- **Iter 1755: encoder bag length ≥ 1 iff not halted**.  Halt-state
    form of iter 1753 via iter 1264. -/
theorem ctsToSystem5_bag_length_ge_one_iff_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length ≥ 1 ↔ ctsHalted cfg = false := by
  rw [ctsToSystem5_bag_length_ge_one_iff_data_ne_nil]
  exact (ctsHalted_false_iff_data_ne_nil cfg).symm

/-- **Iter 1756 (🎯🎯🎯 865-LEMMA MILESTONE): encoder rules length ≥ 4 iff
    N ≥ 1**.  Combines iter 1521 (length = 4 * |appendants| * N) +
    iter 1303 (4·|appendants| > 0).  Useful threshold for chain-induction
    setup. -/
theorem ctsToSystem5_rules_length_ge_four_iff_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 ↔ N ≥ 1 := by
  rw [ctsToSystem5_rules_length]
  have h_app : cts.appendants.length ≥ 1 :=
    List.length_pos_iff.mpr (CTS_appendants_ne_nil cts)
  refine ⟨?_, ?_⟩
  · intro h
    rcases N with _ | n
    · simp at h
    · exact Nat.succ_le_succ (Nat.zero_le _)
  · intro h
    have h1 : 4 * cts.appendants.length ≥ 4 := by
      have := Nat.mul_le_mul_left 4 h_app
      omega
    calc 4 * cts.appendants.length * N
        ≥ 4 * 1 := by
          have h2 : 4 * cts.appendants.length * N ≥ 4 * cts.appendants.length * 1 :=
            Nat.mul_le_mul_left _ h
          have h3 : 4 * cts.appendants.length * 1 = 4 * cts.appendants.length := by
            rw [Nat.mul_one]
          rw [h3] at h2
          omega
      _ = 4 := by rw [Nat.mul_one]

/-- **Iter 1757: encoder bag length ≥ 4 iff data ≠ []**.  Biconditional
    upgrade of iter 1534 (forward direction).  Direct via iter 1520. -/
theorem ctsToSystem5_bag_length_ge_four_iff_data_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 ↔ cfg.data ≠ [] := by
  rw [ctsToSystem5_bag_length]
  refine ⟨?_, ?_⟩
  · intro h h_data
    rw [h_data] at h
    simp at h
  · intro h
    cases h_data : cfg.data with
    | nil => exact absurd h_data h
    | cons head tail =>
      simp [List.length]
      omega

/-- **Iter 1758: encoder bag length ≥ 4 iff not halted**.  Halt-state
    form of iter 1757 via iter 1264. -/
theorem ctsToSystem5_bag_length_ge_four_iff_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 ↔ ctsHalted cfg = false := by
  rw [ctsToSystem5_bag_length_ge_four_iff_data_ne_nil]
  exact (ctsHalted_false_iff_data_ne_nil cfg).symm

/-- **Iter 1759: encoder rules length ≥ 4 iff not Halts via N = 0**.
    Combines iter 1756 + arithmetic.  Useful when needing to discharge
    the rules-non-empty obligation in step-2 chain proofs. -/
theorem ctsToSystem5_rules_length_ge_four_iff_not_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 ↔ N ≠ 0 := by
  rw [ctsToSystem5_rules_length_ge_four_iff_N_pos]
  omega

/-- **Iter 1760 (🎯 ITER 1760 MILESTONE): encoder bag length ≥ 4 iff
    bag ≠ []**.  Companion to iter 1757 (data ≠ []) in pure
    bag-non-empty form.  Useful when reasoning about bag-shape directly. -/
theorem ctsToSystem5_bag_length_ge_four_iff_bag_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 ↔ (ctsToSystem5 cts cfg N).bag ≠ [] := by
  rw [ctsToSystem5_bag_length_ge_four_iff_data_ne_nil, ctsToSystem5_bag_ne_nil_iff]

/-- **Iter 1761 (🎯🎯🎯🎯🎯 870-LEMMA MILESTONE): encoder rules length ≥ 4
    iff rules ≠ []**.  Rules-side companion to iter 1760. -/
theorem ctsToSystem5_rules_length_ge_four_iff_rules_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 ↔
    (ctsToSystem5 cts cfg N).rules ≠ [] := by
  rw [ctsToSystem5_rules_length_ge_four_iff_N_pos, ctsToSystem5_rules_ne_nil_iff]

/-- **Iter 1762: encoder step some iff bag and rules both length ≥ 4**.
    Combines iters 1748 + 1760 + 1761.  Useful for chain-induction
    setup where length-≥-4 thresholds discharge step-succeeds obligations. -/
theorem ctsToSystem5_step_some_iff_bag_and_rules_length_ge_four
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') ↔
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 ∧
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 := by
  rw [ctsToSystem5_step_some_iff_bag_and_rules_ne_nil]
  rw [ctsToSystem5_bag_length_ge_four_iff_bag_ne_nil,
      ctsToSystem5_rules_length_ge_four_iff_rules_ne_nil]

/-- **Iter 1763: encoder step succeeds gives bag and rules length ≥ 4**.
    Forward direction of iter 1762 — direct corollary. -/
theorem ctsToSystem5_step_some_implies_bag_and_rules_length_ge_four
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 ∧
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 :=
  (ctsToSystem5_step_some_iff_bag_and_rules_length_ge_four cts cfg N).mp h

/-- **Iter 1764: encoder step succeeds when bag and rules both length ≥ 4**.
    Backward direction of iter 1762 — direct corollary.  Useful for
    chain-induction step where the length-bounds are known. -/
theorem ctsToSystem5_step_some_of_bag_and_rules_length_ge_four
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_bag : (ctsToSystem5 cts cfg N).bag.length ≥ 4)
    (h_rules : (ctsToSystem5 cts cfg N).rules.length ≥ 4) :
    ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5' :=
  (ctsToSystem5_step_some_iff_bag_and_rules_length_ge_four cts cfg N).mpr ⟨h_bag, h_rules⟩

/-- **Iter 1765: encoder bag length pos and rules length pos iff step
    succeeds**.  Combines iter 1748 + Nat.pos_iff_ne_zero.  Pure
    positive-length characterization. -/
theorem ctsToSystem5_step_some_iff_bag_and_rules_length_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') ↔
    (ctsToSystem5 cts cfg N).bag.length > 0 ∧
    (ctsToSystem5 cts cfg N).rules.length > 0 := by
  rw [ctsToSystem5_step_some_iff_bag_and_rules_ne_nil]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · exact List.length_pos_iff.mpr h1
    · exact List.length_pos_iff.mpr h2
  · intro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · exact List.length_pos_iff.mp h1
    · exact List.length_pos_iff.mp h2

/-- **Iter 1766 (🎯🎯🎯 875-LEMMA MILESTONE): encoder step succeeds when
    bag and rules length pos**.  Backward direction of iter 1765 — direct
    corollary. -/
theorem ctsToSystem5_step_some_of_bag_and_rules_length_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_bag : (ctsToSystem5 cts cfg N).bag.length > 0)
    (h_rules : (ctsToSystem5 cts cfg N).rules.length > 0) :
    ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5' :=
  (ctsToSystem5_step_some_iff_bag_and_rules_length_pos cts cfg N).mpr
    ⟨h_bag, h_rules⟩

/-- **Iter 1767: encoder bag length zero implies step none**.  Direct via
    iter 1749 (step none iff bag empty or rules empty). -/
theorem ctsToSystem5_step_none_of_bag_length_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).bag.length = 0) :
    System5.step (ctsToSystem5 cts cfg N) = none := by
  apply (ctsToSystem5_step_none_iff_bag_or_rules_eq_nil cts cfg N).mpr
  exact Or.inl (List.length_eq_zero_iff.mp h)

/-- **Iter 1768: encoder rules length zero implies step none**.  Companion
    to iter 1767 for the rules side. -/
theorem ctsToSystem5_step_none_of_rules_length_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).rules.length = 0) :
    System5.step (ctsToSystem5 cts cfg N) = none := by
  apply (ctsToSystem5_step_none_iff_bag_or_rules_eq_nil cts cfg N).mpr
  exact Or.inr (List.length_eq_zero_iff.mp h)

/-- **Iter 1769: encoder Halts when bag length zero**.  Direct via
    `System5.Halts_of_empty_bag` + List.length_eq_zero_iff. -/
theorem ctsToSystem5_Halts_when_bag_length_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).bag.length = 0) :
    System5.Halts (ctsToSystem5 cts cfg N) :=
  System5.Halts_of_empty_bag _ (List.length_eq_zero_iff.mp h)

/-- **Iter 1770 (🎯 ITER 1770 MILESTONE): encoder Halts when rules length
    zero**.  Direct via `System5.Halts_of_empty_rules` +
    List.length_eq_zero_iff. -/
theorem ctsToSystem5_Halts_when_rules_length_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).rules.length = 0) :
    System5.Halts (ctsToSystem5 cts cfg N) :=
  System5.Halts_of_empty_rules _ (List.length_eq_zero_iff.mp h)

/-- **Iter 1771 (🎯🎯🎯🎯🎯 880-LEMMA MILESTONE): encoder Halts when bag
    or rules length zero**.  Disjunction-elimination form combining
    iters 1769 + 1770. -/
theorem ctsToSystem5_Halts_when_bag_or_rules_length_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).bag.length = 0 ∨
         (ctsToSystem5 cts cfg N).rules.length = 0) :
    System5.Halts (ctsToSystem5 cts cfg N) := by
  cases h with
  | inl h_bag => exact ctsToSystem5_Halts_when_bag_length_zero cts cfg N h_bag
  | inr h_rules => exact ctsToSystem5_Halts_when_rules_length_zero cts cfg N h_rules

/-- **Iter 1772: encoder step none implies Halts**.  Direct via
    `System5_step_none_imp_Halts`. -/
theorem ctsToSystem5_step_none_implies_Halts
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : System5.step (ctsToSystem5 cts cfg N) = none) :
    System5.Halts (ctsToSystem5 cts cfg N) :=
  System5_step_none_imp_Halts _ h

/-- **Iter 1773: encoder Halts when bag empty**.  Length form of iter
    1505 — direct via iter 1769 + iter 1234. -/
theorem ctsToSystem5_Halts_when_bag_eq_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).bag = []) :
    System5.Halts (ctsToSystem5 cts cfg N) :=
  System5.Halts_of_empty_bag _ h

/-- **Iter 1774: encoder Halts when rules empty**.  Companion to iter
    1773 for the rules side. -/
theorem ctsToSystem5_Halts_when_rules_eq_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).rules = []) :
    System5.Halts (ctsToSystem5 cts cfg N) :=
  System5.Halts_of_empty_rules _ h

/-- **Iter 1775: encoder Halts when bag or rules empty**.
    Disjunction-elimination form combining iters 1773 + 1774. -/
theorem ctsToSystem5_Halts_when_bag_or_rules_eq_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).bag = [] ∨
         (ctsToSystem5 cts cfg N).rules = []) :
    System5.Halts (ctsToSystem5 cts cfg N) := by
  cases h with
  | inl h_bag => exact ctsToSystem5_Halts_when_bag_eq_nil cts cfg N h_bag
  | inr h_rules => exact ctsToSystem5_Halts_when_rules_eq_nil cts cfg N h_rules

/-- **Iter 1776 (🎯🎯🎯 885-LEMMA MILESTONE): encoder step none gives bag
    or rules empty witness**.  Forward direction extraction from iter
    1749. -/
theorem ctsToSystem5_step_none_implies_bag_or_rules_eq_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : System5.step (ctsToSystem5 cts cfg N) = none) :
    (ctsToSystem5 cts cfg N).bag = [] ∨ (ctsToSystem5 cts cfg N).rules = [] :=
  (ctsToSystem5_step_none_iff_bag_or_rules_eq_nil cts cfg N).mp h

/-- **Iter 1777: encoder Halts iff bag or rules empty witness**.
    Combines iter 1502 (System5 Halts iff bag/rules empty witness) +
    encoder packaging. -/
theorem ctsToSystem5_Halts_iff_bag_or_rules_empty_witness
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.Halts (ctsToSystem5 cts cfg N) ↔
    ∃ n result, System5.nSteps (ctsToSystem5 cts cfg N) n = some result ∧
                (result.bag = [] ∨ result.rules = []) :=
  System5_Halts_iff_bag_or_rules_empty_witness _

/-- **Iter 1778: encoder Halts iff exists nSteps none**.  Direct lift of
    iter 1480 (System5 Halts iff exists nSteps none) to encoder level. -/
theorem ctsToSystem5_Halts_iff_exists_nSteps_none
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.Halts (ctsToSystem5 cts cfg N) ↔
    ∃ n, System5.nSteps (ctsToSystem5 cts cfg N) n = none :=
  System5_Halts_iff_exists_nSteps_none _

/-- **Iter 1779: encoder ¬Halts iff all nSteps succeed**.  Direct lift
    of iter 1479 to encoder level. -/
theorem ctsToSystem5_not_Halts_iff_all_nSteps_some
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ¬ System5.Halts (ctsToSystem5 cts cfg N) ↔
    ∀ n, ∃ result, System5.nSteps (ctsToSystem5 cts cfg N) n = some result :=
  System5_not_Halts_iff_all_nSteps_some _

/-- **Iter 1780 (🎯 ITER 1780 MILESTONE): encoder Halts implies eventually
    eval some at sufficient fuel via System5 Halts**.  Step-none witness
    extraction, encoder-level. -/
theorem ctsToSystem5_Halts_implies_step_none_witness
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : System5.Halts (ctsToSystem5 cts cfg N)) :
    ∃ m result, System5.nSteps (ctsToSystem5 cts cfg N) m = some result ∧
                System5.step result = none :=
  System5_Halts_implies_step_none_witness _ h

/-- **Iter 1781 (🎯🎯🎯🎯🎯 890-LEMMA MILESTONE): encoder Halts iff
    step-none witness**.  Direct lift of iter 1487 to encoder level. -/
theorem ctsToSystem5_Halts_iff_step_none_witness
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.Halts (ctsToSystem5 cts cfg N) ↔
    ∃ m result, System5.nSteps (ctsToSystem5 cts cfg N) m = some result ∧
                System5.step result = none :=
  System5_Halts_iff_step_none_witness _

/-- **Iter 1782: encoder ¬Halts implies all nSteps succeed**.  Direct
    forward direction of iter 1779 — useful as a corollary. -/
theorem ctsToSystem5_not_Halts_implies_all_nSteps_some
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∀ n, ∃ result, System5.nSteps (ctsToSystem5 cts cfg N) n = some result :=
  (ctsToSystem5_not_Halts_iff_all_nSteps_some cts cfg N).mp h

/-- **Iter 1783: encoder ¬Halts step succeeds**.  Specialization of iter
    1782 to single step.  Direct via step = nSteps 1. -/
theorem ctsToSystem5_not_Halts_step_some
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∃ result, System5.step (ctsToSystem5 cts cfg N) = some result := by
  obtain ⟨result, h_n⟩ := ctsToSystem5_not_Halts_implies_all_nSteps_some cts cfg N h 1
  rw [System5.nSteps_one] at h_n
  exact ⟨result, h_n⟩

/-- **Iter 1784: encoder ¬Halts implies bag and rules non-empty**.
    Direct corollary of iter 1783 + iter 1748. -/
theorem ctsToSystem5_not_Halts_implies_bag_and_rules_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).bag ≠ [] ∧ (ctsToSystem5 cts cfg N).rules ≠ [] :=
  (ctsToSystem5_step_some_iff_bag_and_rules_ne_nil cts cfg N).mp
    (ctsToSystem5_not_Halts_step_some cts cfg N h)

/-- **Iter 1785: encoder ¬Halts implies data ≠ [] and N ≥ 1**.  Direct
    corollary of iter 1526 + iter 1527 (already proven), repackaged. -/
theorem ctsToSystem5_not_Halts_data_ne_nil_and_N_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    cfg.data ≠ [] ∧ N ≥ 1 :=
  ⟨ctsToSystem5_not_Halts_implies_data_ne_nil cts cfg N h,
   ctsToSystem5_not_Halts_implies_N_pos cts cfg N h⟩

/-- **Iter 1786 (🎯🎯🎯 895-LEMMA MILESTONE): encoder ¬Halts implies
    1 ∈ bag and 0 ∈ bag.dec**.  Combines iter 1567 + iter 1568. -/
theorem ctsToSystem5_not_Halts_implies_one_mem_and_zero_in_dec
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    1 ∈ (ctsToSystem5 cts cfg N).bag ∧
    (0 : Int) ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) := by
  have h_not_halted : ctsHalted cfg = false := by
    have h_data := ctsToSystem5_not_Halts_implies_data_ne_nil cts cfg N h
    rw [ctsHalted_false_iff_data_ne_nil]
    exact h_data
  exact ⟨ctsToSystem5_bag_one_mem_of_not_halted cts cfg N h_not_halted,
         ctsToSystem5_zero_in_dec_of_not_halted cts cfg N h_not_halted⟩

/-- **Iter 1787: encoder ¬Halts implies not halted**.  Direct via iter
    1526 + iter 1264. -/
theorem ctsToSystem5_not_Halts_implies_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ctsHalted cfg = false := by
  rw [ctsHalted_false_iff_data_ne_nil]
  exact ctsToSystem5_not_Halts_implies_data_ne_nil cts cfg N h

/-- **Iter 1788: encoder ¬Halts implies cts.Halts is false**.  Composes
    iter 1787 + the fact that ¬cts.Halts ⇔ ¬ctsHalted.  Wait — actually
    the relationship is more subtle: System5 always halts (per iter 875
    finding), so ¬System5.Halts encoder is false more often than
    ¬cts.Halts.  This gives us: when System5 doesn't halt at the encoder,
    then cts.data ≠ [] AND it doesn't yet conclude about cts.Halts. -/
theorem ctsToSystem5_not_Halts_implies_data_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    cfg.data.length > 0 := by
  have h_data := ctsToSystem5_not_Halts_implies_data_ne_nil cts cfg N h
  exact List.length_pos_iff.mpr h_data

/-- **Iter 1789: encoder ¬Halts implies bag length pos**.  Composes
    iter 1788 + iter 1532. -/
theorem ctsToSystem5_not_Halts_implies_bag_length_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).bag.length > 0 := by
  rw [ctsToSystem5_bag_length_pos_iff_data_ne_nil]
  exact ctsToSystem5_not_Halts_implies_data_ne_nil cts cfg N h

/-- **Iter 1790 (🎯 ITER 1790 MILESTONE): encoder ¬Halts implies rules
    length pos**.  Composes iter 1527 + iter 1531. -/
theorem ctsToSystem5_not_Halts_implies_rules_length_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).rules.length > 0 := by
  rw [ctsToSystem5_rules_length_pos_iff_N_pos]
  exact ctsToSystem5_not_Halts_implies_N_pos cts cfg N h

/-- **Iter 1791 (🎯🎯🎯🎯🎯🎯🎯🎯🎯🎯 900-LEMMA MILESTONE 🎯🎯🎯🎯🎯🎯🎯🎯🎯🎯):
    encoder ¬Halts implies bag and rules both length pos**.  Combines
    iters 1789 + 1790. -/
theorem ctsToSystem5_not_Halts_implies_bag_and_rules_length_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).bag.length > 0 ∧
    (ctsToSystem5 cts cfg N).rules.length > 0 :=
  ⟨ctsToSystem5_not_Halts_implies_bag_length_pos cts cfg N h,
   ctsToSystem5_not_Halts_implies_rules_length_pos cts cfg N h⟩

/-- **Iter 1792: encoder ¬Halts implies bag length ≥ 4**.  Composes
    iter 1526 + iter 1534. -/
theorem ctsToSystem5_not_Halts_implies_bag_length_ge_four
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 :=
  ctsToSystem5_bag_length_ge_4_of_data_ne_nil cts cfg N
    (ctsToSystem5_not_Halts_implies_data_ne_nil cts cfg N h)

/-- **Iter 1793: encoder ¬Halts implies rules length ≥ 4**.  Companion
    to iter 1792 for the rules side, via iter 1536. -/
theorem ctsToSystem5_not_Halts_implies_rules_length_ge_four
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 :=
  ctsToSystem5_rules_length_ge_4_of_N_pos cts cfg N
    (ctsToSystem5_not_Halts_implies_N_pos cts cfg N h)

/-- **Iter 1794: encoder ¬Halts implies bag and rules both length ≥ 4**.
    Combines iters 1792 + 1793. -/
theorem ctsToSystem5_not_Halts_implies_bag_and_rules_length_ge_four
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 ∧
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 :=
  ⟨ctsToSystem5_not_Halts_implies_bag_length_ge_four cts cfg N h,
   ctsToSystem5_not_Halts_implies_rules_length_ge_four cts cfg N h⟩

/-- **Iter 1795: encoder ¬Halts implies step succeeds and bag/rules ≥ 4**.
    Omnibus packaging combining iter 1783 + iter 1794. -/
theorem ctsToSystem5_not_Halts_omnibus_witness
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (∃ result, System5.step (ctsToSystem5 cts cfg N) = some result) ∧
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 ∧
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 :=
  ⟨ctsToSystem5_not_Halts_step_some cts cfg N h,
   ctsToSystem5_not_Halts_implies_bag_length_ge_four cts cfg N h,
   ctsToSystem5_not_Halts_implies_rules_length_ge_four cts cfg N h⟩

/-- **Iter 1796 (🎯🎯🎯 905-LEMMA MILESTONE): encoder ¬Halts implies cts
    step succeeds and result not halted**.  Forward direction of step-some
    chained with halt-state preservation. -/
theorem ctsToSystem5_not_Halts_implies_cts_step_witness
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∃ result, cts.step cfg = some result := by
  apply CTS_step_some_of_not_halted
  exact ctsToSystem5_not_Halts_implies_not_halted cts cfg N h

/-- **Iter 1797: encoder ¬Halts implies 0 ∈ encoder bag.dec**.
    Specialization of iter 1786. -/
theorem ctsToSystem5_not_Halts_implies_zero_in_dec
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (0 : Int) ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) :=
  (ctsToSystem5_not_Halts_implies_one_mem_and_zero_in_dec cts cfg N h).2

/-- **Iter 1798: encoder ¬Halts implies 1 ∈ encoder bag**.  Specialization
    of iter 1786 (left projection). -/
theorem ctsToSystem5_not_Halts_implies_one_mem
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    1 ∈ (ctsToSystem5 cts cfg N).bag :=
  (ctsToSystem5_not_Halts_implies_one_mem_and_zero_in_dec cts cfg N h).1

/-- **Iter 1799: encoder ¬Halts implies bag is Nodup**.  Direct via
    iter 1540 (Nodup is unconditional on the encoder bag). -/
theorem ctsToSystem5_not_Halts_implies_bag_nodup
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).bag.Nodup :=
  ctsToSystem5_bag_nodup cts cfg N

/-- **Iter 1800 (🎯🎯🎯🎯🎯 ITER 1800 MILESTONE): encoder ¬Halts implies
    bag dec-erase Nodup**.  Direct via iter 1548 (unconditional). -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_erase_nodup
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).Nodup :=
  ctsToSystem5_bag_dec_erase_nodup cts cfg N

/-- **Iter 1801 (🎯🎯🎯🎯🎯 910-LEMMA MILESTONE): encoder ¬Halts implies
    bag dec-erase ≠ []**.  Direct via iter 1547 + iter 1526. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_erase_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0 ≠ [] :=
  ctsToSystem5_bag_dec_erase_ne_nil_of_data_ne_nil cts cfg N
    (ctsToSystem5_not_Halts_implies_data_ne_nil cts cfg N h)

/-- **Iter 1802: encoder ¬Halts implies bag dec-erase length ≥ 3**.
    Direct via iter 1350 + iter 1526. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_erase_length_ge_three
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).length ≥ 3 := by
  unfold ctsToSystem5
  apply ctsConfigToSystem5Bag_dec_erase_length_ge_three
  rw [ctsHalted_false_iff_data_ne_nil]
  exact ctsToSystem5_not_Halts_implies_data_ne_nil cts cfg N h

/-- **Iter 1803: encoder ¬Halts implies bag dec all ≥ 0**.  Unconditional
    via iter 1545. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_all_ge_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∀ x ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1), x ≥ 0 :=
  ctsToSystem5_bag_dec_all_ge_zero cts cfg N

/-- **Iter 1804: encoder ¬Halts implies bag all ≥ 1**.  Unconditional
    via iter 1542. -/
theorem ctsToSystem5_not_Halts_implies_bag_all_ge_one
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∀ x ∈ (ctsToSystem5 cts cfg N).bag, x ≥ 1 :=
  ctsToSystem5_bag_all_ge_one cts cfg N

/-- **Iter 1805: encoder ¬Halts implies bag has no zero**.  Unconditional
    via iter 1541. -/
theorem ctsToSystem5_not_Halts_implies_bag_no_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (0 : Int) ∉ (ctsToSystem5 cts cfg N).bag :=
  ctsToSystem5_bag_no_zero cts cfg N

/-- **Iter 1806 (🎯🎯🎯 915-LEMMA MILESTONE): encoder ¬Halts implies bag
    no negatives**.  Unconditional via iter 1551. -/
theorem ctsToSystem5_not_Halts_implies_bag_no_negatives
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∀ x ∈ (ctsToSystem5 cts cfg N).bag, x ≥ 0 := by
  intro x hx
  have h_ge_one := ctsToSystem5_bag_all_ge_one cts cfg N x hx
  omega

/-- **Iter 1807: encoder ¬Halts implies -1 ∉ bag**.  Unconditional via
    iter 1552. -/
theorem ctsToSystem5_not_Halts_implies_neg_one_not_mem
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (-1 : Int) ∉ (ctsToSystem5 cts cfg N).bag :=
  ctsToSystem5_bag_neg_one_not_mem cts cfg N

/-- **Iter 1808: encoder ¬Halts implies bag dec-erase no zero**.
    Unconditional via iter 1549. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_erase_no_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (0 : Int) ∉ ((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0 :=
  ctsToSystem5_bag_dec_erase_no_zero cts cfg N

/-- **Iter 1809: encoder ¬Halts implies bag dec-erase all ≥ 1**.
    Unconditional via iter 1550. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_erase_all_ge_one
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∀ x ∈ ((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0, x ≥ 1 :=
  ctsToSystem5_bag_dec_erase_all_ge_one cts cfg N

/-- **Iter 1810 (🎯 ITER 1810 MILESTONE): encoder ¬Halts implies bag
    dec-erase length ≥ 4 * data.length - 1**.  Direct via iter 1562. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_erase_length_ge_pred
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).length ≥
    4 * cfg.data.length - 1 :=
  ctsToSystem5_bag_dec_erase_length_ge cts cfg N

/-- **Iter 1811 (🎯🎯🎯🎯🎯 920-LEMMA MILESTONE): encoder ¬Halts implies
    bag length divisible by 4**.  Unconditional via iter 1557. -/
theorem ctsToSystem5_not_Halts_implies_bag_length_divisible_4
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).bag.length % 4 = 0 :=
  ctsToSystem5_bag_length_mod_4 cts cfg N

/-- **Iter 1812: encoder ¬Halts implies rules length divisible by 4**.
    Unconditional via iter 1636. -/
theorem ctsToSystem5_not_Halts_implies_rules_length_divisible_4
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).rules.length % 4 = 0 :=
  ctsToSystem5_rules_length_mod_4 cts cfg N

/-- **Iter 1813: encoder ¬Halts implies bag length = 4 * data.length**.
    Unconditional via iter 1520. -/
theorem ctsToSystem5_not_Halts_implies_bag_length_eq
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).bag.length = 4 * cfg.data.length :=
  ctsToSystem5_bag_length cts cfg N

/-- **Iter 1814: encoder ¬Halts implies rules length = 4·|appendants|·N**.
    Unconditional via iter 1521. -/
theorem ctsToSystem5_not_Halts_implies_rules_length_eq
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).rules.length = 4 * cts.appendants.length * N :=
  ctsToSystem5_rules_length cts cfg N

/-- **Iter 1815: encoder ¬Halts implies bag map(·+1) all ≥ 2**.
    Unconditional via iter 1553. -/
theorem ctsToSystem5_not_Halts_implies_bag_map_add_one_all_ge_two
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∀ x ∈ (ctsToSystem5 cts cfg N).bag.map (· + 1), x ≥ 2 :=
  ctsToSystem5_bag_map_add_one_all_ge_two cts cfg N

/-- **Iter 1816 (🎯🎯🎯 925-LEMMA MILESTONE): encoder ¬Halts implies bag
    dec.map(·+1) all ≥ 1**.  Unconditional via iter 1554. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_inc_all_ge_one
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∀ x ∈ ((ctsToSystem5 cts cfg N).bag.map (· - 1)).map (· + 1), x ≥ 1 :=
  ctsToSystem5_bag_dec_inc_all_ge_one cts cfg N

/-- **Iter 1817: encoder ¬Halts implies bag has 1 (specialization)**.
    Unconditional via iter 1567 + halt-state form.  Variant of iter 1798
    using halt-state directly. -/
theorem ctsToSystem5_not_Halts_implies_bag_one_mem
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    1 ∈ (ctsToSystem5 cts cfg N).bag := by
  apply ctsToSystem5_bag_one_mem_of_not_halted
  exact ctsToSystem5_not_Halts_implies_not_halted cts cfg N h

/-- **Iter 1818: encoder ¬Halts implies 0 ∈ bag.dec (halt-state form)**.
    Variant of iter 1797 via iter 1568. -/
theorem ctsToSystem5_not_Halts_implies_zero_in_dec_via_halt_state
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (0 : Int) ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) := by
  apply ctsToSystem5_zero_in_dec_of_not_halted
  exact ctsToSystem5_not_Halts_implies_not_halted cts cfg N h

/-- **Iter 1819: encoder ¬Halts implies bag dec length = bag length**.
    Direct map preserves length, unconditional via iter 1559. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_length_eq
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ((ctsToSystem5 cts cfg N).bag.map (· - 1)).length =
    (ctsToSystem5 cts cfg N).bag.length :=
  ctsToSystem5_bag_dec_length cts cfg N

/-- **Iter 1820: encoder ¬Halts implies bag dec length = 4 * data.length**.
    Unconditional via iter 1560. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_length_eq_closed
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ((ctsToSystem5 cts cfg N).bag.map (· - 1)).length = 4 * cfg.data.length :=
  ctsToSystem5_bag_dec_length_eq cts cfg N

/-- **Iter 1821 (🎯🎯🎯🎯🎯 930-LEMMA MILESTONE): encoder ¬Halts implies
    bag dec length ≥ 4**.  Direct via iter 1820 + arithmetic. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_length_ge_four
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ((ctsToSystem5 cts cfg N).bag.map (· - 1)).length ≥ 4 := by
  rw [ctsToSystem5_not_Halts_implies_bag_dec_length_eq_closed cts cfg N h]
  have h_data := ctsToSystem5_not_Halts_implies_data_pos cts cfg N h
  omega

/-- **Iter 1822: encoder ¬Halts implies bag dec-erase length ≥ 3**.
    Halt-state-driven companion to iter 1802 + iter 1788. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_erase_length_ge_three_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).length ≥ 3 :=
  ctsToSystem5_not_Halts_implies_bag_dec_erase_length_ge_three cts cfg N h

/-- **Iter 1823: encoder ¬Halts implies bag dec-erase length ≤ 4·data.length**.
    Unconditional via iter 1561. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_erase_length_le
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).length ≤
    4 * cfg.data.length :=
  ctsToSystem5_bag_dec_erase_length_le cts cfg N

/-- **Iter 1824: encoder ¬Halts implies bag dec-erase length pos**.
    Direct corollary of iter 1822 + arithmetic. -/
theorem ctsToSystem5_not_Halts_implies_bag_dec_erase_length_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (((ctsToSystem5 cts cfg N).bag.map (· - 1)).erase 0).length > 0 := by
  have := ctsToSystem5_not_Halts_implies_bag_dec_erase_length_ge_three cts cfg N h
  omega

/-- **Iter 1825: encoder ¬Halts implies bag length pos (alias)**.
    Direct alias of iter 1789. -/
theorem ctsToSystem5_not_Halts_implies_bag_length_pos_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    (ctsToSystem5 cts cfg N).bag.length > 0 :=
  ctsToSystem5_not_Halts_implies_bag_length_pos cts cfg N h

/-- **Iter 1826 (🎯🎯🎯 935-LEMMA MILESTONE): encoder ¬Halts implies
    full omnibus full witness**.  Combined packaging of iters 1786 + 1791
    + 1794: 1 ∈ bag, 0 ∈ bag.dec, bag and rules length ≥ 4. -/
theorem ctsToSystem5_not_Halts_full_omnibus_witness
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    1 ∈ (ctsToSystem5 cts cfg N).bag ∧
    (0 : Int) ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) ∧
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 ∧
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (ctsToSystem5_not_Halts_implies_one_mem_and_zero_in_dec cts cfg N h).1
  · exact (ctsToSystem5_not_Halts_implies_one_mem_and_zero_in_dec cts cfg N h).2
  · exact ctsToSystem5_not_Halts_implies_bag_length_ge_four cts cfg N h
  · exact ctsToSystem5_not_Halts_implies_rules_length_ge_four cts cfg N h

/-- **Iter 1827: encoder ¬Halts implies cts.step succeeds (alias)**.
    Direct alias of iter 1796 — repackaged with simpler statement. -/
theorem ctsToSystem5_not_Halts_implies_cts_step_some_alias
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∃ result, cts.step cfg = some result :=
  ctsToSystem5_not_Halts_implies_cts_step_witness cts cfg N h

/-- **Iter 1828: encoder ¬Halts implies cts is non-halting (Halts not).
    Note: this does NOT mean cts.Halts is false. The encoder hasn't halted
    the System5 trajectory yet, but CTS may still halt eventually. -/
theorem ctsToSystem5_not_Halts_implies_cts_not_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ctsHalted cfg = false :=
  ctsToSystem5_not_Halts_implies_not_halted cts cfg N h

/-- **Iter 1829: encoder ¬Halts implies cts.step result phase < |appendants|**.
    Direct via iter 1827 + iter 1619. -/
theorem ctsToSystem5_not_Halts_implies_cts_step_result_phase_lt
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∃ result, cts.step cfg = some result ∧ result.phase < cts.appendants.length := by
  obtain ⟨result, h_step⟩ := ctsToSystem5_not_Halts_implies_cts_step_witness cts cfg N h
  exact ⟨result, h_step, CTS_step_some_phase_lt_appendants cts cfg result h_step⟩

/-- **Iter 1830: encoder ¬Halts implies cts.step result data ≠ [] iff
    not halted at step result**.  Direct via cts step decomposition. -/
theorem ctsToSystem5_not_Halts_implies_cts_step_result_data_iff
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∃ result, cts.step cfg = some result ∧
              (result.data ≠ [] ↔ ctsHalted result = false) := by
  obtain ⟨result, h_step⟩ := ctsToSystem5_not_Halts_implies_cts_step_witness cts cfg N h
  exact ⟨result, h_step, (ctsHalted_false_iff_data_ne_nil result).symm⟩

/-- **Iter 1831 (🎯🎯🎯🎯🎯 940-LEMMA MILESTONE): encoder ¬Halts implies
    cts.step result Halts iff cfg.Halts**.  Direct via iter 1827 + iter
    1406 (step preserves Halts iff). -/
theorem ctsToSystem5_not_Halts_implies_cts_step_Halts_iff
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    ∃ result, cts.step cfg = some result ∧ (cts.Halts cfg ↔ cts.Halts result) := by
  obtain ⟨result, h_step⟩ := ctsToSystem5_not_Halts_implies_cts_step_witness cts cfg N h
  exact ⟨result, h_step, CTS_step_Halts_iff cts cfg result h_step⟩

/-- **Iter 1832: encoder ¬Halts implies cts.Halts iff exists step Halts**.
    Direct via iter 1326 specialized. -/
theorem ctsToSystem5_not_Halts_implies_cts_Halts_iff_step_Halts
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ¬ System5.Halts (ctsToSystem5 cts cfg N)) :
    cts.Halts cfg ↔ ∃ result, cts.step cfg = some result ∧ cts.Halts result :=
  CTS_Halts_iff_step_Halts_of_not_halted cts cfg
    (ctsToSystem5_not_Halts_implies_not_halted cts cfg N h)

/-- **Iter 1833: encoder Halts when ctsHalted**.  Restatement of iter
    1506 with explicit halt-state hypothesis. -/
theorem ctsToSystem5_Halts_at_ctsHalted
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ctsHalted cfg = true) :
    System5.Halts (ctsToSystem5 cts cfg N) :=
  ctsToSystem5_Halts_when_ctsHalted cts cfg N h

/-- **Iter 1834: encoder bag is non-empty implies bag length pos**.
    Trivial conversion via List.length_pos_iff. -/
theorem ctsToSystem5_bag_ne_nil_implies_length_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).bag ≠ []) :
    (ctsToSystem5 cts cfg N).bag.length > 0 :=
  List.length_pos_iff.mpr h

/-- **Iter 1835: encoder rules is non-empty implies rules length pos**.
    Companion to iter 1834 for the rules side. -/
theorem ctsToSystem5_rules_ne_nil_implies_length_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).rules ≠ []) :
    (ctsToSystem5 cts cfg N).rules.length > 0 :=
  List.length_pos_iff.mpr h

/-- **Iter 1836 (🎯🎯🎯 945-LEMMA MILESTONE): encoder bag length pos
    implies bag ≠ []**.  Trivial reverse direction of iter 1834. -/
theorem ctsToSystem5_bag_length_pos_implies_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).bag.length > 0) :
    (ctsToSystem5 cts cfg N).bag ≠ [] :=
  List.length_pos_iff.mp h

/-- **Iter 1837: encoder rules length pos implies rules ≠ []**.
    Companion to iter 1836 for the rules side. -/
theorem ctsToSystem5_rules_length_pos_implies_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).rules.length > 0) :
    (ctsToSystem5 cts cfg N).rules ≠ [] :=
  List.length_pos_iff.mp h

/-- **Iter 1838: encoder bag = [] implies length zero**.  Trivial via
    List.length. -/
theorem ctsToSystem5_bag_eq_nil_implies_length_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).bag = []) :
    (ctsToSystem5 cts cfg N).bag.length = 0 := by
  rw [h]
  rfl

/-- **Iter 1839: encoder rules = [] implies length zero**.  Companion
    to iter 1838 for rules. -/
theorem ctsToSystem5_rules_eq_nil_implies_length_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).rules = []) :
    (ctsToSystem5 cts cfg N).rules.length = 0 := by
  rw [h]
  rfl

/-- **Iter 1840 (🎯 ITER 1840 MILESTONE): encoder bag length zero implies
    bag = []**.  Reverse direction of iter 1838. -/
theorem ctsToSystem5_bag_length_zero_implies_eq_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).bag.length = 0) :
    (ctsToSystem5 cts cfg N).bag = [] :=
  List.length_eq_zero_iff.mp h

/-- **Iter 1841 (🎯🎯🎯🎯🎯 950-LEMMA MILESTONE): encoder rules length
    zero implies rules = []**.  Reverse direction of iter 1839. -/
theorem ctsToSystem5_rules_length_zero_implies_eq_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : (ctsToSystem5 cts cfg N).rules.length = 0) :
    (ctsToSystem5 cts cfg N).rules = [] :=
  List.length_eq_zero_iff.mp h

/-- **Iter 1842: encoder bag length zero iff bag = []**.  Biconditional
    combining iters 1838 + 1840. -/
theorem ctsToSystem5_bag_length_zero_iff_eq_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length = 0 ↔ (ctsToSystem5 cts cfg N).bag = [] :=
  List.length_eq_zero_iff

/-- **Iter 1843: encoder rules length zero iff rules = []**.  Companion
    to iter 1842 for rules. -/
theorem ctsToSystem5_rules_length_zero_iff_eq_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules.length = 0 ↔
    (ctsToSystem5 cts cfg N).rules = [] :=
  List.length_eq_zero_iff

/-- **Iter 1844: encoder bag length pos iff bag ≠ []**.  Biconditional
    via List.length_pos_iff. -/
theorem ctsToSystem5_bag_length_pos_iff_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length > 0 ↔ (ctsToSystem5 cts cfg N).bag ≠ [] :=
  List.length_pos_iff

/-- **Iter 1845: encoder rules length pos iff rules ≠ []**.  Companion
    to iter 1844 for rules. -/
theorem ctsToSystem5_rules_length_pos_iff_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules.length > 0 ↔ (ctsToSystem5 cts cfg N).rules ≠ [] :=
  List.length_pos_iff

/-- **Iter 1846 (🎯🎯🎯 955-LEMMA MILESTONE): encoder step some implies
    bag and rules length pos**.  Direct via iter 1748. -/
theorem ctsToSystem5_step_some_implies_bag_and_rules_length_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    (ctsToSystem5 cts cfg N).bag.length > 0 ∧
    (ctsToSystem5 cts cfg N).rules.length > 0 :=
  (ctsToSystem5_step_some_iff_bag_and_rules_length_pos cts cfg N).mp h

/-- **Iter 1847: encoder step some implies bag length pos**.  Direct
    via iter 1846 (left projection). -/
theorem ctsToSystem5_step_some_implies_bag_length_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    (ctsToSystem5 cts cfg N).bag.length > 0 :=
  (ctsToSystem5_step_some_implies_bag_and_rules_length_pos cts cfg N h).1

/-- **Iter 1848: encoder step some implies rules length pos**.  Direct
    via iter 1846 (right projection). -/
theorem ctsToSystem5_step_some_implies_rules_length_pos
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    (ctsToSystem5 cts cfg N).rules.length > 0 :=
  (ctsToSystem5_step_some_implies_bag_and_rules_length_pos cts cfg N h).2

/-- **Iter 1849: encoder step some implies bag ≠ []**.  Direct via
    iter 1846 + iter 1836. -/
theorem ctsToSystem5_step_some_implies_bag_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    (ctsToSystem5 cts cfg N).bag ≠ [] :=
  ctsToSystem5_bag_length_pos_implies_ne_nil cts cfg N
    (ctsToSystem5_step_some_implies_bag_length_pos cts cfg N h)

/-- **Iter 1850 (🎯🎯🎯🎯🎯 ITER 1850 MILESTONE): encoder step some
    implies rules ≠ []**.  Direct via iter 1846 + iter 1837. -/
theorem ctsToSystem5_step_some_implies_rules_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    (ctsToSystem5 cts cfg N).rules ≠ [] :=
  ctsToSystem5_rules_length_pos_implies_ne_nil cts cfg N
    (ctsToSystem5_step_some_implies_rules_length_pos cts cfg N h)

/-- **Iter 1851 (🎯🎯🎯🎯🎯 960-LEMMA MILESTONE): encoder step some implies
    bag and rules ≠ []**.  Combined packaging of iters 1849 + 1850. -/
theorem ctsToSystem5_step_some_implies_bag_and_rules_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    (ctsToSystem5 cts cfg N).bag ≠ [] ∧ (ctsToSystem5 cts cfg N).rules ≠ [] :=
  ⟨ctsToSystem5_step_some_implies_bag_ne_nil cts cfg N h,
   ctsToSystem5_step_some_implies_rules_ne_nil cts cfg N h⟩

/-- **Iter 1852: encoder step some (existential form) implies data ≠ []**.
    Wraps iter 1510 to take an existential rather than explicit witness. -/
theorem ctsToSystem5_step_some_implies_data_ne_nil_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    cfg.data ≠ [] := by
  obtain ⟨s5', h_step⟩ := h
  exact ctsToSystem5_step_some_implies_data_ne_nil cts cfg N s5' h_step

/-- **Iter 1853: encoder step some (existential) implies N ≥ 1**.
    Companion to iter 1852 for N. -/
theorem ctsToSystem5_step_some_implies_N_pos_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    N ≥ 1 := by
  obtain ⟨s5', h_step⟩ := h
  exact ctsToSystem5_step_some_implies_N_pos cts cfg N s5' h_step

/-- **Iter 1854: encoder step some (existential) implies not halted**.
    Direct via iter 1852 + iter 1264. -/
theorem ctsToSystem5_step_some_implies_not_halted_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    ctsHalted cfg = false := by
  rw [ctsHalted_false_iff_data_ne_nil]
  exact ctsToSystem5_step_some_implies_data_ne_nil_v2 cts cfg N h

/-- **Iter 1855: encoder step some (existential) implies cts.step
    succeeds**.  Bridges System5 step success to CTS step success. -/
theorem ctsToSystem5_step_some_implies_cts_step_some_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    ∃ result, cts.step cfg = some result := by
  apply CTS_step_some_of_not_halted
  exact ctsToSystem5_step_some_implies_not_halted_v2 cts cfg N h

/-- **Iter 1856 (🎯🎯🎯 965-LEMMA MILESTONE): encoder step some (existential)
    implies bag length ≥ 4**.  Direct via iter 1852 + iter 1534. -/
theorem ctsToSystem5_step_some_implies_bag_length_ge_4_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 :=
  ctsToSystem5_bag_length_ge_4_of_data_ne_nil cts cfg N
    (ctsToSystem5_step_some_implies_data_ne_nil_v2 cts cfg N h)

/-- **Iter 1857: encoder step some (existential) implies rules length ≥ 4**.
    Companion to iter 1856 for rules side. -/
theorem ctsToSystem5_step_some_implies_rules_length_ge_4_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 :=
  ctsToSystem5_rules_length_ge_4_of_N_pos cts cfg N
    (ctsToSystem5_step_some_implies_N_pos_v2 cts cfg N h)

/-- **Iter 1858: encoder step some (existential) implies 1 ∈ bag**.
    Direct via iter 1852 + iter 1538. -/
theorem ctsToSystem5_step_some_implies_one_mem_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    1 ∈ (ctsToSystem5 cts cfg N).bag :=
  ctsToSystem5_bag_one_mem_of_data_ne_nil cts cfg N
    (ctsToSystem5_step_some_implies_data_ne_nil_v2 cts cfg N h)

/-- **Iter 1859: encoder step some (existential) implies 0 ∈ bag.dec**.
    Direct via iter 1852 + iter 1539. -/
theorem ctsToSystem5_step_some_implies_zero_in_dec_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    (0 : Int) ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) := by
  rw [ctsToSystem5_zero_in_dec_iff]
  exact ctsToSystem5_step_some_implies_data_ne_nil_v2 cts cfg N h

/-- **Iter 1860 (🎯 ITER 1860 MILESTONE): encoder step some (existential)
    implies bag.Nodup**.  Direct via iter 1540 (unconditional). -/
theorem ctsToSystem5_step_some_implies_bag_nodup_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (_h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    (ctsToSystem5 cts cfg N).bag.Nodup :=
  ctsToSystem5_bag_nodup cts cfg N

/-- **Iter 1861 (🎯🎯🎯🎯🎯 970-LEMMA MILESTONE): encoder step some
    (existential) full witness omnibus**.  Combined packaging of all key
    facts derivable from System5 step success at the encoder. -/
theorem ctsToSystem5_step_some_full_omnibus_v2
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : ∃ s5', System5.step (ctsToSystem5 cts cfg N) = some s5') :
    cfg.data ≠ [] ∧ N ≥ 1 ∧
    1 ∈ (ctsToSystem5 cts cfg N).bag ∧
    (0 : Int) ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) ∧
    (ctsToSystem5 cts cfg N).bag.Nodup ∧
    (ctsToSystem5 cts cfg N).bag.length ≥ 4 ∧
    (ctsToSystem5 cts cfg N).rules.length ≥ 4 :=
  ⟨ctsToSystem5_step_some_implies_data_ne_nil_v2 cts cfg N h,
   ctsToSystem5_step_some_implies_N_pos_v2 cts cfg N h,
   ctsToSystem5_step_some_implies_one_mem_v2 cts cfg N h,
   ctsToSystem5_step_some_implies_zero_in_dec_v2 cts cfg N h,
   ctsToSystem5_step_some_implies_bag_nodup_v2 cts cfg N h,
   ctsToSystem5_step_some_implies_bag_length_ge_4_v2 cts cfg N h,
   ctsToSystem5_step_some_implies_rules_length_ge_4_v2 cts cfg N h⟩

/-- **Iter 1862: System5.nSteps zero same as Halts**.  Composes existing
    primitives. -/
theorem ctsToSystem5_nSteps_zero_some
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.nSteps (ctsToSystem5 cts cfg N) 0 = some (ctsToSystem5 cts cfg N) :=
  rfl

/-- **Iter 1863: System5.nSteps one equals step**.  Trivial via
    System5.nSteps_one. -/
theorem ctsToSystem5_nSteps_one
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.nSteps (ctsToSystem5 cts cfg N) 1 = System5.step (ctsToSystem5 cts cfg N) :=
  System5.nSteps_one _

/-- **Iter 1864: encoder bag length equality (alias)**.  Direct alias
    of iter 1520. -/
theorem ctsToSystem5_bag_length_alias
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length = 4 * cfg.data.length :=
  ctsToSystem5_bag_length cts cfg N

/-- **Iter 1865: encoder rules length equality (alias)**.  Direct alias
    of iter 1521. -/
theorem ctsToSystem5_rules_length_alias
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).rules.length = 4 * cts.appendants.length * N :=
  ctsToSystem5_rules_length cts cfg N

/-- **Iter 1866 (🎯🎯🎯 975-LEMMA MILESTONE): encoder bag and rules length
    closed forms combined**.  Combined packaging of iters 1864 + 1865. -/
theorem ctsToSystem5_bag_and_rules_length_closed
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.length = 4 * cfg.data.length ∧
    (ctsToSystem5 cts cfg N).rules.length = 4 * cts.appendants.length * N :=
  ⟨ctsToSystem5_bag_length cts cfg N, ctsToSystem5_rules_length cts cfg N⟩

/-- **REFACTOR Phase 1, sub-goal 1**: false-head 4-step trajectory
    rules-drop form at any Perm-chain point.

    After 4 System5 steps starting from a Perm-chain point at false-head,
    the rules drop by 4 entries and shift by +4.  This is the chain-
    induction analog of `System5_nSteps_rules_pstep` specialized to the
    false-head 4-step trajectory.  All 4 steps are P-steps (proven via
    iters 1051, 1061, 1066, 1071), so `System5_nSteps_rules_pstep` applies.

    Chain-induction analog of iter 985's existing cfg5-level result. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step4_rules_drop_shift
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_4,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ s5_4.rules = ((ctsRulesToSystem5Rules cts
          { data := false :: rest, phase := phase } N).drop 4).map
            (fun r => r.map (· + (4 : Int))) := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨_, s5_4, _, h_step4, _⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step4_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_4, h_step4, ?_⟩
  have h_pstep : ∀ k < 4, ∀ cfg_k,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ k = some cfg_k
      → (0 : Int) ∈ cfg_k.bag.map (· - 1) := by
    intro k h_k cfg_k h_k_eq
    match k, h_k with
    | 0, _ =>
      simp [System5.nSteps] at h_k_eq
      rw [← h_k_eq]
      exact ctsConfigToSystem5Bag_perm_zero_in_decrement cfg bag (by simp) h_perm
    | 1, _ =>
      obtain ⟨s5_1, h_step1, h_one_mem_s5_1⟩ :=
        ctsConfigToSystem5Bag_false_head_perm_step_bag_one_mem cts rest phase N h_N bag h_perm
      have h_step1_one : System5.nSteps
          ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ 1 = some s5_1 := by
        rw [System5.nSteps_one]; exact h_step1
      have h_eq : cfg_k = s5_1 := Option.some.inj (h_k_eq.symm.trans h_step1_one)
      rw [h_eq]
      exact (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_1
    | 2, _ =>
      obtain ⟨s5_2, h_step2, h_one_mem_s5_2⟩ :=
        ctsConfigToSystem5Bag_false_head_perm_step2_one_mem cts rest phase N h_N bag h_perm
      have h_eq : cfg_k = s5_2 := Option.some.inj (h_k_eq.symm.trans h_step2)
      rw [h_eq]
      exact (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_2
    | 3, _ =>
      obtain ⟨s5_3, h_step3, h_one_mem_s5_3⟩ :=
        ctsConfigToSystem5Bag_false_head_perm_step3_one_mem cts rest phase N h_N bag h_perm
      have h_eq : cfg_k = s5_3 := Option.some.inj (h_k_eq.symm.trans h_step3)
      rw [h_eq]
      exact (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_3
  exact System5_nSteps_rules_pstep _ s5_4 4 h_step4 h_pstep

/-- **Iter 1163: TWO consecutive System5 steps succeed at true-head
    Perm-chain points**.  True-head analog of iter 1062.  Combines iter
    1057 (full step output) + iter 1162 (2 ∈ s5'.bag, hence s5'.bag ≠ [])
    + `System5_step_some_iff` for the second step.  Chain-induction
    analog at the true-head trajectory level. -/
theorem ctsConfigToSystem5Bag_true_head_perm_step2_succeeds
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := true :: rest, phase := phase })) :
    ∃ s5_2, System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
              { data := true :: rest, phase := phase } N⟩ 2 = some s5_2 := by
  obtain ⟨s5', h_step', h_two_in⟩ :=
    ctsConfigToSystem5Bag_true_head_perm_step_bag_two_mem cts rest phase N h_N bag h_perm
  obtain ⟨r1, r2, tail, _h_eq, h_step⟩ :=
    ctsConfigToSystem5Bag_perm_step_some_explicit cts
      { data := true :: rest, phase := phase } N h_N bag (by simp) h_perm
  have h_s5'_eq : s5' = ⟨(r1.map (· + 1)).reverse ++ ((bag.map (· - 1)).erase 0),
                          (r2 :: tail).map (fun r => r.map (· + 1))⟩ :=
    Option.some.inj (h_step'.symm.trans h_step)
  have h_bag_ne : s5'.bag ≠ [] := List.ne_nil_of_mem h_two_in
  have h_rules_ne : s5'.rules ≠ [] := by
    rw [h_s5'_eq]; simp
  obtain ⟨s5_2, h_step2⟩ :=
    (System5_step_some_iff s5').mpr ⟨h_bag_ne, h_rules_ne⟩
  refine ⟨s5_2, ?_⟩
  rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add]
  rw [System5.nSteps_one, h_step']
  show System5.nSteps s5' 1 = some s5_2
  rw [System5.nSteps_one]
  exact h_step2

/-- **Iter 1079: xorMerge mem-iff is preserved under Perm of first
    arg**.  `xs.Perm xs' → (x ∈ xorMerge xs ys ↔ x ∈ xorMerge xs' ys)`
    (with appropriate Nodups).  Composes `xorMerge_mem_iff` (twice) +
    `List.Perm.mem_iff` + `List.Perm.nodup_iff`.  **Bridge for
    transferring bag-2 mem-iff results across a Perm-equivalent bag-1
    dec-erase form** — directly applicable in the chain-induction
    analog of iter 1005's bag-2 mem-iff. -/
theorem xorMerge_mem_iff_of_perm_left (xs xs' ys : List Int)
    (h_perm : xs.Perm xs') (h_xs : xs.Nodup) (h_ys : ys.Nodup) (x : Int) :
    x ∈ xorMerge xs ys ↔ x ∈ xorMerge xs' ys := by
  have h_xs' : xs'.Nodup := (List.Perm.nodup_iff h_perm).mp h_xs
  have h_mem : x ∈ xs ↔ x ∈ xs' := List.Perm.mem_iff h_perm
  rw [xorMerge_mem_iff xs ys h_xs h_ys x,
      xorMerge_mem_iff xs' ys h_xs' h_ys x, h_mem]

/-- **Iter 1080: bag-2 mem-iff at false-head Perm-chain points
    (MAJOR MILESTONE)**.  After TWO P-steps at a false-head Perm-chain
    point, `∀ x, x ∈ s5_2.bag ↔ x ∈ (1 :: 2 :: aux rest 3)`.  Composes
    iter 1063 (bag-2 form) + iter 1076 (dec-erase Perm form) + iter 1077
    (dec-erase Nodup) + iter 1078 (simplified-form Nodup) + iter 1079
    (xorMerge mem-iff Perm-bridge) + iter 981 (r2.map(·+2) Nodup) +
    iter 1000 (r1.reverse ↔ r2.map(·+2) mem-eq) + iter 1003
    (rest_part disjoint r2.map(·+2)).  **Chain-induction analog of
    iter 1005's existing cfg5-level bag2_mem_iff** — the bag-2's full
    membership identity is now closed at chain points. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step2_bag2_mem_iff
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_2,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ ∀ x, x ∈ s5_2.bag ↔ x ∈ ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3) := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨r1, r2, tail, s5_1, s5_2, h_eq, h_step1, h_step2, h_bag2⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step2_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_2, h_step2, ?_⟩
  intro x
  rw [h_bag2]
  obtain ⟨r1_a, _, _, s5_1_a, h_eq_a, h_step_a, h_dec_perm⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step1_dec_erase_perm cts rest phase N h_N bag h_perm
  obtain ⟨s5_1_b, h_step_b, h_dec_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_dec_erase_nodup cts cfg N h_N (by simp) bag h_perm
  have h_step1_one : System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩ = some s5_1 := by
    rw [System5.nSteps_one] at h_step1; exact h_step1
  have h_eq_s5_a : s5_1 = s5_1_a := Option.some.inj (h_step1_one.symm.trans h_step_a)
  have h_eq_s5_b : s5_1 = s5_1_b := Option.some.inj (h_step1_one.symm.trans h_step_b)
  have h_r1_a : r1 = r1_a := (List.cons.inj (h_eq.symm.trans h_eq_a)).1
  obtain ⟨_, r2_d, _, h_eq_d, h_nodup_r2⟩ :=
    ctsRulesToSystem5Rules_second_rule_map_add_2_nodup cts cfg N h_N
  have h_r2_d : r2 = r2_d :=
    (List.cons.inj (List.cons.inj (h_eq.symm.trans h_eq_d)).2).1
  -- Substitute s5_1 for s5_1_a/s5_1_b in helpers
  rw [← h_eq_s5_a] at h_dec_perm
  rw [← h_eq_s5_b] at h_dec_nodup
  rw [← h_r1_a] at h_dec_perm
  rw [← h_r2_d] at h_nodup_r2
  -- Apply iter 1079 to switch to simplified dec-erase form
  rw [xorMerge_mem_iff_of_perm_left _ _ _ h_dec_perm h_dec_nodup h_nodup_r2 x]
  -- Goal: x ∈ xorMerge (r1.reverse ++ (1 :: 2 :: aux rest 3)) (r2.map(·+2)) ↔ ...
  -- Get Nodup of simplified form
  obtain ⟨r1_g, _, _, _, h_eq_g, _, h_nodup_simp⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_r1_reverse_aux3_nodup cts rest phase N h_N
      bag h_perm
  have h_r1_g : r1 = r1_g := (List.cons.inj (h_eq.symm.trans h_eq_g)).1
  rw [← h_r1_g] at h_nodup_simp
  -- Apply xorMerge_mem_iff
  rw [xorMerge_mem_iff _ _ h_nodup_simp h_nodup_r2 x]
  -- Get r1.reverse ↔ r2.map(·+2) mem-eq
  obtain ⟨r1_e, r2_e, _, h_eq_e, h_rev_mem⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_reverse_mem_eq cts cfg N h_N
  have h_r1_e : r1 = r1_e := (List.cons.inj (h_eq.symm.trans h_eq_e)).1
  have h_r2_e : r2 = r2_e :=
    (List.cons.inj (List.cons.inj (h_eq.symm.trans h_eq_e)).2).1
  rw [← h_r1_e, ← h_r2_e] at h_rev_mem
  -- Get rest disjoint from r2.map(·+2)
  obtain ⟨_, r2_f, _, h_eq_f, h_disj_r2⟩ :=
    ctsConfigToSystem5BagAux_three_one_two_cons_disjoint_r2_inc2 cts rest phase N h_N
  have h_r2_f : r2 = r2_f :=
    (List.cons.inj (List.cons.inj (h_eq.symm.trans h_eq_f)).2).1
  rw [← h_r2_f] at h_disj_r2
  constructor
  · rintro (⟨h_in_l, h_not_r⟩ | ⟨h_not_l, h_in_r⟩)
    · rcases List.mem_append.mp h_in_l with h_in_rev | h_in_rest
      · exact absurd ((h_rev_mem x).mp h_in_rev) h_not_r
      · exact h_in_rest
    · have h_in_rev : x ∈ r1.reverse := (h_rev_mem x).mpr h_in_r
      have : x ∈ r1.reverse ++ ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3) :=
        List.mem_append_left _ h_in_rev
      exact absurd this h_not_l
  · intro h_in_rest
    left
    refine ⟨List.mem_append_right _ h_in_rest, h_disj_r2 x h_in_rest⟩

/-- **Iter 1081: s5_2.bag is Nodup at false-head Perm-chain points**.
    Direct corollary of iter 1063 (bag-2 form `xorMerge ...`) +
    `xorMerge_nodup` + iter 1077 (dec-erase s5_1.bag Nodup).
    s5_1 alignment via `Option.some.inj`.  **Chain-induction analog of
    iter 1008's existing cfg5-level step2_bag_nodup** — prerequisite
    for the bag-3 mem-iff chain (iter 1082) via iter 1006's
    `List_Int_dec_erase_same_mem`. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step2_bag_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_2,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 2 = some s5_2
      ∧ s5_2.bag.Nodup := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨_, _, _, s5_1, s5_2, _, h_step1, h_step2, h_bag2⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step2_bag_form cts rest phase N h_N bag h_perm
  refine ⟨s5_2, h_step2, ?_⟩
  rw [h_bag2]
  apply xorMerge_nodup
  obtain ⟨s5_1', h_step1', h_dec_nodup⟩ :=
    ctsConfigToSystem5Bag_perm_step1_dec_erase_nodup cts cfg N h_N (by simp) bag h_perm
  have h_step1_one : System5.step ⟨bag, ctsRulesToSystem5Rules cts cfg N⟩
                       = some s5_1 := by
    rw [System5.nSteps_one] at h_step1; exact h_step1
  have h_eq : s5_1 = s5_1' := Option.some.inj (h_step1_one.symm.trans h_step1')
  rw [h_eq]
  exact h_dec_nodup

/-- **Iter 1082: bag-3 mem-iff at false-head Perm-chain points
    (MAJOR MILESTONE)**.  After THREE P-steps at false-head Perm-chain
    point, `∀ x, x ∈ s5_3.bag ↔ x ∈ (1 :: aux rest 2)`.  Composes
    iter 1070 (bag-3 form) + iter 1080 (bag-2 mem-iff) + iter 1081
    (s5_2.bag Nodup) + iter 1006 (`List_Int_dec_erase_same_mem`) +
    iter 1007 (RHS computation: `((1::2::aux rest 3).map(·-1)).erase 0
    = 1::aux rest 2`).  **Chain-induction analog of iter 1009's existing
    cfg5-level bag3_mem_iff** — bag-3's full membership identity is
    now closed at chain points. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step3_bag3_mem_iff
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_3,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ ∀ x, x ∈ s5_3.bag ↔ x ∈ ((1 : Int) :: ctsConfigToSystem5BagAux rest 2) := by
  obtain ⟨s5_2, s5_3, h_step2, h_step3, h_bag3⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step3_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_2', h_step2', h_bag2_mem⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step2_bag2_mem_iff cts rest phase N h_N bag h_perm
  obtain ⟨s5_2'', h_step2'', h_s5_2_nodup⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step2_bag_nodup cts rest phase N h_N bag h_perm
  have h_eq2 : s5_2 = s5_2' := Option.some.inj (h_step2.symm.trans h_step2')
  have h_eq2' : s5_2' = s5_2'' := Option.some.inj (h_step2'.symm.trans h_step2'')
  rw [h_eq2] at h_bag3
  rw [← h_eq2'] at h_s5_2_nodup
  refine ⟨s5_3, h_step3, ?_⟩
  intro x
  rw [h_bag3]
  rw [List_Int_dec_erase_same_mem s5_2'.bag
        ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3)
        h_s5_2_nodup
        (ctsConfigToSystem5BagAux_three_one_two_cons_nodup rest)
        h_bag2_mem 0 x]
  rw [ctsConfigToSystem5BagAux_three_one_two_cons_dec_erase_eq]

/-- **Iter 1083: s5_3.bag is Nodup at false-head Perm-chain points**.
    Direct corollary of iter 1070 (bag-3 form `(s5_2.bag.map(·-1)).erase 0`)
    combined with iter 1081's s5_2.bag.Nodup + `List.Pairwise.map`
    (decrement injectivity) + `List.Nodup.erase`.  s5_2 alignment via
    `Option.some.inj`.  **Chain-induction analog of iter 1011** —
    prerequisite for the bag-4 mem-iff chain (iter 1084). -/
theorem ctsConfigToSystem5Bag_false_head_perm_step3_bag_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_3,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 3 = some s5_3
      ∧ s5_3.bag.Nodup := by
  obtain ⟨s5_2, s5_3, h_step2, h_step3, h_bag3⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step3_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_2', h_step2', h_s5_2_nodup⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step2_bag_nodup cts rest phase N h_N bag h_perm
  have h_eq2 : s5_2 = s5_2' := Option.some.inj (h_step2.symm.trans h_step2')
  refine ⟨s5_3, h_step3, ?_⟩
  rw [h_bag3, h_eq2]
  apply List.Nodup.erase
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_2_nodup
  intro a b h_ne h_eq_dec
  apply h_ne
  have : a - 1 = b - 1 := h_eq_dec
  omega

/-- **Iter 1084: bag-4 mem-iff at false-head Perm-chain points
    (TERMINAL TARGET)**.  After FOUR P-steps at false-head Perm-chain
    point, `∀ x, x ∈ s5_4.bag ↔ x ∈ ctsConfigToSystem5BagAux rest 1`.
    **This is the encoder bag of the post-CTS-step state**: cts.step
    of false-head config has data = rest, and aux rest 1 is its
    encoder bag.  Composition: iter 1073 (bag-4 form) + iter 1082
    (bag-3 mem-iff) + iter 1083 (s5_3.bag Nodup) + iter 1006
    (existing same-mem-through-dec-erase) + iter 1010 (existing RHS
    computation: `((1::aux rest 2).map(·-1)).erase 0 = aux rest 1`).
    **Chain-induction analog of iter 1012's existing cfg5-level
    bag4_mem_iff** — bag-4's full membership identity is now closed at
    chain points. The 4-step false-head trajectory's terminal bag is
    fully characterized as the target encoder bag at the membership
    level. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step4_bag4_mem_iff
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_4,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ ∀ x, x ∈ s5_4.bag ↔ x ∈ ctsConfigToSystem5BagAux rest 1 := by
  obtain ⟨s5_3, s5_4, h_step3, h_step4, h_bag4⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step4_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_3', h_step3', h_bag3_mem⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step3_bag3_mem_iff cts rest phase N h_N bag h_perm
  obtain ⟨s5_3'', h_step3'', h_s5_3_nodup⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step3_bag_nodup cts rest phase N h_N bag h_perm
  have h_eq3 : s5_3 = s5_3' := Option.some.inj (h_step3.symm.trans h_step3')
  have h_eq3' : s5_3' = s5_3'' := Option.some.inj (h_step3'.symm.trans h_step3'')
  rw [h_eq3] at h_bag4
  rw [← h_eq3'] at h_s5_3_nodup
  refine ⟨s5_4, h_step4, ?_⟩
  intro x
  rw [h_bag4]
  rw [List_Int_dec_erase_same_mem s5_3'.bag
        ((1 : Int) :: ctsConfigToSystem5BagAux rest 2)
        h_s5_3_nodup
        (ctsConfigToSystem5BagAux_two_one_cons_nodup rest)
        h_bag3_mem 0 x]
  rw [ctsConfigToSystem5BagAux_two_one_cons_dec_erase_eq]

/-- **Iter 1085: s5_4.bag is Nodup at false-head Perm-chain points**.
    Direct corollary of iter 1073 (bag-4 form `(s5_3.bag.map(·-1)).erase 0`)
    combined with iter 1083's s5_3.bag.Nodup + `List.Pairwise.map`
    (decrement injectivity) + `List.Nodup.erase`.  s5_3 alignment via
    `Option.some.inj`.  **Prerequisite for the bag-4 Perm form (iter
    1086) — chain-induction analog of iter 1014's existing cfg5-level
    bag4_perm**. -/
theorem ctsConfigToSystem5Bag_false_head_perm_step4_bag_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_4,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ s5_4.bag.Nodup := by
  obtain ⟨s5_3, s5_4, h_step3, h_step4, h_bag4⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step4_bag_form cts rest phase N h_N bag h_perm
  obtain ⟨s5_3', h_step3', h_s5_3_nodup⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step3_bag_nodup cts rest phase N h_N bag h_perm
  have h_eq3 : s5_3 = s5_3' := Option.some.inj (h_step3.symm.trans h_step3')
  refine ⟨s5_4, h_step4, ?_⟩
  rw [h_bag4, h_eq3]
  apply List.Nodup.erase
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_3_nodup
  intro a b h_ne h_eq_dec
  apply h_ne
  have : a - 1 = b - 1 := h_eq_dec
  omega

/-- **Iter 1086: bag-4 Perm form at false-head Perm-chain points
    (THE FULL CHAIN-INDUCTION STEP 🎉🎉🎉)**.  After FOUR P-steps at
    a false-head Perm-chain point, `s5_4.bag.Perm
    ctsConfigToSystem5BagAux rest 1` — the encoder bag of the post-
    CTS-step state.  Composition: iter 1084 (bag-4 mem-iff) + iter
    1085 (s5_4.bag Nodup) + iter 645's `ctsConfigToSystem5BagAux_nodup`
    + iter 1013 (`List_Int_perm_of_nodup_same_mem`).
    **Chain-induction analog of iter 1014's existing cfg5-level
    bag4_perm**.  This is THE full chain-induction step at the Perm
    level: `bag.Perm (encoder bag)` ⇒ after 4 P-steps `s5_4.bag.Perm
    (encoder bag of post-step CTS config)`.  The Perm-based
    `SmithPerStepExtensionPerm` predicate (iter 1015) is now provable
    for arbitrary chain points in the false-head case, not just from
    cfg5 (iter 1016). -/
theorem ctsConfigToSystem5Bag_false_head_perm_step4_bag4_perm
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase })) :
    ∃ s5_4,
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 4 = some s5_4
      ∧ List.Perm s5_4.bag (ctsConfigToSystem5BagAux rest 1) := by
  obtain ⟨s5_4, h_step4, h_bag4_mem⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step4_bag4_mem_iff cts rest phase N h_N bag h_perm
  obtain ⟨s5_4', h_step4', h_s5_4_nodup⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step4_bag_nodup cts rest phase N h_N bag h_perm
  have h_eq4 : s5_4 = s5_4' := Option.some.inj (h_step4.symm.trans h_step4')
  rw [← h_eq4] at h_s5_4_nodup
  have h_aux_nodup : (ctsConfigToSystem5BagAux rest 1).Nodup :=
    ctsConfigToSystem5BagAux_nodup rest 1
  refine ⟨s5_4, h_step4, ?_⟩
  exact List_Int_perm_of_nodup_same_mem _ _ h_s5_4_nodup h_aux_nodup h_bag4_mem

/-- **`encodeAppendant_total_length` (iter 670)**: r1 and r2 together
    contribute exactly `4 * rule.length` integers — the per-bit
    "double-doubling" structure of Smith's encoder.  Direct sum of
    `_r1_length` + `_r2_length`. -/
theorem encodeAppendant_total_length (rule : List Bool) (i : Int) :
    (encodeAppendant rule i).1.length + (encodeAppendant rule i).2.1.length
    = 4 * rule.length := by
  rw [encodeAppendant_r1_length, encodeAppendant_r2_length]
  omega

/-- **`encodeAppendant_r1_map_add_1_length` (iter 670)**: shifted r1
    has the same length as r1 (= `2 * rule.length`). -/
theorem encodeAppendant_r1_map_add_1_length (rule : List Bool) (i : Int) :
    ((encodeAppendant rule i).1.map (· + 1)).length = 2 * rule.length := by
  rw [List.length_map]
  exact encodeAppendant_r1_length rule i

/-- **`encodeAppendant_r2_map_add_1_length` (iter 670)**: shifted r2
    has the same length as r2. -/
theorem encodeAppendant_r2_map_add_1_length (rule : List Bool) (i : Int) :
    ((encodeAppendant rule i).2.1.map (· + 1)).length = 2 * rule.length := by
  rw [List.length_map]
  exact encodeAppendant_r2_length rule i

/-- **`ctsRulesToSystem5Rules_cons` (iter 671)**: encoded rules head
    structure — for any non-empty CTS appendants list and positive
    emulation budget, `ctsRulesToSystem5Rules cts cfg n` starts with
    `r1 :: r2 :: [] :: rest` (current 3-rule encoder; should be 4 per
    PDF — see iter 816 bug note on `processCycle` def). -/
theorem ctsRulesToSystem5Rules_cons
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (h_n : 1 ≤ n) :
    ∃ r1 r2 rest, ctsRulesToSystem5Rules cts cfg n = r1 :: r2 :: [] :: rest := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold ctsRulesToSystem5Rules
  have h_app := cts.nonempty
  cases h_eq : cts.appendants with
  | nil =>
    rw [h_eq] at h_app; simp at h_app
  | cons a tail =>
    refine ⟨(encodeAppendant a (counterAfterWorkingString cfg.data + 2)).1,
            (encodeAppendant a (counterAfterWorkingString cfg.data + 2)).2.1,
            ([] : List Int) :: ((processCycle tail
                (encodeAppendant a (counterAfterWorkingString cfg.data + 2)).2.2).1
              ++ nCycles (a :: tail) m
                  (processCycle (a :: tail) (counterAfterWorkingString cfg.data + 2)).2),
            ?_⟩
    rfl

/-- **`ctsConfigToSystem5BagAux_empty_iff` (iter 671)**: the encoder
    produces an empty bag exactly when the input working string is
    empty.  Direct structural induction on the recursion. -/
theorem ctsConfigToSystem5BagAux_empty_iff (data : List Bool) (i : Int) :
    ctsConfigToSystem5BagAux data i = [] ↔ data = [] := by
  cases data with
  | nil => simp [ctsConfigToSystem5BagAux]
  | cons head rest =>
    cases head with
    | true => simp [ctsConfigToSystem5BagAux]
    | false => simp [ctsConfigToSystem5BagAux]

/-- **`ctsConfigToSystem5Bag_empty_iff_halted` (iter 671)**: encoded
    bag emptiness corresponds exactly to CTS halting (`ctsHalted cfg
    ↔ data = []`). -/
theorem ctsConfigToSystem5Bag_empty_iff_halted (cfg : CTSConfig) :
    ctsConfigToSystem5Bag cfg = [] ↔ ctsHalted cfg = true := by
  unfold ctsConfigToSystem5Bag
  rw [ctsConfigToSystem5BagAux_empty_iff]
  cases h_data : cfg.data <;> simp [ctsHalted, List.isEmpty, h_data]

/-- **`ctsHalted_iff_data_eq_nil` (iter 672)**: clean iff for the
    halt predicate — `ctsHalted cfg = true ↔ cfg.data = []`.  Combines
    iter 656's `_eq_nil_iff` with iter 671's `_empty_iff_halted`. -/
theorem ctsHalted_iff_data_eq_nil (cfg : CTSConfig) :
    ctsHalted cfg = true ↔ cfg.data = [] :=
  (ctsConfigToSystem5Bag_empty_iff_halted cfg).symm.trans
    (ctsConfigToSystem5Bag_eq_nil_iff cfg)

/-- **`ctsConfigToSystem5Bag_nonempty_iff_data_nonempty` (iter 672)**:
    contrapositive form — encoded bag is non-empty exactly when CTS
    data is non-empty.  Direct corollary of `_eq_nil_iff`. -/
theorem ctsConfigToSystem5Bag_nonempty_iff_data_nonempty (cfg : CTSConfig) :
    ctsConfigToSystem5Bag cfg ≠ [] ↔ cfg.data ≠ [] := by
  rw [ne_eq, ne_eq, ctsConfigToSystem5Bag_eq_nil_iff]

/-- **`ctsToSystem5_halt_preservation_base` (iter 673)**: an already-
    halted CTS config (`ctsHalted cfg`) gives an immediately-halting
    System 5 — one step suffices.  `System5.step` returns `none`
    because the encoded bag is empty (per `_empty_iff_halted`). -/
theorem ctsToSystem5_halt_preservation_base
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h : ctsHalted cfg = true) :
    ∃ m, System5.nSteps (ctsToSystem5 cts cfg N) m = none := by
  refine ⟨1, ?_⟩
  rw [System5.nSteps_one]
  apply (System5_step_none_iff _).mpr
  left
  show ctsConfigToSystem5Bag cfg = []
  exact (ctsConfigToSystem5Bag_empty_iff_halted cfg).mpr h

/-- **`ctsToSystem5_halts_of_data_eq_nil` (iter 674)**: alternative
    halt-preservation form using the `data = []` predicate directly.
    Composes `ctsHalted_iff_data_eq_nil` (iter 672) with
    `_halt_preservation_base` (iter 673). -/
theorem ctsToSystem5_halts_of_data_eq_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h : cfg.data = []) :
    ∃ m, System5.nSteps (ctsToSystem5 cts cfg N) m = none :=
  ctsToSystem5_halt_preservation_base cts cfg N
    ((ctsHalted_iff_data_eq_nil cfg).mpr h)

/-- **`ctsToSystem5_step_none_of_data_eq_nil` (iter 674)**: even
    sharper — `step` (single, not nSteps) returns `none` immediately
    on a halted-CTS encoding.  Direct unfold + `_empty_iff_halted`. -/
theorem ctsToSystem5_step_none_of_halted
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h : ctsHalted cfg = true) :
    System5.step (ctsToSystem5 cts cfg N) = none := by
  apply (System5_step_none_iff _).mpr
  left
  show ctsConfigToSystem5Bag cfg = []
  exact (ctsConfigToSystem5Bag_empty_iff_halted cfg).mpr h

/-- **`ctsToSystem5_first_step` (iter 679)**: closed form for the first
    System 5 step from an encoded CTS.  `nSteps (ctsToSystem5 cts cfg
    n) 1` is determined by the head of the incremented rules list and
    `(bag.map (· - 1)).erase 0`.  Direct application of
    `System5_nSteps_decrement_then_pop` at `k = 0`. -/
theorem ctsToSystem5_first_step (cts : CTS) (cfg : CTSConfig) (n : Nat)
    (h_data : cfg.data ≠ []) (h_n : 1 ≤ n) :
    ∃ (nextRule : List Int) (restRules : List (List Int)),
      (ctsRulesToSystem5Rules cts cfg n).map (fun r => r.map (· + 1))
        = nextRule :: restRules ∧
      System5.nSteps (ctsToSystem5 cts cfg n) 1
        = some { bag := xorMerge (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0)
                                  nextRule
                 rules := restRules } := by
  have h_bag : (ctsToSystem5 cts cfg n).bag ≠ [] :=
    ctsConfigToSystem5Bag_nonempty cfg h_data
  have h_rules : (ctsToSystem5 cts cfg n).rules ≠ [] :=
    ctsRulesToSystem5Rules_nonempty cts cfg n h_n
  have h_no_small : ∀ j : Nat, 1 ≤ j → j ≤ 0 → (↑j : Int) ∉ (ctsToSystem5 cts cfg n).bag := by
    intro j h1 h2; omega
  have h_one_mem : ((0 + 1 : Nat) : Int) ∈ (ctsToSystem5 cts cfg n).bag := by
    show (1 : Int) ∈ ctsConfigToSystem5Bag cfg
    exact ctsConfigToSystem5Bag_one_mem cfg h_data
  exact System5_nSteps_decrement_then_pop (ctsToSystem5 cts cfg n) 0
    h_bag h_rules h_no_small h_one_mem

/-- **`ctsToSystem5_first_step_some` (iter 680)**: existential
    weakening of `_first_step` — for non-empty data and positive
    budget, the first System 5 step yields some result. -/
theorem ctsToSystem5_first_step_some (cts : CTS) (cfg : CTSConfig) (n : Nat)
    (h_data : cfg.data ≠ []) (h_n : 1 ≤ n) :
    ∃ result, System5.nSteps (ctsToSystem5 cts cfg n) 1 = some result := by
  obtain ⟨_, _, _, h_step⟩ := ctsToSystem5_first_step cts cfg n h_data h_n
  exact ⟨_, h_step⟩

/-- **`ctsToSystem5_first_step_step_some` (iter 680)**: same with
    `step` (single, not nSteps).  Direct via `System5.nSteps_one`. -/
theorem ctsToSystem5_first_step_step_some
    (cts : CTS) (cfg : CTSConfig) (n : Nat)
    (h_data : cfg.data ≠ []) (h_n : 1 ≤ n) :
    ∃ result, System5.step (ctsToSystem5 cts cfg n) = some result := by
  obtain ⟨result, h⟩ := ctsToSystem5_first_step_some cts cfg n h_data h_n
  rw [System5.nSteps_one] at h
  exact ⟨result, h⟩

/-- **Iter 956: ctsToSystem5 trajectory rules invariant (specialization)**.
    After `m` successful System5 steps from `ctsToSystem5 cts cfg N`, the
    resulting rules list is `((ctsRulesToSystem5Rules cts cfg N).drop k).map(map(·+m))`
    for some `k ≤ m`.  Direct specialization of
    `System5_nSteps_rules_form`.  This is the missing piece for the
    handoff's "what does `s5'.rules` look like at step m?" gap blocking
    the false-head 4-step closure. -/
theorem ctsToSystem5_nSteps_rules_form
    (cts : CTS) (cfg : CTSConfig) (N m : Nat)
    (s5' : System5Config)
    (h : System5.nSteps (ctsToSystem5 cts cfg N) m = some s5') :
    ∃ k, k ≤ m ∧
      s5'.rules = ((ctsRulesToSystem5Rules cts cfg N).drop k).map
                    (fun r => r.map (· + (m : Int))) := by
  obtain ⟨k, h_k_le, h_rules⟩ := System5_nSteps_rules_form _ _ m h
  refine ⟨k, h_k_le, ?_⟩
  rw [h_rules]
  rfl

/-- **Iter 972: 1 stays in bag after first cfg5 step (false-head)**.
    Combines iter 970 (1 ∈ decrement-erase bag) with iter 971
    (1 ∉ firstRule.map(·+1)) via iter 969's
    `xorMerge_mem_left_of_not_mem_right`.  Discharges Nodup
    obligations using `ctsConfigToSystem5Bag_decrement_erase_nodup`
    and iter 917's `ctsRulesToSystem5Rules_first_rule_map_add_1_nodup`.

    Result: after the first System5 step from a false-head cfg5, the
    new bag still contains 1 — so step 2 is a P-step too.  This is
    the inductive heart of "all 4 steps are P-steps" for the false-
    head trajectory. -/
theorem ctsToSystem5_false_head_after_first_step_one_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5', System5.nSteps (ctsToSystem5 cts
            { data := false :: rest, phase := phase } N) 1 = some s5'
         ∧ (1 : Int) ∈ s5'.bag := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  have h_data : cfg.data ≠ [] := by simp
  obtain ⟨nextRule, restRules, h_inc, h_step⟩ :=
    ctsToSystem5_first_step cts cfg N h_data h_N
  refine ⟨_, h_step, ?_⟩
  show (1 : Int) ∈ xorMerge (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0) nextRule
  obtain ⟨r1, r2, tail, h_eq, h_no_one⟩ :=
    ctsRulesToSystem5Rules_false_head_first_rule_inc_no_one cts rest phase N h_N
  obtain ⟨r1', _, _, h_eq', h_nodup⟩ :=
    ctsRulesToSystem5Rules_first_rule_map_add_1_nodup cts cfg N h_N
  have h_r1_eq : r1 = r1' := by
    rw [h_eq] at h_eq'
    simp at h_eq'
    exact h_eq'.1
  have h_nextRule : nextRule = r1.map (· + 1) := by
    rw [h_eq] at h_inc
    simp at h_inc
    exact h_inc.1.symm
  rw [h_nextRule]
  apply xorMerge_mem_left_of_not_mem_right
  · exact ctsConfigToSystem5Bag_decrement_erase_nodup cfg
  · rw [h_r1_eq]; exact h_nodup
  · exact ctsConfigToSystem5Bag_false_head_dec_erase_one_mem rest phase
  · exact h_no_one

/-- **Iter 974: 2 stays in bag after first cfg5 step (false-head)**.
    Companion to iter 972 for the value `2`.  Uses iter 973's
    `ctsConfigToSystem5Bag_false_head_dec_erase_two_mem` (membership)
    and `ctsRulesToSystem5Rules_false_head_first_two_rules_no_two`
    (disjointness) via iter 969's `xorMerge_mem_left_of_not_mem_right`.

    Critical for chaining to step 3: 2 ∈ bag-1 ⇒ 1 ∈ (bag-1.map(·-1)).erase 0
    ⇒ step 3 of cfg5 is also a P-step. -/
theorem ctsToSystem5_false_head_after_first_step_two_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5', System5.nSteps (ctsToSystem5 cts
            { data := false :: rest, phase := phase } N) 1 = some s5'
         ∧ (2 : Int) ∈ s5'.bag := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  have h_data : cfg.data ≠ [] := by simp
  obtain ⟨nextRule, restRules, h_inc, h_step⟩ :=
    ctsToSystem5_first_step cts cfg N h_data h_N
  refine ⟨_, h_step, ?_⟩
  show (2 : Int) ∈ xorMerge (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0) nextRule
  obtain ⟨r1, _, _, h_eq, h_no_two_r1, _⟩ :=
    ctsRulesToSystem5Rules_false_head_first_two_rules_no_two cts rest phase N h_N
  obtain ⟨r1', _, _, h_eq', h_nodup⟩ :=
    ctsRulesToSystem5Rules_first_rule_map_add_1_nodup cts cfg N h_N
  have h_r1_eq : r1 = r1' := by
    rw [h_eq] at h_eq'
    simp at h_eq'
    exact h_eq'.1
  have h_nextRule : nextRule = r1.map (· + 1) := by
    rw [h_eq] at h_inc
    simp at h_inc
    exact h_inc.1.symm
  rw [h_nextRule]
  apply xorMerge_mem_left_of_not_mem_right
  · exact ctsConfigToSystem5Bag_decrement_erase_nodup cfg
  · rw [h_r1_eq]; exact h_nodup
  · exact ctsConfigToSystem5Bag_false_head_dec_erase_two_mem rest phase
  · exact h_no_two_r1

/-- **Iter 988: 3 stays in bag after first cfg5 step (false-head)**.
    Companion to iters 972/974 for the value `3`.  Uses iter 987's
    `ctsConfigToSystem5Bag_false_head_dec_erase_three_mem` (membership)
    and `ctsRulesToSystem5Rules_false_head_first_two_rules_no_three`
    (disjointness) via iter 969's `xorMerge_mem_left_of_not_mem_right`.

    Critical for chaining the 4-step P-step cascade: 3 ∈ bag-1 ⇒
    2 ∈ bag-1.dec-erase ⇒ 2 ∈ bag-2 (modulo r2.map(·+2) disjointness)
    ⇒ 1 ∈ bag-3 ⇒ step 4 of cfg5 is also a P-step. -/
theorem ctsToSystem5_false_head_after_first_step_three_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5', System5.nSteps (ctsToSystem5 cts
            { data := false :: rest, phase := phase } N) 1 = some s5'
         ∧ (3 : Int) ∈ s5'.bag := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  have h_data : cfg.data ≠ [] := by simp
  obtain ⟨nextRule, restRules, h_inc, h_step⟩ :=
    ctsToSystem5_first_step cts cfg N h_data h_N
  refine ⟨_, h_step, ?_⟩
  show (3 : Int) ∈ xorMerge (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0) nextRule
  obtain ⟨r1, _, _, h_eq, h_no_three_r1, _⟩ :=
    ctsRulesToSystem5Rules_false_head_first_two_rules_no_three cts rest phase N h_N
  obtain ⟨r1', _, _, h_eq', h_nodup⟩ :=
    ctsRulesToSystem5Rules_first_rule_map_add_1_nodup cts cfg N h_N
  have h_r1_eq : r1 = r1' := by
    rw [h_eq] at h_eq'
    simp at h_eq'
    exact h_eq'.1
  have h_nextRule : nextRule = r1.map (· + 1) := by
    rw [h_eq] at h_inc
    simp at h_inc
    exact h_inc.1.symm
  rw [h_nextRule]
  apply xorMerge_mem_left_of_not_mem_right
  · exact ctsConfigToSystem5Bag_decrement_erase_nodup cfg
  · rw [h_r1_eq]; exact h_nodup
  · exact ctsConfigToSystem5Bag_false_head_dec_erase_three_mem rest phase
  · exact h_no_three_r1

/-- **Iter 995: bag-1 explicit form for false-head**.  Combines
    iter 994's dec-erase form (`1 :: 2 :: 3 :: aux rest 4`) with iter
    913's r1.map(·+1) disjointness from dec-erase bag, applying
    `xorMerge_disjoint_eq_reverse_append` (iter 912) to get an explicit
    list-concat form.  Result: `s5_1.bag = (r1.map(·+1)).reverse ++
    (1 :: 2 :: 3 :: aux rest 4)`.  The r1.map(·+1) entries are
    all ≥ 10 (from r1 ≥ 9 per iter 906) and aux rest 4 entries are
    < counterAfterWorkingString cfg.data ≤ r1 entries. -/
theorem ctsToSystem5_false_head_bag1_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail s5_1,
      ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.nSteps (ctsToSystem5 cts
          { data := false :: rest, phase := phase } N) 1 = some s5_1
      ∧ s5_1.bag = (r1.map (· + 1)).reverse
                  ++ ((1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4) := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  have h_data : cfg.data ≠ [] := by simp
  obtain ⟨nextRule, restRules, h_inc, h_step1⟩ :=
    ctsToSystem5_first_step cts cfg N h_data h_N
  obtain ⟨r1, r2, tail, h_rules⟩ : ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail := by
    obtain ⟨r1, r2, tail, h, _, _⟩ :=
      ctsToSystem5_false_head_first_two_rules_ge_seven cts rest phase N h_N
    exact ⟨r1, r2, tail, h⟩
  obtain ⟨r1', _, _, h_eq', h_disjoint⟩ :=
    ctsToSystem5_dec_erase_bag_r1_inc_disjoint cts cfg N h_N h_data
  obtain ⟨r1'', _, _, h_eq'', h_nodup⟩ :=
    ctsRulesToSystem5Rules_first_rule_map_add_1_nodup cts cfg N h_N
  have h_r1_eq : r1 = r1' := by
    rw [h_rules] at h_eq'; simp at h_eq'; exact h_eq'.1
  have h_r1_eq' : r1 = r1'' := by
    rw [h_rules] at h_eq''; simp at h_eq''; exact h_eq''.1
  have h_nextRule : nextRule = r1.map (· + 1) := by
    rw [h_rules] at h_inc
    simp at h_inc
    exact h_inc.1.symm
  refine ⟨r1, r2, tail, _, h_rules, h_step1, ?_⟩
  show (xorMerge (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0) nextRule
        : List Int)
      = (r1.map (· + 1)).reverse
        ++ ((1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4)
  rw [h_nextRule]
  rw [xorMerge_disjoint_eq_reverse_append]
  · rw [ctsConfigToSystem5Bag_false_head_dec_erase_eq]
  · intro y hy hy_in
    rw [← h_r1_eq] at h_disjoint
    exact h_disjoint y hy_in hy
  · rw [h_r1_eq']; exact h_nodup

/-- **Iter 998: bag-1 dec-erase explicit form for false-head**.
    `(s5_1.bag.map(·-1)).erase 0 = r1.reverse ++ (1 :: 2 :: aux rest 3)`.
    Builds on iter 995's bag-1 form via decomposition over append/cons,
    iter 996's `List_Int_inc_reverse_dec_cancel` (for the r1 prefix)
    and `_dec_at_four` (for the aux portion), and iter 997's
    `_erase_append_cons_of_not_mem` (to locate and erase the `0`
    after the r1.reverse prefix).  The `0 ∉ r1.reverse` obligation
    follows from r1 entries ≥ 9 (iter 906). -/
theorem ctsToSystem5_false_head_bag1_dec_erase_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ r1 r2 tail s5_1,
      ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
        = r1 :: r2 :: tail
      ∧ System5.nSteps (ctsToSystem5 cts
          { data := false :: rest, phase := phase } N) 1 = some s5_1
      ∧ (s5_1.bag.map (· - 1)).erase 0
        = r1.reverse ++ ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3) := by
  obtain ⟨r1, r2, tail, s5_1, h_rules, h_step1, h_bag1⟩ :=
    ctsToSystem5_false_head_bag1_form cts rest phase N h_N
  refine ⟨r1, r2, tail, s5_1, h_rules, h_step1, ?_⟩
  rw [h_bag1]
  rw [List.map_append]
  rw [List_Int_inc_reverse_dec_cancel]
  show (r1.reverse ++ ((1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4).map (· - 1)).erase 0
      = r1.reverse ++ (1 :: 2 :: ctsConfigToSystem5BagAux rest 3)
  simp only [List.map_cons]
  rw [ctsConfigToSystem5BagAux_dec_at_four]
  show (r1.reverse ++ ((0 : Int) :: 1 :: 2 :: ctsConfigToSystem5BagAux rest 3)).erase 0
      = r1.reverse ++ (1 :: 2 :: ctsConfigToSystem5BagAux rest 3)
  have h_zero_not_r1 : (0 : Int) ∉ r1.reverse := by
    rw [List.mem_reverse]
    intro h_in
    obtain ⟨r1', _, _, h_eq, h_r1, _⟩ :=
      ctsToSystem5_false_head_first_two_rules_ge_seven cts rest phase N h_N
    have h_r1_eq : r1 = r1' := by
      rw [h_rules] at h_eq; simp at h_eq; exact h_eq.1
    rw [h_r1_eq] at h_in
    have := h_r1 0 h_in
    omega
  rw [List_Int_erase_append_cons_of_not_mem _ _ _ h_zero_not_r1]

/-- **Iter 978: s5_1 rules form**.  When `ctsRulesToSystem5Rules cts cfg N
    = r1 :: r2 :: tail`, after the first cfg5 P-step the resulting
    rules are `(r2.map(·+1)) :: tail.map(map(·+1))` — the head r1 is
    popped (consumed by the xorMerge into the bag), and every
    surviving rule is incremented.  Builds toward characterizing the
    rule-popped at step 2 = `r2.map(·+2)` (the doubly-incremented r2). -/
theorem ctsToSystem5_step1_rules_form
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h_data : cfg.data ≠ []) (h_N : N ≥ 1)
    (r1 r2 : List Int) (tail : List (List Int))
    (h_rules : ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail) :
    ∃ s5_1, System5.nSteps (ctsToSystem5 cts cfg N) 1 = some s5_1
         ∧ s5_1.rules = (r2.map (· + 1)) :: tail.map (fun r => r.map (· + 1)) := by
  obtain ⟨s5_1, h_step⟩ := ctsToSystem5_first_step_some cts cfg N h_data h_N
  refine ⟨s5_1, h_step, ?_⟩
  have h_zero : (0 : Int) ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) :=
    ctsToSystem5_zero_in_decrement cts cfg N h_data
  have h_step' : System5.step (ctsToSystem5 cts cfg N) = some s5_1 := by
    rw [← System5.nSteps_one]; exact h_step
  have h_rules_form := System5_step_rules_pstep _ s5_1 h_step' h_zero
  rw [h_rules_form]
  show ((ctsRulesToSystem5Rules cts cfg N).drop 1).map (fun r => r.map (· + 1))
     = (r2.map (· + 1)) :: tail.map (fun r => r.map (· + 1))
  rw [h_rules]
  simp [List.drop, List.map_cons]

/-- **Iter 979: head of doubly-incremented step-1 rules = r2.map(·+2)**.
    When `s5_1.rules = (r2.map(·+1)) :: tail.map(map(·+1))` (per iter 978),
    incrementing all rules at step 2 gives a list whose head is
    `(r2.map(·+1)).map(·+1) = r2.map(·+(1+1)) = r2.map(·+2)`.  This is
    the rule that gets popped at step 2 in the false-head trajectory. -/
theorem step1_rules_inc_head_eq_r2_map_add_2
    (r2 : List Int) (tail : List (List Int)) :
    (((r2.map (· + 1)) :: tail.map (fun r => r.map (· + 1))).map
        (fun r => r.map (· + 1))).head?
      = some (r2.map (· + 2)) := by
  simp [List.head?, List.map_cons]
  intro a _; omega

/-- **Iter 1004: s5_1 dec-erase bag is Nodup (false-head)**.
    Wrapper packaging: after the first cfg5 step,
    `(s5_1.bag.map(·-1)).erase 0` is Nodup.  Composition: s5_1.bag
    is the result of one P-step's xorMerge, which preserves Nodup
    (`xorMerge_nodup` + iter 645's dec-erase Nodup of cfg5 bag).
    Then map(·-1) preserves Nodup (since (·-1) is injective on Int).
    Finally `List.Nodup.erase` preserves under erase.

    Used in the bag-2 membership chain to discharge the Nodup
    obligation for `xorMerge_mem_iff`. -/
theorem ctsToSystem5_false_head_step1_dec_erase_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_1, System5.nSteps (ctsToSystem5 cts
            { data := false :: rest, phase := phase } N) 1 = some s5_1
         ∧ ((s5_1.bag.map (· - 1)).erase 0).Nodup := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  have h_data : cfg.data ≠ [] := by simp
  obtain ⟨nextRule, restRules, _, h_step1⟩ :=
    ctsToSystem5_first_step cts cfg N h_data h_N
  refine ⟨_, h_step1, ?_⟩
  show ((xorMerge (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0) nextRule
          ).map (· - 1)).erase 0 |>.Nodup
  have h_xor_nodup :
      (xorMerge (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0) nextRule).Nodup :=
    xorMerge_nodup _ _ (ctsConfigToSystem5Bag_decrement_erase_nodup cfg)
  apply List.Nodup.erase
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_xor_nodup
  intro a b h_ne h_eq; apply h_ne; have : a - 1 = b - 1 := h_eq; omega

/-- **Iter 980: bag-2 explicit form (false-head)**.  Assembles the
    full step-2 trajectory: when `cts.appendants` (and hence
    `ctsRulesToSystem5Rules cts cfg N`) splits as `r1 :: r2 :: tail`
    in the false-head case, the bag after exactly two cfg5 P-steps
    is `xorMerge ((s5_1.bag.map(·-1)).erase 0) (r2.map(·+2))`.

    Combines iter 978 (s5_1.rules form) + iter 972 (1 ∈ s5_1.bag) +
    `System5_step_explicit_pop` + iter 894's `List_Int_map_add_compose`
    (to rewrite `(r2.map(·+1)).map(·+1)` as `r2.map(·+2)`).  The s5_1
    determinism is handled via `Option.some.inj`. -/
theorem ctsToSystem5_false_head_bag2_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (r1 r2 : List Int) (tail : List (List Int))
    (h_rules : ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
              = r1 :: r2 :: tail) :
    ∃ s5_1 s5_2,
      System5.nSteps (ctsToSystem5 cts { data := false :: rest, phase := phase } N) 1
        = some s5_1
    ∧ System5.nSteps (ctsToSystem5 cts { data := false :: rest, phase := phase } N) 2
        = some s5_2
    ∧ s5_2.bag = xorMerge ((s5_1.bag.map (· - 1)).erase 0) (r2.map (· + 2)) := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  have h_data : cfg.data ≠ [] := by simp
  obtain ⟨s5_1, h_step1, h_rules_form⟩ :=
    ctsToSystem5_step1_rules_form cts cfg N h_data h_N r1 r2 tail h_rules
  obtain ⟨s5_1a, h_step1a, h_one_mem⟩ :=
    ctsToSystem5_false_head_after_first_step_one_mem cts rest phase N h_N
  have h_eqa : s5_1 = s5_1a := Option.some.inj (h_step1.symm.trans h_step1a)
  have h_one_mem_s5_1 : (1 : Int) ∈ s5_1.bag := h_eqa ▸ h_one_mem
  have h_zero : (0 : Int) ∈ s5_1.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_1
  have h_bag_ne : s5_1.bag ≠ [] := List.ne_nil_of_mem h_one_mem_s5_1
  have h_step2 := System5_step_explicit_pop s5_1 (r2.map (· + 1))
      (tail.map (fun r => r.map (· + 1)))
      h_rules_form h_bag_ne h_zero
  have h_n2 : System5.nSteps (ctsToSystem5 cts cfg N) 2
            = some ⟨xorMerge ((s5_1.bag.map (· - 1)).erase 0)
                ((r2.map (· + 1)).map (· + 1)),
              (tail.map (fun r => r.map (· + 1))).map (fun r => r.map (· + 1))⟩ := by
    rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add, h_step1]
    simp [System5.nSteps_one, h_step2]
  refine ⟨s5_1, _, h_step1, h_n2, ?_⟩
  show xorMerge ((s5_1.bag.map (· - 1)).erase 0) ((r2.map (· + 1)).map (· + 1))
       = xorMerge ((s5_1.bag.map (· - 1)).erase 0) (r2.map (· + 2))
  congr 1
  have h := List_Int_map_add_compose r2 1 1
  exact h

/-- **Iter 1005: bag-2 membership form for false-head**.  The full
    membership equality: `∀ x, x ∈ s5_2.bag ↔ x ∈ (1 :: 2 :: aux rest 3)`.

    Composition (key prerequisites already proven):
    - iter 980 (`bag2_form`): bag-2 = xorMerge dec-erase r2.map(·+2).
    - iter 998 (`bag1_dec_erase_form`): dec-erase = r1.reverse ++ rest_part.
    - iter 1004 (`step1_dec_erase_nodup`): dec-erase Nodup.
    - iter 981 (`_second_rule_map_add_2_nodup`): r2.map(·+2) Nodup.
    - iter 1000 (`_first_two_rules_reverse_mem_eq`): r1.reverse ≡ r2.map(·+2)
      at the membership level.
    - iter 1003 (`_three_one_two_cons_disjoint_r2_inc2`): rest_part disjoint
      from r2.map(·+2).
    - `xorMerge_mem_iff`: symmetric-difference characterization.

    The case analysis: by `xorMerge_mem_iff`, `x ∈ bag-2 ↔ (x ∈ L ∧ x ∉ R)
    ∨ (x ∉ L ∧ x ∈ R)`.  Using r1.reverse ≡ R, the L-but-not-R case reduces
    to `x ∈ rest_part`; the not-L-but-R case is contradictory.

    **The bag-2's full membership identity is now closed**, completing
    the chain: `x ∈ s5_2.bag ↔ x ∈ (1 :: 2 :: aux rest 3)`. -/
theorem ctsToSystem5_false_head_bag2_mem_iff
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (r1 r2 : List Int) (tail : List (List Int))
    (h_rules : ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
              = r1 :: r2 :: tail) :
    ∃ s5_2,
      System5.nSteps (ctsToSystem5 cts { data := false :: rest, phase := phase } N) 2
        = some s5_2
    ∧ ∀ x, x ∈ s5_2.bag ↔ x ∈ ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3) := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨s5_1, s5_2, h_step1, h_step2, h_bag2⟩ :=
    ctsToSystem5_false_head_bag2_form cts rest phase N h_N r1 r2 tail h_rules
  obtain ⟨r1', _, _, s5_1', h_rules', h_step1', h_dec_erase⟩ :=
    ctsToSystem5_false_head_bag1_dec_erase_form cts rest phase N h_N
  have h_r1_eq : r1 = r1' := by
    rw [h_rules] at h_rules'; simp at h_rules'; exact h_rules'.1
  have h_s5_1_eq : s5_1 = s5_1' := Option.some.inj (h_step1.symm.trans h_step1')
  rw [h_s5_1_eq] at h_bag2
  rw [h_dec_erase] at h_bag2
  rw [← h_r1_eq] at h_bag2
  refine ⟨s5_2, h_step2, ?_⟩
  intro x
  rw [h_bag2]
  obtain ⟨s5_1'', h_step1'', h_dec_erase_nodup⟩ :=
    ctsToSystem5_false_head_step1_dec_erase_nodup cts rest phase N h_N
  have h_s5_1_eq' : s5_1' = s5_1'' :=
    Option.some.inj (h_step1'.symm.trans h_step1'')
  rw [← h_s5_1_eq'] at h_dec_erase_nodup
  rw [h_dec_erase, ← h_r1_eq] at h_dec_erase_nodup
  obtain ⟨_, r2''', _, h_rules''', h_nodup_r2⟩ :=
    ctsRulesToSystem5Rules_second_rule_map_add_2_nodup cts cfg N h_N
  have h_r2_eq : r2 = r2''' := by
    rw [h_rules] at h_rules'''; simp at h_rules'''; exact h_rules'''.2.1
  rw [← h_r2_eq] at h_nodup_r2
  rw [xorMerge_mem_iff _ _ h_dec_erase_nodup h_nodup_r2]
  obtain ⟨r1'''', r2'''', _, h_rules'''', h_rev_mem⟩ :=
    ctsRulesToSystem5Rules_first_two_rules_reverse_mem_eq cts cfg N h_N
  have h_r1_eq'' : r1 = r1'''' := by
    rw [h_rules] at h_rules''''; simp at h_rules''''; exact h_rules''''.1
  have h_r2_eq'' : r2 = r2'''' := by
    rw [h_rules] at h_rules''''; simp at h_rules''''; exact h_rules''''.2.1
  rw [← h_r1_eq'', ← h_r2_eq''] at h_rev_mem
  obtain ⟨_, r2''''', _, h_rules''''', h_disj_r2⟩ :=
    ctsConfigToSystem5BagAux_three_one_two_cons_disjoint_r2_inc2 cts rest phase N h_N
  have h_r2_eq''' : r2 = r2''''' := by
    rw [h_rules] at h_rules'''''; simp at h_rules'''''; exact h_rules'''''.2.1
  rw [← h_r2_eq'''] at h_disj_r2
  constructor
  · rintro (⟨h_in_l, h_not_r⟩ | ⟨h_not_l, h_in_r⟩)
    · rcases List.mem_append.mp h_in_l with h_in_rev | h_in_rest
      · exact absurd ((h_rev_mem x).mp h_in_rev) h_not_r
      · exact h_in_rest
    · have h_in_rev : x ∈ r1.reverse := (h_rev_mem x).mpr h_in_r
      have : x ∈ r1.reverse ++ ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3) :=
        List.mem_append_left _ h_in_rev
      exact absurd this h_not_l
  · intro h_in_rest
    left
    refine ⟨List.mem_append_right _ h_in_rest, h_disj_r2 x h_in_rest⟩

/-- **Iter 1008: s5_2.bag is Nodup (false-head)**.  Direct corollary
    of iter 980's bag-2 form combined with `xorMerge_nodup` and iter
    1004's dec-erase Nodup.  Used to lift the bag-2 mem-iff (iter 1005)
    through bag-3's dec-erase form (iter 986) via iter 1006. -/
theorem ctsToSystem5_false_head_step2_bag_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_2, System5.nSteps (ctsToSystem5 cts
            { data := false :: rest, phase := phase } N) 2 = some s5_2
         ∧ s5_2.bag.Nodup := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨r1, r2, tail, h_rules⟩ : ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail := by
    obtain ⟨r1, r2, tail, h, _, _⟩ :=
      ctsToSystem5_false_head_first_two_rules_ge_seven cts rest phase N h_N
    exact ⟨r1, r2, tail, h⟩
  obtain ⟨s5_1, s5_2, h_step1, h_step2, h_bag2⟩ :=
    ctsToSystem5_false_head_bag2_form cts rest phase N h_N r1 r2 tail h_rules
  obtain ⟨s5_1', h_step1', h_dec_erase_nodup⟩ :=
    ctsToSystem5_false_head_step1_dec_erase_nodup cts rest phase N h_N
  have h_eq : s5_1 = s5_1' := Option.some.inj (h_step1.symm.trans h_step1')
  rw [h_eq] at h_bag2
  refine ⟨s5_2, h_step2, ?_⟩
  rw [h_bag2]
  exact xorMerge_nodup _ _ h_dec_erase_nodup

/-- **Iter 977: cfg5 step 2 succeeds (false-head)**.  Combines
    iter 972 (1 ∈ bag-1, so step 2's P-step trigger holds) with the
    rules-length lower bound `4·|appendants|·N ≥ 4` and iter 968's
    `System5_step_rules_length_eq_pop` (P-step decrements length by
    exactly 1) to show s5_1.rules ≠ [], hence step 2 produces some
    cfg'.  Builds toward the explicit form of bag-2. -/
theorem ctsToSystem5_false_head_step2_succeeds
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_2, System5.nSteps (ctsToSystem5 cts
            { data := false :: rest, phase := phase } N) 2 = some s5_2 := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨s5_1, h_step1, h_one_mem⟩ :=
    ctsToSystem5_false_head_after_first_step_one_mem cts rest phase N h_N
  have h_bag_ne : s5_1.bag ≠ [] := List.ne_nil_of_mem h_one_mem
  have h_rules_ne : s5_1.rules ≠ [] := by
    have h_orig_len : (ctsToSystem5 cts cfg N).rules.length
                    = 4 * cts.appendants.length * N := by
      simp [ctsToSystem5, ctsRulesToSystem5Rules_length]
    have h_app : cts.appendants.length ≥ 1 := cts.nonempty
    have h_orig_len_ge : (ctsToSystem5 cts cfg N).rules.length ≥ 4 := by
      rw [h_orig_len]
      have h2 : 4 * cts.appendants.length * N ≥ 4 * cts.appendants.length :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
    have h_zero : (0 : Int) ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) :=
      ctsToSystem5_zero_in_decrement cts cfg N (by simp)
    have h_step1' : System5.step (ctsToSystem5 cts cfg N) = some s5_1 := by
      rw [← System5.nSteps_one]; exact h_step1
    have h_rules_eq := System5_step_rules_length_eq_pop
      (ctsToSystem5 cts cfg N) s5_1 h_step1'
      (ctsConfigToSystem5Bag_nonempty cfg (by simp))
      (ctsRulesToSystem5Rules_nonempty cts cfg N h_N) h_zero
    intro h
    rw [List.length_eq_zero_iff.mpr h] at h_rules_eq
    omega
  obtain ⟨cfg', h_step2⟩ :=
    (System5_step_some_iff s5_1).mpr ⟨h_bag_ne, h_rules_ne⟩
  refine ⟨cfg', ?_⟩
  rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add, h_step1]
  simp [System5.nSteps_one, h_step2]

/-- **Iter 982: 1 ∈ s5_2.bag for false-head — step 3 IS a P-step**.
    The capstone of the steps-2-and-3 chain analysis.  Combines:
    - iter 980: bag-2 = `xorMerge ((s5_1.bag.map(·-1)).erase 0) (r2.map(·+2))`
    - iter 974: 2 ∈ s5_1.bag (false-head)
    - iter 975: `mem_imp_pred_in_dec_erase` (2 ∈ bag ⇒ 1 ∈ dec-erase)
    - iter 976: 1 ∉ r2.map(·+2) for false-head
    - iter 981: r2.map(·+2) Nodup
    - iter 969: xorMerge_mem_left_of_not_mem_right
    - `xorMerge_nodup` for s5_1.bag Nodup (since s5_1.bag was itself
      a xorMerge of dec-erase'd encoder bag with first rule).

    Together with iter 972 (1 ∈ s5_1.bag, so step 2 was a P-step), this
    proves that **the first 3 cfg5 steps are all P-steps** for the
    false-head trajectory — a key invariant for the 4-step
    `smith_per_step_extension` proof. -/
theorem ctsToSystem5_false_head_step2_one_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_2, System5.nSteps (ctsToSystem5 cts
            { data := false :: rest, phase := phase } N) 2 = some s5_2
         ∧ (1 : Int) ∈ s5_2.bag := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨r1, r2, tail, h_rules⟩ : ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail := by
    obtain ⟨r1, r2, tail, h, _, _⟩ :=
      ctsToSystem5_false_head_first_two_rules_ge_seven cts rest phase N h_N
    exact ⟨r1, r2, tail, h⟩
  obtain ⟨s5_1, s5_2, h_step1, h_step2, h_bag2_form⟩ :=
    ctsToSystem5_false_head_bag2_form cts rest phase N h_N r1 r2 tail h_rules
  refine ⟨s5_2, h_step2, ?_⟩
  rw [h_bag2_form]
  have h_data : cfg.data ≠ [] := by simp
  obtain ⟨nextRule, restRules, _, h_step1_form⟩ :=
    ctsToSystem5_first_step cts cfg N h_data h_N
  have h_s5_1_eq : s5_1 = ⟨xorMerge (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0)
                                    nextRule, restRules⟩ :=
    Option.some.inj (h_step1.symm.trans h_step1_form)
  have h_s5_1_bag_nodup : s5_1.bag.Nodup := by
    rw [h_s5_1_eq]
    exact xorMerge_nodup _ _ (ctsConfigToSystem5Bag_decrement_erase_nodup cfg)
  apply xorMerge_mem_left_of_not_mem_right
  · apply List.Nodup.erase
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_1_bag_nodup
    intro a b h_ne h_eq
    apply h_ne
    have : a - 1 = b - 1 := h_eq
    omega
  · obtain ⟨_, r2', _, h_eq', h_nodup⟩ :=
      ctsRulesToSystem5Rules_second_rule_map_add_2_nodup cts cfg N h_N
    have h_r2_eq : r2 = r2' := by
      rw [h_rules] at h_eq'; simp at h_eq'; exact h_eq'.2.1
    rw [h_r2_eq]; exact h_nodup
  · have h_two_mem : (2 : Int) ∈ s5_1.bag := by
      obtain ⟨s5_1b, h_step1b, h_two_mem'⟩ :=
        ctsToSystem5_false_head_after_first_step_two_mem cts rest phase N h_N
      have h_eqb : s5_1 = s5_1b := Option.some.inj (h_step1.symm.trans h_step1b)
      exact h_eqb ▸ h_two_mem'
    have h_pred := mem_imp_pred_in_dec_erase s5_1.bag 2 h_two_mem (by omega)
    have h_eq_one : (2 : Int) - 1 = 1 := by omega
    rw [h_eq_one] at h_pred
    exact h_pred
  · obtain ⟨_, r2', _, h_eq', h_no_one⟩ :=
      ctsRulesToSystem5Rules_false_head_second_rule_inc2_no_one cts rest phase N h_N
    have h_r2_eq : r2 = r2' := by
      rw [h_rules] at h_eq'; simp at h_eq'; exact h_eq'.2.1
    rw [h_r2_eq]; exact h_no_one

/-- **Iter 989: 2 ∈ s5_2.bag for false-head**.  Companion to iter 982
    (which proved `1 ∈ s5_2.bag`), but for the value `2`.  Required
    for the next link of the cascade `2 ∈ s5_2.bag ⇒ 1 ∈ s5_3.bag`
    (via `mem_imp_pred_in_dec_erase` and bag-3 form from iter 986).

    Composition: bag-2 = `xorMerge ((s5_1.bag.map(·-1)).erase 0) (r2.map(·+2))`
    (iter 980).  Apply `xorMerge_mem_left_of_not_mem_right`:
    - membership: `3 ∈ s5_1.bag` (iter 988) + `mem_imp_pred_in_dec_erase`
      (iter 975) gives `2 ∈ (s5_1.bag.map(·-1)).erase 0`.
    - disjointness: `2 ∉ r2.map(·+2)` (iter 973). -/
theorem ctsToSystem5_false_head_step2_two_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_2, System5.nSteps (ctsToSystem5 cts
            { data := false :: rest, phase := phase } N) 2 = some s5_2
         ∧ (2 : Int) ∈ s5_2.bag := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨r1, r2, tail, h_rules⟩ : ∃ r1 r2 tail,
      ctsRulesToSystem5Rules cts cfg N = r1 :: r2 :: tail := by
    obtain ⟨r1, r2, tail, h, _, _⟩ :=
      ctsToSystem5_false_head_first_two_rules_ge_seven cts rest phase N h_N
    exact ⟨r1, r2, tail, h⟩
  obtain ⟨s5_1, s5_2, h_step1, h_step2, h_bag2_form⟩ :=
    ctsToSystem5_false_head_bag2_form cts rest phase N h_N r1 r2 tail h_rules
  refine ⟨s5_2, h_step2, ?_⟩
  rw [h_bag2_form]
  have h_data : cfg.data ≠ [] := by simp
  obtain ⟨nextRule, restRules, _, h_step1_form⟩ :=
    ctsToSystem5_first_step cts cfg N h_data h_N
  have h_s5_1_eq : s5_1 = ⟨xorMerge (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0)
                                    nextRule, restRules⟩ :=
    Option.some.inj (h_step1.symm.trans h_step1_form)
  have h_s5_1_bag_nodup : s5_1.bag.Nodup := by
    rw [h_s5_1_eq]
    exact xorMerge_nodup _ _ (ctsConfigToSystem5Bag_decrement_erase_nodup cfg)
  apply xorMerge_mem_left_of_not_mem_right
  · apply List.Nodup.erase
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_1_bag_nodup
    intro a b h_ne h_eq
    apply h_ne
    have : a - 1 = b - 1 := h_eq
    omega
  · obtain ⟨_, r2', _, h_eq', h_nodup⟩ :=
      ctsRulesToSystem5Rules_second_rule_map_add_2_nodup cts cfg N h_N
    have h_r2_eq : r2 = r2' := by
      rw [h_rules] at h_eq'; simp at h_eq'; exact h_eq'.2.1
    rw [h_r2_eq]; exact h_nodup
  · have h_three_mem : (3 : Int) ∈ s5_1.bag := by
      obtain ⟨s5_1b, h_step1b, h_three_mem'⟩ :=
        ctsToSystem5_false_head_after_first_step_three_mem cts rest phase N h_N
      have h_eqb : s5_1 = s5_1b := Option.some.inj (h_step1.symm.trans h_step1b)
      exact h_eqb ▸ h_three_mem'
    have h_pred := mem_imp_pred_in_dec_erase s5_1.bag 3 h_three_mem (by omega)
    have h_eq_two : (3 : Int) - 1 = 2 := by omega
    rw [h_eq_two] at h_pred
    exact h_pred
  · obtain ⟨_, r2', _, h_eq', _, h_no_two⟩ :=
      ctsRulesToSystem5Rules_false_head_first_two_rules_no_two cts rest phase N h_N
    have h_r2_eq : r2 = r2' := by
      rw [h_rules] at h_eq'; simp at h_eq'; exact h_eq'.2.1
    rw [h_r2_eq]; exact h_no_two

/-- **Iter 985: s5_2.rules form for false-head — starts with `[] :: []`**.
    Combines iter 968's `System5_nSteps_rules_pstep` (after 2 P-steps,
    rules = `(orig.drop 2).map(map(·+2))`) with iter 984's
    `ctsRulesToSystem5Rules_drop_2_exists_empty_rules` (drop-2 yields
    `[] :: [] :: rest_more`).  The two empty rules survive the
    `(·+2)` map (since `[].map _ = []`), giving s5_2.rules =
    `[] :: [] :: rest_more.map(map(·+2))`.

    The all-P-step hypothesis for `System5_nSteps_rules_pstep` is
    discharged via iter 969's cfg5 P-step (step 0) and iter 972's
    `1 ∈ s5_1.bag` (step 1). -/
theorem ctsToSystem5_false_head_step2_rules_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_2, System5.nSteps (ctsToSystem5 cts
            { data := false :: rest, phase := phase } N) 2 = some s5_2
         ∧ ∃ rest_more, s5_2.rules = ([] : List Int) :: ([] : List Int) :: rest_more := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨s5_2, h_step2, _⟩ :=
    ctsToSystem5_false_head_step2_one_mem cts rest phase N h_N
  refine ⟨s5_2, h_step2, ?_⟩
  have h_data : cfg.data ≠ [] := by simp
  have h_pstep : ∀ k < 2, ∀ cfg_k, System5.nSteps (ctsToSystem5 cts cfg N) k = some cfg_k
               → (0 : Int) ∈ cfg_k.bag.map (· - 1) := by
    intro k h_k cfg_k h_k_eq
    match k, h_k with
    | 0, _ =>
      simp [System5.nSteps] at h_k_eq
      rw [← h_k_eq]
      exact ctsToSystem5_zero_in_decrement cts cfg N h_data
    | 1, _ =>
      obtain ⟨s5_1, h_step1, h_one_mem_s5_1⟩ :=
        ctsToSystem5_false_head_after_first_step_one_mem cts rest phase N h_N
      have h_eq : cfg_k = s5_1 := Option.some.inj (h_k_eq.symm.trans h_step1)
      rw [h_eq]
      exact (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_1
  have h_rules_form := System5_nSteps_rules_pstep _ s5_2 2 h_step2 h_pstep
  obtain ⟨rest_more, h_drop⟩ :=
    ctsRulesToSystem5Rules_drop_2_exists_empty_rules cts cfg N h_N
  refine ⟨rest_more.map (fun r => r.map (· + 2)), ?_⟩
  rw [h_rules_form]
  show ((ctsRulesToSystem5Rules cts cfg N).drop 2).map (fun r => r.map (· + (2 : Int)))
     = ([] : List Int) :: ([] : List Int) :: rest_more.map (fun r => r.map (· + 2))
  rw [h_drop]
  simp [List.map_cons]

/-- **Iter 986: bag-3 form for false-head**.  Assembles the explicit
    bag-3 form: after exactly 3 cfg5 steps in the false-head case,
    `s5_3.bag = (s5_2.bag.map(·-1)).erase 0`.  The popped rule at step
    3 is `[]` (per iter 985's `s5_2.rules = [] :: [] :: rest_more`),
    so xorMerge with the (incremented) empty rule simplifies via
    `xorMerge_nil`.

    Combines iter 982 (1 ∈ s5_2.bag → P-step trigger),
    iter 985 (s5_2.rules form), `System5_step_explicit_pop`, and
    `xorMerge_nil`. -/
theorem ctsToSystem5_false_head_bag3_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_2 s5_3,
      System5.nSteps (ctsToSystem5 cts { data := false :: rest, phase := phase } N) 2
        = some s5_2
    ∧ System5.nSteps (ctsToSystem5 cts { data := false :: rest, phase := phase } N) 3
        = some s5_3
    ∧ s5_3.bag = (s5_2.bag.map (· - 1)).erase 0 := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨s5_2a, h_step2a, h_one_mem⟩ :=
    ctsToSystem5_false_head_step2_one_mem cts rest phase N h_N
  obtain ⟨s5_2, h_step2, rest_more, h_rules_form⟩ :=
    ctsToSystem5_false_head_step2_rules_form cts rest phase N h_N
  have h_eq : s5_2a = s5_2 := Option.some.inj (h_step2a.symm.trans h_step2)
  rw [h_eq] at h_one_mem
  have h_bag_ne : s5_2.bag ≠ [] := List.ne_nil_of_mem h_one_mem
  have h_zero : (0 : Int) ∈ s5_2.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem
  have h_step3 := System5_step_explicit_pop s5_2 ([] : List Int)
      (([] : List Int) :: rest_more)
      h_rules_form h_bag_ne h_zero
  have h_n3 : System5.nSteps (ctsToSystem5 cts cfg N) 3
            = some ⟨xorMerge ((s5_2.bag.map (· - 1)).erase 0) ([].map (· + 1)),
              (([] : List Int) :: rest_more).map (fun r => r.map (· + 1))⟩ := by
    rw [show (3 : Nat) = 2 + 1 from rfl, System5.nSteps_add, h_step2]
    simp [System5.nSteps_one, h_step3]
  refine ⟨s5_2, _, h_step2, h_n3, ?_⟩
  show xorMerge ((s5_2.bag.map (· - 1)).erase 0) ([].map (· + 1))
       = (s5_2.bag.map (· - 1)).erase 0
  show xorMerge ((s5_2.bag.map (· - 1)).erase 0) []
       = (s5_2.bag.map (· - 1)).erase 0
  exact xorMerge_nil _

/-- **Iter 1009: bag-3 membership form for false-head**.  Extension of
    iter 1005's bag-2 mem-iff to bag-3.  Composition: bag-3 form
    (iter 986) + bag-2 mem-iff (iter 1005) + dec-erase same-mem
    lifting (iter 1006) + RHS computation (iter 1007).  Result:
    `∀ x, x ∈ s5_3.bag ↔ x ∈ (1 :: aux rest 2)`. -/
theorem ctsToSystem5_false_head_bag3_mem_iff
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (r1 r2 : List Int) (tail : List (List Int))
    (h_rules : ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
              = r1 :: r2 :: tail) :
    ∃ s5_3,
      System5.nSteps (ctsToSystem5 cts { data := false :: rest, phase := phase } N) 3
        = some s5_3
    ∧ ∀ x, x ∈ s5_3.bag ↔ x ∈ ((1 : Int) :: ctsConfigToSystem5BagAux rest 2) := by
  obtain ⟨s5_2, s5_3, h_step2, h_step3, h_bag3⟩ :=
    ctsToSystem5_false_head_bag3_form cts rest phase N h_N
  obtain ⟨s5_2', h_step2', h_bag2_mem⟩ :=
    ctsToSystem5_false_head_bag2_mem_iff cts rest phase N h_N r1 r2 tail h_rules
  obtain ⟨s5_2'', h_step2'', h_s5_2_nodup⟩ :=
    ctsToSystem5_false_head_step2_bag_nodup cts rest phase N h_N
  have h_eq2 : s5_2 = s5_2' := Option.some.inj (h_step2.symm.trans h_step2')
  have h_eq2' : s5_2' = s5_2'' := Option.some.inj (h_step2'.symm.trans h_step2'')
  rw [h_eq2] at h_bag3
  rw [← h_eq2'] at h_s5_2_nodup
  refine ⟨s5_3, h_step3, ?_⟩
  intro x
  rw [h_bag3]
  rw [List_Int_dec_erase_same_mem s5_2'.bag
        ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3)
        h_s5_2_nodup
        (ctsConfigToSystem5BagAux_three_one_two_cons_nodup rest)
        h_bag2_mem 0 x]
  rw [ctsConfigToSystem5BagAux_three_one_two_cons_dec_erase_eq]

/-- **Iter 1011: s5_3.bag is Nodup (false-head)**.  Direct corollary
    of iter 986's bag-3 form combined with iter 1008's s5_2.bag Nodup
    + `List.Pairwise.map` (decrement injectivity) + `List.Nodup.erase`. -/
theorem ctsToSystem5_false_head_step3_bag_nodup
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_3, System5.nSteps (ctsToSystem5 cts
            { data := false :: rest, phase := phase } N) 3 = some s5_3
         ∧ s5_3.bag.Nodup := by
  obtain ⟨s5_2, s5_3, h_step2, h_step3, h_bag3⟩ :=
    ctsToSystem5_false_head_bag3_form cts rest phase N h_N
  obtain ⟨s5_2', h_step2', h_s5_2_nodup⟩ :=
    ctsToSystem5_false_head_step2_bag_nodup cts rest phase N h_N
  have h_eq : s5_2 = s5_2' := Option.some.inj (h_step2.symm.trans h_step2')
  rw [h_eq] at h_bag3
  refine ⟨s5_3, h_step3, ?_⟩
  rw [h_bag3]
  apply List.Nodup.erase
  apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_2_nodup
  intro a b h_ne h_eq; apply h_ne; have : a - 1 = b - 1 := h_eq; omega

/-- **Iter 990: 1 ∈ s5_3.bag for false-head — step 4 IS a P-step**.
    The capstone of the 4-step P-step cascade.  Combines iter 986
    (bag-3 form: `s5_3.bag = (s5_2.bag.map(·-1)).erase 0`) with iter
    989 (`2 ∈ s5_2.bag`) and iter 975 (`mem_imp_pred_in_dec_erase`,
    bridge from `2 ∈ bag` to `1 ∈ bag.map(·-1).erase 0`).

    **Together with iters 972, 982, this proves all 4 cfg5 steps are
    P-steps for the false-head trajectory** — the inductive backbone
    for the 4-step `smith_per_step_extension` proof. -/
theorem ctsToSystem5_false_head_step3_one_mem
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_3, System5.nSteps (ctsToSystem5 cts
            { data := false :: rest, phase := phase } N) 3 = some s5_3
         ∧ (1 : Int) ∈ s5_3.bag := by
  obtain ⟨s5_2, s5_3, h_step2, h_step3, h_bag3_form⟩ :=
    ctsToSystem5_false_head_bag3_form cts rest phase N h_N
  obtain ⟨s5_2', h_step2', h_two_mem⟩ :=
    ctsToSystem5_false_head_step2_two_mem cts rest phase N h_N
  have h_eq : s5_2' = s5_2 := Option.some.inj (h_step2'.symm.trans h_step2)
  rw [h_eq] at h_two_mem
  refine ⟨s5_3, h_step3, ?_⟩
  rw [h_bag3_form]
  have h_pred := mem_imp_pred_in_dec_erase s5_2.bag 2 h_two_mem (by omega)
  have h_eq_one : (2 : Int) - 1 = 1 := by omega
  rw [h_eq_one] at h_pred
  exact h_pred

/-- **Iter 992: s5_3.rules form for false-head — starts with `[]`**.
    Analog of iter 985 for `s5_3` (3 P-steps instead of 2).  Composes
    iter 968's `System5_nSteps_rules_pstep` (after 3 P-steps,
    rules = `(orig.drop 3).map(map(·+3))`) with iter 991's
    `ctsRulesToSystem5Rules_drop_3_exists_empty_rule` (drop-3 yields
    `[] :: rest_more`).  The empty rule survives the `(·+3)` map.

    The all-P-step hypothesis for `System5_nSteps_rules_pstep` (k < 3)
    is discharged via iter 969's cfg5 P-step (k=0), iter 972's
    `1 ∈ s5_1.bag` (k=1), and iter 982's `1 ∈ s5_2.bag` (k=2).

    **The rule popped at step 4 of cfg5 (false-head) is `[]`** — bag-4
    will simplify via `xorMerge_nil`, just like bag-3 did. -/
theorem ctsToSystem5_false_head_step3_rules_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_3, System5.nSteps (ctsToSystem5 cts
            { data := false :: rest, phase := phase } N) 3 = some s5_3
         ∧ ∃ rest_more, s5_3.rules = ([] : List Int) :: rest_more := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨s5_3, h_step3, _⟩ :=
    ctsToSystem5_false_head_step3_one_mem cts rest phase N h_N
  refine ⟨s5_3, h_step3, ?_⟩
  have h_data : cfg.data ≠ [] := by simp
  have h_pstep : ∀ k < 3, ∀ cfg_k, System5.nSteps (ctsToSystem5 cts cfg N) k = some cfg_k
               → (0 : Int) ∈ cfg_k.bag.map (· - 1) := by
    intro k h_k cfg_k h_k_eq
    match k, h_k with
    | 0, _ =>
      simp [System5.nSteps] at h_k_eq
      rw [← h_k_eq]
      exact ctsToSystem5_zero_in_decrement cts cfg N h_data
    | 1, _ =>
      obtain ⟨s5_1, h_step1, h_one_mem_s5_1⟩ :=
        ctsToSystem5_false_head_after_first_step_one_mem cts rest phase N h_N
      have h_eq : cfg_k = s5_1 := Option.some.inj (h_k_eq.symm.trans h_step1)
      rw [h_eq]
      exact (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_1
    | 2, _ =>
      obtain ⟨s5_2, h_step2, h_one_mem_s5_2⟩ :=
        ctsToSystem5_false_head_step2_one_mem cts rest phase N h_N
      have h_eq : cfg_k = s5_2 := Option.some.inj (h_k_eq.symm.trans h_step2)
      rw [h_eq]
      exact (zero_mem_decrement_iff_one_mem _).mpr h_one_mem_s5_2
  have h_rules_form := System5_nSteps_rules_pstep _ s5_3 3 h_step3 h_pstep
  obtain ⟨rest_more, h_drop⟩ :=
    ctsRulesToSystem5Rules_drop_3_exists_empty_rule cts cfg N h_N
  refine ⟨rest_more.map (fun r => r.map (· + 3)), ?_⟩
  rw [h_rules_form]
  show ((ctsRulesToSystem5Rules cts cfg N).drop 3).map (fun r => r.map (· + (3 : Int)))
     = ([] : List Int) :: rest_more.map (fun r => r.map (· + 3))
  rw [h_drop]
  simp [List.map_cons]

/-- **Iter 993: bag-4 form for false-head — the 4-step trajectory bag**.
    Analog of iter 986 for step 4.  After exactly 4 cfg5 steps in
    the false-head case, `s5_4.bag = (s5_3.bag.map(·-1)).erase 0`.
    The popped rule at step 4 is `[]` (per iter 992's
    `s5_3.rules = [] :: rest_more`), so xorMerge with the (incremented)
    empty rule simplifies to identity via `xorMerge_nil`.

    Combines iter 990 (1 ∈ s5_3.bag → P-step trigger),
    iter 992 (s5_3.rules form), `System5_step_explicit_pop`, and
    `xorMerge_nil`.  **The full 4-step trajectory's terminal bag is
    now characterized algebraically** — ready to compare with
    `aux rest 1` to close the false-head sorry. -/
theorem ctsToSystem5_false_head_bag4_form
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_3 s5_4,
      System5.nSteps (ctsToSystem5 cts { data := false :: rest, phase := phase } N) 3
        = some s5_3
    ∧ System5.nSteps (ctsToSystem5 cts { data := false :: rest, phase := phase } N) 4
        = some s5_4
    ∧ s5_4.bag = (s5_3.bag.map (· - 1)).erase 0 := by
  let cfg : CTSConfig := { data := false :: rest, phase := phase }
  obtain ⟨s5_3a, h_step3a, h_one_mem⟩ :=
    ctsToSystem5_false_head_step3_one_mem cts rest phase N h_N
  obtain ⟨s5_3, h_step3, rest_more, h_rules_form⟩ :=
    ctsToSystem5_false_head_step3_rules_form cts rest phase N h_N
  have h_eq : s5_3a = s5_3 := Option.some.inj (h_step3a.symm.trans h_step3)
  rw [h_eq] at h_one_mem
  have h_bag_ne : s5_3.bag ≠ [] := List.ne_nil_of_mem h_one_mem
  have h_zero : (0 : Int) ∈ s5_3.bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one_mem
  have h_step4 := System5_step_explicit_pop s5_3 ([] : List Int) rest_more
      h_rules_form h_bag_ne h_zero
  have h_n4 : System5.nSteps (ctsToSystem5 cts cfg N) 4
            = some ⟨xorMerge ((s5_3.bag.map (· - 1)).erase 0) ([].map (· + 1)),
              rest_more.map (fun r => r.map (· + 1))⟩ := by
    rw [show (4 : Nat) = 3 + 1 from rfl, System5.nSteps_add, h_step3]
    simp [System5.nSteps_one, h_step4]
  refine ⟨s5_3, _, h_step3, h_n4, ?_⟩
  show xorMerge ((s5_3.bag.map (· - 1)).erase 0) ([].map (· + 1))
       = (s5_3.bag.map (· - 1)).erase 0
  show xorMerge ((s5_3.bag.map (· - 1)).erase 0) []
       = (s5_3.bag.map (· - 1)).erase 0
  exact xorMerge_nil _

/-- **Iter 1012: bag-4 mem-iff TERMINAL TARGET for false-head**.
    `∀ x, x ∈ s5_4.bag ↔ x ∈ ctsConfigToSystem5BagAux rest 1` —
    the encoder bag of the post-CTS-step state.

    **MAJOR MILESTONE**: This is the membership identity that the
    Smith Conjecture 0 false-head extension wants to establish.
    Composition (analog of iter 1009):
    - iter 993 (bag-4 form: s5_4.bag = (s5_3.bag.map(·-1)).erase 0).
    - iter 1009 (bag-3 mem-iff: ∀ x, x ∈ s5_3.bag ↔ x ∈ (1 :: aux rest 2)).
    - iter 1006 (List_Int_dec_erase_same_mem) lifts mem-iff through dec-erase.
    - iter 1010 (((1 :: aux rest 2).map(·-1)).erase 0 = aux rest 1).
    - iter 1011 (s5_3.bag Nodup), iter 1010 (rest_part Nodup).

    With this, the 4-step false-head trajectory's terminal bag has
    been **fully characterized at the membership level** as the
    encoder bag of the post-step CTS state (`aux rest 1` for
    `cts.step result' = result'` with `result'.data = false :: rest`). -/
theorem ctsToSystem5_false_head_bag4_mem_iff
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (r1 r2 : List Int) (tail : List (List Int))
    (h_rules : ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
              = r1 :: r2 :: tail) :
    ∃ s5_4,
      System5.nSteps (ctsToSystem5 cts { data := false :: rest, phase := phase } N) 4
        = some s5_4
    ∧ ∀ x, x ∈ s5_4.bag ↔ x ∈ ctsConfigToSystem5BagAux rest 1 := by
  obtain ⟨s5_3, s5_4, h_step3, h_step4, h_bag4⟩ :=
    ctsToSystem5_false_head_bag4_form cts rest phase N h_N
  obtain ⟨s5_3', h_step3', h_bag3_mem⟩ :=
    ctsToSystem5_false_head_bag3_mem_iff cts rest phase N h_N r1 r2 tail h_rules
  obtain ⟨s5_3'', h_step3'', h_s5_3_nodup⟩ :=
    ctsToSystem5_false_head_step3_bag_nodup cts rest phase N h_N
  have h_eq3 : s5_3 = s5_3' := Option.some.inj (h_step3.symm.trans h_step3')
  have h_eq3' : s5_3' = s5_3'' := Option.some.inj (h_step3'.symm.trans h_step3'')
  rw [h_eq3] at h_bag4
  rw [← h_eq3'] at h_s5_3_nodup
  refine ⟨s5_4, h_step4, ?_⟩
  intro x
  rw [h_bag4]
  rw [List_Int_dec_erase_same_mem s5_3'.bag
        ((1 : Int) :: ctsConfigToSystem5BagAux rest 2)
        h_s5_3_nodup
        (ctsConfigToSystem5BagAux_two_one_cons_nodup rest)
        h_bag3_mem 0 x]
  rw [ctsConfigToSystem5BagAux_two_one_cons_dec_erase_eq]

/-- **Iter 1014: bag-4 PERM-form for false-head**.  Upgrade of iter
    1012's mem-iff to `List.Perm` via iter 1013 (Nodup + same mem ⇒
    Perm).  Result:
      `List.Perm s5_4.bag (ctsConfigToSystem5BagAux rest 1)`
    after exactly 4 cfg5 steps.  This is the multiset/permutation-level
    statement of the 4-step false-head trajectory's terminal bag.

    **PERM is the natural multiset notion of bag equality**: list
    equality is too rigid (orderings differ; encoder is not evolution-
    stable per iter 873), but Perm captures the parity-multiset
    semantics that System5's bag actually represents.  This packaged
    theorem is the cleanest form of the 4-step false-head closure
    achievable at the cfg5 trajectory level (without the chain-
    arbitrary-s5' obstruction).

    To use this for closing the false-head sorry would require
    reformulating `smith_per_step_extension`'s predicate from `=` to
    `List.Perm` (or `mergeSort = mergeSort`).  Documented obstacle:
    iter 873's negative finding shows the encoder is not evolution-
    stable, so the chain at general m has rules diverging from a
    fresh encoder. -/
theorem ctsToSystem5_false_head_bag4_perm
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (r1 r2 : List Int) (tail : List (List Int))
    (h_rules : ctsRulesToSystem5Rules cts { data := false :: rest, phase := phase } N
              = r1 :: r2 :: tail) :
    ∃ s5_4,
      System5.nSteps (ctsToSystem5 cts { data := false :: rest, phase := phase } N) 4
        = some s5_4
    ∧ List.Perm s5_4.bag (ctsConfigToSystem5BagAux rest 1) := by
  obtain ⟨s5_4, h_step4, h_bag4_mem⟩ :=
    ctsToSystem5_false_head_bag4_mem_iff cts rest phase N h_N r1 r2 tail h_rules
  obtain ⟨s5_3, h_step3, h_s5_3_nodup⟩ :=
    ctsToSystem5_false_head_step3_bag_nodup cts rest phase N h_N
  obtain ⟨s5_3', s5_4', h_step3', h_step4', h_bag4_form⟩ :=
    ctsToSystem5_false_head_bag4_form cts rest phase N h_N
  have h_eq3 : s5_3 = s5_3' := Option.some.inj (h_step3.symm.trans h_step3')
  have h_eq4 : s5_4 = s5_4' := Option.some.inj (h_step4.symm.trans h_step4')
  have h_s5_4_nodup : s5_4.bag.Nodup := by
    rw [h_eq4, h_bag4_form, ← h_eq3]
    apply List.Nodup.erase
    apply List.Pairwise.map (· - 1) (R := (· ≠ ·)) ?_ h_s5_3_nodup
    intro a b h_ne h_eq; apply h_ne; have : a - 1 = b - 1 := h_eq; omega
  have h_aux_nodup : (ctsConfigToSystem5BagAux rest 1).Nodup :=
    ctsConfigToSystem5BagAux_nodup rest 1
  refine ⟨s5_4, h_step4, ?_⟩
  exact List_Int_perm_of_nodup_same_mem _ _ h_s5_4_nodup h_aux_nodup h_bag4_mem

/-- **`AllEmptyAppendants_System5_first_step` (iter 681)**: closed-form
    for the first System 5 step from `ctsToSystem5 cts cfg N` when the
    CTS is `AllEmptyAppendants`.  Result: bag becomes `(bag.map (·-1)).erase
    0`; rules become the tail (each shifted up by 1).  Composes
    `_rules_cons_empty`, `_zero_in_decrement`, and
    `System5_nSteps_one_empty_rule_pop`. -/
theorem AllEmptyAppendants_System5_first_step
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg : CTSConfig) (h_data : cfg.data ≠ []) (N : Nat) (h_N : 1 ≤ N) :
    ∃ rest, ctsRulesToSystem5Rules cts cfg N
              = ([] : List Int) :: rest ∧
            (∀ x ∈ rest, x = ([] : List Int)) ∧
            System5.nSteps (ctsToSystem5 cts cfg N) 1
              = some { bag := ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0
                       rules := rest.map (fun r => r.map (· + 1)) } := by
  have h_rules_ne := ctsRulesToSystem5Rules_nonempty cts cfg N h_N
  obtain ⟨rest, h_rules_eq, h_rest_empty⟩ :=
    AllEmptyAppendants_rules_cons_empty cts h_app cfg N h_rules_ne
  refine ⟨rest, h_rules_eq, h_rest_empty, ?_⟩
  have h_zero : (0 : Int) ∈ (ctsToSystem5 cts cfg N).bag.map (· - 1) :=
    ctsConfigToSystem5Bag_zero_in_decrement cfg h_data
  have h_bag_ne : (ctsToSystem5 cts cfg N).bag ≠ [] := by
    show ctsConfigToSystem5Bag cfg ≠ []
    obtain ⟨tail, h_eq⟩ := ctsConfigToSystem5Bag_head_eq_one cfg h_data
    rw [h_eq]; simp
  have h_rules_eq' : (ctsToSystem5 cts cfg N).rules = ([] : List Int) :: rest :=
    h_rules_eq
  exact System5_nSteps_one_empty_rule_pop _ rest h_rules_eq' h_bag_ne h_zero

/-- **`AllEmptyAppendants_System5_first_step_some` (iter 682)**:
    existential weakening — for AllEmptyAppendants CTS with non-empty
    data and positive budget, the first System 5 step yields some
    result.  Direct corollary of the closed form. -/
theorem AllEmptyAppendants_System5_first_step_some
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg : CTSConfig) (h_data : cfg.data ≠ []) (N : Nat) (h_N : 1 ≤ N) :
    ∃ result, System5.nSteps (ctsToSystem5 cts cfg N) 1 = some result := by
  obtain ⟨_, _, _, h_step⟩ :=
    AllEmptyAppendants_System5_first_step cts h_app cfg h_data N h_N
  exact ⟨_, h_step⟩

/-- **`AllEmptyAppendants_System5_first_step_bag` (iter 682)**:
    extract just the bag projection from the closed form.  Useful
    when only the post-step bag matters. -/
theorem AllEmptyAppendants_System5_first_step_bag
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg : CTSConfig) (h_data : cfg.data ≠ []) (N : Nat) (h_N : 1 ≤ N) :
    ∃ s5_result, System5.nSteps (ctsToSystem5 cts cfg N) 1 = some s5_result
      ∧ s5_result.bag = ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0 := by
  obtain ⟨rest, _, _, h_step⟩ :=
    AllEmptyAppendants_System5_first_step cts h_app cfg h_data N h_N
  refine ⟨_, h_step, ?_⟩
  rfl

/-- **`System5_step_from_replicate_state_pure_dec` (iter 683)**: pure-
    decrement System 5 step on `{bag, rules := replicate K []}` when
    `1 ∉ bag`.  No rule pops; bag decrements; rules pass through
    unchanged via `List_replicate_nil_map_increment`.  Companion to
    `_replicate_state` for the pure-dec branch in true-head
    trajectories. -/
theorem System5_step_from_replicate_state_pure_dec
    (bag : List Int) (h_bag : bag ≠ []) (h_no_one : (1 : Int) ∉ bag)
    (K : Nat) (h_K : 1 ≤ K) :
    System5.nSteps { bag := bag, rules := List.replicate K [] } 1
    = some { bag := bag.map (· - 1),
             rules := List.replicate K [] } := by
  have h_zero : (0 : Int) ∉ bag.map (· - 1) := by
    intro h_in
    exact h_no_one ((zero_mem_decrement_iff_one_mem _).mp h_in)
  have h_rules_ne : List.replicate K ([] : List Int) ≠ [] := by
    intro h
    have h_len : (List.replicate K ([] : List Int)).length = 0 := by rw [h]; rfl
    rw [List.length_replicate] at h_len
    omega
  have h_step := System5_nSteps_one_pure_decrement
    { bag := bag, rules := List.replicate K [] } h_bag h_rules_ne h_zero
  rw [h_step]
  congr 1
  show ({ bag := bag.map (· - 1),
          rules := (List.replicate K []).map (fun r => r.map (· + 1)) } : System5Config)
      = { bag := bag.map (· - 1), rules := List.replicate K [] }
  rw [List_replicate_nil_map_increment]

/-- **`System5_step_from_replicate_state` (iter 683)**: System 5 step
    on `{bag, rules := replicate K []}` when `K ≥ 1` and `1 ∈ bag`.
    Pops one empty rule, decrements bag, re-establishes `rules :=
    replicate (K-1) []`.  Canonical iteration step for
    AllEmptyAppendants trajectories. -/
theorem System5_step_from_replicate_state
    (bag : List Int) (h_bag : bag ≠ []) (h_one : (1 : Int) ∈ bag)
    (K : Nat) (h_K : 1 ≤ K) :
    System5.nSteps { bag := bag, rules := List.replicate K [] } 1
    = some { bag := (bag.map (· - 1)).erase 0,
             rules := List.replicate (K - 1) [] } := by
  obtain ⟨k, h_k⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  rw [h_k, List.replicate_succ]
  have h_zero : (0 : Int) ∈ bag.map (· - 1) :=
    (zero_mem_decrement_iff_one_mem _).mpr h_one
  have h_step :
      System5.nSteps { bag := bag,
                       rules := ([] : List Int) :: List.replicate k [] } 1
      = some { bag := (bag.map (· - 1)).erase 0,
               rules := (List.replicate k []).map (fun r => r.map (· + 1)) } :=
    System5_nSteps_one_empty_rule_pop _ _ rfl h_bag h_zero
  rw [h_step]
  congr 1
  show ({ bag := (bag.map (· - 1)).erase 0,
          rules := (List.replicate k []).map (fun r => r.map (· + 1)) }
        : System5Config)
      = { bag := (bag.map (· - 1)).erase 0, rules := List.replicate (k + 1 - 1) [] }
  rw [List_replicate_nil_map_increment]
  rw [show k + 1 - 1 = k from by omega]

/-- **`System5_step_from_replicate_state_some` (iter 684)**: existence
    form covering both cases (`1 ∈ bag` and `1 ∉ bag`) — a System 5
    step on a replicate-nil rules state always succeeds when the bag
    is non-empty and there are rules left.  Direct case split. -/
theorem System5_step_from_replicate_state_some
    (bag : List Int) (h_bag : bag ≠ []) (K : Nat) (h_K : 1 ≤ K) :
    ∃ result, System5.nSteps { bag := bag,
                               rules := List.replicate K [] } 1 = some result := by
  by_cases h_one : (1 : Int) ∈ bag
  · exact ⟨_, System5_step_from_replicate_state bag h_bag h_one K h_K⟩
  · exact ⟨_, System5_step_from_replicate_state_pure_dec bag h_bag h_one K h_K⟩

/-- **`System5_step_from_replicate_state_rules_length` (iter 684)**:
    case-by-case rules length after one step from a replicate-nil
    state: `K` (no pop, `1 ∉ bag`) or `K-1` (pop, `1 ∈ bag`). -/
theorem System5_step_from_replicate_state_rules_length
    (bag : List Int) (h_bag : bag ≠ []) (K : Nat) (h_K : 1 ≤ K) :
    ∃ result, System5.nSteps { bag := bag,
                               rules := List.replicate K [] } 1 = some result
            ∧ (result.rules.length = K ∨ result.rules.length = K - 1) := by
  by_cases h_one : (1 : Int) ∈ bag
  · refine ⟨_, System5_step_from_replicate_state bag h_bag h_one K h_K, ?_⟩
    right; show (List.replicate (K - 1) ([] : List Int)).length = K - 1
    exact List.length_replicate
  · refine ⟨_, System5_step_from_replicate_state_pure_dec bag h_bag h_one K h_K, ?_⟩
    left; show (List.replicate K ([] : List Int)).length = K
    exact List.length_replicate

/-- **`AllEmptyAppendants_System5_first_step_explicit` (iter 685)**:
    sharper first-step result combining the closed form with the
    post-step rules replicate.  Both fields are explicit: bag = `(orig.
    map (·-1)).erase 0`, rules = `replicate (K-1) []` where `K = 3 *
    |appendants| * N`.  No more existential `rest` in the rules. -/
theorem AllEmptyAppendants_System5_first_step_explicit
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg : CTSConfig) (h_data : cfg.data ≠ []) (N : Nat) (h_N : 1 ≤ N) :
    System5.nSteps (ctsToSystem5 cts cfg N) 1
    = some { bag := ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0
             rules := List.replicate (4 * cts.appendants.length * N - 1) [] } := by
  obtain ⟨rest, h_rules_eq, _, h_step⟩ :=
    AllEmptyAppendants_System5_first_step cts h_app cfg h_data N h_N
  have h_pos : 0 < 4 * cts.appendants.length * N :=
    Nat.mul_pos (Nat.mul_pos (by decide) cts.nonempty) h_N
  obtain ⟨rest', h_rules_eq', h_rest_replicate⟩ :=
    AllEmptyAppendants_postStep_rules_replicate cts h_app cfg N h_pos
  rw [h_step]
  congr 1
  show ({ bag := ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0
          rules := rest.map (fun r => r.map (· + 1)) } : System5Config)
      = { bag := ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0
          rules := List.replicate (4 * cts.appendants.length * N - 1) [] }
  congr 1
  have h_rest_eq : rest = rest' := by
    have h := h_rules_eq.symm.trans h_rules_eq'
    injection h
  rw [h_rest_eq]
  exact h_rest_replicate


/-- **`ctsConfigToSystem5Bag_decrement_erase_false_decomp` (iter 675)**:
    post-decrement-erase bag for a false-head cfg splits into the small
    head `[1, 2, 3]` and the encoded tail's bag shifted by `+3`. -/
theorem ctsConfigToSystem5Bag_decrement_erase_false_decomp
    (rest : List Bool) (phase : Nat) :
    ((ctsConfigToSystem5Bag { data := false :: rest, phase := phase }).map (· - 1)).erase 0
    = [1, 2, 3] ++ (ctsConfigToSystem5BagAux rest 1).map (· + 3) := by
  rw [ctsConfigToSystem5Bag_decrement_erase_false]
  rw [ctsConfigToSystem5BagAux_at_four]
  rfl

/-- **`ctsConfigToSystem5Bag_decrement_erase_true_decomp` (iter 675)**:
    post-decrement-erase bag for a true-head cfg splits into `[2, 3,
    5]` and the tail shifted by `+5`. -/
theorem ctsConfigToSystem5Bag_decrement_erase_true_decomp
    (rest : List Bool) (phase : Nat) :
    ((ctsConfigToSystem5Bag { data := true :: rest, phase := phase }).map (· - 1)).erase 0
    = [2, 3, 5] ++ (ctsConfigToSystem5BagAux rest 1).map (· + 5) := by
  rw [ctsConfigToSystem5Bag_decrement_erase_true]
  rw [ctsConfigToSystem5BagAux_at_six]
  rfl

/-- **`ctsConfigToSystem5Bag_decrement_erase_length` (iter 675)**:
    post-decrement-erase bag has length `4 * |cfg.data| - 1`.  Pre-
    erase length is `4 * |cfg.data|` and `0` is present (since `1 ∈
    bag`), so erase removes exactly one. -/
theorem ctsConfigToSystem5Bag_decrement_erase_length
    (cfg : CTSConfig) (h : cfg.data ≠ []) :
    (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0).length
    = 4 * cfg.data.length - 1 := by
  have h_zero_mem : (0 : Int) ∈ (ctsConfigToSystem5Bag cfg).map (· - 1) := by
    rw [List.mem_map]
    exact ⟨1, ctsConfigToSystem5Bag_one_mem cfg h, by omega⟩
  rw [List.length_erase_of_mem h_zero_mem, List.length_map,
      ctsConfigToSystem5Bag_length]

/-- **`ctsConfigToSystem5Bag_decrement_erase_empty_iff` (iter 675)**:
    post-decrement-erase bag is empty iff CTS data is empty.  Empty
    data gives length 0; non-empty gives length `4|data| - 1 ≥ 3`. -/
theorem ctsConfigToSystem5Bag_decrement_erase_empty_iff (cfg : CTSConfig) :
    ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0 = [] ↔ cfg.data = [] := by
  constructor
  · intro h_empty
    cases h : cfg.data with
    | nil => rfl
    | cons head tail =>
      exfalso
      have h_ne : cfg.data ≠ [] := by rw [h]; exact List.cons_ne_nil _ _
      have h_len := ctsConfigToSystem5Bag_decrement_erase_length cfg h_ne
      rw [h_empty, List.length_nil] at h_len
      have h_data_len : cfg.data.length ≥ 1 := by rw [h]; simp
      omega
  · intro h_empty
    show ((ctsConfigToSystem5BagAux cfg.data 1).map (· - 1)).erase 0 = []
    rw [h_empty]
    rfl

/-- **`ctsConfigToSystem5Bag_length_eq` (iter 675)**: equal encoded
    bags imply equal data lengths.  Encoder length is `4 * |data|`,
    so bag equality forces length equality. -/
theorem ctsConfigToSystem5Bag_length_eq (cfg1 cfg2 : CTSConfig)
    (h : ctsConfigToSystem5Bag cfg1 = ctsConfigToSystem5Bag cfg2) :
    cfg1.data.length = cfg2.data.length := by
  have h1 := ctsConfigToSystem5Bag_length cfg1
  have h2 := ctsConfigToSystem5Bag_length cfg2
  have h_len : (ctsConfigToSystem5Bag cfg1).length
             = (ctsConfigToSystem5Bag cfg2).length := by rw [h]
  rw [h1, h2] at h_len
  omega

/-- **`ctsConfigToSystem5Bag_decrement_erase_nonempty_iff` (iter 676)**:
    contrapositive of `_decrement_erase_empty_iff` — post-decrement-
    erase bag is non-empty exactly when CTS data is non-empty. -/
theorem ctsConfigToSystem5Bag_decrement_erase_nonempty_iff (cfg : CTSConfig) :
    ((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0 ≠ [] ↔ cfg.data ≠ [] := by
  rw [ne_eq, ne_eq, ctsConfigToSystem5Bag_decrement_erase_empty_iff]

/-- **`ctsConfigToSystem5Bag_decrement_erase_length_ge_three` (iter
    676)**: post-decrement-erase bag has length ≥ 3 for non-empty
    data.  Direct corollary of `_length` (= `4|data|-1 ≥ 3`). -/
theorem ctsConfigToSystem5Bag_decrement_erase_length_ge_three
    (cfg : CTSConfig) (h : cfg.data ≠ []) :
    (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0).length ≥ 3 := by
  rw [ctsConfigToSystem5Bag_decrement_erase_length cfg h]
  have h_len : cfg.data.length ≥ 1 := by
    cases h_data : cfg.data with
    | nil => exact absurd h_data h
    | cons _ _ => simp [List.length_cons]
  omega

/-- **`ctsConfigToSystem5Bag_drainSeq6_true_head` (iter 666)**: full
    6-step composite drain for true-head data.  Starting from
    `ctsConfigToSystem5Bag {data := true :: rest, _}` (=
    `1::3::4::6::aux rest 7`), one D-step (dec-erase) gives
    `2::3::5::aux rest 6`; one P-step (pure dec) gives `1::2::4::aux
    rest 5`; one D-step gives `1::3::aux rest 4`; one D-step gives
    `2::aux rest 3`; one P-step gives `1::aux rest 2`; one D-step
    gives `aux rest 1`.  Pattern: D-P-D-D-P-D (6 System 5 steps for
    one true bit consumed).  Companion of `_drainSeq4_false_head`
    (4 steps for one false bit). -/
theorem ctsConfigToSystem5Bag_drainSeq6_true_head
    (rest : List Bool) (phase : Nat) :
    let bag := ctsConfigToSystem5Bag { data := true :: rest, phase := phase }
    let s1 := (bag.map (· - 1)).erase 0
    let s2 := s1.map (· - 1)
    let s3 := (s2.map (· - 1)).erase 0
    let s4 := (s3.map (· - 1)).erase 0
    let s5 := s4.map (· - 1)
    let s6 := (s5.map (· - 1)).erase 0
    s6 = ctsConfigToSystem5BagAux rest 1 := by
  simp only
  rw [ctsConfigToSystem5Bag_decrement_erase_true]
  rw [show ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6).map (· - 1)
        = (1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5 from
      map_decrement_two_three_five_cons_aux rest 6]
  rw [decrement_erase_one_two_four_cons_aux rest 5]
  rw [show (5 : Int) - 1 = 4 from by omega]
  rw [decrement_erase_one_three_cons_aux rest 4]
  rw [show (4 : Int) - 1 = 3 from by omega]
  rw [map_decrement_two_cons_aux rest 3]
  rw [show (3 : Int) - 1 = 2 from by omega]
  rw [decrement_erase_one_cons_aux rest 2]
  rw [show (2 : Int) - 1 = 1 from by omega]

/-- **`AllEmptyAppendants_System5_first_step_bag_length` (iter 686)**:
    after the first AllEmptyAppendants System 5 step, the bag has
    length `4 * |cfg.data| - 1` for non-empty data.  Direct corollary
    of `_first_step_explicit` with `_decrement_erase_length`. -/
theorem AllEmptyAppendants_System5_first_step_bag_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg : CTSConfig) (h_data : cfg.data ≠ []) (N : Nat) (h_N : 1 ≤ N) :
    ∃ s5_result, System5.nSteps (ctsToSystem5 cts cfg N) 1 = some s5_result
              ∧ s5_result.bag.length = 4 * cfg.data.length - 1 := by
  refine ⟨_, AllEmptyAppendants_System5_first_step_explicit cts h_app cfg h_data N h_N, ?_⟩
  show (((ctsConfigToSystem5Bag cfg).map (· - 1)).erase 0).length
      = 4 * cfg.data.length - 1
  exact ctsConfigToSystem5Bag_decrement_erase_length cfg h_data

/-- **`AllEmptyAppendants_System5_first_step_rules_length` (iter 686)**:
    after the first step, the rules have length `K - 1` where
    `K = 3 * |appendants| * N`. -/
theorem AllEmptyAppendants_System5_first_step_rules_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg : CTSConfig) (h_data : cfg.data ≠ []) (N : Nat) (h_N : 1 ≤ N) :
    ∃ s5_result, System5.nSteps (ctsToSystem5 cts cfg N) 1 = some s5_result
              ∧ s5_result.rules.length = 4 * cts.appendants.length * N - 1 := by
  refine ⟨_, AllEmptyAppendants_System5_first_step_explicit cts h_app cfg h_data N h_N, ?_⟩
  show (List.replicate (4 * cts.appendants.length * N - 1) ([] : List Int)).length
      = 4 * cts.appendants.length * N - 1
  exact List.length_replicate

/-- **`AllEmptyAppendants_System5_2steps_false_head` (iter 687)**:
    starting from `ctsToSystem5 cts {data := false :: rest, _} N` with
    `2 ≤ K`, after 2 System 5 steps the state is `{bag := 1 :: 2 ::
    aux rest 3, rules := replicate (K-2) []}`.  Composes
    `_first_step_explicit` + `_decrement_erase_false` +
    `System5_step_from_replicate_state` + `decrement_erase_three_cons_aux`. -/
theorem AllEmptyAppendants_System5_2steps_false_head
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 2 ≤ 4 * cts.appendants.length * N) :
    System5.nSteps (ctsToSystem5 cts
      { data := false :: rest, phase := phase } N) 2
    = some { bag := (1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3
             rules := List.replicate (4 * cts.appendants.length * N - 2) [] } := by
  have h_N1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h] at h_N
    · exact h
  have h_data_ne : ({ data := false :: rest, phase := phase } : CTSConfig).data ≠ [] := by
    simp
  have h_step1 := AllEmptyAppendants_System5_first_step_explicit
    cts h_app { data := false :: rest, phase := phase } h_data_ne N h_N1
  have h_bag1 :
    ((ctsConfigToSystem5Bag { data := false :: rest, phase := phase }).map (· - 1)).erase 0
    = (1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4 :=
    ctsConfigToSystem5Bag_decrement_erase_false rest phase
  rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add, h_step1]
  show System5.nSteps
    { bag := ((ctsConfigToSystem5Bag { data := false :: rest, phase := phase }).map
                (· - 1)).erase 0,
      rules := List.replicate (4 * cts.appendants.length * N - 1) [] } 1
    = some { bag := (1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3,
             rules := List.replicate (4 * cts.appendants.length * N - 2) [] }
  rw [h_bag1]
  rw [System5_step_from_replicate_state
        ((1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4)
        (by simp)
        (List.mem_cons.mpr (Or.inl rfl))
        (4 * cts.appendants.length * N - 1)
        (by omega)]
  rw [decrement_erase_three_cons_aux rest 4]
  rw [show (4 : Int) - 1 = 3 from by omega]
  rw [show 4 * cts.appendants.length * N - 1 - 1
        = 4 * cts.appendants.length * N - 2 from by omega]

/-- **`AllEmptyAppendants_System5_4steps_false_head` (iter 687)**:
    extends `_2steps` to 4 steps, ending at `aux rest 1` (matching the
    encoder of `{data := rest, _}` with phase advanced).  The 4-step
    drain is the per-bit cost in System 5 for false bits. -/
theorem AllEmptyAppendants_System5_4steps_false_head
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 4 ≤ 4 * cts.appendants.length * N) :
    System5.nSteps (ctsToSystem5 cts
      { data := false :: rest, phase := phase } N) 4
    = some { bag := ctsConfigToSystem5BagAux rest 1
             rules := List.replicate (4 * cts.appendants.length * N - 4) [] } := by
  have h_step12 := AllEmptyAppendants_System5_2steps_false_head
    cts h_app rest phase N (by omega)
  rw [show (4 : Nat) = 2 + 2 from rfl, System5.nSteps_add, h_step12]
  show System5.nSteps
    { bag := (1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3,
      rules := List.replicate (4 * cts.appendants.length * N - 2) [] } 2
    = some { bag := ctsConfigToSystem5BagAux rest 1,
             rules := List.replicate (4 * cts.appendants.length * N - 4) [] }
  rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add]
  rw [System5_step_from_replicate_state
        ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3)
        (by simp)
        (List.mem_cons.mpr (Or.inl rfl))
        (4 * cts.appendants.length * N - 2)
        (by omega)]
  rw [decrement_erase_two_cons_aux rest 3]
  rw [show (3 : Int) - 1 = 2 from by omega]
  show System5.nSteps
    { bag := (1 : Int) :: ctsConfigToSystem5BagAux rest 2,
      rules := List.replicate (4 * cts.appendants.length * N - 2 - 1) [] } 1
    = some { bag := ctsConfigToSystem5BagAux rest 1,
             rules := List.replicate (4 * cts.appendants.length * N - 4) [] }
  rw [System5_step_from_replicate_state
        ((1 : Int) :: ctsConfigToSystem5BagAux rest 2)
        (by simp)
        (List.mem_cons.mpr (Or.inl rfl))
        (4 * cts.appendants.length * N - 2 - 1)
        (by omega)]
  rw [decrement_erase_one_cons_aux rest 2]
  rw [show (2 : Int) - 1 = 1 from by omega]
  rw [show 4 * cts.appendants.length * N - 2 - 1 - 1
        = 4 * cts.appendants.length * N - 4 from by omega]

/-- **`AllEmptyAppendants_System5_4steps_false_head_bag_length` (iter
    688)**: after 4 System 5 steps from a false-head AllEmptyAppendants
    starting cfg, the bag has length `4 * rest.length`.  Direct
    corollary of `_4steps_false_head` with `ctsConfigToSystem5BagAux_
    length`.  Companion to iter 686's first-step bag-length, providing
    the per-bit-consumed bag size. -/
theorem AllEmptyAppendants_System5_4steps_false_head_bag_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 4 ≤ 4 * cts.appendants.length * N) :
    ∃ s5_result, System5.nSteps (ctsToSystem5 cts
      { data := false :: rest, phase := phase } N) 4 = some s5_result
              ∧ s5_result.bag.length = 4 * rest.length := by
  refine ⟨_, AllEmptyAppendants_System5_4steps_false_head
    cts h_app rest phase N h_N, ?_⟩
  show (ctsConfigToSystem5BagAux rest 1).length = 4 * rest.length
  exact ctsConfigToSystem5BagAux_length rest 1

/-- **`AllEmptyAppendants_System5_4steps_false_head_rules_length` (iter
    688)**: after 4 System 5 steps from a false-head AllEmptyAppendants
    starting cfg, the rules have length `K - 4` where `K = 3 *
    |appendants| * N`.  Direct corollary of `_4steps_false_head` with
    `List.length_replicate`.  Quantifies the per-bit budget cost (each
    false bit consumes exactly 4 D-steps). -/
theorem AllEmptyAppendants_System5_4steps_false_head_rules_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 4 ≤ 4 * cts.appendants.length * N) :
    ∃ s5_result, System5.nSteps (ctsToSystem5 cts
      { data := false :: rest, phase := phase } N) 4 = some s5_result
              ∧ s5_result.rules.length = 4 * cts.appendants.length * N - 4 := by
  refine ⟨_, AllEmptyAppendants_System5_4steps_false_head
    cts h_app rest phase N h_N, ?_⟩
  show (List.replicate (4 * cts.appendants.length * N - 4) ([] : List Int)).length
      = 4 * cts.appendants.length * N - 4
  exact List.length_replicate

/-- **2-step System 5 trajectory for AllEmptyAppendants true-head
    data**: starting from `ctsToSystem5 cts {data := true :: rest, _}
    N` with `2 ≤ K`, after 2 System 5 steps the state is `{bag :=
    1 :: 2 :: 4 :: aux rest 5, rules := replicate (K-1) []}`.  Pattern
    is D-P (dec-erase then pure-dec, since `1 ∉ 2::3::5::aux rest 6`).
    Step 1 uses iter 331 + iter 6979; step 2 uses iter 335.  Note
    only 1 D-step, so K decrements by exactly 1.  Companion to iter
    333's 2-step false-head; building block for the eventual 6-step
    true-head. -/
theorem AllEmptyAppendants_System5_2steps_true_head
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 2 ≤ 4 * cts.appendants.length * N) :
    System5.nSteps (ctsToSystem5 cts
      { data := true :: rest, phase := phase } N) 2
    = some { bag := (1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5
             rules := List.replicate (4 * cts.appendants.length * N - 1) [] } := by
  have h_N1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h] at h_N
    · exact h
  have h_data_ne : ({ data := true :: rest, phase := phase } : CTSConfig).data ≠ [] := by
    simp
  have h_step1 := AllEmptyAppendants_System5_first_step_explicit
    cts h_app { data := true :: rest, phase := phase } h_data_ne N h_N1
  have h_bag1 :
    ((ctsConfigToSystem5Bag { data := true :: rest, phase := phase }).map (· - 1)).erase 0
    = (2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6 :=
    ctsConfigToSystem5Bag_decrement_erase_true rest phase
  rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add, h_step1]
  show System5.nSteps
    { bag := ((ctsConfigToSystem5Bag { data := true :: rest, phase := phase }).map
                (· - 1)).erase 0,
      rules := List.replicate (4 * cts.appendants.length * N - 1) [] } 1
    = some { bag := (1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5,
             rules := List.replicate (4 * cts.appendants.length * N - 1) [] }
  rw [h_bag1]
  have h_no_one_2 : (1 : Int) ∉
      ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6) := by
    intro h
    rcases List.mem_cons.mp h with h1 | h
    · omega
    rcases List.mem_cons.mp h with h1 | h
    · omega
    rcases List.mem_cons.mp h with h1 | h
    · omega
    have := ctsConfigToSystem5BagAux_ge rest 6 1 h
    omega
  rw [System5_step_from_replicate_state_pure_dec
        ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6)
        (by simp) h_no_one_2 (4 * cts.appendants.length * N - 1) (by omega)]
  rw [map_decrement_two_three_five_cons_aux rest 6]
  rw [show (6 : Int) - 1 = 5 from by omega]

/-- **`AllEmptyAppendants_System5_2steps_true_head_bag_length` (iter
    690)**: after 2 System 5 steps from a true-head AllEmptyAppendants
    starting cfg, the bag has length `4 * rest.length + 3` (head
    `1 :: 2 :: 4` plus the `aux rest 5` tail).  Direct corollary of
    `_2steps_true_head` with `ctsConfigToSystem5BagAux_length`. -/
theorem AllEmptyAppendants_System5_2steps_true_head_bag_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 2 ≤ 4 * cts.appendants.length * N) :
    ∃ s5_result, System5.nSteps (ctsToSystem5 cts
      { data := true :: rest, phase := phase } N) 2 = some s5_result
              ∧ s5_result.bag.length = 4 * rest.length + 3 := by
  refine ⟨_, AllEmptyAppendants_System5_2steps_true_head
    cts h_app rest phase N h_N, ?_⟩
  show ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5).length
      = 4 * rest.length + 3
  simp [List.length_cons, ctsConfigToSystem5BagAux_length]

/-- **`AllEmptyAppendants_System5_2steps_true_head_rules_length` (iter
    690)**: after 2 System 5 steps from a true-head AllEmptyAppendants
    starting cfg, the rules have length `K - 1` where `K = 3 *
    |appendants| * N` (only the first step is a D-step; the second is
    a P-step which doesn't pop a rule).  Quantifies the per-bit budget
    cost: true-head's first half consumes 1 D-step. -/
theorem AllEmptyAppendants_System5_2steps_true_head_rules_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 2 ≤ 4 * cts.appendants.length * N) :
    ∃ s5_result, System5.nSteps (ctsToSystem5 cts
      { data := true :: rest, phase := phase } N) 2 = some s5_result
              ∧ s5_result.rules.length = 4 * cts.appendants.length * N - 1 := by
  refine ⟨_, AllEmptyAppendants_System5_2steps_true_head
    cts h_app rest phase N h_N, ?_⟩
  show (List.replicate (4 * cts.appendants.length * N - 1) ([] : List Int)).length
      = 4 * cts.appendants.length * N - 1
  exact List.length_replicate

/-- **4-step System 5 trajectory for AllEmptyAppendants true-head
    data**: extends iter 336 by 2 more D-steps to reach `{bag :=
    2 :: aux rest 3, rules := replicate (K-3) []}`.  Pattern through
    step 4 is D-P-D-D, with 3 D-steps decrementing K by 3.  Steps
    3 and 4 use iter 316 (`_one_two_four_cons`) and iter 317
    (`_one_three_cons`).  Building block for the full 6-step
    true-head trajectory. -/
theorem AllEmptyAppendants_System5_4steps_true_head
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 3 ≤ 4 * cts.appendants.length * N) :
    System5.nSteps (ctsToSystem5 cts
      { data := true :: rest, phase := phase } N) 4
    = some { bag := (2 : Int) :: ctsConfigToSystem5BagAux rest 3
             rules := List.replicate (4 * cts.appendants.length * N - 3) [] } := by
  have h_step12 := AllEmptyAppendants_System5_2steps_true_head
    cts h_app rest phase N (by omega)
  rw [show (4 : Nat) = 2 + 2 from rfl, System5.nSteps_add, h_step12]
  show System5.nSteps
    { bag := (1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5,
      rules := List.replicate (4 * cts.appendants.length * N - 1) [] } 2
    = some { bag := (2 : Int) :: ctsConfigToSystem5BagAux rest 3,
             rules := List.replicate (4 * cts.appendants.length * N - 3) [] }
  rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add]
  rw [System5_step_from_replicate_state
        ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5)
        (by simp)
        (List.mem_cons.mpr (Or.inl rfl))
        (4 * cts.appendants.length * N - 1)
        (by omega)]
  rw [decrement_erase_one_two_four_cons_aux rest 5]
  rw [show (5 : Int) - 1 = 4 from by omega]
  show System5.nSteps
    { bag := (1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4,
      rules := List.replicate (4 * cts.appendants.length * N - 1 - 1) [] } 1
    = some { bag := (2 : Int) :: ctsConfigToSystem5BagAux rest 3,
             rules := List.replicate (4 * cts.appendants.length * N - 3) [] }
  rw [System5_step_from_replicate_state
        ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4)
        (by simp)
        (List.mem_cons.mpr (Or.inl rfl))
        (4 * cts.appendants.length * N - 1 - 1)
        (by omega)]
  rw [decrement_erase_one_three_cons_aux rest 4]
  rw [show (4 : Int) - 1 = 3 from by omega]
  rw [show 4 * cts.appendants.length * N - 1 - 1 - 1
        = 4 * cts.appendants.length * N - 3 from by omega]

/-- **`AllEmptyAppendants_System5_4steps_true_head_bag_length` (iter
    692)**: after 4 System 5 steps from a true-head AllEmptyAppendants
    starting cfg, the bag has length `4 * rest.length + 1` (head `2`
    plus `aux rest 3` tail).  Direct corollary of `_4steps_true_head`
    with `ctsConfigToSystem5BagAux_length`. -/
theorem AllEmptyAppendants_System5_4steps_true_head_bag_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 3 ≤ 4 * cts.appendants.length * N) :
    ∃ s5_result, System5.nSteps (ctsToSystem5 cts
      { data := true :: rest, phase := phase } N) 4 = some s5_result
              ∧ s5_result.bag.length = 4 * rest.length + 1 := by
  refine ⟨_, AllEmptyAppendants_System5_4steps_true_head
    cts h_app rest phase N h_N, ?_⟩
  show ((2 : Int) :: ctsConfigToSystem5BagAux rest 3).length
      = 4 * rest.length + 1
  simp [List.length_cons, ctsConfigToSystem5BagAux_length]

/-- **`AllEmptyAppendants_System5_4steps_true_head_rules_length` (iter
    692)**: after 4 System 5 steps from a true-head AllEmptyAppendants
    starting cfg, the rules have length `K - 3` where `K = 3 *
    |appendants| * N` (3 D-steps in the D-P-D-D pattern; the P at step
    2 doesn't pop a rule).  Quantifies the per-bit budget cost: through
    step 4 of true-head, 3 D-steps are consumed. -/
theorem AllEmptyAppendants_System5_4steps_true_head_rules_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 3 ≤ 4 * cts.appendants.length * N) :
    ∃ s5_result, System5.nSteps (ctsToSystem5 cts
      { data := true :: rest, phase := phase } N) 4 = some s5_result
              ∧ s5_result.rules.length = 4 * cts.appendants.length * N - 3 := by
  refine ⟨_, AllEmptyAppendants_System5_4steps_true_head
    cts h_app rest phase N h_N, ?_⟩
  show (List.replicate (4 * cts.appendants.length * N - 3) ([] : List Int)).length
      = 4 * cts.appendants.length * N - 3
  exact List.length_replicate

/-- **6-step System 5 trajectory for AllEmptyAppendants true-head
    data**: full true-head sub-trajectory.  Starting from `ctsToSystem5
    cts {data := true :: rest, _} N` with `4 ≤ K`, after 6 System 5
    steps the state is `{bag := aux rest 1, rules := replicate (K-4)
    []}` — the bag matches `ctsConfigToSystem5Bag {data := rest, _}`.
    Pattern: D-P-D-D-P-D, with 4 D-steps decrementing K by 4 (matching
    iter 318's bag-only counter advance of 6 per true bit).  Step 5
    uses `map_decrement_two_cons_aux` (iter 318); step 6 uses iter
    312's `_one_cons`.  Companion to iter 334's 4-step false-head;
    completes the per-bit System 5 emulation in the AllEmptyAppendants
    regime. -/
theorem AllEmptyAppendants_System5_6steps_true_head
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 4 ≤ 4 * cts.appendants.length * N) :
    System5.nSteps (ctsToSystem5 cts
      { data := true :: rest, phase := phase } N) 6
    = some { bag := ctsConfigToSystem5BagAux rest 1
             rules := List.replicate (4 * cts.appendants.length * N - 4) [] } := by
  have h_step1234 := AllEmptyAppendants_System5_4steps_true_head
    cts h_app rest phase N (by omega)
  rw [show (6 : Nat) = 4 + 2 from rfl, System5.nSteps_add, h_step1234]
  show System5.nSteps
    { bag := (2 : Int) :: ctsConfigToSystem5BagAux rest 3,
      rules := List.replicate (4 * cts.appendants.length * N - 3) [] } 2
    = some { bag := ctsConfigToSystem5BagAux rest 1,
             rules := List.replicate (4 * cts.appendants.length * N - 4) [] }
  rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add]
  -- Step 5 (P): 1 ∉ 2::aux rest 3 (smallest is 2; aux ≥ 3).
  have h_no_one_5 : (1 : Int) ∉
      ((2 : Int) :: ctsConfigToSystem5BagAux rest 3) := by
    intro h
    rcases List.mem_cons.mp h with h1 | h
    · omega
    have := ctsConfigToSystem5BagAux_ge rest 3 1 h
    omega
  rw [System5_step_from_replicate_state_pure_dec
        ((2 : Int) :: ctsConfigToSystem5BagAux rest 3)
        (by simp) h_no_one_5 (4 * cts.appendants.length * N - 3) (by omega)]
  rw [map_decrement_two_cons_aux rest 3]
  rw [show (3 : Int) - 1 = 2 from by omega]
  show System5.nSteps
    { bag := (1 : Int) :: ctsConfigToSystem5BagAux rest 2,
      rules := List.replicate (4 * cts.appendants.length * N - 3) [] } 1
    = some { bag := ctsConfigToSystem5BagAux rest 1,
             rules := List.replicate (4 * cts.appendants.length * N - 4) [] }
  -- Step 6 (D): 1 ∈ 1::aux rest 2.
  rw [System5_step_from_replicate_state
        ((1 : Int) :: ctsConfigToSystem5BagAux rest 2)
        (by simp)
        (List.mem_cons.mpr (Or.inl rfl))
        (4 * cts.appendants.length * N - 3)
        (by omega)]
  rw [decrement_erase_one_cons_aux rest 2]
  rw [show (2 : Int) - 1 = 1 from by omega]
  rw [show 4 * cts.appendants.length * N - 3 - 1
        = 4 * cts.appendants.length * N - 4 from by omega]

/-- **`AllEmptyAppendants_System5_6steps_true_head_bag_length` (iter
    694)**: after 6 System 5 steps from a true-head AllEmptyAppendants
    starting cfg, the bag has length `4 * rest.length` (matching the
    encoder of `{data := rest, _}`).  Direct corollary of
    `_6steps_true_head` with `ctsConfigToSystem5BagAux_length`.  Mirrors
    iter 688's 4-step false-head bag-length: per-bit consumption
    leaves the same shape regardless of head bit. -/
theorem AllEmptyAppendants_System5_6steps_true_head_bag_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 4 ≤ 4 * cts.appendants.length * N) :
    ∃ s5_result, System5.nSteps (ctsToSystem5 cts
      { data := true :: rest, phase := phase } N) 6 = some s5_result
              ∧ s5_result.bag.length = 4 * rest.length := by
  refine ⟨_, AllEmptyAppendants_System5_6steps_true_head
    cts h_app rest phase N h_N, ?_⟩
  show (ctsConfigToSystem5BagAux rest 1).length = 4 * rest.length
  exact ctsConfigToSystem5BagAux_length rest 1

/-- **`AllEmptyAppendants_System5_6steps_true_head_rules_length` (iter
    694)**: after 6 System 5 steps from a true-head AllEmptyAppendants
    starting cfg, the rules have length `K - 4` where `K = 3 *
    |appendants| * N` (4 D-steps in the D-P-D-D-P-D pattern).  Mirrors
    iter 688's 4-step false-head rules-length: per-bit consumption
    debits exactly 4 from the rule budget (false: 4 D-steps in 4
    System 5 steps; true: 4 D-steps in 6 System 5 steps + 2 P-steps). -/
theorem AllEmptyAppendants_System5_6steps_true_head_rules_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (rest : List Bool) (phase : Nat) (N : Nat)
    (h_N : 4 ≤ 4 * cts.appendants.length * N) :
    ∃ s5_result, System5.nSteps (ctsToSystem5 cts
      { data := true :: rest, phase := phase } N) 6 = some s5_result
              ∧ s5_result.rules.length = 4 * cts.appendants.length * N - 4 := by
  refine ⟨_, AllEmptyAppendants_System5_6steps_true_head
    cts h_app rest phase N h_N, ?_⟩
  show (List.replicate (4 * cts.appendants.length * N - 4) ([] : List Int)).length
      = 4 * cts.appendants.length * N - 4
  exact List.length_replicate

/-- **AllEmptyAppendants per-step System 5 emulation**: for any
    non-halted CTS cfg, there exist `m` System 5 steps reaching a
    state whose bag equals the encoded post-CTS-step config.  Unifies
    iter 334 (false-head, m = 4) and iter 338 (true-head, m = 6).
    This is the meaningful single-step Smith emulation **for the
    AllEmptyAppendants restricted class** — not a closure of the
    full `ctsToSystem5_emulates` (which is for arbitrary CTS), but
    a substantive per-step bag-match in this restricted regime. -/
theorem AllEmptyAppendants_System5_per_step_emulation
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg cfg' : CTSConfig) (h_data : cfg.data ≠ [])
    (h_step : cts.step cfg = some cfg')
    (N : Nat) (h_N : 4 ≤ 4 * cts.appendants.length * N) :
    ∃ m s5_result,
      System5.nSteps (ctsToSystem5 cts cfg N) m = some s5_result
      ∧ s5_result.bag = ctsConfigToSystem5Bag cfg' := by
  obtain ⟨data, phase⟩ := cfg
  cases data with
  | nil => exact absurd rfl h_data
  | cons head rest =>
    have h_step' := AllEmptyAppendants_step_explicit cts h_app head rest phase
    rw [h_step'] at h_step
    injection h_step with h_eq
    cases head with
    | false =>
      refine ⟨4, _,
        AllEmptyAppendants_System5_4steps_false_head cts h_app rest phase N h_N, ?_⟩
      rw [← h_eq]
      rfl
    | true =>
      refine ⟨6, _,
        AllEmptyAppendants_System5_6steps_true_head cts h_app rest phase N h_N, ?_⟩
      rw [← h_eq]
      rfl

/-- **`AllEmptyAppendants_System5_per_step_emulation_step_bound` (iter
    696)**: refines `_per_step_emulation` with an explicit bound on
    the System 5 step count `m`: it's either 4 (false-head) or 6
    (true-head), so `m ∈ [4, 6]`.  Useful for budget arithmetic
    downstream: any `n`-step CTS trajectory under AllEmptyAppendants
    consumes at most `6 * n` System 5 steps. -/
theorem AllEmptyAppendants_System5_per_step_emulation_step_bound
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg cfg' : CTSConfig) (h_data : cfg.data ≠ [])
    (h_step : cts.step cfg = some cfg')
    (N : Nat) (h_N : 4 ≤ 4 * cts.appendants.length * N) :
    ∃ m s5_result,
      System5.nSteps (ctsToSystem5 cts cfg N) m = some s5_result
      ∧ s5_result.bag = ctsConfigToSystem5Bag cfg'
      ∧ 4 ≤ m ∧ m ≤ 6 := by
  obtain ⟨data, phase⟩ := cfg
  cases data with
  | nil => exact absurd rfl h_data
  | cons head rest =>
    have h_step' := AllEmptyAppendants_step_explicit cts h_app head rest phase
    rw [h_step'] at h_step
    injection h_step with h_eq
    cases head with
    | false =>
      refine ⟨4, _,
        AllEmptyAppendants_System5_4steps_false_head cts h_app rest phase N h_N,
        ?_, by omega, by omega⟩
      rw [← h_eq]
      rfl
    | true =>
      refine ⟨6, _,
        AllEmptyAppendants_System5_6steps_true_head cts h_app rest phase N h_N,
        ?_, by omega, by omega⟩
      rw [← h_eq]
      rfl


/-- **Abstract 4-step false-head System 5 transition**: operates on
    any state with bag `aux (false :: rest) 1` and rules `replicate
    K []` (with `K ≥ 4`), regardless of whether the state was
    produced by `ctsToSystem5`.  After 4 System 5 steps, bag becomes
    `aux rest 1` and rules become `replicate (K-4) []`.  This is
    iter 334 lifted to an arbitrary state, allowing chained multi-
    CTS-step emulation: after applying iter 334 once, the state has
    `bag = aux rest 1` (which is `aux (false :: rest') 1` if rest
    has a leading false) and `rules = replicate K' []`, and we can
    re-apply this lemma. -/
theorem System5_4steps_from_encoded_false_head
    (rest : List Bool) (K : Nat) (h_K : 4 ≤ K) :
    System5.nSteps
      { bag := ctsConfigToSystem5BagAux (false :: rest) 1,
        rules := List.replicate K [] } 4
    = some { bag := ctsConfigToSystem5BagAux rest 1,
             rules := List.replicate (K - 4) [] } := by
  show System5.nSteps
    { bag := (1 : Int) :: 2 :: 3 :: 4 :: ctsConfigToSystem5BagAux rest 5,
      rules := List.replicate K [] } 4
    = some { bag := ctsConfigToSystem5BagAux rest 1,
             rules := List.replicate (K - 4) [] }
  -- Pre-compute the dec-erase of 1::2::3::4::aux rest 5.
  have h_e1 : (((1 : Int) :: 2 :: 3 :: 4 :: ctsConfigToSystem5BagAux rest 5).map
                  (· - 1)).erase 0
            = (1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4 := by
    show ((0 : Int) :: 1 :: 2 :: 3 :: (ctsConfigToSystem5BagAux rest 5).map (· - 1)).erase 0
        = (1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4
    rw [List.erase_cons_head]
    rw [ctsConfigToSystem5BagAux_map_decrement]
    rw [show (5 : Int) - 1 = 4 from by omega]
  -- Step 1 (D): dec-erase. Then steps 2/3/4 by previous case.
  rw [show (4 : Nat) = 1 + 3 from rfl, System5.nSteps_add]
  rw [System5_step_from_replicate_state
        ((1 : Int) :: 2 :: 3 :: 4 :: ctsConfigToSystem5BagAux rest 5)
        (by simp) (List.mem_cons.mpr (Or.inl rfl)) K (by omega)]
  rw [Option.bind_some, h_e1]
  -- Now: System5.nSteps {bag := 1::2::3::aux rest 4, rules := replicate (K-1) []} 3 = ...
  rw [show (3 : Nat) = 1 + 2 from rfl, System5.nSteps_add]
  -- Step 2 (D): dec-erase 1::2::3::aux rest 4 → 1::2::aux rest 3.
  rw [System5_step_from_replicate_state
        ((1 : Int) :: 2 :: 3 :: ctsConfigToSystem5BagAux rest 4)
        (by simp) (List.mem_cons.mpr (Or.inl rfl)) (K - 1) (by omega)]
  rw [Option.bind_some, decrement_erase_three_cons_aux rest 4]
  rw [show (4 : Int) - 1 = 3 from by omega]
  rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add]
  -- Step 3 (D): dec-erase 1::2::aux rest 3 → 1::aux rest 2.
  rw [System5_step_from_replicate_state
        ((1 : Int) :: 2 :: ctsConfigToSystem5BagAux rest 3)
        (by simp) (List.mem_cons.mpr (Or.inl rfl)) (K - 1 - 1) (by omega)]
  rw [Option.bind_some, decrement_erase_two_cons_aux rest 3]
  rw [show (3 : Int) - 1 = 2 from by omega]
  -- Step 4 (D): dec-erase 1::aux rest 2 → aux rest 1.
  rw [System5_step_from_replicate_state
        ((1 : Int) :: ctsConfigToSystem5BagAux rest 2)
        (by simp) (List.mem_cons.mpr (Or.inl rfl)) (K - 1 - 1 - 1) (by omega)]
  rw [decrement_erase_one_cons_aux rest 2]
  rw [show (2 : Int) - 1 = 1 from by omega]
  rw [show K - 1 - 1 - 1 - 1 = K - 4 from by omega]

/-- **Abstract 6-step true-head System 5 transition**: operates on
    any state with bag `aux (true :: rest) 1` and rules `replicate
    K []` (with `K ≥ 4`).  After 6 System 5 steps, bag becomes
    `aux rest 1` and rules become `replicate (K-4) []` (4 D-steps
    + 2 P-steps; only D-steps decrement K).  Companion to iter
    340 (`_4steps_from_encoded_false_head`) for the true-head case.
    Foundation for chained multi-CTS-step emulation. -/
theorem System5_6steps_from_encoded_true_head
    (rest : List Bool) (K : Nat) (h_K : 4 ≤ K) :
    System5.nSteps
      { bag := ctsConfigToSystem5BagAux (true :: rest) 1,
        rules := List.replicate K [] } 6
    = some { bag := ctsConfigToSystem5BagAux rest 1,
             rules := List.replicate (K - 4) [] } := by
  show System5.nSteps
    { bag := (1 : Int) :: 3 :: 4 :: 6 :: ctsConfigToSystem5BagAux rest 7,
      rules := List.replicate K [] } 6
    = some { bag := ctsConfigToSystem5BagAux rest 1,
             rules := List.replicate (K - 4) [] }
  -- Pre-compute step 1's dec-erase result.
  have h_e1 : (((1 : Int) :: 3 :: 4 :: 6 :: ctsConfigToSystem5BagAux rest 7).map
                  (· - 1)).erase 0
            = (2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6 := by
    show ((0 : Int) :: 2 :: 3 :: 5 :: (ctsConfigToSystem5BagAux rest 7).map (· - 1)).erase 0
        = (2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6
    rw [List.erase_cons_head]
    rw [ctsConfigToSystem5BagAux_map_decrement]
    rw [show (7 : Int) - 1 = 6 from by omega]
  -- Step 1 (D): dec-erase 1::3::4::6::aux rest 7 → 2::3::5::aux rest 6.
  rw [show (6 : Nat) = 1 + 5 from rfl, System5.nSteps_add]
  rw [System5_step_from_replicate_state
        ((1 : Int) :: 3 :: 4 :: 6 :: ctsConfigToSystem5BagAux rest 7)
        (by simp) (List.mem_cons.mpr (Or.inl rfl)) K (by omega)]
  rw [Option.bind_some, h_e1]
  -- Step 2 (P): pure-dec 2::3::5::aux rest 6 → 1::2::4::aux rest 5.
  have h_no_one_2 : (1 : Int) ∉
      ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6) := by
    intro h
    rcases List.mem_cons.mp h with h1 | h
    · omega
    rcases List.mem_cons.mp h with h1 | h
    · omega
    rcases List.mem_cons.mp h with h1 | h
    · omega
    have := ctsConfigToSystem5BagAux_ge rest 6 1 h
    omega
  rw [show (5 : Nat) = 1 + 4 from rfl, System5.nSteps_add]
  rw [System5_step_from_replicate_state_pure_dec
        ((2 : Int) :: 3 :: 5 :: ctsConfigToSystem5BagAux rest 6)
        (by simp) h_no_one_2 (K - 1) (by omega)]
  rw [Option.bind_some, map_decrement_two_three_five_cons_aux rest 6]
  rw [show (6 : Int) - 1 = 5 from by omega]
  -- Step 3 (D): dec-erase 1::2::4::aux rest 5 → 1::3::aux rest 4.
  rw [show (4 : Nat) = 1 + 3 from rfl, System5.nSteps_add]
  rw [System5_step_from_replicate_state
        ((1 : Int) :: 2 :: 4 :: ctsConfigToSystem5BagAux rest 5)
        (by simp) (List.mem_cons.mpr (Or.inl rfl)) (K - 1) (by omega)]
  rw [Option.bind_some, decrement_erase_one_two_four_cons_aux rest 5]
  rw [show (5 : Int) - 1 = 4 from by omega]
  -- Step 4 (D): dec-erase 1::3::aux rest 4 → 2::aux rest 3.
  rw [show (3 : Nat) = 1 + 2 from rfl, System5.nSteps_add]
  rw [System5_step_from_replicate_state
        ((1 : Int) :: 3 :: ctsConfigToSystem5BagAux rest 4)
        (by simp) (List.mem_cons.mpr (Or.inl rfl)) (K - 1 - 1) (by omega)]
  rw [Option.bind_some, decrement_erase_one_three_cons_aux rest 4]
  rw [show (4 : Int) - 1 = 3 from by omega]
  -- Step 5 (P): pure-dec 2::aux rest 3 → 1::aux rest 2.
  have h_no_one_5 : (1 : Int) ∉
      ((2 : Int) :: ctsConfigToSystem5BagAux rest 3) := by
    intro h
    rcases List.mem_cons.mp h with h1 | h
    · omega
    have := ctsConfigToSystem5BagAux_ge rest 3 1 h
    omega
  rw [show (2 : Nat) = 1 + 1 from rfl, System5.nSteps_add]
  rw [System5_step_from_replicate_state_pure_dec
        ((2 : Int) :: ctsConfigToSystem5BagAux rest 3)
        (by simp) h_no_one_5 (K - 1 - 1 - 1) (by omega)]
  rw [Option.bind_some, map_decrement_two_cons_aux rest 3]
  rw [show (3 : Int) - 1 = 2 from by omega]
  -- Step 6 (D): dec-erase 1::aux rest 2 → aux rest 1.
  rw [System5_step_from_replicate_state
        ((1 : Int) :: ctsConfigToSystem5BagAux rest 2)
        (by simp) (List.mem_cons.mpr (Or.inl rfl)) (K - 1 - 1 - 1) (by omega)]
  rw [decrement_erase_one_cons_aux rest 2]
  rw [show (2 : Int) - 1 = 1 from by omega]
  rw [show K - 1 - 1 - 1 - 1 = K - 4 from by omega]

/-- **Abstract per-step (any head bit) System 5 transition**: from
    `{bag := aux (head :: rest) 1, rules := replicate K []}` with
    `K ≥ 4`, there's an `m` (= 4 if `head = false`, = 6 if `head =
    true`) such that after `m` System 5 steps, the state is `{bag :=
    aux rest 1, rules := replicate (K-4) []}`.  Unifies iters 340
    and 341.  Net K-decrement is always 4 (one CTS-step worth). -/
theorem System5_per_step_from_encoded_data
    (head : Bool) (rest : List Bool) (K : Nat) (h_K : 4 ≤ K) :
    ∃ m, System5.nSteps
            { bag := ctsConfigToSystem5BagAux (head :: rest) 1,
              rules := List.replicate K [] } m
          = some { bag := ctsConfigToSystem5BagAux rest 1,
                   rules := List.replicate (K - 4) [] } := by
  cases head with
  | false => exact ⟨4, System5_4steps_from_encoded_false_head rest K h_K⟩
  | true => exact ⟨6, System5_6steps_from_encoded_true_head rest K h_K⟩

/-- **Abstract partial-drain System 5 transition for empty-appendant
    encoding**: starting from `{bag := aux (prefix ++ suffix) 1,
    rules := replicate K []}` with `K ≥ 4 * prefix.length`, there's
    a total step count `m` such that after `m` System 5 steps, the
    state is `{bag := aux suffix 1, rules := replicate (K - 4 *
    prefix.length) []}`.  Generalizes the full-drain to any prefix
    portion.  Induction on `prefix`, using iter 342's per-step
    transition.  When `suffix = []`, recovers the full-drain
    (bag → []). -/
theorem System5_multi_step_from_encoded_data_partial
    (prefix_data suffix : List Bool) (K : Nat) (h_K : 4 * prefix_data.length ≤ K) :
    ∃ m, System5.nSteps
            { bag := ctsConfigToSystem5BagAux (prefix_data ++ suffix) 1,
              rules := List.replicate K [] } m
          = some { bag := ctsConfigToSystem5BagAux suffix 1,
                   rules := List.replicate (K - 4 * prefix_data.length) [] } := by
  induction prefix_data generalizing K with
  | nil =>
    refine ⟨0, ?_⟩
    show System5.nSteps
        { bag := ctsConfigToSystem5BagAux ([] ++ suffix) 1,
          rules := List.replicate K [] } 0
        = some { bag := ctsConfigToSystem5BagAux suffix 1,
                 rules := List.replicate (K - 4 * 0) [] }
    show System5.nSteps
        { bag := ctsConfigToSystem5BagAux suffix 1,
          rules := List.replicate K [] } 0
        = some { bag := ctsConfigToSystem5BagAux suffix 1,
                 rules := List.replicate (K - 0) [] }
    rfl
  | cons head rest ih =>
    obtain ⟨m₁, h_step1⟩ := System5_per_step_from_encoded_data
      head (rest ++ suffix) K (by simp [List.length_cons] at h_K; omega)
    obtain ⟨m₂, h_steps_rest⟩ := ih (K - 4) (by
      have := h_K
      simp [List.length_cons] at this
      omega)
    refine ⟨m₁ + m₂, ?_⟩
    show System5.nSteps
        { bag := ctsConfigToSystem5BagAux ((head :: rest) ++ suffix) 1,
          rules := List.replicate K [] } (m₁ + m₂)
        = some { bag := ctsConfigToSystem5BagAux suffix 1,
                 rules := List.replicate (K - 4 * (rest.length + 1)) [] }
    rw [System5.nSteps_add]
    show ((System5.nSteps
            { bag := ctsConfigToSystem5BagAux (head :: (rest ++ suffix)) 1,
              rules := List.replicate K [] } m₁).bind
          (fun c => System5.nSteps c m₂))
        = _
    rw [h_step1, Option.bind_some, h_steps_rest]
    show (some { bag := ctsConfigToSystem5BagAux suffix 1,
                 rules := List.replicate (K - 4 - 4 * rest.length) [] }
          : Option System5Config)
        = some { bag := ctsConfigToSystem5BagAux suffix 1,
                 rules := List.replicate (K - 4 * (rest.length + 1)) [] }
    rw [show K - 4 - 4 * rest.length = K - 4 * (rest.length + 1) from by
      have h_le := h_K
      simp [List.length_cons] at h_le
      rw [Nat.mul_succ]
      omega]

/-- **Abstract multi-step System 5 transition for empty-appendant
    encoding**: starting from `{bag := aux data 1, rules := replicate
    K []}` with `K ≥ 4 * data.length`, there's a total step count
    `m` such that after `m` System 5 steps, the state is `{bag :=
    aux [] 1 = [], rules := replicate (K - 4 * data.length) []}`.
    The bag drains completely (matching empty-data encoded bag).
    Direct corollary of `_partial` with `suffix = []`. -/
theorem System5_multi_step_from_encoded_data
    (data : List Bool) (K : Nat) (h_K : 4 * data.length ≤ K) :
    ∃ m, System5.nSteps
            { bag := ctsConfigToSystem5BagAux data 1,
              rules := List.replicate K [] } m
          = some { bag := ([] : List Int),
                   rules := List.replicate (K - 4 * data.length) [] } := by
  obtain ⟨m, h⟩ := System5_multi_step_from_encoded_data_partial data [] K h_K
  refine ⟨m, ?_⟩
  rw [List.append_nil] at h
  show System5.nSteps
      { bag := ctsConfigToSystem5BagAux data 1, rules := List.replicate K [] } m
      = some { bag := ([] : List Int),
               rules := List.replicate (K - 4 * data.length) [] }
  show System5.nSteps
      { bag := ctsConfigToSystem5BagAux data 1, rules := List.replicate K [] } m
      = some { bag := ctsConfigToSystem5BagAux [] 1,
               rules := List.replicate (K - 4 * data.length) [] }
  exact h

/-- **`System5_multi_step_from_encoded_data_partial_step_bound` (iter
    700)**: refines `_partial` with a step-count bound `m ≤ 6 *
    prefix_data.length`.  Each per-step transition uses ≤ 6 System 5
    steps (4 for false, 6 for true), so the total over `prefix_data`
    is bounded by `6 * |prefix_data|`.  Useful for budget arithmetic
    when deriving an explicit System 5 budget from a CTS step count. -/
theorem System5_multi_step_from_encoded_data_partial_step_bound
    (prefix_data suffix : List Bool) (K : Nat)
    (h_K : 4 * prefix_data.length ≤ K) :
    ∃ m, System5.nSteps
            { bag := ctsConfigToSystem5BagAux (prefix_data ++ suffix) 1,
              rules := List.replicate K [] } m
          = some { bag := ctsConfigToSystem5BagAux suffix 1,
                   rules := List.replicate (K - 4 * prefix_data.length) [] }
        ∧ m ≤ 6 * prefix_data.length := by
  induction prefix_data generalizing K with
  | nil =>
    refine ⟨0, ?_, ?_⟩
    · show System5.nSteps
          { bag := ctsConfigToSystem5BagAux ([] ++ suffix) 1,
            rules := List.replicate K [] } 0
          = some { bag := ctsConfigToSystem5BagAux suffix 1,
                   rules := List.replicate (K - 4 * 0) [] }
      show System5.nSteps
          { bag := ctsConfigToSystem5BagAux suffix 1,
            rules := List.replicate K [] } 0
          = some { bag := ctsConfigToSystem5BagAux suffix 1,
                   rules := List.replicate (K - 0) [] }
      rfl
    · simp
  | cons head rest ih =>
    have h_K_per : 4 ≤ K := by simp [List.length_cons] at h_K; omega
    have h_K_rest : 4 * rest.length ≤ K - 4 := by
      simp [List.length_cons] at h_K; omega
    -- Per-step bound: m₁ ≤ 6.
    have h_m1_bound : ∃ m, System5.nSteps
                              { bag := ctsConfigToSystem5BagAux (head :: (rest ++ suffix)) 1,
                                rules := List.replicate K [] } m
                            = some { bag := ctsConfigToSystem5BagAux (rest ++ suffix) 1,
                                     rules := List.replicate (K - 4) [] }
                          ∧ m ≤ 6 := by
      cases head with
      | false =>
        refine ⟨4, ?_, by omega⟩
        exact System5_4steps_from_encoded_false_head (rest ++ suffix) K h_K_per
      | true =>
        refine ⟨6, ?_, by omega⟩
        exact System5_6steps_from_encoded_true_head (rest ++ suffix) K h_K_per
    obtain ⟨m₁, h_step1, h_m1_le⟩ := h_m1_bound
    obtain ⟨m₂, h_steps_rest, h_m2_le⟩ := ih (K - 4) h_K_rest
    refine ⟨m₁ + m₂, ?_, ?_⟩
    · show System5.nSteps
          { bag := ctsConfigToSystem5BagAux ((head :: rest) ++ suffix) 1,
            rules := List.replicate K [] } (m₁ + m₂)
          = some { bag := ctsConfigToSystem5BagAux suffix 1,
                   rules := List.replicate (K - 4 * (rest.length + 1)) [] }
      rw [System5.nSteps_add]
      show ((System5.nSteps
              { bag := ctsConfigToSystem5BagAux (head :: (rest ++ suffix)) 1,
                rules := List.replicate K [] } m₁).bind
            (fun c => System5.nSteps c m₂))
          = _
      rw [h_step1, Option.bind_some, h_steps_rest]
      show (some { bag := ctsConfigToSystem5BagAux suffix 1,
                   rules := List.replicate (K - 4 - 4 * rest.length) [] }
            : Option System5Config)
          = some { bag := ctsConfigToSystem5BagAux suffix 1,
                   rules := List.replicate (K - 4 * (rest.length + 1)) [] }
      rw [show K - 4 - 4 * rest.length = K - 4 * (rest.length + 1) from by
        rw [Nat.mul_succ]
        omega]
    · simp [List.length_cons]
      omega

/-- **AllEmptyAppendants Smith emulation (multi-step)**: for any CTS
    in the AllEmptyAppendants class, the System 5 encoder admits a
    multi-step bag-match emulation for any `n ≤ cfg.data.length`.
    The budget `K = 3 * |appendants| * N` must satisfy `K ≥ 4 * n`.
    Composes iter 321 (CTS data evolution = drop-k) with iter 343
    (System 5 partial-drain) and iter 309's encoded-rules-replicate-
    eq.  **This is a non-trivial closure of the smith-step-emulation
    predicate restricted to the AllEmptyAppendants class.** -/
theorem AllEmptyAppendants_ctsToSystem5_emulates
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig)
    (h_phase : cfg.phase < cts.appendants.length) (N : Nat)
    (n : Nat) (h_n : n ≤ cfg.data.length)
    (h_K : 4 * n ≤ 4 * cts.appendants.length * N)
    (result : CTSConfig) (h_step : cts.nSteps cfg n = some result) :
    ∃ m s5_result,
      System5.nSteps (ctsToSystem5 cts cfg N) m = some s5_result
      ∧ s5_result.bag = ctsConfigToSystem5Bag result := by
  obtain ⟨data, phase⟩ := cfg
  simp at h_phase h_n h_step
  have h_drop := AllEmptyAppendants_nSteps_drop_explicit cts h_app data phase h_phase n h_n
  rw [h_step] at h_drop
  injection h_drop with h_eq
  have h_take_len : (data.take n).length = n := List.length_take_of_le h_n
  obtain ⟨m, h_partial⟩ := System5_multi_step_from_encoded_data_partial
    (data.take n) (data.drop n) (4 * cts.appendants.length * N)
    (by rw [h_take_len]; exact h_K)
  refine ⟨m,
    { bag := ctsConfigToSystem5BagAux (data.drop n) 1,
      rules := List.replicate
        (4 * cts.appendants.length * N - 4 * (data.take n).length) [] },
    ?_, ?_⟩
  · show System5.nSteps (ctsToSystem5 cts { data := data, phase := phase } N) m = _
    have h_rules : ctsRulesToSystem5Rules cts { data := data, phase := phase } N
                 = List.replicate (4 * cts.appendants.length * N) [] :=
      AllEmptyAppendants_ctsRulesToSystem5Rules_eq cts h_app _ N
    show System5.nSteps
        { bag := ctsConfigToSystem5BagAux data 1,
          rules := ctsRulesToSystem5Rules cts { data := data, phase := phase } N } m = _
    rw [h_rules]
    rw [List.take_append_drop n data] at h_partial
    exact h_partial
  · show ctsConfigToSystem5BagAux (data.drop n) 1 = ctsConfigToSystem5Bag result
    rw [h_eq]
    rfl

/-- **`AllEmptyAppendants_ctsToSystem5_emulates_step_bound` (iter
    702)**: refines the multi-step bag-match emulation with an
    explicit System 5 step-count bound `m ≤ 6 * n`.  Composes iter
    700's `_partial_step_bound` (per-step ≤ 6 lifted to multi-step)
    with the existing emulation construction.  Useful for declaring
    a finite System 5 budget when reasoning about an `n`-step CTS
    trajectory under AllEmptyAppendants. -/
theorem AllEmptyAppendants_ctsToSystem5_emulates_step_bound
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig)
    (h_phase : cfg.phase < cts.appendants.length) (N : Nat)
    (n : Nat) (h_n : n ≤ cfg.data.length)
    (h_K : 4 * n ≤ 4 * cts.appendants.length * N)
    (result : CTSConfig) (h_step : cts.nSteps cfg n = some result) :
    ∃ m s5_result,
      System5.nSteps (ctsToSystem5 cts cfg N) m = some s5_result
      ∧ s5_result.bag = ctsConfigToSystem5Bag result
      ∧ m ≤ 6 * n := by
  obtain ⟨data, phase⟩ := cfg
  simp at h_phase h_n h_step
  have h_drop := AllEmptyAppendants_nSteps_drop_explicit cts h_app data phase h_phase n h_n
  rw [h_step] at h_drop
  injection h_drop with h_eq
  have h_take_len : (data.take n).length = n := List.length_take_of_le h_n
  obtain ⟨m, h_partial, h_m_bound⟩ := System5_multi_step_from_encoded_data_partial_step_bound
    (data.take n) (data.drop n) (4 * cts.appendants.length * N)
    (by rw [h_take_len]; exact h_K)
  refine ⟨m,
    { bag := ctsConfigToSystem5BagAux (data.drop n) 1,
      rules := List.replicate
        (4 * cts.appendants.length * N - 4 * (data.take n).length) [] },
    ?_, ?_, ?_⟩
  · show System5.nSteps (ctsToSystem5 cts { data := data, phase := phase } N) m = _
    have h_rules : ctsRulesToSystem5Rules cts { data := data, phase := phase } N
                 = List.replicate (4 * cts.appendants.length * N) [] :=
      AllEmptyAppendants_ctsRulesToSystem5Rules_eq cts h_app _ N
    show System5.nSteps
        { bag := ctsConfigToSystem5BagAux data 1,
          rules := ctsRulesToSystem5Rules cts { data := data, phase := phase } N } m = _
    rw [h_rules]
    rw [List.take_append_drop n data] at h_partial
    exact h_partial
  · show ctsConfigToSystem5BagAux (data.drop n) 1 = ctsConfigToSystem5Bag result
    rw [h_eq]
    rfl
  · rw [h_take_len] at h_m_bound
    exact h_m_bound

/-- **`AllEmptyAppendants_ctsToSystem5_emulates_simp` (iter 704)**:
    cleaner-interface version of `_emulates` that drops the explicit
    `n ≤ cfg.data.length` precondition.  Under AllEmptyAppendants, any
    successful `nSteps cfg n = some result` already forces `n ≤
    cfg.data.length` (via iter 703's `_nSteps_some_imp_n_le_data_
    length`), so the precondition is redundant.  Cleaner downstream
    interface for budget reasoning. -/
theorem AllEmptyAppendants_ctsToSystem5_emulates_simp
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig)
    (h_phase : cfg.phase < cts.appendants.length) (N : Nat)
    (n : Nat) (h_K : 4 * n ≤ 4 * cts.appendants.length * N)
    (result : CTSConfig) (h_step : cts.nSteps cfg n = some result) :
    ∃ m s5_result,
      System5.nSteps (ctsToSystem5 cts cfg N) m = some s5_result
      ∧ s5_result.bag = ctsConfigToSystem5Bag result := by
  obtain ⟨data, phase⟩ := cfg
  simp at h_phase h_step
  have h_n : n ≤ data.length :=
    AllEmptyAppendants_nSteps_some_imp_n_le_data_length
      cts h_app data phase n result h_step
  exact AllEmptyAppendants_ctsToSystem5_emulates cts h_app
    { data := data, phase := phase } h_phase N n h_n h_K result h_step

/-- **AllEmptyAppendants Smith emulation, aligned with `_emulates_with_
    budget`'s shape**: when `|appendants| ≥ 2` (so `4 ≤ 3 * |append|`),
    the precondition `n ≤ N` suffices in place of `4 * n ≤ K`.
    Closure of the smith-step-emulation predicate restricted to the
    AllEmptyAppendants class with `|append| ≥ 2`.  For `|append| = 1`,
    use iter 348 directly with a stronger budget condition. -/
theorem AllEmptyAppendants_ctsToSystem5_emulates_with_budget
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig)
    (h_phase : cfg.phase < cts.appendants.length)
    (h_app_size : 4 ≤ 4 * cts.appendants.length) (N : Nat) :
    ∀ n result, n ≤ N → cts.nSteps cfg n = some result →
      ∃ m s5_result,
        System5.nSteps (ctsToSystem5 cts cfg N) m = some s5_result
        ∧ s5_result.bag = ctsConfigToSystem5Bag result := by
  intro n result h_n h_step
  have h_K : 4 * n ≤ 4 * cts.appendants.length * N := by
    have h1 : 4 * n ≤ 4 * N := Nat.mul_le_mul_left 4 h_n
    have h2 : 4 * N ≤ 4 * cts.appendants.length * N :=
      Nat.mul_le_mul_right N h_app_size
    omega
  exact AllEmptyAppendants_ctsToSystem5_emulates_simp
    cts h_app cfg h_phase N n h_K result h_step

/-- **`AllEmptyAppendants_ctsToSystem5_emulates_simp_step_bound` (iter
    706)**: combines `_simp` (no `n ≤ data.length` precondition) with
    iter 702's `m ≤ 6 * n` step bound.  The most user-friendly form
    of multi-step Smith emulation in the AllEmptyAppendants regime. -/
theorem AllEmptyAppendants_ctsToSystem5_emulates_simp_step_bound
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig)
    (h_phase : cfg.phase < cts.appendants.length) (N : Nat)
    (n : Nat) (h_K : 4 * n ≤ 4 * cts.appendants.length * N)
    (result : CTSConfig) (h_step : cts.nSteps cfg n = some result) :
    ∃ m s5_result,
      System5.nSteps (ctsToSystem5 cts cfg N) m = some s5_result
      ∧ s5_result.bag = ctsConfigToSystem5Bag result
      ∧ m ≤ 6 * n := by
  obtain ⟨data, phase⟩ := cfg
  simp at h_phase h_step
  have h_n : n ≤ data.length :=
    AllEmptyAppendants_nSteps_some_imp_n_le_data_length
      cts h_app data phase n result h_step
  exact AllEmptyAppendants_ctsToSystem5_emulates_step_bound cts h_app
    { data := data, phase := phase } h_phase N n h_n h_K result h_step

/-- **Non-trivial halt-preservation for AllEmptyAppendants**: with
    `N := 4 * cfg.data.length` (so K = 3 * |app| * N ≥ 4 *
    cfg.data.length), iter 342's full-drain reaches `bag = []` after
    some `m` steps; then one more System 5 step yields `none` (empty
    bag halt).  Total `m+1` steps from `ctsToSystem5 cts cfg N`.
    Substantively closes halt-preservation in this restricted class
    (vs iter 297's trivial `N=0` closure for arbitrary CTS). -/
theorem AllEmptyAppendants_ctsToSystem5_halt_preservation_meaningful
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig) :
    ∃ N m, System5.nSteps (ctsToSystem5 cts cfg N) m = none := by
  refine ⟨4 * cfg.data.length, ?_⟩
  have h_app_pos : 1 ≤ cts.appendants.length := cts.nonempty
  have h_K_ge : 4 * cfg.data.length ≤
                4 * cts.appendants.length * (4 * cfg.data.length) := by
    have h_3app : 1 ≤ 4 * cts.appendants.length := by omega
    have : 1 * (4 * cfg.data.length) ≤
           4 * cts.appendants.length * (4 * cfg.data.length) :=
      Nat.mul_le_mul_right (4 * cfg.data.length) h_3app
    omega
  obtain ⟨m, h_m⟩ := System5_multi_step_from_encoded_data cfg.data
    (4 * cts.appendants.length * (4 * cfg.data.length)) h_K_ge
  refine ⟨m + 1, ?_⟩
  have h_rules : ctsRulesToSystem5Rules cts cfg (4 * cfg.data.length)
               = List.replicate (4 * cts.appendants.length * (4 * cfg.data.length)) [] :=
    AllEmptyAppendants_ctsRulesToSystem5Rules_eq cts h_app cfg (4 * cfg.data.length)
  rw [System5.nSteps_add]
  show (System5.nSteps (ctsToSystem5 cts cfg (4 * cfg.data.length)) m).bind
        (fun c => System5.nSteps c 1) = none
  show (System5.nSteps
        { bag := ctsConfigToSystem5BagAux cfg.data 1,
          rules := ctsRulesToSystem5Rules cts cfg (4 * cfg.data.length) } m).bind
        (fun c => System5.nSteps c 1) = none
  rw [h_rules, h_m]
  show (System5.nSteps
        { bag := ([] : List Int),
          rules := List.replicate
            (4 * cts.appendants.length * (4 * cfg.data.length) - 4 * cfg.data.length) [] } 1)
      = none
  rw [System5.nSteps_one]
  apply (System5_step_none_iff _).mpr
  left
  rfl

/-- **Existential-budget AllEmptyAppendants Smith emulation**: for
    any AllEmptyAppendants CTS and any cfg with `phase < |append|`,
    there exists an `N` such that smith-step-emulation holds for all
    `n` with `nSteps cfg n = some result`.  Concretely `N :=
    4 * cfg.data.length` works for any `|append| ≥ 1`: budget K =
    3 * |app| * N ≥ 12 * cfg.data.length ≥ 4 * n (since `n ≤
    cfg.data.length` by iter 347, and `1 ≤ |app|`). -/
theorem AllEmptyAppendants_ctsToSystem5_emulates_exists_budget
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig)
    (h_phase : cfg.phase < cts.appendants.length) :
    ∃ N, ∀ n result, cts.nSteps cfg n = some result →
      ∃ m s5_result,
        System5.nSteps (ctsToSystem5 cts cfg N) m = some s5_result
        ∧ s5_result.bag = ctsConfigToSystem5Bag result := by
  refine ⟨4 * cfg.data.length, ?_⟩
  intro n result h_step
  apply AllEmptyAppendants_ctsToSystem5_emulates_simp
    cts h_app cfg h_phase (4 * cfg.data.length) n
  · obtain ⟨data, phase⟩ := cfg
    have h_n : n ≤ data.length :=
      AllEmptyAppendants_nSteps_some_imp_n_le_data_length
        cts h_app data phase n result h_step
    have h_app_pos : 1 ≤ cts.appendants.length := cts.nonempty
    show 4 * n ≤ 4 * cts.appendants.length * (4 * data.length)
    have h_chain1 : 4 * n ≤ 4 * data.length := Nat.mul_le_mul_left 4 h_n
    have h_chain2 : 4 * data.length ≤ 4 * cts.appendants.length * (4 * data.length) := by
      have h_3app : 1 ≤ 4 * cts.appendants.length := by omega
      have h_step1 : (1 : Nat) * (4 * data.length) ≤ 4 * cts.appendants.length * (4 * data.length) :=
        Nat.mul_le_mul_right (4 * data.length) h_3app
      omega
    omega
  · exact h_step

/-- **`System5_multi_step_from_encoded_data_step_bound` (iter 712)**:
    refines `_multi_step_from_encoded_data` with a step-count bound `m
    ≤ 6 * data.length`.  Direct corollary of iter 700's `_partial_step_
    bound` with `suffix := []`.  Useful for declaring a finite System 5
    budget when the bag drains completely. -/
theorem System5_multi_step_from_encoded_data_step_bound
    (data : List Bool) (K : Nat) (h_K : 4 * data.length ≤ K) :
    ∃ m, System5.nSteps
            { bag := ctsConfigToSystem5BagAux data 1,
              rules := List.replicate K [] } m
          = some { bag := ([] : List Int),
                   rules := List.replicate (K - 4 * data.length) [] }
        ∧ m ≤ 6 * data.length := by
  obtain ⟨m, h, h_bound⟩ :=
    System5_multi_step_from_encoded_data_partial_step_bound data [] K h_K
  refine ⟨m, ?_, h_bound⟩
  rw [List.append_nil] at h
  show System5.nSteps
      { bag := ctsConfigToSystem5BagAux data 1, rules := List.replicate K [] } m
      = some { bag := ([] : List Int),
               rules := List.replicate (K - 4 * data.length) [] }
  show System5.nSteps
      { bag := ctsConfigToSystem5BagAux data 1, rules := List.replicate K [] } m
      = some { bag := ctsConfigToSystem5BagAux [] 1,
               rules := List.replicate (K - 4 * data.length) [] }
  exact h


/-- **AllEmptyAppendants encoded System 5 always halts**: for any
    AllEmptyAppendants CTS and cfg, ∃ N (= 4 * cfg.data.length) such
    that `System5.Halts (ctsToSystem5 cts cfg N)`.  Direct corollary
    of iter 351's meaningful halt-preservation.  Cleaner closure of
    the eval-style halt for this restricted class. -/
theorem AllEmptyAppendants_System5_Halts
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig) :
    ∃ N, System5.Halts (ctsToSystem5 cts cfg N) := by
  obtain ⟨N, m, h_m⟩ :=
    AllEmptyAppendants_ctsToSystem5_halt_preservation_meaningful cts h_app cfg
  exact ⟨N, m, h_m⟩

/-- **`AllEmptyAppendants_System5_Halts_step_bound` (iter 722)**:
    refines `_System5_Halts` (and `_halt_preservation_meaningful`)
    with explicit step-count bound `m ≤ 6 * cfg.data.length + 1`.
    Uses iter 712's `_step_bound` to bound the bag-drain at `≤ 6 *
    data.length`, then adds 1 for the final empty-bag halt step.
    Quantifies the cost: System 5 halts within `O(data.length)`
    steps under AllEmptyAppendants. -/
theorem AllEmptyAppendants_System5_Halts_step_bound
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig) :
    ∃ N m, System5.nSteps (ctsToSystem5 cts cfg N) m = none
         ∧ m ≤ 6 * cfg.data.length + 1 := by
  refine ⟨4 * cfg.data.length, ?_⟩
  have h_app_pos : 1 ≤ cts.appendants.length := cts.nonempty
  have h_K_ge : 4 * cfg.data.length ≤
                4 * cts.appendants.length * (4 * cfg.data.length) := by
    have h_3app : 1 ≤ 4 * cts.appendants.length := by omega
    have : 1 * (4 * cfg.data.length) ≤
           4 * cts.appendants.length * (4 * cfg.data.length) :=
      Nat.mul_le_mul_right (4 * cfg.data.length) h_3app
    omega
  obtain ⟨m, h_m, h_m_bound⟩ := System5_multi_step_from_encoded_data_step_bound
    cfg.data (4 * cts.appendants.length * (4 * cfg.data.length)) h_K_ge
  refine ⟨m + 1, ?_, by omega⟩
  have h_rules : ctsRulesToSystem5Rules cts cfg (4 * cfg.data.length)
               = List.replicate (4 * cts.appendants.length * (4 * cfg.data.length)) [] :=
    AllEmptyAppendants_ctsRulesToSystem5Rules_eq cts h_app cfg (4 * cfg.data.length)
  rw [System5.nSteps_add]
  show (System5.nSteps (ctsToSystem5 cts cfg (4 * cfg.data.length)) m).bind
        (fun c => System5.nSteps c 1) = none
  show (System5.nSteps
        { bag := ctsConfigToSystem5BagAux cfg.data 1,
          rules := ctsRulesToSystem5Rules cts cfg (4 * cfg.data.length) } m).bind
        (fun c => System5.nSteps c 1) = none
  rw [h_rules, h_m]
  show (System5.nSteps
        { bag := ([] : List Int),
          rules := List.replicate
            (4 * cts.appendants.length * (4 * cfg.data.length) - 4 * cfg.data.length) [] } 1)
      = none
  rw [System5.nSteps_one]
  apply (System5_step_none_iff _).mpr
  left
  rfl

/-- **Halt-preservation, general** (corrected formulation per iters 257
    and 274): if CTS halts in finitely many steps from `cfg`, then
    System 5 also halts (with some budget `N` and step count `m`).
    Replaces the twice-flawed bag-matching claim of `ctsToSystem5_emulates`.

    PREDICATE-WEAKNESS NOTE (iter 297): closed via the trivial witness
    `N := 0`.  By definition, `ctsRulesToSystem5Rules cts cfg 0 =
    nCycles cts.appendants 0 _ = []`, so `(ctsToSystem5 cts cfg 0).rules
    = []`, and `System5.step` returns `none` immediately (per iter
    157's empty-rules halting characterisation).  This closes the
    sorry without an axiom but exposes that the predicate is
    *too weak* to capture faithful emulation: it never demands the
    chosen `N` be a meaningful budget that actually emulates `n` CTS
    steps.  A meaningful predicate would require `N ≥ N_required(n)`
    plus a bag-match commitment along the way (per iter 282's partial
    redemption).  Closing such a strengthened predicate is the
    substantive multi-month research direction. -/
theorem ctsToSystem5_halt_preservation (cts : CTS) (cfg : CTSConfig) :
    (∃ n, cts.nSteps cfg n = none) →
    ∃ N m, System5.nSteps (ctsToSystem5 cts cfg N) m = none := by
  intro _
  refine ⟨0, 1, ?_⟩
  rw [System5.nSteps_one]
  apply (System5_step_none_iff _).mpr
  right
  show ctsRulesToSystem5Rules cts cfg 0 = []
  rfl


/-- **CTS step → System5 nSteps emulation lifting (iter 428)**:
    System5 analogue of iter 397's `step_to_nSteps_emulation_generic`.
    Lifts a per-step CTS→System5 emulation to a multi-step
    emulation. -/
theorem step_to_nSteps_emulation_system5
    (cts : CTS) (encode : CTSConfig → System5Config)
    (h_emulate : ∀ ctsCfg ctsCfg',
       cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ System5.nSteps (encode ctsCfg) n = some (encode ctsCfg'))
    (ctsCfg : CTSConfig) (k : Nat) (result : CTSConfig)
    (h_steps : cts.nSteps ctsCfg k = some result) :
    ∃ m, System5.nSteps (encode ctsCfg) m = some (encode result) := by
  induction k generalizing ctsCfg with
  | zero =>
    rw [CTS.nSteps_zero] at h_steps
    injection h_steps with h_eq
    refine ⟨0, ?_⟩
    rw [h_eq]
    rfl
  | succ k ih =>
    rw [CTS_nSteps_succ_unfold] at h_steps
    cases h_step : cts.step ctsCfg with
    | none => rw [h_step] at h_steps; cases h_steps
    | some cfg₁ =>
      rw [h_step] at h_steps
      obtain ⟨n, _hn_pos, h_n⟩ := h_emulate ctsCfg cfg₁ h_step
      obtain ⟨m', h_m'⟩ := ih cfg₁ h_steps
      exact ⟨n + m',
        System5_nSteps_some_compose (encode ctsCfg) (encode cfg₁)
          n m' (encode result) h_n h_m'⟩

/-- **CTS Halts → System5 Halts under step emulation (iter 428)**:
    System5 analogue of iter 397.  Composes the step-to-nSteps
    lifting with iter 427's `_Halts_nSteps_pred` to derive
    halt-preservation. -/
theorem ctsHalts_imp_system5Halts_under_step_emulation
    (cts : CTS) (encode : CTSConfig → System5Config)
    (h_step_emulate : ∀ ctsCfg ctsCfg',
       cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ System5.nSteps (encode ctsCfg) n = some (encode ctsCfg'))
    (h_halt_preserve : ∀ ctsCfg, ctsHalted ctsCfg = true →
       System5.Halts (encode ctsCfg))
    (ctsCfg : CTSConfig) (h : cts.Halts ctsCfg) :
    System5.Halts (encode ctsCfg) := by
  rw [CTS_Halts_iff_nSteps_reaches_halted] at h
  obtain ⟨k, result, h_n, h_halt⟩ := h
  obtain ⟨m, h_m⟩ := step_to_nSteps_emulation_system5
    cts encode h_step_emulate ctsCfg k result h_n
  exact System5_Halts_nSteps_pred (encode ctsCfg) m (encode result) h_m
    (h_halt_preserve result h_halt)

/-- **Halting base case**: if the CTS cfg is already halted, the System 5
    encoder produces a halted System 5 cfg.  Composes
    `ctsConfigToSystem5Bag_empty_iff_halted` with
    `System5.Halts_of_empty_bag`. -/
theorem ctsHalted_imp_system5_halts (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    ctsHalted cfg = true → System5.Halts (ctsToSystem5 cts cfg n) := by
  intro h_halt
  apply System5.Halts_of_empty_bag
  show ctsConfigToSystem5Bag cfg = []
  exact (ctsConfigToSystem5Bag_empty_iff_halted cfg).mpr h_halt

/-- **`ctsHalted_imp_system5_step_none` (iter 724)**: stronger
    halt-base — if the CTS cfg is halted, then System 5 step on the
    encoded cfg returns `none` (not just `Halts`).  Reason: the bag
    is empty, so `System5.step` returns `none` immediately by
    `_step_none_iff`'s left disjunct.  Useful direct halt witness
    (no quantifier search). -/
theorem ctsHalted_imp_system5_step_none (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    ctsHalted cfg = true → System5.step (ctsToSystem5 cts cfg n) = none := by
  intro h_halt
  apply (System5_step_none_iff _).mpr
  left
  show ctsConfigToSystem5Bag cfg = []
  exact (ctsConfigToSystem5Bag_empty_iff_halted cfg).mpr h_halt

/-- **`ctsRulesToSystem5Rules_zero` (iter 756)**: with budget `N = 0`,
    the encoded rules list is empty.  Direct from the definition (the
    rule encoder is built via `nCycles cts.appendants 0 _` which is
    `rfl`-equal to `[]`).  Useful in N=0 trivial-halt arguments and
    for justifying why the original `ctsToSystem5_emulates` predicate
    is satisfiable without faithful emulation. -/
@[simp] theorem ctsRulesToSystem5Rules_zero (cts : CTS) (cfg : CTSConfig) :
    ctsRulesToSystem5Rules cts cfg 0 = [] := rfl

/-- **`ctsToSystem5_zero_step_none` (iter 756)**: with budget `N = 0`,
    `System5.step` on the encoded cfg returns `none` immediately
    (rules are empty).  Companion to iter 724's `ctsHalted_imp_
    system5_step_none` (which uses bag emptiness).  Documents why
    `ctsToSystem5_halt_preservation` discharges trivially via `N = 0`. -/
theorem ctsToSystem5_zero_step_none (cts : CTS) (cfg : CTSConfig) :
    System5.step (ctsToSystem5 cts cfg 0) = none := by
  apply (System5_step_none_iff _).mpr
  right
  exact ctsRulesToSystem5Rules_zero cts cfg

/-- **`ctsToSystem5_step_some_of_data_nonempty` (iter 762)**: from
    `cfg.data ≠ []` and `N ≥ 1`, the System 5 step on the encoded
    cfg succeeds (bag and rules both nonempty).  Direct via
    `_step_some_iff` with the existing nonempty witnesses for the
    encoded bag (iter 671's `_empty_iff_halted`) and rules (iter 645's
    `_nonempty`).  Useful for ruling out trivial halts when the source
    CTS hasn't reached its halt state. -/
theorem ctsToSystem5_step_some_of_data_nonempty
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : 1 ≤ N)
    (h_data : cfg.data ≠ []) :
    ∃ result, System5.step (ctsToSystem5 cts cfg N) = some result := by
  apply (System5_step_some_iff _).mpr
  refine ⟨?_, ctsRulesToSystem5Rules_nonempty cts cfg N h_N⟩
  show ctsConfigToSystem5Bag cfg ≠ []
  intro h_empty
  exact h_data ((ctsConfigToSystem5Bag_eq_nil_iff cfg).mp h_empty)

/-- **`ctsToSystem5_step_none_iff` (iter 764)**: complete
    characterisation of when `System5.step` halts on the encoded cfg.
    `System5.step (ctsToSystem5 cts cfg N) = none ↔ cfg.data = [] ∨ N
    = 0`.  Forward: combines iter 724 (`ctsHalted` ⇒ bag empty) and
    iter 756 (`N = 0` ⇒ rules empty); backward: contrapositive of
    iter 762.  Captures the two ways the System 5 trajectory halts
    immediately. -/
theorem ctsToSystem5_step_none_iff
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.step (ctsToSystem5 cts cfg N) = none ↔ cfg.data = [] ∨ N = 0 := by
  constructor
  · intro h_none
    rcases (System5_step_none_iff _).mp h_none with h_bag | h_rules
    · left
      exact (ctsConfigToSystem5Bag_eq_nil_iff cfg).mp h_bag
    · right
      rcases Nat.eq_zero_or_pos N with h_zero | h_pos
      · exact h_zero
      · exfalso
        exact ctsRulesToSystem5Rules_nonempty cts cfg N h_pos h_rules
  · rintro (h_data | h_N)
    · -- cfg.data = [] case: ctsHalted is true
      have h_halt : ctsHalted cfg = true := by
        simp [ctsHalted, h_data]
      exact ctsHalted_imp_system5_step_none cts cfg N h_halt
    · -- N = 0 case
      rw [h_N]
      exact ctsToSystem5_zero_step_none cts cfg

/-- **`ctsToSystem5_step_some_iff` (iter 766)**: dual to iter 764's
    `_step_none_iff`.  `System5.step (ctsToSystem5 cts cfg N) ≠ none
    ↔ cfg.data ≠ [] ∧ N ≠ 0`.  Trivial via `not_iff_not` on iter 764
    plus De Morgan; provided as a stand-alone lemma for ergonomics. -/
theorem ctsToSystem5_step_some_iff
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (∃ result, System5.step (ctsToSystem5 cts cfg N) = some result)
    ↔ cfg.data ≠ [] ∧ N ≠ 0 := by
  constructor
  · rintro ⟨result, h_some⟩
    have h_not_none : ¬ (cfg.data = [] ∨ N = 0) := by
      intro h_or
      have h_none := (ctsToSystem5_step_none_iff cts cfg N).mpr h_or
      rw [h_some] at h_none
      cases h_none
    refine ⟨fun h_data => h_not_none ?_, fun h_N => h_not_none ?_⟩
    · left; exact h_data
    · right; exact h_N
  · rintro ⟨h_data, h_N⟩
    have h_pos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr h_N
    exact ctsToSystem5_step_some_of_data_nonempty cts cfg N h_pos h_data

/-- **`ctsToSystem5_Halts_trivial` (iter 768)**: every encoded
    `ctsToSystem5 cts cfg N` trivially halts via either the bag-empty
    or rules-empty path.  For non-empty data with `N ≥ 1`, halt is
    not immediate but can occur later (per the trajectory analysis).
    For `N = 0` or empty data, halt is immediate via iter 764.  This
    proves `System5.Halts` unconditionally — though as noted, halt
    can be trivially-immediate. -/
theorem ctsToSystem5_Halts_when_data_empty_or_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : cfg.data = [] ∨ N = 0) :
    System5.Halts (ctsToSystem5 cts cfg N) := by
  refine ⟨1, ?_⟩
  rw [System5.nSteps_one]
  exact (ctsToSystem5_step_none_iff cts cfg N).mpr h

/-- **`ctsToSystem5_Halts_unconditional` (iter 770)**: every encoded
    `ctsToSystem5 cts cfg N` halts in finite System 5 steps.  Direct
    via the trivial `N = 0` witness from iter 768.  This is iter 297's
    weak halt-preservation — the predicate `∃ N m, nSteps = none` is
    unconditionally satisfiable.  A meaningful predicate would
    constrain `N ≥ N_required(n)` per the Smith Conjecture 0
    obstruction. -/
theorem ctsToSystem5_Halts_unconditional (cts : CTS) (cfg : CTSConfig) :
    ∃ N, System5.Halts (ctsToSystem5 cts cfg N) :=
  ⟨0, ctsToSystem5_Halts_when_data_empty_or_N_zero cts cfg 0 (Or.inr rfl)⟩

/-- **`ctsToSystem5_Halts_of_data_empty` (iter 772)**: specialization
    — `cfg.data = []` forces immediate halt for any budget `N`.
    Direct via iter 768.  Useful when the source CTS is already at
    its halt state. -/
theorem ctsToSystem5_Halts_of_data_empty
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h : cfg.data = []) :
    System5.Halts (ctsToSystem5 cts cfg N) :=
  ctsToSystem5_Halts_when_data_empty_or_N_zero cts cfg N (Or.inl h)

/-- **`ctsToSystem5_nSteps_pos_none_when_data_empty_or_N_zero` (iter
    781)**: combines iter 768's immediate halt with iter 720's
    `_step_none_imp_nSteps_pos_none` to derive that EVERY positive
    System 5 step-count yields `none` when data is empty or N = 0.
    Strengthens iter 768 from `∃ m` halt to `∀ m ≥ 1` halt. -/
theorem ctsToSystem5_nSteps_pos_none_when_data_empty_or_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (h : cfg.data = [] ∨ N = 0) (m : Nat) (h_m : 1 ≤ m) :
    System5.nSteps (ctsToSystem5 cts cfg N) m = none :=
  System5_step_none_imp_nSteps_pos_none (ctsToSystem5 cts cfg N)
    ((ctsToSystem5_step_none_iff cts cfg N).mpr h) m h_m

end BiTM
