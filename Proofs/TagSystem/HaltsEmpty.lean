/-
  TagSystem.HaltsEmpty

  Tag-system halt-empty infrastructure extracted from
  `BiTM.CockeMinskyConstruction`.

  Contents:
    * `tagNSteps` (discrete-step iterator) and helpers
    * `Tag_HaltsEmpty_step_decompose`, `Tag_HaltsEmpty_induction`
      (strong induction principle)
    * `tagNSteps`-vs-`Tag.eval` bridges in both directions
    * Structural facts: post-nil is none, uniqueness of nil step
      count, penultimate config form
    * Empty-production necessity for halt-empty on non-empty cfgs

  All declarations live in the `TagSystem` namespace.  Extracted
  in a refactor reducing `CockeMinskyConstruction.lean` by ~500
  lines.  See git log for the original iter-by-iter history
  (iters 526–544).
-/

import TagSystem.Basic
import TagSystem.TagToCTS

namespace TagSystem

open TagSystem

/-- Run a 2-tag system for exactly `n` steps; `none` if it halts early.
    Local helper used to state the step-simulation invariant; the
    eval-based form lives in `TagSystem.Basic`. -/
def tagNSteps {k : Nat} (ts : Tag k) (cfg : TagConfig k) : Nat → Option (TagConfig k)
  | 0 => some cfg
  | n + 1 =>
    match ts.step cfg with
    | none => none
    | some cfg' => tagNSteps ts cfg' n

/-- If the tag system steps successfully then it wasn't halted. -/
private theorem tag_step_some_not_halted {k : Nat} (ts : Tag k)
    (cfg cfg' : TagConfig k) :
    ts.step cfg = some cfg' → tagHalted cfg = false := by
  intro h
  cases cfg with
  | nil => simp [Tag.step] at h
  | cons _ tl =>
    cases tl with
    | nil => simp [Tag.step] at h
    | cons _ _ => simp [tagHalted]

/-- `tagNSteps` cleanly composes with `Tag.eval`: prepending `n` exact
    steps shifts the fuel by `n`. -/
theorem tag_nSteps_prepend_eval {k : Nat} (ts : Tag k)
    (cfg cfg' : TagConfig k) (n fuel : Nat) :
    tagNSteps ts cfg n = some cfg' →
    ts.eval cfg (fuel + n) = ts.eval cfg' fuel := by
  intro h_nsteps
  induction n generalizing cfg with
  | zero =>
    simp [tagNSteps] at h_nsteps
    rw [h_nsteps]; simp
  | succ n ih =>
    simp only [tagNSteps] at h_nsteps
    split at h_nsteps
    · simp at h_nsteps
    · rename_i cfg'' h_step
      rw [Nat.add_succ]
      have h_nh := tag_step_some_not_halted ts cfg cfg'' h_step
      rw [Tag.eval_step ts cfg cfg'' (fuel + n) h_nh h_step]
      exact ih cfg'' h_nsteps

/-- If a tag system reaches `cfg'` in `n` exact steps and `cfg'` halts-empty,
    then `cfg` halts-empty. -/
theorem tag_haltsEmpty_after_nSteps {k : Nat} (ts : Tag k)
    (cfg cfg' : TagConfig k) (n : Nat) :
    tagNSteps ts cfg n = some cfg' →
    ts.HaltsEmpty cfg' → ts.HaltsEmpty cfg := by
  intro h_nsteps ⟨fuel, h_eval⟩
  exact ⟨fuel + n, by rw [tag_nSteps_prepend_eval ts cfg cfg' n fuel h_nsteps]; exact h_eval⟩

/-- Composition: `n + m` exact steps factor as `n` then `m`. -/
theorem tagNSteps_add {k : Nat} (ts : Tag k) (cfg : TagConfig k) (n m : Nat) :
    tagNSteps ts cfg (n + m)
      = (tagNSteps ts cfg n).bind (fun c => tagNSteps ts c m) := by
  induction n generalizing cfg with
  | zero =>
    rw [Nat.zero_add]
    simp [tagNSteps]
  | succ n ih =>
    rw [Nat.succ_add]
    show (match ts.step cfg with
          | none => none
          | some cfg' => tagNSteps ts cfg' (n + m))
        = (match ts.step cfg with
            | none => none
            | some cfg' => tagNSteps ts cfg' n).bind
          (fun c => tagNSteps ts c m)
    cases ts.step cfg with
    | none => rfl
    | some c => exact ih c

/-- Zero exact steps is the identity. -/
@[simp] theorem tagNSteps_zero {k : Nat} (ts : Tag k) (cfg : TagConfig k) :
    tagNSteps ts cfg 0 = some cfg := rfl

/-- One exact step is `Tag.step`. -/
theorem tagNSteps_one {k : Nat} (ts : Tag k) (cfg : TagConfig k) :
    tagNSteps ts cfg 1 = ts.step cfg := by
  show (match ts.step cfg with
        | none => none
        | some cfg' => tagNSteps ts cfg' 0) = ts.step cfg
  cases ts.step cfg with
  | none => rfl
  | some _ => rfl

/-- The empty word halts-empty: `eval [] 0 = some []`. -/
theorem Tag.haltsEmpty_nil {k : Nat} (ts : Tag k) :
    ts.HaltsEmpty ([] : TagConfig k) :=
  ⟨0, by simp [Tag.eval, tagHalted]⟩

/-- If `tagNSteps` reaches the empty word in `n` steps, the starting
    config halts-empty.  This is the bridge from a concrete simulation
    step (e.g. `cmStep_sim_empty_halt`) to the abstract `HaltsEmpty`
    conclusion that downstream theorems consume. -/
theorem tagNSteps_eq_nil_implies_haltsEmpty {k : Nat} (ts : Tag k)
    (cfg : TagConfig k) (n : Nat) :
    tagNSteps ts cfg n = some [] → ts.HaltsEmpty cfg :=
  fun h => tag_haltsEmpty_after_nSteps ts cfg [] n h (Tag.haltsEmpty_nil ts)
/-- **Tag step-or-halted dichotomy (iter 526)**: Tag analog of
    iter 515/516/517 — any tag cfg either is halted (length < 2)
    or admits a step.  Direct corollary of
    `Tag.step_none_iff_halted`. -/
theorem tag_step_or_halted {k : Nat} (ts : Tag k) (cfg : TagConfig k) :
    tagHalted cfg = true ∨ ∃ cfg', ts.step cfg = some cfg' := by
  cases h_step : ts.step cfg with
  | none => left; exact (Tag.step_none_iff_halted ts cfg).mp h_step
  | some cfg' => right; exact ⟨cfg', rfl⟩

/-- **Tag `HaltsEmpty` step decomposition (iter 527)**: any cfg
    with `HaltsEmpty` is either already empty or admits a step
    leading to a `HaltsEmpty` cfg.  Note: the singleton case `[a]`
    is impossible since `eval` returns `some [a]` (length 1 is
    halted), never `some []`. -/
theorem Tag_HaltsEmpty_step_decompose {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (h : ts.HaltsEmpty cfg) :
    cfg = [] ∨ ∃ cfg', ts.step cfg = some cfg' ∧ ts.HaltsEmpty cfg' := by
  match cfg with
  | [] => left; rfl
  | [a] =>
    exfalso
    obtain ⟨fuel, h_eval⟩ := h
    have h_halt : tagHalted ([a] : TagConfig k) = true :=
      (Tag.step_none_iff_halted ts ([a] : TagConfig k)).mp rfl
    rw [Tag.eval_halted ts _ fuel h_halt] at h_eval
    injection h_eval with h_l
    cases h_l
  | a :: b :: rest =>
    right
    refine ⟨rest ++ ts.productions a, rfl, ?_⟩
    obtain ⟨fuel, h_eval⟩ := h
    have h_step : ts.step (a :: b :: rest) = some (rest ++ ts.productions a) := rfl
    have h_nh : tagHalted (a :: b :: rest : TagConfig k) = false := by
      simp [tagHalted, List.length_cons]
    cases fuel with
    | zero => simp [Tag.eval, h_nh] at h_eval
    | succ n =>
      rw [Tag.eval_step ts _ _ n h_nh h_step] at h_eval
      exact ⟨n, h_eval⟩

/-- **Strong induction on `HaltsEmpty` (iter 528)**: any property
    `P` that holds for `[]` and propagates backwards along single
    `step`s (within `HaltsEmpty` configs) holds for every
    `HaltsEmpty` cfg.  Factors out the fuel-induction pattern
    repeated throughout the cmHaltsEmpty-style proofs.  Proof:
    induction on the fuel witnessing `HaltsEmpty cfg`. -/
theorem Tag_HaltsEmpty_induction {k : Nat} (ts : Tag k)
    (P : TagConfig k → Prop)
    (h_nil : P [])
    (h_back : ∀ cfg cfg', ts.step cfg = some cfg' →
              ts.HaltsEmpty cfg' → P cfg' → P cfg)
    (cfg : TagConfig k) (h : ts.HaltsEmpty cfg) : P cfg := by
  obtain ⟨fuel, h_eval⟩ := h
  induction fuel generalizing cfg with
  | zero =>
    -- eval cfg 0 = if tagHalted cfg then some cfg else none
    -- so result `some []` forces tagHalted ∧ cfg = []
    by_cases h_halt : tagHalted cfg = true
    · rw [Tag.eval_halted ts cfg 0 h_halt] at h_eval
      injection h_eval with h_eq; rw [h_eq]; exact h_nil
    · simp [Tag.eval] at h_eval
      simp [h_halt] at h_eval
  | succ n ih =>
    by_cases h_halt : tagHalted cfg = true
    · rw [Tag.eval_halted ts cfg (n+1) h_halt] at h_eval
      injection h_eval with h_eq; rw [h_eq]; exact h_nil
    · have h_nh : tagHalted cfg = false := by
        cases h_eq : tagHalted cfg with
        | true => exact absurd h_eq h_halt
        | false => rfl
      cases h_step : ts.step cfg with
      | none =>
        -- impossible: step = none ↔ halted, contradicting h_nh
        have h_halt_true := (Tag.step_none_iff_halted ts cfg).mp h_step
        rw [h_halt_true] at h_nh; cases h_nh
      | some cfg' =>
        rw [Tag.eval_step ts cfg cfg' n h_nh h_step] at h_eval
        have h_he' : ts.HaltsEmpty cfg' := ⟨n, h_eval⟩
        exact h_back cfg cfg' h_step h_he' (ih cfg' h_eval)

/-- **`HaltsEmpty → ∃ n, tagNSteps = some []` (iter 529)**:
    converse of `tagNSteps_eq_nil_implies_haltsEmpty` — derived
    cleanly via iter 528's induction principle.  Establishes the
    biconditional `HaltsEmpty cfg ↔ ∃ n, tagNSteps cfg n = some []`,
    bridging the eval-based and discrete-step formulations of
    halt-empty.  Genuine consumer of the iter 528 abstraction. -/
theorem haltsEmpty_implies_tagNSteps_eq_nil {k : Nat} (ts : Tag k)
    (cfg : TagConfig k) (h : ts.HaltsEmpty cfg) :
    ∃ n, tagNSteps ts cfg n = some [] := by
  apply Tag_HaltsEmpty_induction ts (fun cfg => ∃ n, tagNSteps ts cfg n = some [])
  · -- P []: 0 steps suffice
    exact ⟨0, by simp [tagNSteps]⟩
  · -- backwards: step cfg = some cfg' & P cfg' ⇒ P cfg
    intro cfg cfg' h_step _ ⟨n, h_n⟩
    refine ⟨n + 1, ?_⟩
    show (match ts.step cfg with
          | none => none
          | some c => tagNSteps ts c n) = some []
    rw [h_step]; exact h_n
  · exact h

/-- **`HaltsEmpty ↔ ∃ n, tagNSteps cfg n = some []` (iter 530)**:
    biconditional packaging of iter 529 (forward) and the existing
    `tagNSteps_eq_nil_implies_haltsEmpty` (backward).  The
    eval-based `HaltsEmpty` and the discrete-step formulation are
    fully equivalent.  Useful for proofs that need to switch between
    the two halt-empty formulations. -/
theorem haltsEmpty_iff_tagNSteps_eq_nil {k : Nat} (ts : Tag k)
    (cfg : TagConfig k) :
    ts.HaltsEmpty cfg ↔ ∃ n, tagNSteps ts cfg n = some [] :=
  ⟨haltsEmpty_implies_tagNSteps_eq_nil ts cfg,
   fun ⟨n, h⟩ => tagNSteps_eq_nil_implies_haltsEmpty ts cfg n h⟩

/-- **`tagNSteps_after_nil` (iter 531)**: once a tag trajectory
    reaches the empty word at step `n`, every later step count
    `n + (k+1)` returns `none` (because `step [] = none`).  Useful
    for reasoning about minimal halt-empty witnesses and ruling
    out spurious extended trajectories.  Direct corollary of
    `tagNSteps_add` plus the fact that `step` on `[]` is none. -/
theorem tagNSteps_after_nil {k : Nat} (ts : Tag k) (cfg : TagConfig k) (n j : Nat)
    (h_n : tagNSteps ts cfg n = some []) :
    tagNSteps ts cfg (n + (j + 1)) = none := by
  rw [tagNSteps_add, h_n]
  show tagNSteps ts ([] : TagConfig k) (j + 1) = none
  show (match ts.step ([] : TagConfig k) with
        | none => none
        | some cfg' => tagNSteps ts cfg' j) = none
  rfl

/-- **`tagNSteps_eq_nil_unique` (iter 532)**: a tag trajectory
    reaches the empty word at exactly one step count.  If
    `tagNSteps cfg n₁ = some []` and `tagNSteps cfg n₂ = some []`,
    then `n₁ = n₂`.  Direct corollary of iter 531 (post-nil is
    none) — any later step would return none, contradicting reaching
    `[]` again. -/
theorem tagNSteps_eq_nil_unique {k : Nat} (ts : Tag k) (cfg : TagConfig k) (n₁ n₂ : Nat)
    (h₁ : tagNSteps ts cfg n₁ = some []) (h₂ : tagNSteps ts cfg n₂ = some []) :
    n₁ = n₂ := by
  rcases Nat.lt_or_ge n₁ n₂ with h_lt | h_ge
  · exfalso
    have h_eq : n₂ = n₁ + ((n₂ - n₁ - 1) + 1) := by omega
    rw [h_eq] at h₂
    rw [tagNSteps_after_nil ts cfg n₁ (n₂ - n₁ - 1) h₁] at h₂
    cases h₂
  · rcases Nat.lt_or_ge n₂ n₁ with h_lt' | h_ge'
    · exfalso
      have h_eq : n₁ = n₂ + ((n₁ - n₂ - 1) + 1) := by omega
      rw [h_eq] at h₁
      rw [tagNSteps_after_nil ts cfg n₂ (n₁ - n₂ - 1) h₂] at h₁
      cases h₁
    · omega

/-- **`tagNSteps_some_before_nil` (iter 533)**: every step count
    `m ≤ n` before reaching `[]` produces some config.  The
    trajectory is alive at every intermediate step.  Proof: if
    `tagNSteps cfg m = none`, then `tagNSteps cfg n = none.bind _
    = none` via `tagNSteps_add`, contradicting `some []`. -/
theorem tagNSteps_some_before_nil {k : Nat} (ts : Tag k) (cfg : TagConfig k) (n m : Nat)
    (h_n : tagNSteps ts cfg n = some []) (h_m : m ≤ n) :
    ∃ cfg', tagNSteps ts cfg m = some cfg' := by
  cases h_eq : tagNSteps ts cfg m with
  | none =>
    exfalso
    have h_split : n = m + (n - m) := by omega
    rw [h_split, tagNSteps_add, h_eq] at h_n
    cases h_n
  | some cfg' => exact ⟨cfg', rfl⟩

/-- **`tagNSteps_nonempty_before_nil` (iter 534)**: strengthening
    of iter 533 — for `m < n`, the intermediate config is not only
    `some` but also non-empty.  If it were `[]`, by iter 532's
    uniqueness `m = n`, contradicting `m < n`. -/
theorem tagNSteps_nonempty_before_nil {k : Nat} (ts : Tag k) (cfg : TagConfig k) (n m : Nat)
    (h_n : tagNSteps ts cfg n = some []) (h_m : m < n) :
    ∃ cfg', tagNSteps ts cfg m = some cfg' ∧ cfg' ≠ [] := by
  obtain ⟨cfg', h_some⟩ := tagNSteps_some_before_nil ts cfg n m h_n (Nat.le_of_lt h_m)
  refine ⟨cfg', h_some, ?_⟩
  intro h_nil
  rw [h_nil] at h_some
  have h_eq : m = n := tagNSteps_eq_nil_unique ts cfg m n h_some h_n
  omega

/-- **`tagNSteps_succ_nil_decompose` (iter 535)**: a trajectory of
    length `n + 1` ending at `[]` factors through some
    `cfg'` reached at step `n` such that `step cfg' = some []`.
    Establishes that there is a unique "last interesting step" right
    before the trajectory reaches `[]`.  Combines `tagNSteps_add`
    and `tagNSteps_one`. -/
theorem tagNSteps_succ_nil_decompose {k : Nat} (ts : Tag k) (cfg : TagConfig k) (n : Nat)
    (h : tagNSteps ts cfg (n + 1) = some []) :
    ∃ cfg', tagNSteps ts cfg n = some cfg' ∧ ts.step cfg' = some [] := by
  rw [tagNSteps_add] at h
  cases h_n : tagNSteps ts cfg n with
  | none => rw [h_n] at h; cases h
  | some cfg' =>
    refine ⟨cfg', rfl, ?_⟩
    rw [h_n] at h
    show ts.step cfg' = some []
    rw [← tagNSteps_one]
    exact h

/-- **`tagNSteps_penultimate_form` (iter 536)**: characterize the
    penultimate config in a halt-empty trajectory.  If
    `tagNSteps cfg (n+1) = some []`, then at step `n` the
    trajectory is at exactly `[a, b]` for some `a, b`, with
    `ts.productions a = []` (since `step [a, b] = some ([] ++ prods a)`
    must equal `some []`).  Strengthens iter 535 to a structural
    description of the penultimate cfg. -/
theorem tagNSteps_penultimate_form {k : Nat} (ts : Tag k) (cfg : TagConfig k) (n : Nat)
    (h : tagNSteps ts cfg (n + 1) = some []) :
    ∃ a b : Fin k, tagNSteps ts cfg n = some [a, b] ∧ ts.productions a = [] := by
  obtain ⟨cfg', h_some, h_step⟩ := tagNSteps_succ_nil_decompose ts cfg n h
  match cfg' with
  | [] => simp [Tag.step] at h_step
  | [_] => simp [Tag.step] at h_step
  | a :: b :: rest =>
    have h_step' : rest ++ ts.productions a = [] := by
      have : ts.step (a :: b :: rest) = some (rest ++ ts.productions a) := rfl
      rw [this] at h_step
      injection h_step
    have h_rest : rest = [] := by
      cases rest with
      | nil => rfl
      | cons _ _ => simp at h_step'
    have h_prod : ts.productions a = [] := by
      rw [h_rest, List.nil_append] at h_step'
      exact h_step'
    refine ⟨a, b, ?_, h_prod⟩
    rw [h_rest] at h_some
    exact h_some

/-- **`haltsEmpty_nonempty_implies_empty_production` (iter 537)**:
    structural necessary condition — if a non-empty cfg
    halts-empty, the tag system must have at least one symbol
    `a : Fin k` with `ts.productions a = []`.  Otherwise no
    trajectory could ever reach `[]` (every step appends a
    non-empty production).  Direct corollary of
    `haltsEmpty_iff_tagNSteps_eq_nil` and iter 536. -/
theorem haltsEmpty_nonempty_implies_empty_production
    {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (h : ts.HaltsEmpty cfg) (h_ne : cfg ≠ []) :
    ∃ a : Fin k, ts.productions a = [] := by
  obtain ⟨n, h_n⟩ := (haltsEmpty_iff_tagNSteps_eq_nil ts cfg).mp h
  cases n with
  | zero =>
    simp [tagNSteps] at h_n
    exact absurd h_n h_ne
  | succ m =>
    obtain ⟨a, _, _, h_prod⟩ := tagNSteps_penultimate_form ts cfg m h_n
    exact ⟨a, h_prod⟩

/-- **`no_empty_production_no_haltsEmpty` (iter 538)**:
    contrapositive of iter 537 — if every symbol has non-empty
    production, no non-empty cfg can halt-empty.  Direct
    consequence: tag systems built without an "empty"
    production symbol cannot terminate to `[]` from any input. -/
theorem no_empty_production_no_haltsEmpty {k : Nat} (ts : Tag k)
    (h_no_empty : ∀ a : Fin k, ts.productions a ≠ [])
    (cfg : TagConfig k) (h_ne : cfg ≠ []) :
    ¬ ts.HaltsEmpty cfg := by
  intro h
  obtain ⟨a, h_prod⟩ := haltsEmpty_nonempty_implies_empty_production ts cfg h h_ne
  exact h_no_empty a h_prod

/-- **`haltsEmpty_singleton_false` (iter 539)**: a singleton tag
    config `[a]` never halts-empty, regardless of the tag system's
    productions.  Reason: `tagHalted [a] = true` (length 1 < 2),
    so `eval [a] fuel` returns `some [a]` forever — never `some []`.
    Unconditional sanity check, separate from the empty-production
    family of iters 537/538. -/
theorem haltsEmpty_singleton_false {k : Nat} (ts : Tag k) (a : Fin k) :
    ¬ ts.HaltsEmpty [a] := by
  intro h
  rcases Tag_HaltsEmpty_step_decompose ts [a] h with h_nil | ⟨_, h_step, _⟩
  · cases h_nil
  · simp [Tag.step] at h_step

/-- **`haltsEmpty_iff_step_or_nil` (iter 540)**: full biconditional
    packaging of iter 527 (forward decomposition) with its
    converse: `HaltsEmpty cfg ↔ cfg = [] ∨ ∃ cfg', step cfg = some
    cfg' ∧ HaltsEmpty cfg'`.  Recursively unfolds the `HaltsEmpty`
    predicate one step at a time.  Useful for inductive arguments
    that case-split on `cfg = []` vs the step branch. -/
theorem haltsEmpty_iff_step_or_nil {k : Nat} (ts : Tag k) (cfg : TagConfig k) :
    ts.HaltsEmpty cfg ↔ cfg = [] ∨ ∃ cfg', ts.step cfg = some cfg' ∧ ts.HaltsEmpty cfg' := by
  constructor
  · exact Tag_HaltsEmpty_step_decompose ts cfg
  · intro h
    rcases h with h_nil | ⟨cfg', h_step, h_he'⟩
    · rw [h_nil]; exact Tag.haltsEmpty_nil ts
    · obtain ⟨fuel, h_eval⟩ := h_he'
      have h_nh := tag_step_some_not_halted ts cfg cfg' h_step
      exact ⟨fuel + 1, by rw [Tag.eval_step ts cfg cfg' fuel h_nh h_step]; exact h_eval⟩

/-- **`haltsEmpty_step_iff` (iter 541)**: if `step cfg = some cfg'`,
    then `HaltsEmpty cfg ↔ HaltsEmpty cfg'`.  Both directions:
    forward via `Tag_HaltsEmpty_step_decompose` (cfg ≠ [] case
    forced since step succeeds), backward via `Tag.eval_step`
    extending the fuel witness by 1.  Cleaner restatement of
    iter 540 specialized to a known step.  Useful for trajectory-
    style inductions where a step witness is already in hand. -/
theorem haltsEmpty_step_iff {k : Nat} (ts : Tag k) (cfg cfg' : TagConfig k)
    (h_step : ts.step cfg = some cfg') :
    ts.HaltsEmpty cfg ↔ ts.HaltsEmpty cfg' := by
  constructor
  · intro h
    rcases Tag_HaltsEmpty_step_decompose ts cfg h with h_nil | ⟨cfg'', h_step', h_he⟩
    · rw [h_nil] at h_step; cases h_step
    · rw [h_step'] at h_step
      injection h_step with h_eq
      rw [← h_eq]; exact h_he
  · intro h_he'
    obtain ⟨fuel, h_eval⟩ := h_he'
    have h_nh := tag_step_some_not_halted ts cfg cfg' h_step
    exact ⟨fuel + 1, by rw [Tag.eval_step ts cfg cfg' fuel h_nh h_step]; exact h_eval⟩

/-- **`haltsEmpty_nSteps_iff` (iter 542)**: lift iter 541 to nSteps
    — `tagNSteps cfg n = some cfg' → (HaltsEmpty cfg ↔ HaltsEmpty
    cfg')`.  Forward direction packages the new content; backward
    matches the existing `tag_haltsEmpty_after_nSteps`.  Proof:
    induction on n via repeated application of iter 541. -/
theorem haltsEmpty_nSteps_iff {k : Nat} (ts : Tag k) (cfg cfg' : TagConfig k) (n : Nat)
    (h_n : tagNSteps ts cfg n = some cfg') :
    ts.HaltsEmpty cfg ↔ ts.HaltsEmpty cfg' := by
  induction n generalizing cfg with
  | zero =>
    simp [tagNSteps] at h_n
    rw [h_n]
  | succ m ih =>
    cases h_step : ts.step cfg with
    | none =>
      have h_n' : tagNSteps ts cfg (m + 1) = none := by
        show (match ts.step cfg with | none => none | some c => tagNSteps ts c m) = none
        rw [h_step]
      rw [h_n'] at h_n
      cases h_n
    | some c =>
      have h_n' : tagNSteps ts c m = some cfg' := by
        have h_unfold : tagNSteps ts cfg (m + 1) =
            (match ts.step cfg with | none => none | some c' => tagNSteps ts c' m) := rfl
        rw [h_unfold, h_step] at h_n
        exact h_n
      rw [haltsEmpty_step_iff ts cfg c h_step]
      exact ih c h_n'

/-- **`tagNSteps_eq_nil_implies_eval_eq_nil` (iter 543)**: a
    discrete-step witness `tagNSteps cfg n = some []` produces a
    matching eval-based witness `Tag.eval cfg n = some []` at the
    same step count.  Direct corollary of the existing
    `tag_nSteps_prepend_eval` instantiated with `cfg' := []`,
    `fuel := 0`.  Bridges the two halt-empty witness shapes
    quantitatively (vs the existential biconditional iter 530). -/
theorem tagNSteps_eq_nil_implies_eval_eq_nil {k : Nat} (ts : Tag k)
    (cfg : TagConfig k) (n : Nat)
    (h : tagNSteps ts cfg n = some []) :
    Tag.eval ts cfg n = some [] := by
  have h_eval := tag_nSteps_prepend_eval ts cfg [] n 0 h
  have h_zero : Tag.eval ts ([] : TagConfig k) 0 = some [] := by
    simp [Tag.eval, tagHalted]
  rw [Nat.zero_add] at h_eval
  rw [h_eval, h_zero]
/-- **`eval_eq_nil_implies_tagNSteps_eq_nil_le` (iter 544)**:
    converse of iter 543 — an eval-based witness `Tag.eval cfg fuel
    = some []` extracts a discrete-step witness at some `n ≤ fuel`.
    The discrete count `n` may be strictly less than `fuel` because
    `eval` halts early once a halted config is reached.  Proof:
    induction on `fuel` with case-split on `tagHalted cfg`. -/
theorem eval_eq_nil_implies_tagNSteps_eq_nil_le {k : Nat} (ts : Tag k)
    (cfg : TagConfig k) (fuel : Nat)
    (h : Tag.eval ts cfg fuel = some []) :
    ∃ n, n ≤ fuel ∧ tagNSteps ts cfg n = some [] := by
  induction fuel generalizing cfg with
  | zero =>
    -- eval cfg 0 = if tagHalted cfg then some cfg else none = some []
    -- so tagHalted cfg = true and cfg = []
    simp [Tag.eval] at h
    obtain ⟨_, h_eq⟩ := h
    refine ⟨0, Nat.le_refl 0, ?_⟩
    show some cfg = some []
    rw [h_eq]
  | succ m ih =>
    by_cases h_halt : tagHalted cfg = true
    · rw [Tag.eval_halted ts cfg (m + 1) h_halt] at h
      injection h with h_eq
      refine ⟨0, Nat.zero_le _, ?_⟩
      show some cfg = some []
      rw [h_eq]
    · have h_nh : tagHalted cfg = false := by
        cases h_eq : tagHalted cfg with
        | true => exact absurd h_eq h_halt
        | false => rfl
      cases h_step : ts.step cfg with
      | none =>
        have h_halt_true := (Tag.step_none_iff_halted ts cfg).mp h_step
        rw [h_halt_true] at h_nh; cases h_nh
      | some cfg' =>
        rw [Tag.eval_step ts cfg cfg' m h_nh h_step] at h
        obtain ⟨n', h_le, h_n'⟩ := ih cfg' h
        refine ⟨n' + 1, by omega, ?_⟩
        show (match ts.step cfg with
              | none => none
              | some c => tagNSteps ts c n') = some []
        rw [h_step]; exact h_n'

-- ============================================================================
-- CTS halt-induction (iter 545; extracted in refactor)
-- ============================================================================

/-- CTS step ↔ halted analog of `Tag.step_none_iff_halted`. -/
theorem CTS_step_none_iff_halted (cts : CTS) (cfg : CTSConfig) :
    cts.step cfg = none ↔ ctsHalted cfg = true := by
  cases h_data : cfg.data with
  | nil => simp [CTS.step, h_data, ctsHalted, List.isEmpty]
  | cons head rest => simp [CTS.step, h_data, ctsHalted, List.isEmpty]

/-- **`CTS_Halts_induction` (iter 545)**: CTS analog of iter 528 —
    strong induction principle over halting CTS configs.  Any
    property `P` that holds on halted configs (data = []) and is
    preserved backwards through one step holds on every halting
    cfg.  Proof: induction on the fuel witnessing `cts.Halts cfg`,
    using `CTS_step_none_iff_halted` to dispatch the dead
    `step = none` branch. -/
theorem CTS_Halts_induction (cts : CTS) (P : CTSConfig → Prop)
    (h_halt : ∀ cfg, ctsHalted cfg = true → P cfg)
    (h_back : ∀ cfg cfg', cts.step cfg = some cfg' →
              cts.Halts cfg' → P cfg' → P cfg)
    (cfg : CTSConfig) (h : cts.Halts cfg) : P cfg := by
  obtain ⟨fuel, result, h_eval⟩ := h
  induction fuel generalizing cfg with
  | zero =>
    simp [CTS.eval] at h_eval
    obtain ⟨h_halted, _⟩ := h_eval
    exact h_halt cfg h_halted
  | succ m ih =>
    by_cases h_halted : ctsHalted cfg = true
    · exact h_halt cfg h_halted
    · have h_nh : ctsHalted cfg = false := by
        cases h_eq : ctsHalted cfg with
        | true => exact absurd h_eq h_halted
        | false => rfl
      cases h_step : cts.step cfg with
      | none =>
        have h_halt_true := (CTS_step_none_iff_halted cts cfg).mp h_step
        rw [h_halt_true] at h_nh; cases h_nh
      | some cfg' =>
        have h_eval_step :
            cts.eval cfg (m + 1) = cts.eval cfg' m := by
          show (if ctsHalted cfg then some cfg
                else match cts.step cfg with
                  | none => some cfg
                  | some c' => cts.eval c' m) = cts.eval cfg' m
          rw [if_neg (by rw [h_nh]; decide), h_step]
        rw [h_eval_step] at h_eval
        have h_he' : cts.Halts cfg' := ⟨m, result, h_eval⟩
        exact h_back cfg cfg' h_step h_he' (ih cfg' h_eval)

-- ============================================================================
-- CTS nSteps succ unfold/decompose (extracted in refactor)
-- ============================================================================

/-- Helper: `CTS.nSteps cts cfg (n+1)` unfolds to the match. -/
theorem CTS_nSteps_succ_unfold (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    cts.nSteps cfg (n + 1)
    = match cts.step cfg with
      | none => none
      | some cfg' => cts.nSteps cfg' n := rfl

/-- **CTS nSteps succ decomposition**: `cts.nSteps cfg (n+1) = some result`
    iff there's an intermediate `result'` with `cts.nSteps cfg n = some result'`
    and `cts.step result' = some result`.  Building block for the inductive
    case of `ctsToSystem5_emulates_with_budget`. -/
theorem CTS_nSteps_succ_decompose (cts : CTS) (cfg result : CTSConfig) (n : Nat)
    (h : cts.nSteps cfg (n + 1) = some result) :
    ∃ result', cts.nSteps cfg n = some result' ∧ cts.step result' = some result := by
  induction n generalizing cfg with
  | zero =>
    refine ⟨cfg, rfl, ?_⟩
    rw [CTS_nSteps_succ_unfold] at h
    cases h_step : cts.step cfg with
    | none => rw [h_step] at h; cases h
    | some r =>
      rw [h_step] at h
      simp [CTS.nSteps] at h
      rw [h]
  | succ n ih =>
    rw [CTS_nSteps_succ_unfold] at h
    cases h_step : cts.step cfg with
    | none => rw [h_step] at h; cases h
    | some cfg' =>
      rw [h_step] at h
      simp at h
      obtain ⟨result', h_nsteps, h_last⟩ := ih cfg' h
      refine ⟨result', ?_, h_last⟩
      rw [CTS_nSteps_succ_unfold, h_step]
      exact h_nsteps

-- ============================================================================
-- CTS halt-related nSteps cluster (extracted in refactor)
-- ============================================================================

/-- Once halted, CTS stays halted: `nSteps cfg (n+1) = none` for any
    halted `cfg` (since `step cfg = none` and propagates). -/
theorem ctsHalted_nSteps_succ_eq_none (cts : CTS) (cfg : CTSConfig) (n : Nat)
    (h : ctsHalted cfg = true) :
    cts.nSteps cfg (n + 1) = none := by
  rw [CTS_nSteps_succ_unfold]
  have h_step : cts.step cfg = none := (CTS_step_none_iff_halted cts cfg).mpr h
  rw [h_step]

theorem ctsHalted_nSteps_eq_none (cts : CTS) (cfg : CTSConfig) (n : Nat)
    (h_halt : ctsHalted cfg = true) (h_n : 1 ≤ n) :
    cts.nSteps cfg n = none := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ctsHalted_nSteps_succ_eq_none cts cfg m h_halt

/-- **Halt-decomposition**: if `cts.nSteps cfg n = none`, then some
    intermediate state at step `k < n` is halted.  Useful for connecting
    "CTS halts" to "CTS reaches a halted intermediate state", which in
    turn is needed for halting-preservation arguments through the
    encoder. -/
theorem CTS_nSteps_none_decompose (cts : CTS) (cfg : CTSConfig) (n : Nat)
    (h : cts.nSteps cfg n = none) :
    ∃ k < n, ∃ cfg', cts.nSteps cfg k = some cfg' ∧ ctsHalted cfg' = true := by
  induction n generalizing cfg with
  | zero => simp [CTS.nSteps] at h
  | succ m ih =>
    rw [CTS_nSteps_succ_unfold] at h
    by_cases h_halt_cfg : ctsHalted cfg = true
    · refine ⟨0, by omega, cfg, ?_, h_halt_cfg⟩
      rfl
    · have h_step_some : ∃ cfg', cts.step cfg = some cfg' := by
        cases h_step : cts.step cfg with
        | none =>
          exact absurd ((CTS_step_none_iff_halted cts cfg).mp h_step) h_halt_cfg
        | some cfg' => exact ⟨cfg', rfl⟩
      obtain ⟨cfg', h_step_eq⟩ := h_step_some
      rw [h_step_eq] at h
      simp at h
      obtain ⟨k', h_k', cfg_h, h_n', h_halt⟩ := ih cfg' h
      refine ⟨k' + 1, by omega, cfg_h, ?_, h_halt⟩
      rw [CTS_nSteps_succ_unfold, h_step_eq]
      exact h_n'

/-- **Reverse direction**: if CTS reaches a halted intermediate state at
    step `k`, then `nSteps cfg (k+1) = none`. -/
theorem CTS_nSteps_none_of_reaches_halted
    (cts : CTS) (cfg cfg' : CTSConfig) (k : Nat)
    (h_n : cts.nSteps cfg k = some cfg') (h_halt : ctsHalted cfg' = true) :
    cts.nSteps cfg (k + 1) = none := by
  rw [← CTS.nSteps_add cts cfg cfg' k 1 h_n]
  exact ctsHalted_nSteps_succ_eq_none cts cfg' 0 h_halt

/-- **Halts iff reaches halted state** — bidirectional CTS form. -/
theorem CTS_nSteps_halts_iff_reaches_halted (cts : CTS) (cfg : CTSConfig) :
    (∃ n, cts.nSteps cfg n = none) ↔
    ∃ k cfg', cts.nSteps cfg k = some cfg' ∧ ctsHalted cfg' = true := by
  constructor
  · intro ⟨n, h⟩
    obtain ⟨k, _, cfg', h_n, h_halt⟩ := CTS_nSteps_none_decompose cts cfg n h
    exact ⟨k, cfg', h_n, h_halt⟩
  · intro ⟨k, cfg', h_n, h_halt⟩
    exact ⟨k + 1, CTS_nSteps_none_of_reaches_halted cts cfg cfg' k h_n h_halt⟩

/-- **CTS bridge (nSteps → Halts)**: analog of `nSteps_none_imp_halts` for
    `CTS`.  Same structure: induction on n, use `CTS_step_none_iff_halted`
    to extract halted-ness when `step = none`. -/
theorem CTS_nSteps_none_imp_halts (cts : CTS) (cfg : CTSConfig) :
    (∃ n, cts.nSteps cfg n = none) → cts.Halts cfg := by
  rintro ⟨n, h⟩
  induction n generalizing cfg with
  | zero => simp [CTS.nSteps] at h
  | succ n ih =>
    rw [CTS_nSteps_succ_unfold] at h
    cases h_step : cts.step cfg with
    | none =>
      have h_halt := (CTS_step_none_iff_halted cts cfg).mp h_step
      refine ⟨0, cfg, ?_⟩
      simp [CTS.eval, h_halt]
    | some cfg' =>
      rw [h_step] at h
      simp at h
      obtain ⟨fuel, result, h_eval⟩ := ih cfg' h
      refine ⟨fuel + 1, result, ?_⟩
      have h_not_halt : ctsHalted cfg = false :=
        cts_step_some_not_halted cts cfg cfg' h_step
      simp [CTS.eval, h_not_halt, h_step, h_eval]

/-- **CTS bridge (Halts → nSteps)**: converse of `CTS_nSteps_none_imp_halts`. -/
theorem CTS_halts_imp_nSteps_none (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg → (∃ n, cts.nSteps cfg n = none) := by
  rintro ⟨fuel, result, h_eval⟩
  induction fuel generalizing cfg with
  | zero =>
    cases h_halt : ctsHalted cfg with
    | true =>
      refine ⟨1, ?_⟩
      rw [CTS_nSteps_succ_unfold, (CTS_step_none_iff_halted cts cfg).mpr h_halt]
    | false =>
      simp [CTS.eval, h_halt] at h_eval
  | succ fuel ih =>
    cases h_halt : ctsHalted cfg with
    | true =>
      refine ⟨1, ?_⟩
      rw [CTS_nSteps_succ_unfold, (CTS_step_none_iff_halted cts cfg).mpr h_halt]
    | false =>
      simp [CTS.eval, h_halt] at h_eval
      cases h_step : cts.step cfg with
      | none =>
        have h_halt' : ctsHalted cfg = true := (CTS_step_none_iff_halted cts cfg).mp h_step
        rw [h_halt'] at h_halt
        exact Bool.noConfusion h_halt
      | some cfg' =>
        rw [h_step] at h_eval
        obtain ⟨n, hn⟩ := ih cfg' h_eval
        refine ⟨n + 1, ?_⟩
        rw [CTS_nSteps_succ_unfold, h_step]
        exact hn

-- ============================================================================
-- CTS exact-step-form theorems (iters 555/557/559; extracted in refactor)
-- ============================================================================

/-- **`CTS_Halts_exact_step_form` (iter 555)**: CTS analog of iter
    553/554.  For any halting CTS cfg, there's an exact step `N`
    reaching a halted cfg (`ctsHalted = true`), and beyond `N` all
    nSteps return `none`. -/
theorem CTS_Halts_exact_step_form (cts : CTS) (cfg : CTSConfig)
    (h : cts.Halts cfg) :
    ∃ N result, cts.nSteps cfg N = some result ∧ ctsHalted result = true ∧
                ∀ k, k > N → cts.nSteps cfg k = none := by
  have h_existence := CTS_halts_imp_nSteps_none cts cfg h
  obtain ⟨N, result, h_n, h_halt⟩ :=
    (CTS_nSteps_halts_iff_reaches_halted cts cfg).mp h_existence
  refine ⟨N, result, h_n, h_halt, ?_⟩
  intro k h_k
  have h_add := CTS.nSteps_add cts cfg result N (k - N) h_n
  have h_kN : N + (k - N) = k := by omega
  rw [h_kN] at h_add
  rw [← h_add]
  exact ctsHalted_nSteps_eq_none cts result (k - N) h_halt (by omega)

/-- **`CTS_Halts_exact_step_form_unique` (iter 557)**: CTS analog
    of iter 556.  Same uniqueness argument transposed to CTS. -/
theorem CTS_Halts_exact_step_form_unique (cts : CTS) (cfg : CTSConfig)
    (N₁ N₂ : Nat) (result₁ result₂ : CTSConfig)
    (h₁_n : cts.nSteps cfg N₁ = some result₁)
    (h₁_eventual : ∀ k, k > N₁ → cts.nSteps cfg k = none)
    (h₂_n : cts.nSteps cfg N₂ = some result₂)
    (h₂_eventual : ∀ k, k > N₂ → cts.nSteps cfg k = none) :
    N₁ = N₂ := by
  rcases Nat.lt_or_ge N₁ N₂ with h_lt | h_ge
  · have h_none := h₁_eventual N₂ h_lt
    rw [h_none] at h₂_n; cases h₂_n
  · rcases Nat.lt_or_ge N₂ N₁ with h_lt' | h_ge'
    · have h_none := h₂_eventual N₁ h_lt'
      rw [h_none] at h₁_n; cases h₁_n
    · omega

/-- **`CTS_Halts_iff_exact_step_witness` (iter 559)**: CTS analog of
    iter 558. -/
theorem CTS_Halts_iff_exact_step_witness (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔
    ∃ N result, cts.nSteps cfg N = some result ∧ ctsHalted result = true ∧
                ∀ k, k > N → cts.nSteps cfg k = none := by
  constructor
  · exact CTS_Halts_exact_step_form cts cfg
  · rintro ⟨N, result, h_n, h_halt, _⟩
    exact CTS_nSteps_none_imp_halts cts cfg
      ⟨N + 1, CTS_nSteps_none_of_reaches_halted cts cfg result N h_n h_halt⟩

/-- **`haltsEmpty_iff_exact_step_witness` (iter 560)**: Tag-side
    biconditional analog of iter 558/559.  `HaltsEmpty cfg ↔` an
    exact-step witness reaching `[]` exists with eventually-none
    beyond.  Forward direction: iter 529 (existence) + iter 531
    (post-nil-is-none).  Reverse: from the existence-of-N witness,
    by iter 530 reverse direction, HaltsEmpty.  Combined with iter
    532's uniqueness, this gives a complete characterization at the
    Tag layer matching iter 558/559's BiTM/CTS forms. -/
theorem haltsEmpty_iff_exact_step_witness {k : Nat} (ts : Tag k) (cfg : TagConfig k) :
    ts.HaltsEmpty cfg ↔
    ∃ N, tagNSteps ts cfg N = some [] ∧
         ∀ j, j > N → tagNSteps ts cfg j = none := by
  constructor
  · intro h
    obtain ⟨N, h_n⟩ := haltsEmpty_implies_tagNSteps_eq_nil ts cfg h
    refine ⟨N, h_n, ?_⟩
    intro j h_j
    have h_split : j = N + ((j - N - 1) + 1) := by omega
    rw [h_split]
    exact tagNSteps_after_nil ts cfg N (j - N - 1) h_n
  · rintro ⟨N, h_n, _⟩
    exact tagNSteps_eq_nil_implies_haltsEmpty ts cfg N h_n

-- ============================================================================
-- CTS eval-side lemmas (extracted in refactor)
-- ============================================================================

/-- **General `cts.eval` returns `some` only with halted result**:
    when `eval cfg fuel = some result`, the result is always halted
    (`ctsHalted result = true`).  This is general to all CTS, not
    just AllEmptyAppendants.  Induction on fuel with case analysis
    on `ctsHalted cfg` and `cts.step cfg`; the `step = none` else
    branch returns `some cfg`, where `cfg` must be halted by
    `CTS_step_none_iff_halted`. -/
theorem CTS_eval_some_imp_halted (cts : CTS) (cfg : CTSConfig)
    (fuel : Nat) (result : CTSConfig)
    (h : cts.eval cfg fuel = some result) :
    ctsHalted result = true := by
  induction fuel generalizing cfg with
  | zero =>
    simp [CTS.eval] at h
    obtain ⟨h_halt, h_eq⟩ := h
    rw [← h_eq]; exact h_halt
  | succ k ih =>
    simp [CTS.eval] at h
    by_cases h_halt : ctsHalted cfg = true
    · rw [if_pos h_halt] at h
      injection h with h_eq
      rw [← h_eq]; exact h_halt
    · rw [if_neg h_halt] at h
      cases h_step : cts.step cfg with
      | none =>
        rw [h_step] at h
        simp at h
        rw [← h]
        exact (CTS_step_none_iff_halted cts cfg).mp h_step
      | some cfg' =>
        rw [h_step] at h
        simp at h
        exact ih cfg' h

/-- **`cts.eval` returns `some result` only with empty data**: direct
    corollary of iter 360 — `ctsHalted result = true` ⟺ `result.data
    = []` (via `List.isEmpty_iff`). -/
theorem CTS_eval_some_data_empty (cts : CTS) (cfg : CTSConfig)
    (fuel : Nat) (result : CTSConfig)
    (h : cts.eval cfg fuel = some result) :
    result.data = [] := by
  have h_halt := CTS_eval_some_imp_halted cts cfg fuel result h
  unfold ctsHalted at h_halt
  exact List.isEmpty_iff.mp h_halt

/-- **`cts.eval` on a halted cfg returns the cfg itself**: regardless
    of fuel, eval immediately returns `some cfg`.  Both fuel=0 and
    fuel=k+1 branches of `eval` short-circuit on `ctsHalted cfg`. -/
theorem CTS_eval_halted_self (cts : CTS) (cfg : CTSConfig)
    (h : ctsHalted cfg = true) (fuel : Nat) :
    cts.eval cfg fuel = some cfg := by
  cases fuel with
  | zero => simp [CTS.eval, h]
  | succ k => simp [CTS.eval, h]

/-- **CTS Halts iff `eval` succeeds with empty data**: combines
    `Halts` def with iter 361's `eval-some-implies-data-empty`.  The
    enriched `result.data = []` constraint is automatic. -/
theorem CTS_Halts_iff_eval_data_empty (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ∃ fuel result, cts.eval cfg fuel = some result
                                    ∧ result.data = [] := by
  constructor
  · intro ⟨fuel, result, h_eval⟩
    exact ⟨fuel, result, h_eval, CTS_eval_some_data_empty cts cfg fuel result h_eval⟩
  · intro ⟨fuel, result, h_eval, _⟩
    exact ⟨fuel, result, h_eval⟩

/-- **CTS `eval` fuel-succ monotonicity**: if `eval cfg fuel = some
    result`, then `eval cfg (fuel + 1) = some result`. -/
theorem CTS_eval_fuel_succ (cts : CTS) (cfg : CTSConfig) (fuel : Nat)
    (result : CTSConfig) (h : cts.eval cfg fuel = some result) :
    cts.eval cfg (fuel + 1) = some result := by
  induction fuel generalizing cfg with
  | zero =>
    simp [CTS.eval] at h
    obtain ⟨h_halt, h_eq⟩ := h
    rw [← h_eq]
    exact CTS_eval_halted_self cts cfg h_halt 1
  | succ k ih =>
    by_cases h_halt : ctsHalted cfg = true
    · simp [CTS.eval, h_halt] at h
      rw [← h]
      exact CTS_eval_halted_self cts cfg h_halt _
    · simp [CTS.eval, h_halt] at h
      cases h_step : cts.step cfg with
      | none =>
        rw [h_step] at h
        simp at h
        rw [← h]
        have h_state : ctsHalted cfg = true :=
          (CTS_step_none_iff_halted cts cfg).mp h_step
        exact absurd h_state h_halt
      | some cfg' =>
        rw [h_step] at h
        simp [CTS.eval, h_halt, h_step]
        exact ih cfg' h

/-- **CTS `eval` fuel monotonicity (multi-step)**. -/
theorem CTS_eval_fuel_le (cts : CTS) (cfg : CTSConfig)
    (fuel fuel' : Nat) (h_le : fuel ≤ fuel') (result : CTSConfig)
    (h : cts.eval cfg fuel = some result) :
    cts.eval cfg fuel' = some result := by
  obtain ⟨k, h_k⟩ : ∃ k, fuel' = fuel + k := ⟨fuel' - fuel, by omega⟩
  rw [h_k]
  clear h_k h_le fuel'
  induction k with
  | zero => exact h
  | succ j ih =>
    rw [show fuel + (j + 1) = (fuel + j) + 1 from by omega]
    exact CTS_eval_fuel_succ cts cfg (fuel + j) result ih

/-- **`ctsHalted` iff `data = []`**. -/
theorem ctsHalted_iff_data_empty (cfg : CTSConfig) :
    ctsHalted cfg = true ↔ cfg.data = [] := by
  unfold ctsHalted
  exact List.isEmpty_iff

/-- **CTS `Halts` on empty-data config**: any cfg with `data = []`
    halts (it's already halted, fuel = 0 suffices). -/
theorem CTS_Halts_empty_data (cts : CTS) (phase : Nat) :
    cts.Halts { data := [], phase := phase } := by
  refine ⟨0, { data := [], phase := phase }, ?_⟩
  simp [CTS.eval, ctsHalted, List.isEmpty]

/-- **CTS Halts implies eval stabilizes for large fuel**: for any
    halting cfg, `∃ fuel result, ∀ fuel' ≥ fuel, eval cfg fuel' =
    some result`. -/
theorem CTS_Halts_eval_stable (cts : CTS) (cfg : CTSConfig)
    (h : cts.Halts cfg) :
    ∃ fuel result, ∀ fuel' ≥ fuel, cts.eval cfg fuel' = some result := by
  obtain ⟨fuel, result, h_eval⟩ := h
  exact ⟨fuel, result, fun fuel' h_le =>
    CTS_eval_fuel_le cts cfg fuel fuel' h_le result h_eval⟩

/-- **CTS `nSteps` reaching a halted state produces matching `eval`**:
    if `nSteps cfg n = some result` and `ctsHalted result = true`,
    then `eval cfg n = some result`. -/
theorem CTS_nSteps_some_halted_imp_eval
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (result : CTSConfig)
    (h_n : cts.nSteps cfg n = some result) (h_halt : ctsHalted result = true) :
    cts.eval cfg n = some result := by
  induction n generalizing cfg with
  | zero =>
    rw [CTS.nSteps_zero] at h_n
    injection h_n with h_eq
    rw [← h_eq]
    rw [← h_eq] at h_halt
    exact CTS_eval_halted_self cts cfg h_halt 0
  | succ k ih =>
    rw [CTS_nSteps_succ_unfold] at h_n
    cases h_step : cts.step cfg with
    | none => rw [h_step] at h_n; cases h_n
    | some cfg₁ =>
      rw [h_step] at h_n
      have h_not_halt : ctsHalted cfg ≠ true := by
        intro h_halt_cfg
        have := (CTS_step_none_iff_halted cts cfg).mpr h_halt_cfg
        rw [this] at h_step
        cases h_step
      simp [CTS.eval, h_not_halt, h_step]
      exact ih cfg₁ h_n

/-- **`cts.Halts` iff `nSteps` reaches a halted state**. -/
theorem CTS_Halts_iff_nSteps_reaches_halted (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ∃ k cfg', cts.nSteps cfg k = some cfg' ∧ ctsHalted cfg' = true := by
  constructor
  · intro h_halts
    exact (CTS_nSteps_halts_iff_reaches_halted cts cfg).mp
      (CTS_halts_imp_nSteps_none cts cfg h_halts)
  · intro ⟨k, cfg', h_n, h_halt⟩
    apply CTS_nSteps_none_imp_halts
    exact (CTS_nSteps_halts_iff_reaches_halted cts cfg).mpr ⟨k, cfg', h_n, h_halt⟩

/-- **`CTS_eval_some_imp_nSteps_le` (iter 563)**: an eval-success
    witness `cts.eval cfg fuel = some result` extracts a
    discrete-step witness at some `n ≤ fuel`.  The discrete count
    may be strictly less because `eval` halts early on already-
    halted configs.  Direct fuel induction with case-split on
    `ctsHalted cfg`. -/
theorem CTS_eval_some_imp_nSteps_le (cts : CTS) (cfg : CTSConfig) (fuel : Nat)
    (result : CTSConfig) (h : cts.eval cfg fuel = some result) :
    ∃ n, n ≤ fuel ∧ cts.nSteps cfg n = some result := by
  induction fuel generalizing cfg with
  | zero =>
    simp [CTS.eval] at h
    obtain ⟨_, h_eq⟩ := h
    refine ⟨0, Nat.le_refl 0, ?_⟩
    show some cfg = some result
    rw [h_eq]
  | succ m ih =>
    by_cases h_halt : ctsHalted cfg = true
    · simp [CTS.eval, h_halt] at h
      refine ⟨0, Nat.zero_le _, ?_⟩
      show some cfg = some result
      rw [h]
    · have h_nh : ctsHalted cfg = false := by
        cases h_eq : ctsHalted cfg with
        | true => exact absurd h_eq h_halt
        | false => rfl
      cases h_step : cts.step cfg with
      | none =>
        have h_state := (CTS_step_none_iff_halted cts cfg).mp h_step
        rw [h_state] at h_nh; cases h_nh
      | some cfg' =>
        have h_eval' : cts.eval cfg' m = some result := by
          simp [CTS.eval, h_nh, h_step] at h
          exact h
        obtain ⟨n', h_le, h_n'⟩ := ih cfg' h_eval'
        refine ⟨n' + 1, by omega, ?_⟩
        rw [CTS_nSteps_succ_unfold, h_step]
        exact h_n'

-- ============================================================================
-- CTS Halts step/nSteps propagation cluster (extracted in refactor)
-- ============================================================================

/-- **CTS `Halts` step-predecessor**: if `cts.step cfg = some cfg'`
    and `cts.Halts cfg'`, then `cts.Halts cfg`.  Backward Halts-
    propagation under stepping.  Useful for "if a successor halts,
    so does the predecessor". -/
theorem CTS_Halts_step_pred
    (cts : CTS) (cfg cfg' : CTSConfig) (h_step : cts.step cfg = some cfg')
    (h : cts.Halts cfg') :
    cts.Halts cfg := by
  obtain ⟨fuel, res, h_eval⟩ := h
  refine ⟨fuel + 1, res, ?_⟩
  by_cases h_halt : ctsHalted cfg = true
  · simp [CTS.eval, h_halt]
    exfalso
    have := (CTS_step_none_iff_halted cts cfg).mpr h_halt
    rw [this] at h_step
    cases h_step
  · simp [CTS.eval, h_halt, h_step]
    exact h_eval

/-- **CTS `Halts` step-successor**: forward Halts-propagation. -/
theorem CTS_Halts_step_succ
    (cts : CTS) (cfg cfg' : CTSConfig) (h_step : cts.step cfg = some cfg')
    (h : cts.Halts cfg) :
    cts.Halts cfg' := by
  obtain ⟨fuel, res, h_eval⟩ := h
  have h_not_halt : ctsHalted cfg ≠ true := by
    intro h_halt
    have := (CTS_step_none_iff_halted cts cfg).mpr h_halt
    rw [this] at h_step
    cases h_step
  cases fuel with
  | zero =>
    simp [CTS.eval] at h_eval
    obtain ⟨h_halt, _⟩ := h_eval
    exact absurd h_halt h_not_halt
  | succ k =>
    simp [CTS.eval, h_not_halt, h_step] at h_eval
    exact ⟨k, res, h_eval⟩

/-- **CTS `Halts` step iff**: combines pred + succ. -/
theorem CTS_Halts_step_iff
    (cts : CTS) (cfg cfg' : CTSConfig) (h_step : cts.step cfg = some cfg') :
    cts.Halts cfg ↔ cts.Halts cfg' :=
  ⟨CTS_Halts_step_succ cts cfg cfg' h_step,
   CTS_Halts_step_pred cts cfg cfg' h_step⟩

/-- **CTS `Halts` propagates under nSteps**: forward nSteps-Halts
    propagation. -/
theorem CTS_Halts_nSteps_succ
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (h : cts.Halts cfg)
    (result : CTSConfig) (h_n : cts.nSteps cfg n = some result) :
    cts.Halts result := by
  induction n generalizing cfg with
  | zero =>
    rw [CTS.nSteps_zero] at h_n
    injection h_n with h_eq
    rw [← h_eq]
    exact h
  | succ k ih =>
    rw [CTS_nSteps_succ_unfold] at h_n
    cases h_step : cts.step cfg with
    | none => rw [h_step] at h_n; cases h_n
    | some cfg₁ =>
      rw [h_step] at h_n
      have h_halts₁ := CTS_Halts_step_succ cts cfg cfg₁ h_step h
      exact ih cfg₁ h_halts₁ h_n

/-- **CTS `Halts` predecessor under nSteps**. -/
theorem CTS_Halts_nSteps_pred
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (result : CTSConfig)
    (h_n : cts.nSteps cfg n = some result) (h : cts.Halts result) :
    cts.Halts cfg := by
  induction n generalizing cfg with
  | zero =>
    rw [CTS.nSteps_zero] at h_n
    injection h_n with h_eq
    rw [h_eq]
    exact h
  | succ k ih =>
    rw [CTS_nSteps_succ_unfold] at h_n
    cases h_step : cts.step cfg with
    | none => rw [h_step] at h_n; cases h_n
    | some cfg₁ =>
      rw [h_step] at h_n
      have h_halts₁ := ih cfg₁ h_n
      exact CTS_Halts_step_pred cts cfg cfg₁ h_step h_halts₁

/-- **CTS `Halts` iff under nSteps**. -/
theorem CTS_Halts_nSteps_iff
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (result : CTSConfig)
    (h_n : cts.nSteps cfg n = some result) :
    cts.Halts cfg ↔ cts.Halts result :=
  ⟨fun h => CTS_Halts_nSteps_succ cts cfg n h result h_n,
   CTS_Halts_nSteps_pred cts cfg n result h_n⟩

/-- **`haltsEmpty_eval_exact_step_form` (iter 567)**: Tag analog of
    iter 566.  An eval-success witness `Tag.eval cfg fuel = some []`
    produces an exact-step witness with `N ≤ fuel`.  Combines iter
    544 (`eval_eq_nil_implies_tagNSteps_eq_nil_le`) with iter 531
    (`tagNSteps_after_nil`). -/
theorem haltsEmpty_eval_exact_step_form {k : Nat} (ts : Tag k)
    (cfg : TagConfig k) (fuel : Nat)
    (h : Tag.eval ts cfg fuel = some []) :
    ∃ N, N ≤ fuel ∧ tagNSteps ts cfg N = some [] ∧
         ∀ j, j > N → tagNSteps ts cfg j = none := by
  obtain ⟨N, h_le, h_n⟩ := eval_eq_nil_implies_tagNSteps_eq_nil_le ts cfg fuel h
  refine ⟨N, h_le, h_n, ?_⟩
  intro j h_j
  have h_split : j = N + ((j - N - 1) + 1) := by omega
  rw [h_split]
  exact tagNSteps_after_nil ts cfg N (j - N - 1) h_n

/-- **CTS `eval` produces an exact `nSteps` witness**: if
    `cts.eval cfg fuel = some result`, then there exists `k ≤ fuel`
    such that `cts.nSteps cfg k = some result` and `result` is
    halted. -/
theorem CTS_eval_some_imp_exists_nSteps
    (cts : CTS) (cfg : CTSConfig) (fuel : Nat) (result : CTSConfig)
    (h : cts.eval cfg fuel = some result) :
    ∃ k, k ≤ fuel ∧ cts.nSteps cfg k = some result ∧ ctsHalted result = true := by
  induction fuel generalizing cfg with
  | zero =>
    cases h_halt : ctsHalted cfg with
    | true =>
      simp [CTS.eval, h_halt] at h
      refine ⟨0, Nat.le_refl _, ?_, ?_⟩
      · rw [CTS.nSteps_zero, h]
      · rw [← h]; exact h_halt
    | false =>
      simp [CTS.eval, h_halt] at h
  | succ fuel ih =>
    cases h_halt : ctsHalted cfg with
    | true =>
      simp [CTS.eval, h_halt] at h
      refine ⟨0, Nat.zero_le _, ?_, ?_⟩
      · rw [CTS.nSteps_zero, h]
      · rw [← h]; exact h_halt
    | false =>
      cases h_step : cts.step cfg with
      | none =>
        have h_h : ctsHalted cfg = true :=
          (CTS_step_none_iff_halted cts cfg).mp h_step
        rw [h_h] at h_halt
        exact Bool.noConfusion h_halt
      | some cfg' =>
        simp [CTS.eval, h_halt, h_step] at h
        obtain ⟨k, h_le, h_n, h_halt_r⟩ := ih cfg' h
        refine ⟨k + 1, Nat.succ_le_succ h_le, ?_, h_halt_r⟩
        rw [CTS_nSteps_succ_unfold, h_step]
        exact h_n

/-- **CTS `nSteps`-witness gives `eval`**. -/
theorem CTS_exists_nSteps_some_imp_eval
    (cts : CTS) (cfg : CTSConfig) (fuel : Nat) (result : CTSConfig)
    (h : ∃ k, k ≤ fuel ∧ cts.nSteps cfg k = some result ∧ ctsHalted result = true) :
    cts.eval cfg fuel = some result := by
  obtain ⟨k, h_le, h_n, h_halt⟩ := h
  have h_eval := CTS_nSteps_some_halted_imp_eval cts cfg k result h_n h_halt
  exact CTS_eval_fuel_le cts cfg k fuel h_le result h_eval

/-- **CTS `eval`/`nSteps` biconditional**. -/
theorem CTS_eval_some_iff_exists_nSteps
    (cts : CTS) (cfg : CTSConfig) (fuel : Nat) (result : CTSConfig) :
    cts.eval cfg fuel = some result ↔
    ∃ k, k ≤ fuel ∧ cts.nSteps cfg k = some result ∧ ctsHalted result = true :=
  ⟨CTS_eval_some_imp_exists_nSteps cts cfg fuel result,
   CTS_exists_nSteps_some_imp_eval cts cfg fuel result⟩

/-- **`CTS_eval_result_unique` (iter 569)**: CTS analog of iter 568.
    Any two eval witnesses for the same cfg agree on the result.
    Proof extends both to `max f₁ f₂` via `CTS_eval_fuel_le`. -/
theorem CTS_eval_result_unique (cts : CTS) (cfg : CTSConfig)
    (f₁ f₂ : Nat) (r₁ r₂ : CTSConfig)
    (h₁ : cts.eval cfg f₁ = some r₁) (h₂ : cts.eval cfg f₂ = some r₂) :
    r₁ = r₂ := by
  have h_le1 : f₁ ≤ max f₁ f₂ := Nat.le_max_left f₁ f₂
  have h_le2 : f₂ ≤ max f₁ f₂ := Nat.le_max_right f₁ f₂
  have h₁' := CTS_eval_fuel_le cts cfg f₁ (max f₁ f₂) h_le1 r₁ h₁
  have h₂' := CTS_eval_fuel_le cts cfg f₂ (max f₁ f₂) h_le2 r₂ h₂
  rw [h₁'] at h₂'
  injection h₂'

/-- **CTS `nSteps`-none succ propagation**: once nSteps reaches `none`
    at step `n`, the next step is also `none`. -/
theorem CTS_nSteps_none_succ
    (cts : CTS) (cfg : CTSConfig) (n : Nat)
    (h : cts.nSteps cfg n = none) :
    cts.nSteps cfg (n + 1) = none := by
  induction n generalizing cfg with
  | zero => simp [CTS.nSteps] at h
  | succ k ih =>
    rw [CTS_nSteps_succ_unfold] at h
    rw [CTS_nSteps_succ_unfold]
    cases h_step : cts.step cfg with
    | none => rfl
    | some cfg' =>
      rw [h_step] at h
      simp at h
      exact ih cfg' h

/-- **CTS `nSteps`-none monotone propagation**. -/
theorem CTS_nSteps_none_propagate
    (cts : CTS) (cfg : CTSConfig) (n m : Nat)
    (h_le : n ≤ m) (h_n : cts.nSteps cfg n = none) :
    cts.nSteps cfg m = none := by
  obtain ⟨k, h_k⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  rw [h_k]
  clear h_k h_le m
  induction k with
  | zero => exact h_n
  | succ j ih =>
    rw [show n + (j + 1) = (n + j) + 1 from by omega]
    exact CTS_nSteps_none_succ cts cfg (n + j) ih

/-- **CTS `nSteps` split**: if `cts.nSteps cfg (n + m) = some result`,
    there is an intermediate `mid` such that `cts.nSteps cfg n = some
    mid ∧ cts.nSteps mid m = some result`. -/
theorem CTS_nSteps_some_split (cts : CTS) (cfg : CTSConfig)
    (n m : Nat) (result : CTSConfig)
    (h : cts.nSteps cfg (n + m) = some result) :
    ∃ mid, cts.nSteps cfg n = some mid ∧ cts.nSteps mid m = some result := by
  induction n generalizing cfg with
  | zero =>
    rw [Nat.zero_add] at h
    exact ⟨cfg, rfl, h⟩
  | succ n ih =>
    rw [Nat.succ_add, CTS_nSteps_succ_unfold] at h
    cases h_step : cts.step cfg with
    | none => rw [h_step] at h; cases h
    | some cfg₁ =>
      rw [h_step] at h
      obtain ⟨mid, h_mid, h_rest⟩ := ih cfg₁ h
      refine ⟨mid, ?_, h_rest⟩
      rw [CTS_nSteps_succ_unfold, h_step]
      exact h_mid

/-- **CTS `nSteps` compose**: converse of `CTS_nSteps_some_split`. -/
theorem CTS_nSteps_some_compose (cts : CTS) (cfg mid : CTSConfig)
    (n m : Nat) (result : CTSConfig)
    (h_n : cts.nSteps cfg n = some mid)
    (h_m : cts.nSteps mid m = some result) :
    cts.nSteps cfg (n + m) = some result := by
  have h_add := CTS.nSteps_add cts cfg mid n m h_n
  rw [h_m] at h_add
  exact h_add.symm

/-- **CTS step-or-halted dichotomy**: any CTS cfg either is halted
    (data empty) or admits a step. -/
theorem cts_step_or_halted (cts : CTS) (cfg : CTSConfig) :
    ctsHalted cfg = true ∨ ∃ cfg', cts.step cfg = some cfg' := by
  cases h_step : cts.step cfg with
  | none => left; exact (CTS_step_none_iff_halted cts cfg).mp h_step
  | some cfg' => right; exact ⟨cfg', rfl⟩

/-- **CTS `Halts` step decomposition**: any halting CTS cfg is
    either already halted or steps to another halting cfg. -/
theorem CTS_Halts_step_decompose
    (cts : CTS) (cfg : CTSConfig) (h : cts.Halts cfg) :
    ctsHalted cfg = true ∨ ∃ cfg', cts.step cfg = some cfg' ∧ cts.Halts cfg' := by
  rcases cts_step_or_halted cts cfg with h_halt | ⟨cfg', h_step⟩
  · left; exact h_halt
  · right
    exact ⟨cfg', h_step, (CTS_Halts_step_iff cts cfg cfg' h_step).mp h⟩

/-- **CTS `Halts` step decomposition non-halted version**. -/
theorem CTS_Halts_step_decompose_non_halted
    (cts : CTS) (cfg : CTSConfig) (h_not_halted : ctsHalted cfg = false)
    (h_halts : cts.Halts cfg) :
    ∃ cfg', cts.step cfg = some cfg' ∧ cts.Halts cfg' := by
  rcases CTS_Halts_step_decompose cts cfg h_halts with h_halt | h_step
  · rw [h_halt] at h_not_halted; exact absurd h_not_halted (by decide)
  · exact h_step

/-- **`CTS_Halts_iff_step_or_halted` (iter 571)**: CTS analog of
    iter 570.  `cts.Halts cfg ↔ ctsHalted cfg = true ∨
    (∃ cfg', cts.step cfg = some cfg' ∧ cts.Halts cfg')`.
    Forward direction is `CTS_Halts_step_decompose`; reverse uses
    `CTS_Halts_empty_data` (halted always halts) and
    `CTS_Halts_step_pred` (predecessor of halting cfg halts). -/
theorem CTS_Halts_iff_step_or_halted (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ctsHalted cfg = true ∨
                    ∃ cfg', cts.step cfg = some cfg' ∧ cts.Halts cfg' := by
  constructor
  · exact CTS_Halts_step_decompose cts cfg
  · rintro (h_halted | ⟨cfg', h_step, h_halts⟩)
    · have h_data : cfg.data = [] := (ctsHalted_iff_data_empty cfg).mp h_halted
      have h_eq : cfg = { data := [], phase := cfg.phase } := by
        cases cfg
        simp at h_data ⊢
        exact h_data
      rw [h_eq]
      exact CTS_Halts_empty_data cts cfg.phase
    · exact CTS_Halts_step_pred cts cfg cfg' h_step h_halts

/-- **CTS step preserves not-Halts**: contrapositive of
    `_Halts_step_pred`. -/
theorem CTS_not_Halts_step_succ
    (cts : CTS) (cfg cfg' : CTSConfig)
    (h_step : cts.step cfg = some cfg') (h : ¬ cts.Halts cfg) :
    ¬ cts.Halts cfg' :=
  fun h_halt' => h (CTS_Halts_step_pred cts cfg cfg' h_step h_halt')

/-- **CTS nSteps preserves not-Halts**. -/
theorem CTS_not_Halts_nSteps_succ
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (r : CTSConfig)
    (h_n : cts.nSteps cfg n = some r) (h : ¬ cts.Halts cfg) :
    ¬ cts.Halts r :=
  fun h_halt' => h (CTS_Halts_nSteps_pred cts cfg n r h_n h_halt')

/-- **`nSteps`-some monotonicity (CTS)**: if `nSteps cfg n = some
    result` and `k ≤ n`, then `nSteps cfg k = some intermediate`
    for some intermediate. -/
theorem CTS_nSteps_some_le
    (cts : CTS) (cfg : CTSConfig) (k n : Nat) (h_le : k ≤ n)
    (result : CTSConfig) (h : cts.nSteps cfg n = some result) :
    ∃ intermediate, cts.nSteps cfg k = some intermediate := by
  cases h_k : cts.nSteps cfg k with
  | none =>
    have h_n := CTS_nSteps_none_propagate cts cfg k n h_le h_k
    rw [h_n] at h
    cases h
  | some intermediate => exact ⟨intermediate, rfl⟩

/-- **CTS nSteps past halt yields none**: if `cts.nSteps cfg n =
    some result` with `result` halted, then for any `k ≥ 1`,
    `cts.nSteps cfg (n + k) = none`. -/
theorem CTS_nSteps_past_halt_eq_none
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (result : CTSConfig)
    (h_n : cts.nSteps cfg n = some result) (h_halt : ctsHalted result = true)
    (k : Nat) (h_k : k ≥ 1) :
    cts.nSteps cfg (n + k) = none := by
  have h_add := CTS.nSteps_add cts cfg result n k h_n
  rw [← h_add]
  exact ctsHalted_nSteps_eq_none cts result k h_halt h_k

/-- **CTS halt-point uniqueness**: both halt counts agree, and so
    do the resulting halted states. -/
theorem CTS_nSteps_halt_unique
    (cts : CTS) (cfg : CTSConfig) (n₁ n₂ : Nat) (r₁ r₂ : CTSConfig)
    (h₁ : cts.nSteps cfg n₁ = some r₁) (h_halt₁ : ctsHalted r₁ = true)
    (h₂ : cts.nSteps cfg n₂ = some r₂) (h_halt₂ : ctsHalted r₂ = true) :
    n₁ = n₂ ∧ r₁ = r₂ := by
  rcases Nat.lt_or_ge n₁ n₂ with h_lt | h_ge
  · obtain ⟨k, hk_pos, rfl⟩ : ∃ k, k ≥ 1 ∧ n₂ = n₁ + k :=
      ⟨n₂ - n₁, by omega, by omega⟩
    rw [CTS_nSteps_past_halt_eq_none cts cfg n₁ r₁ h₁ h_halt₁ k hk_pos] at h₂
    cases h₂
  · rcases Nat.lt_or_eq_of_le h_ge with h_lt | h_eq
    · obtain ⟨k, hk_pos, rfl⟩ : ∃ k, k ≥ 1 ∧ n₁ = n₂ + k :=
        ⟨n₁ - n₂, by omega, by omega⟩
      rw [CTS_nSteps_past_halt_eq_none cts cfg n₂ r₂ h₂ h_halt₂ k hk_pos] at h₁
      cases h₁
    · subst h_eq
      rw [h₁] at h₂
      injection h₂ with h_r
      exact ⟨rfl, h_r⟩

/-- **CTS intermediate-state retrieval**: `nSteps r₁ (n₂ - n₁) =
    some r₂` when both endpoints exist. -/
theorem CTS_nSteps_intermediate
    (cts : CTS) (cfg r₁ r₂ : CTSConfig) (n₁ n₂ : Nat) (h_le : n₁ ≤ n₂)
    (h₁ : cts.nSteps cfg n₁ = some r₁) (h₂ : cts.nSteps cfg n₂ = some r₂) :
    cts.nSteps r₁ (n₂ - n₁) = some r₂ := by
  have h_add := CTS.nSteps_add cts cfg r₁ n₁ (n₂ - n₁) h₁
  have h_sum : n₁ + (n₂ - n₁) = n₂ := by omega
  rw [h_sum] at h_add
  rw [h_add, h₂]

/-- **`ctsHalted` implies `Halts`**. -/
theorem ctsHalted_imp_Halts (cts : CTS) (cfg : CTSConfig)
    (h : ctsHalted cfg = true) :
    cts.Halts cfg := by
  refine ⟨0, cfg, ?_⟩
  simp [CTS.eval, h]

/-- **CTS intermediate-state Halts retrieval**. -/
theorem CTS_nSteps_intermediate_Halts
    (cts : CTS) (cfg r₁ r₂ : CTSConfig) (n₁ n₂ : Nat) (h_le : n₁ ≤ n₂)
    (h₁ : cts.nSteps cfg n₁ = some r₁)
    (h₂ : cts.nSteps cfg n₂ = some r₂) (h_halt₂ : ctsHalted r₂ = true) :
    cts.Halts r₁ :=
  CTS_Halts_nSteps_pred cts r₁ (n₂ - n₁) r₂
    (CTS_nSteps_intermediate cts cfg r₁ r₂ n₁ n₂ h_le h₁ h₂)
    (ctsHalted_imp_Halts cts r₂ h_halt₂)

/-- **Bounded minimum-finder**: given a decidable predicate on
    `Nat`, either there is a least `k ≤ n` satisfying P (with
    minimality below k), or no `m ≤ n` satisfies P.  Replacement
    for `Nat.find` (not available without mathlib). -/
theorem find_min_or_none (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    (∃ k, k ≤ n ∧ P k ∧ ∀ m < k, ¬ P m) ∨ (∀ m ≤ n, ¬ P m) := by
  induction n with
  | zero =>
    by_cases h : P 0
    · exact Or.inl ⟨0, Nat.le_refl _, h,
        fun _ h_lt => absurd h_lt (Nat.not_lt_zero _)⟩
    · exact Or.inr (fun m h_le => by
        obtain rfl := Nat.le_zero.mp h_le; exact h)
  | succ n ih =>
    rcases ih with ⟨k, h_le, h_pk, h_min⟩ | h_none
    · exact Or.inl ⟨k, Nat.le_succ_of_le h_le, h_pk, h_min⟩
    · by_cases h : P (n + 1)
      · refine Or.inl ⟨n + 1, Nat.le_refl _, h, fun m h_lt => ?_⟩
        exact h_none m (Nat.le_of_lt_succ h_lt)
      · refine Or.inr (fun m h_le => ?_)
        rcases Nat.lt_or_eq_of_le h_le with h_lt | h_eq
        · exact h_none m (Nat.le_of_lt_succ h_lt)
        · subst h_eq; exact h

/-- **CTS Halts iff exists nSteps none**. -/
theorem CTS_Halts_iff_exists_nSteps_none
    (cts : CTS) (cfg : CTSConfig) :
    cts.Halts cfg ↔ ∃ n, cts.nSteps cfg n = none :=
  ⟨CTS_halts_imp_nSteps_none cts cfg, CTS_nSteps_none_imp_halts cts cfg⟩

/-- **CTS first nSteps-none**. -/
theorem CTS_Halts_first_none
    (cts : CTS) (cfg : CTSConfig) (h : cts.Halts cfg) :
    ∃ n, cts.nSteps cfg n = none ∧ ∀ m < n, cts.nSteps cfg m ≠ none := by
  obtain ⟨N, hN⟩ := (CTS_Halts_iff_exists_nSteps_none cts cfg).mp h
  rcases find_min_or_none (fun n => cts.nSteps cfg n = none) N with
    ⟨k, _h_le, h_pk, h_min⟩ | h_none
  · exact ⟨k, h_pk, h_min⟩
  · exact absurd hN (h_none N (Nat.le_refl _))

/-- **CTS one-step nSteps unfolds to step**. -/
theorem CTS_nSteps_one (cts : CTS) (cfg : CTSConfig) :
    cts.nSteps cfg 1 = cts.step cfg := by
  show (match cts.step cfg with
        | none => none
        | some cfg' => cts.nSteps cfg' 0) = cts.step cfg
  cases cts.step cfg <;> rfl

/-- **CTS first-none predecessor halts**. -/
theorem CTS_first_none_predecessor_halts
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (hN : cts.nSteps cfg N = none) (h_min : ∀ m < N, cts.nSteps cfg m ≠ none) :
    ∃ k, N = k + 1 ∧ ∃ r, cts.nSteps cfg k = some r ∧ ctsHalted r = true := by
  cases N with
  | zero =>
    rw [CTS.nSteps_zero] at hN
    cases hN
  | succ k =>
    refine ⟨k, rfl, ?_⟩
    cases h_k : cts.nSteps cfg k with
    | none => exact absurd h_k (h_min k (Nat.lt_succ_self k))
    | some r =>
      refine ⟨r, rfl, ?_⟩
      have h_one : cts.nSteps r 1 = none := by
        rw [CTS.nSteps_add cts cfg r k 1 h_k]
        exact hN
      rw [CTS_nSteps_one] at h_one
      exact (CTS_step_none_iff_halted cts r).mp h_one

/-- **CTS halt-time extractor**. -/
theorem CTS_Halts_extract_halt_time
    (cts : CTS) (cfg : CTSConfig) (h : cts.Halts cfg) :
    ∃ k r, cts.nSteps cfg k = some r ∧ ctsHalted r = true ∧
           ∀ m < k, ∀ r', cts.nSteps cfg m = some r' → ctsHalted r' = false := by
  obtain ⟨N, hN, h_min⟩ := CTS_Halts_first_none cts cfg h
  obtain ⟨k, _h_N_eq, r, h_step, h_halt⟩ :=
    CTS_first_none_predecessor_halts cts cfg N hN h_min
  refine ⟨k, r, h_step, h_halt, ?_⟩
  intro m h_lt r' h_m
  cases h_halt'_b : ctsHalted r' with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨h_eq_mn, _⟩ := CTS_nSteps_halt_unique cts cfg m k r' r
                            h_m h_halt'_b h_step h_halt
    omega

/-- **CTS Halts eval at halt time**: enriches halt-time witness
    with matching `eval cfg k = some r`. -/
theorem CTS_Halts_eval_at_halt_time
    (cts : CTS) (cfg : CTSConfig) (h : cts.Halts cfg) :
    ∃ k r, cts.eval cfg k = some r ∧ cts.nSteps cfg k = some r
           ∧ ctsHalted r = true
           ∧ ∀ m < k, ∀ r', cts.nSteps cfg m = some r' → ctsHalted r' = false := by
  obtain ⟨k, r, h_step, h_halt, h_min⟩ := CTS_Halts_extract_halt_time cts cfg h
  exact ⟨k, r,
    CTS_nSteps_some_halted_imp_eval cts cfg k r h_step h_halt,
    h_step, h_halt, h_min⟩

/-- **CTS self-loop nSteps stays at cfg**: if `cts.step cfg = some
    cfg`, then `cts.nSteps cfg n = some cfg` for every n. -/
theorem CTS_self_loop_nSteps_self
    (cts : CTS) (cfg : CTSConfig) (h_self : cts.step cfg = some cfg) (n : Nat) :
    cts.nSteps cfg n = some cfg := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [CTS_nSteps_succ_unfold, h_self]
    exact ih

/-- **CTS self-loop does not halt**: if `cts.step cfg = some cfg`
    (a genuine self-loop), then `¬ cts.Halts cfg`. -/
theorem CTS_self_loop_not_halts
    (cts : CTS) (cfg : CTSConfig) (h_self : cts.step cfg = some cfg) :
    ¬ cts.Halts cfg := by
  intro h_halts
  rw [CTS_Halts_iff_nSteps_reaches_halted] at h_halts
  obtain ⟨k, r, h_n, h_halt_r⟩ := h_halts
  rw [CTS_self_loop_nSteps_self cts cfg h_self k] at h_n
  injection h_n with h_eq
  rw [← h_eq] at h_halt_r
  have h_not_halted : ctsHalted cfg = false :=
    cts_step_some_not_halted cts cfg cfg h_self
  rw [h_halt_r] at h_not_halted
  exact Bool.noConfusion h_not_halted

/-- **CTS periodic-orbit nSteps stays at cfg for k iterations**. -/
theorem CTS_periodic_nSteps_iter
    (cts : CTS) (cfg : CTSConfig) (p : Nat)
    (h_period : cts.nSteps cfg p = some cfg) (k : Nat) :
    cts.nSteps cfg (k * p) = some cfg := by
  induction k with
  | zero => rw [Nat.zero_mul]; rfl
  | succ k ih =>
    have h_add := CTS.nSteps_add cts cfg cfg (k * p) p ih
    rw [Nat.succ_mul, ← h_add]
    exact h_period

/-- **CTS periodic orbit ⇒ not halts**. -/
theorem CTS_periodic_not_halts
    (cts : CTS) (cfg : CTSConfig) (p : Nat) (h_pos : p ≥ 1)
    (h_period : cts.nSteps cfg p = some cfg) :
    ¬ cts.Halts cfg := by
  intro h_halts
  rw [CTS_Halts_iff_nSteps_reaches_halted] at h_halts
  obtain ⟨N, r, h_n, h_halt_r⟩ := h_halts
  have h_iter := CTS_periodic_nSteps_iter cts cfg p h_period (N + 1)
  have h_ge : (N + 1) * p ≥ N + 1 := by
    have : (N + 1) * 1 ≤ (N + 1) * p := Nat.mul_le_mul_left _ h_pos
    omega
  obtain ⟨j, hj_pos, h_eq⟩ : ∃ j, j ≥ 1 ∧ (N + 1) * p = N + j :=
    ⟨(N + 1) * p - N, by omega, by omega⟩
  rw [h_eq] at h_iter
  rw [CTS_nSteps_past_halt_eq_none cts cfg N r h_n h_halt_r j hj_pos] at h_iter
  cases h_iter

/-- **CTS not-Halts iff nSteps always some**. -/
theorem CTS_not_Halts_iff_nSteps_always_some
    (cts : CTS) (cfg : CTSConfig) :
    ¬ cts.Halts cfg ↔ ∀ n, ∃ result, cts.nSteps cfg n = some result := by
  constructor
  · intro h_not_halts n
    cases h_n : cts.nSteps cfg n with
    | none =>
      exfalso
      exact h_not_halts (CTS_nSteps_none_imp_halts cts cfg ⟨n, h_n⟩)
    | some r => exact ⟨r, rfl⟩
  · intro h_all h_halts
    rw [CTS_Halts_iff_nSteps_reaches_halted] at h_halts
    obtain ⟨k, r, h_k, h_halt_r⟩ := h_halts
    obtain ⟨r', h_r'⟩ := h_all (k + 1)
    rw [CTS_nSteps_past_halt_eq_none cts cfg k r h_k h_halt_r 1 (by omega)] at h_r'
    cases h_r'

/-- **CTS Halts ⇒ no period**. -/
theorem CTS_Halts_no_period
    (cts : CTS) (cfg : CTSConfig) (h : cts.Halts cfg)
    (p : Nat) (h_pos : p ≥ 1) :
    cts.nSteps cfg p ≠ some cfg :=
  fun h_period => CTS_periodic_not_halts cts cfg p h_pos h_period h

/-- **Explicit CTS step on false-head data**. -/
theorem CTS_step_false_head (cts : CTS) (rest : List Bool) (phase : Nat) :
    cts.step { data := false :: rest, phase := phase }
    = some { data := rest,
             phase := (phase + 1) % cts.appendants.length } := by
  simp [CTS.step]

/-- **Explicit CTS step on true-head data**. -/
theorem CTS_step_true_head (cts : CTS) (rest : List Bool) (phase : Nat) :
    cts.step { data := true :: rest, phase := phase }
    = some { data := rest ++ cts.currentAppendant phase,
             phase := (phase + 1) % cts.appendants.length } := by
  simp [CTS.step]

/-- **CTS step data-length delta (false head)**. -/
theorem CTS_step_false_head_length (cts : CTS) (rest : List Bool) (phase : Nat) :
    ((cts.step { data := false :: rest, phase := phase }).map
      (fun c => c.data.length)) = some rest.length := by
  rw [CTS_step_false_head]
  rfl

/-- **CTS step data-length delta (true head)**. -/
theorem CTS_step_true_head_length (cts : CTS) (rest : List Bool) (phase : Nat) :
    ((cts.step { data := true :: rest, phase := phase }).map
      (fun c => c.data.length))
    = some (rest.length + (cts.currentAppendant phase).length) := by
  rw [CTS_step_true_head]
  show some (rest ++ cts.currentAppendant phase).length = _
  rw [List.length_append]

/-- **CTS step phase advance**: `cts.step cfg = some cfg'` advances
    phase by exactly 1 (mod appendant list length). -/
theorem CTS_step_phase
    (cts : CTS) (cfg cfg' : CTSConfig) (h_step : cts.step cfg = some cfg') :
    cfg'.phase = (cfg.phase + 1) % cts.appendants.length := by
  obtain ⟨data, phase⟩ := cfg
  cases data with
  | nil => simp [CTS.step] at h_step
  | cons head rest =>
    cases head with
    | false =>
      rw [CTS_step_false_head] at h_step
      injection h_step with h_eq
      rw [← h_eq]
    | true =>
      rw [CTS_step_true_head] at h_step
      injection h_step with h_eq
      rw [← h_eq]

/-- **CTS nSteps phase advance**. -/
theorem CTS_nSteps_phase
    (cts : CTS) (cfg cfg' : CTSConfig) (n : Nat)
    (h_phase : cfg.phase < cts.appendants.length)
    (h : cts.nSteps cfg n = some cfg') :
    cfg'.phase = (cfg.phase + n) % cts.appendants.length := by
  induction n generalizing cfg with
  | zero =>
    simp [CTS.nSteps] at h
    rw [← h]
    show cfg.phase = (cfg.phase + 0) % cts.appendants.length
    rw [Nat.add_zero, Nat.mod_eq_of_lt h_phase]
  | succ k ih =>
    rw [CTS_nSteps_succ_unfold] at h
    cases h_step : cts.step cfg with
    | none => rw [h_step] at h; cases h
    | some cfg₁ =>
      rw [h_step] at h
      have h_phase₁ := CTS_step_phase cts cfg cfg₁ h_step
      have h_phase₁_lt : cfg₁.phase < cts.appendants.length := by
        rw [h_phase₁]
        exact Nat.mod_lt _ cts.nonempty
      have h_phase' := ih cfg₁ h_phase₁_lt h
      rw [h_phase']
      rw [h_phase₁]
      show ((cfg.phase + 1) % cts.appendants.length + k)
            % cts.appendants.length
          = (cfg.phase + (k + 1)) % cts.appendants.length
      rw [Nat.mod_add_mod]
      congr 1
      omega

/-- **CTS step preserves phase < |appendants|**. -/
theorem CTS_step_phase_lt
    (cts : CTS) (cfg cfg' : CTSConfig) (h_step : cts.step cfg = some cfg') :
    cfg'.phase < cts.appendants.length := by
  rw [CTS_step_phase cts cfg cfg' h_step]
  exact Nat.mod_lt _ cts.nonempty

/-- **CTS nSteps preserves phase < |appendants|** for `n ≥ 1`. -/
theorem CTS_nSteps_phase_lt
    (cts : CTS) (cfg cfg' : CTSConfig) (n : Nat) (h_n : 1 ≤ n)
    (h : cts.nSteps cfg n = some cfg') :
    cfg'.phase < cts.appendants.length := by
  cases n with
  | zero => omega
  | succ k =>
    rw [CTS_nSteps_succ_unfold] at h
    cases h_step : cts.step cfg with
    | none => rw [h_step] at h; cases h
    | some cfg₁ =>
      rw [h_step] at h
      have h_phase₁_lt : cfg₁.phase < cts.appendants.length :=
        CTS_step_phase_lt cts cfg cfg₁ h_step
      rw [CTS_nSteps_phase cts cfg₁ cfg' k h_phase₁_lt h]
      exact Nat.mod_lt _ cts.nonempty

/-- CTS analog of `step_some_of_active`: an active CTS config has a step. -/
theorem cts_step_some_of_active (cts : CTS) (cfg : CTSConfig)
    (h : ctsHalted cfg = false) :
    ∃ cfg', cts.step cfg = some cfg' := by
  cases h_step : cts.step cfg with
  | none =>
    have := (CTS_step_none_iff_halted cts cfg).mp h_step
    rw [this] at h
    cases h
  | some cfg' => exact ⟨cfg', rfl⟩

/-- **`Tag_eval_some_imp_halted` (iter 577)**: Tag analog of
    `CTS_eval_some_imp_halted`.  When `Tag.eval cfg fuel = some
    result`, the result is always halted (`tagHalted result = true`).
    Proof: induction on fuel with case-split on `tagHalted cfg`. -/
theorem Tag_eval_some_imp_halted {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (fuel : Nat) (result : TagConfig k)
    (h : ts.eval cfg fuel = some result) :
    tagHalted result = true := by
  induction fuel generalizing cfg with
  | zero =>
    simp [Tag.eval] at h
    obtain ⟨h_halt, h_eq⟩ := h
    rw [← h_eq]; exact h_halt
  | succ k ih =>
    simp [Tag.eval] at h
    by_cases h_halt : tagHalted cfg = true
    · simp [h_halt] at h
      rw [← h]; exact h_halt
    · simp [h_halt] at h
      cases h_step : ts.step cfg with
      | none =>
        rw [h_step] at h
        simp at h
        rw [← h]
        exact (Tag.step_none_iff_halted ts cfg).mp h_step
      | some cfg' =>
        rw [h_step] at h
        simp at h
        exact ih cfg' h

/-- **Tag eval-halted-self (iter 578)**: a halted cfg's eval returns
    itself for any fuel.  Tag analog of `CTS_eval_halted_self`. -/
theorem Tag_eval_halted_self {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (h : tagHalted cfg = true) (fuel : Nat) :
    ts.eval cfg fuel = some cfg := by
  cases fuel with
  | zero => simp [Tag.eval, h]
  | succ k => simp [Tag.eval, h]

/-- **Tag eval fuel-succ monotonicity (iter 578)**: if eval halts
    at fuel `f`, also halts at `f+1` with same result. -/
theorem Tag_eval_fuel_succ {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (fuel : Nat) (result : TagConfig k) (h : ts.eval cfg fuel = some result) :
    ts.eval cfg (fuel + 1) = some result := by
  induction fuel generalizing cfg with
  | zero =>
    simp [Tag.eval] at h
    obtain ⟨h_halt, h_eq⟩ := h
    rw [← h_eq]
    exact Tag_eval_halted_self ts cfg h_halt 1
  | succ m ih =>
    by_cases h_halt : tagHalted cfg = true
    · simp [Tag.eval, h_halt] at h
      rw [← h]
      exact Tag_eval_halted_self ts cfg h_halt _
    · simp [Tag.eval, h_halt] at h
      cases h_step : ts.step cfg with
      | none =>
        rw [h_step] at h
        simp at h
        rw [← h]
        have h_state : tagHalted cfg = true :=
          (Tag.step_none_iff_halted ts cfg).mp h_step
        exact absurd h_state h_halt
      | some cfg' =>
        rw [h_step] at h
        simp [Tag.eval, h_halt, h_step]
        exact ih cfg' h

/-- **Tag eval fuel-le monotonicity (iter 578)**: result stays
    fixed under additional fuel. -/
theorem Tag_eval_fuel_le {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (fuel fuel' : Nat) (h_le : fuel ≤ fuel') (result : TagConfig k)
    (h : ts.eval cfg fuel = some result) :
    ts.eval cfg fuel' = some result := by
  obtain ⟨k, h_k⟩ : ∃ k, fuel' = fuel + k := ⟨fuel' - fuel, by omega⟩
  rw [h_k]
  clear h_k h_le fuel'
  induction k with
  | zero => exact h
  | succ j ih =>
    rw [show fuel + (j + 1) = (fuel + j) + 1 from by omega]
    exact Tag_eval_fuel_succ ts cfg (fuel + j) result ih

/-- **Tag eval result unique (iter 578)**: any two eval witnesses
    for the same cfg agree on the result.  Tag analog of
    `BiTM_eval_result_unique` / `CTS_eval_result_unique`. -/
theorem Tag_eval_result_unique {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (f₁ f₂ : Nat) (r₁ r₂ : TagConfig k)
    (h₁ : ts.eval cfg f₁ = some r₁) (h₂ : ts.eval cfg f₂ = some r₂) :
    r₁ = r₂ := by
  have h_le1 : f₁ ≤ max f₁ f₂ := Nat.le_max_left f₁ f₂
  have h_le2 : f₂ ≤ max f₁ f₂ := Nat.le_max_right f₁ f₂
  have h₁' := Tag_eval_fuel_le ts cfg f₁ (max f₁ f₂) h_le1 r₁ h₁
  have h₂' := Tag_eval_fuel_le ts cfg f₂ (max f₁ f₂) h_le2 r₂ h₂
  rw [h₁'] at h₂'
  injection h₂'

/-- **`Tag_periodic_nSteps_iter` (iter 580 helper)**: if `tagNSteps
    cfg p = some cfg`, then `tagNSteps cfg (k * p) = some cfg`
    for all k.  Tag analog of `CTS_periodic_nSteps_iter`. -/
theorem Tag_periodic_nSteps_iter {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (p : Nat) (h_period : tagNSteps ts cfg p = some cfg) (m : Nat) :
    tagNSteps ts cfg (m * p) = some cfg := by
  induction m with
  | zero => rw [Nat.zero_mul]; rfl
  | succ m ih =>
    rw [Nat.succ_mul, tagNSteps_add, ih]
    exact h_period

/-- **`Tag_periodic_not_haltsEmpty` (iter 580)**: a periodic Tag
    cfg (with period p ≥ 1) cannot have `HaltsEmpty`.  Reason: the
    trajectory cycles without ever reaching `[]`.  Proof: assume
    `HaltsEmpty`; get `N` with `tagNSteps cfg N = some []`; pick
    `m` such that `m * p ≥ N`; then `tagNSteps cfg (m * p)` is both
    `some cfg` (period) and `none` (post-nil), contradiction
    (assuming `cfg ≠ []`; trivially `cfg ≠ []` since `step cfg`
    succeeds for the period). -/
theorem Tag_periodic_not_haltsEmpty {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (p : Nat) (h_pos : p ≥ 1) (h_period : tagNSteps ts cfg p = some cfg) :
    ¬ ts.HaltsEmpty cfg := by
  intro h_he
  obtain ⟨N, hN⟩ := haltsEmpty_implies_tagNSteps_eq_nil ts cfg h_he
  have h_iter := Tag_periodic_nSteps_iter ts cfg p h_period (N + 1)
  have h_ge : (N + 1) * p ≥ N + 1 := by
    have : (N + 1) * 1 ≤ (N + 1) * p := Nat.mul_le_mul_left _ h_pos
    omega
  have h_split : (N + 1) * p = N + ((N + 1) * p - N - 1 + 1) := by omega
  rw [h_split] at h_iter
  rw [tagNSteps_after_nil ts cfg N _ hN] at h_iter
  cases h_iter

/-- **`Tag_HaltsEmpty_no_period` (iter 580)**: contrapositive — a
    HaltsEmpty cfg cannot be periodic. -/
theorem Tag_HaltsEmpty_no_period {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (h : ts.HaltsEmpty cfg) (p : Nat) (h_pos : p ≥ 1) :
    tagNSteps ts cfg p ≠ some cfg :=
  fun h_period => Tag_periodic_not_haltsEmpty ts cfg p h_pos h_period h

/-- **`Tag_self_loop_not_haltsEmpty` (iter 581)**: a Tag self-loop
    cannot have `HaltsEmpty`.  Direct corollary of iter 580 with
    period `p = 1`: `tagNSteps cfg 1 = some cfg` follows from
    `step cfg = some cfg` via `tagNSteps_one`. -/
theorem Tag_self_loop_not_haltsEmpty {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (h_self : ts.step cfg = some cfg) :
    ¬ ts.HaltsEmpty cfg := by
  apply Tag_periodic_not_haltsEmpty ts cfg 1 (Nat.le_refl _)
  rw [tagNSteps_one]
  exact h_self

/-- **`CTS_Halts_eval_exact_step_form` (iter 586)**: CTS analog of
    `Halts_eval_exact_step_form` (BiTM, in HaltInduction).  An
    eval-success witness with fuel `f` produces a full exact-step
    witness with `N ≤ f`.  Combines `CTS_eval_some_imp_nSteps_le`
    with `CTS_eval_some_imp_halted` and `ctsHalted_nSteps_eq_none`. -/
theorem CTS_Halts_eval_exact_step_form (cts : CTS) (cfg : CTSConfig) (fuel : Nat)
    (result : CTSConfig) (h : cts.eval cfg fuel = some result) :
    ∃ N, N ≤ fuel ∧ cts.nSteps cfg N = some result ∧ ctsHalted result = true ∧
         ∀ k, k > N → cts.nSteps cfg k = none := by
  obtain ⟨N, h_le, h_n⟩ := CTS_eval_some_imp_nSteps_le cts cfg fuel result h
  have h_halted : ctsHalted result = true :=
    CTS_eval_some_imp_halted cts cfg fuel result h
  refine ⟨N, h_le, h_n, h_halted, ?_⟩
  intro k h_k
  have h_add := CTS.nSteps_add cts cfg result N (k - N) h_n
  have h_kN : N + (k - N) = k := by omega
  rw [h_kN] at h_add
  rw [← h_add]
  exact ctsHalted_nSteps_eq_none cts result (k - N) h_halted (by omega)

/-- **`Tag_Halts_iff_exists_nSteps_none` (iter 588)**: Tag analog of
    `BiTM_Halts_iff_exists_nSteps_none` / `CTS_Halts_iff_exists_nSteps_none`.
    `Tag.Halts cfg ↔ ∃ n, tagNSteps cfg n = none`. -/
theorem Tag_Halts_iff_exists_nSteps_none {k : Nat} (ts : Tag k) (cfg : TagConfig k) :
    ts.Halts cfg ↔ ∃ n, tagNSteps ts cfg n = none := by
  constructor
  · intro ⟨fuel, result, h_eval⟩
    -- result is halted; nSteps cfg fuel reaches result (forward bound from
    -- iter-544 style); then step result = none gives nSteps cfg (fuel+1) = none.
    induction fuel generalizing cfg with
    | zero =>
      simp [Tag.eval] at h_eval
      obtain ⟨h_halt, h_eq⟩ := h_eval
      refine ⟨1, ?_⟩
      show (match ts.step cfg with
            | none => none
            | some cfg' => tagNSteps ts cfg' 0) = none
      rw [(Tag.step_none_iff_halted ts cfg).mpr h_halt]
    | succ m ih =>
      by_cases h_halt : tagHalted cfg = true
      · refine ⟨1, ?_⟩
        show (match ts.step cfg with
              | none => none
              | some cfg' => tagNSteps ts cfg' 0) = none
        rw [(Tag.step_none_iff_halted ts cfg).mpr h_halt]
      · simp [Tag.eval, h_halt] at h_eval
        cases h_step : ts.step cfg with
        | none =>
          rw [(Tag.step_none_iff_halted ts cfg).mp h_step] at h_halt
          exact absurd rfl h_halt
        | some cfg' =>
          rw [h_step] at h_eval
          obtain ⟨n, h_n⟩ := ih cfg' h_eval
          refine ⟨n + 1, ?_⟩
          show (match ts.step cfg with
                | none => none
                | some c => tagNSteps ts c n) = none
          rw [h_step]; exact h_n
  · rintro ⟨n, h_n⟩
    -- nSteps cfg n = none means trajectory dies at some k ≤ n via step = none.
    -- That cfg_k is halted, eval reaches it.
    induction n generalizing cfg with
    | zero => simp [tagNSteps] at h_n
    | succ m ih =>
      have h_n' : (match ts.step cfg with
                   | none => none
                   | some cfg' => tagNSteps ts cfg' m) = none := h_n
      cases h_step : ts.step cfg with
      | none =>
        have h_halt := (Tag.step_none_iff_halted ts cfg).mp h_step
        exact ⟨0, cfg, by simp [Tag.eval, h_halt]⟩
      | some cfg' =>
        rw [h_step] at h_n'
        obtain ⟨fuel, result, h_eval⟩ := ih cfg' h_n'
        have h_nh := tag_step_some_not_halted ts cfg cfg' h_step
        exact ⟨fuel + 1, result,
          by rw [Tag.eval_step ts cfg cfg' fuel h_nh h_step]; exact h_eval⟩

/-- **`Tag_Halts_iff_eval_some_halted` (iter 587)**: Tag analog of
    `BiTM_Halts_iff_eval_state_zero` / `CTS_Halts_iff_eval_data_empty`.
    `Tag.Halts cfg ↔ ∃ fuel result, eval cfg fuel = some result ∧
    tagHalted result = true`.  Forward direction uses iter 577
    (`Tag_eval_some_imp_halted`); reverse is direct unpacking. -/
theorem Tag_Halts_iff_eval_some_halted {k : Nat} (ts : Tag k) (cfg : TagConfig k) :
    ts.Halts cfg ↔ ∃ fuel result, ts.eval cfg fuel = some result
                                  ∧ tagHalted result = true := by
  constructor
  · intro ⟨fuel, result, h_eval⟩
    exact ⟨fuel, result, h_eval, Tag_eval_some_imp_halted ts cfg fuel result h_eval⟩
  · intro ⟨fuel, result, h_eval, _⟩
    exact ⟨fuel, result, h_eval⟩

/-- **`Tag_periodic_step_not_halted` (iter 585)**: a Tag periodic
    cfg with period p ≥ 1 is not halted.  Reason: `tagNSteps cfg p
    = some cfg` requires step cfg = some cfg₁ (not none), which by
    `tag_step_some_not_halted` implies `tagHalted cfg = false`. -/
theorem Tag_periodic_step_not_halted {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (p : Nat) (h_pos : p ≥ 1) (h_period : tagNSteps ts cfg p = some cfg) :
    tagHalted cfg = false := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  cases h_step : ts.step cfg with
  | none =>
    have : tagNSteps ts cfg (m + 1) = none := by
      show (match ts.step cfg with
            | none => none
            | some cfg' => tagNSteps ts cfg' m) = none
      rw [h_step]
    rw [this] at h_period; cases h_period
  | some cfg' =>
    exact tag_step_some_not_halted ts cfg cfg' h_step

/-- **`Tag_Halts_eval_stable` (iter 579)**: Tag analog of
    `CTS_Halts_eval_stable` / `BiTM_Halts_eval_stable`.  For any
    halting cfg, eval stabilizes to a single result for large
    fuel. -/
theorem Tag_Halts_eval_stable {k : Nat} (ts : Tag k) (cfg : TagConfig k)
    (h : ts.Halts cfg) :
    ∃ fuel result, ∀ fuel' ≥ fuel, ts.eval cfg fuel' = some result := by
  obtain ⟨fuel, result, h_eval⟩ := h
  exact ⟨fuel, result, fun fuel' h_le =>
    Tag_eval_fuel_le ts cfg fuel fuel' h_le result h_eval⟩

/-- **CTS step shifts phase mod L** for any L ≥ 2.  A successful
    step from `⟨data, p⟩` produces `⟨_, (p + 1) % L⟩`.  For
    `L ≥ 2`, `(p + 1) % L ≠ p % L`. -/
theorem cts_step_phase_changes (cts : CTS) (h_len : cts.appendants.length ≥ 2)
    (cfg cfg' : CTSConfig) (h_step : cts.step cfg = some cfg') :
    cfg.phase % cts.appendants.length
      ≠ cfg'.phase % cts.appendants.length := by
  unfold CTS.step at h_step
  cases h_data : cfg.data with
  | nil =>
    rw [h_data] at h_step
    cases h_step
  | cons head rest =>
    rw [h_data] at h_step
    have h_phase_eq : cfg'.phase = (cfg.phase + 1) % cts.appendants.length := by
      injection h_step with h_inj
      rw [← h_inj]
    rw [h_phase_eq, Nat.mod_mod]
    have h_q_lt : cfg.phase % cts.appendants.length < cts.appendants.length :=
      Nat.mod_lt _ (by omega)
    have h_one_mod : 1 % cts.appendants.length = 1 :=
      Nat.mod_eq_of_lt (by omega)
    have h_split : (cfg.phase + 1) % cts.appendants.length
                 = (cfg.phase % cts.appendants.length + 1)
                    % cts.appendants.length := by
      rw [Nat.add_mod, h_one_mod]
    rw [h_split]
    by_cases h_case : cfg.phase % cts.appendants.length + 1 < cts.appendants.length
    · rw [Nat.mod_eq_of_lt h_case]; omega
    · have h_eq_L : cfg.phase % cts.appendants.length + 1 = cts.appendants.length := by omega
      rw [h_eq_L, Nat.mod_self]; omega

/-- A CTS self-loop forces `appendants.length = 1`. -/
theorem cts_self_loop_implies_singleton_appendants
    (cts : CTS) (cfg : CTSConfig) (h_self : cts.step cfg = some cfg) :
    cts.appendants.length = 1 := by
  have h_pos : cts.appendants.length ≥ 1 := cts.nonempty
  match h_len : cts.appendants.length, h_pos with
  | 1, _ => rfl
  | n + 2, _ =>
    exfalso
    have h_ge_two : cts.appendants.length ≥ 2 := by rw [h_len]; omega
    exact cts_step_phase_changes cts h_ge_two cfg cfg h_self rfl

/-- **CTS cycle phase period divides**: if `cfg` is `m`-periodic
    in CTS with `m ≥ 1`, then `cts.appendants.length ∣ m`. -/
theorem cts_cycle_phase_period_divides (cts : CTS) (cfg : CTSConfig) (m : Nat)
    (_h_pos : m ≥ 1) (h_periodic : cts.nSteps cfg m = some cfg) :
    cts.appendants.length ∣ m := by
  suffices h : ∀ k cfg' cfg'',
      cts.nSteps cfg' k = some cfg'' →
      cfg''.phase % cts.appendants.length
        = (cfg'.phase + k) % cts.appendants.length by
    have := h m cfg cfg h_periodic
    have h_L_pos : cts.appendants.length ≥ 1 := cts.nonempty
    have h_lhs : cfg.phase % cts.appendants.length
                = (cfg.phase + m) % cts.appendants.length := this
    have h_split : (cfg.phase + m) % cts.appendants.length
                 = (cfg.phase % cts.appendants.length + m % cts.appendants.length)
                    % cts.appendants.length := by
      rw [Nat.add_mod]
    rw [h_split] at h_lhs
    have h_q_lt : cfg.phase % cts.appendants.length < cts.appendants.length :=
      Nat.mod_lt _ (by omega)
    have h_r_lt : m % cts.appendants.length < cts.appendants.length :=
      Nat.mod_lt _ (by omega)
    have h_r_zero : m % cts.appendants.length = 0 := by
      by_cases h_case : cfg.phase % cts.appendants.length + m % cts.appendants.length
                        < cts.appendants.length
      · rw [Nat.mod_eq_of_lt h_case] at h_lhs
        omega
      · have h_lt_2L : cfg.phase % cts.appendants.length + m % cts.appendants.length
                      < 2 * cts.appendants.length := by omega
        have h_eq : (cfg.phase % cts.appendants.length + m % cts.appendants.length)
                    % cts.appendants.length
                  = cfg.phase % cts.appendants.length + m % cts.appendants.length
                    - cts.appendants.length := by
          rw [Nat.mod_eq_sub_mod (by omega)]
          rw [Nat.mod_eq_of_lt (by omega)]
        rw [h_eq] at h_lhs
        omega
    exact Nat.dvd_of_mod_eq_zero h_r_zero
  intro k
  induction k with
  | zero =>
    intro cfg' cfg'' h
    change some cfg' = some cfg'' at h
    injection h with h_eq
    rw [← h_eq]
    simp
  | succ k ih =>
    intro cfg' cfg'' h
    change (match cts.step cfg' with | none => none | some c => cts.nSteps c k) = some cfg'' at h
    cases h_step : cts.step cfg' with
    | none => rw [h_step] at h; cases h
    | some c =>
      rw [h_step] at h
      have h_c_phase : c.phase = (cfg'.phase + 1) % cts.appendants.length := by
        unfold CTS.step at h_step
        cases h_data : cfg'.data with
        | nil => rw [h_data] at h_step; cases h_step
        | cons _ _ =>
          rw [h_data] at h_step
          injection h_step with h_inj
          rw [← h_inj]
      have h_ih := ih c cfg'' h
      rw [h_ih]
      rw [h_c_phase]
      rw [Nat.add_mod ((cfg'.phase + 1) % cts.appendants.length) k]
      rw [Nat.mod_mod]
      rw [← Nat.add_mod]
      have h_arith : cfg'.phase + 1 + k = cfg'.phase + (k + 1) := by omega
      rw [h_arith]

/-- **Concrete witness** of a CTS self-loop. -/
def selfLoopCTS : CTS where
  appendants := [[true]]
  nonempty := by decide

theorem selfLoopCTS_has_self_step :
    selfLoopCTS.step { data := [true, true], phase := 0 }
      = some { data := [true, true], phase := 0 } := by
  simp [CTS.step, selfLoopCTS, CTS.currentAppendant]

/-- **`selfLoopCTS` is m-periodic for ALL m ≥ 0** at the cfg
    `⟨[true, true], 0⟩`. -/
theorem selfLoopCTS_periodic_all_m (m : Nat) :
    selfLoopCTS.nSteps { data := [true, true], phase := 0 } m
      = some { data := [true, true], phase := 0 } := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (match selfLoopCTS.step { data := [true, true], phase := 0 } with
            | none => none
            | some c => selfLoopCTS.nSteps c m)
            = some { data := [true, true], phase := 0 }
    rw [selfLoopCTS_has_self_step]
    exact ih

/-- **`selfLoopCTS` does not halt**: direct corollary of
    `CTS_self_loop_not_halts` applied to `selfLoopCTS_has_self_step`. -/
theorem selfLoopCTS_not_halts :
    ¬ selfLoopCTS.Halts { data := [true, true], phase := 0 } :=
  CTS_self_loop_not_halts selfLoopCTS _ selfLoopCTS_has_self_step

/-- **Concrete witness** of a Tag self-loop (iter 583).  A 2-symbol
    Tag with productions(0) = productions(1) = [0, 1].  At cfg
    `[0, 1]`, step gives `[] ++ prods 0 = [0, 1]` — self-loop.
    Parallel to `selfLoopCTS`. -/
def selfLoopTag : Tag 2 where
  productions := fun _ => [⟨0, by decide⟩, ⟨1, by decide⟩]

theorem selfLoopTag_has_self_step :
    selfLoopTag.step [⟨0, by decide⟩, ⟨1, by decide⟩]
      = some [⟨0, by decide⟩, ⟨1, by decide⟩] := by
  rfl

/-- **`selfLoopTag` does not have HaltsEmpty** at `[0, 1]`: direct
    corollary of `Tag_self_loop_not_haltsEmpty` (iter 581). -/
theorem selfLoopTag_not_haltsEmpty :
    ¬ selfLoopTag.HaltsEmpty [⟨0, by decide⟩, ⟨1, by decide⟩] :=
  Tag_self_loop_not_haltsEmpty selfLoopTag _ selfLoopTag_has_self_step

/-- **`emptyProdsTag` (iter 584)**: Tag analog of `trivialHaltCTS` —
    every production is `[]`, so each step shrinks length by 2.
    Eventually reaches a halted state (length < 2). -/
def emptyProdsTag (k : Nat) : Tag k where
  productions := fun _ => []

/-- One step on `emptyProdsTag` strictly shrinks length by 2. -/
theorem emptyProdsTag_step_shrinks {k : Nat} (cfg : TagConfig k)
    (h_len : cfg.length ≥ 2) :
    ∃ cfg', (emptyProdsTag k).step cfg = some cfg' ∧ cfg'.length + 2 = cfg.length := by
  match cfg, h_len with
  | a :: b :: rest, _ =>
    refine ⟨rest, ?_, ?_⟩
    · show (emptyProdsTag k).step (a :: b :: rest) = some rest
      simp [Tag.step, emptyProdsTag]
    · show rest.length + 2 = (a :: b :: rest).length
      simp [List.length_cons]

/-- **`emptyProdsTag_Halts` (iter 589)**: every cfg halts under
    `emptyProdsTag` since length monotonically decreases by 2 each
    step.  Tag analog of `AllEmptyAppendants_Halts` (CTS case). -/
theorem emptyProdsTag_Halts {k : Nat} (cfg : TagConfig k) :
    (emptyProdsTag k).Halts cfg := by
  suffices h : ∀ n, ∀ cfg : TagConfig k, cfg.length ≤ n →
      (emptyProdsTag k).Halts cfg from h cfg.length cfg (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro cfg h_le
    have h_eq : cfg.length = 0 := by omega
    have h_halt : tagHalted cfg = true := by unfold tagHalted; rw [h_eq]; rfl
    exact ⟨0, cfg, by simp [Tag.eval, h_halt]⟩
  | succ m ih =>
    intro cfg h_le
    by_cases h_halt : tagHalted cfg = true
    · exact ⟨0, cfg, by simp [Tag.eval, h_halt]⟩
    · have h_ge : cfg.length ≥ 2 := by
        cases h : decide (cfg.length < 2) with
        | true =>
          have : tagHalted cfg = true := by unfold tagHalted; exact h
          exact absurd this h_halt
        | false =>
          have : ¬ (cfg.length < 2) := of_decide_eq_false h
          omega
      obtain ⟨cfg', h_step, h_eq⟩ := emptyProdsTag_step_shrinks cfg h_ge
      have h_le' : cfg'.length ≤ m := by omega
      obtain ⟨fuel, result, h_eval⟩ := ih cfg' h_le'
      have h_nh : tagHalted cfg = false := by
        cases h : tagHalted cfg with
        | true => exact absurd h h_halt
        | false => rfl
      exact ⟨fuel + 1, result,
        by rw [Tag.eval_step (emptyProdsTag k) cfg cfg' fuel h_nh h_step]; exact h_eval⟩

/-- **`emptyProdsTag_tagNSteps_half_length` (iter 590)**: for any
    even-length cfg, `tagNSteps cfg (cfg.length / 2) = some []`.
    Each step shrinks length by 2, so length/2 steps brings it to
    0 (empty). -/
theorem emptyProdsTag_tagNSteps_half_length {k : Nat} :
    ∀ cfg : TagConfig k, cfg.length % 2 = 0 →
      tagNSteps (emptyProdsTag k) cfg (cfg.length / 2) = some []
  | [], _ => by simp
  | [_], h_even => by simp at h_even
  | a :: b :: rest, h_even => by
    have h_rest_even : rest.length % 2 = 0 := by
      have : (a :: b :: rest).length = rest.length + 2 := by simp [List.length_cons]
      omega
    have h_div : (a :: b :: rest).length / 2 = rest.length / 2 + 1 := by
      simp [List.length_cons]; omega
    rw [h_div]
    show (match (emptyProdsTag k).step (a :: b :: rest) with
          | none => none
          | some cfg' => tagNSteps (emptyProdsTag k) cfg' (rest.length / 2)) = some []
    have h_step : (emptyProdsTag k).step (a :: b :: rest) = some rest := by
      simp [Tag.step, emptyProdsTag]
    rw [h_step]
    exact emptyProdsTag_tagNSteps_half_length rest h_rest_even

/-- **`emptyProdsTag_HaltsEmpty_of_even` (iter 592)**: any
    even-length cfg has HaltsEmpty under `emptyProdsTag`.  Direct
    corollary of iter 590 + `tagNSteps_eq_nil_implies_haltsEmpty`. -/
theorem emptyProdsTag_HaltsEmpty_of_even {k : Nat} (cfg : TagConfig k)
    (h_even : cfg.length % 2 = 0) :
    (emptyProdsTag k).HaltsEmpty cfg :=
  tagNSteps_eq_nil_implies_haltsEmpty (emptyProdsTag k) cfg (cfg.length / 2)
    (emptyProdsTag_tagNSteps_half_length cfg h_even)

/-- **`emptyProdsTag_tagNSteps_some_of_le` (iter 602)**: for any
    `n ≤ cfg.length / 2`, `tagNSteps emptyProdsTag cfg n = some _`
    (witness existentially quantified).  Each step shrinks length by 2
    until depleted; up to `length/2` steps remain inside the
    "still-stepable" regime.  Generalises iter 590 from the even
    boundary case to all valid budgets. -/
theorem emptyProdsTag_tagNSteps_some_of_le {k : Nat} :
    ∀ (cfg : TagConfig k) (n : Nat), n ≤ cfg.length / 2 →
      ∃ result, tagNSteps (emptyProdsTag k) cfg n = some result := by
  intro cfg n
  induction n generalizing cfg with
  | zero =>
    intro _
    exact ⟨cfg, rfl⟩
  | succ m ih =>
    intro h_le
    -- m + 1 ≤ length / 2 ⇒ length ≥ 2 (so step succeeds)
    have h_len : cfg.length ≥ 2 := by
      rcases (Nat.lt_or_ge cfg.length 2) with h_lt | h_ge
      · exfalso
        have h_div : cfg.length / 2 = 0 := Nat.div_eq_of_lt h_lt
        omega
      · exact h_ge
    obtain ⟨cfg', h_step, h_eq⟩ := emptyProdsTag_step_shrinks cfg h_len
    have h_le' : m ≤ cfg'.length / 2 := by
      -- cfg'.length + 2 = cfg.length, so cfg'.length / 2 = cfg.length / 2 - 1
      have h_eq' : cfg'.length = cfg.length - 2 := by omega
      rw [h_eq']
      have : (cfg.length - 2) / 2 = cfg.length / 2 - 1 := by omega
      omega
    obtain ⟨result, h_result⟩ := ih cfg' h_le'
    refine ⟨result, ?_⟩
    show tagNSteps (emptyProdsTag k) cfg (m + 1) = some result
    show (match (emptyProdsTag k).step cfg with
          | none => none
          | some cfg'' => tagNSteps (emptyProdsTag k) cfg'' m) = some result
    rw [h_step]
    exact h_result

/-- **`emptyProdsTag_tagNSteps_eq_none_of_gt` (iter 604)**: dual of
    iter 602 — for `n > cfg.length / 2`, `tagNSteps emptyProdsTag cfg n
    = none`.  Proof: structural recursion on `cfg`'s first two elements.
    Length-0/1 configs halt on the very next step; length-≥2 configs
    drop to the tail and recurse on `m = n - 1` against the (smaller)
    tail's halve. -/
theorem emptyProdsTag_tagNSteps_eq_none_of_gt {k : Nat} :
    ∀ (cfg : TagConfig k) (n : Nat), n > cfg.length / 2 →
      tagNSteps (emptyProdsTag k) cfg n = none
  | [], n, h_gt => by
    have h_n_pos : n ≥ 1 := by simp at h_gt; omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show tagNSteps (emptyProdsTag k) ([] : TagConfig k) (m + 1) = none
    rfl
  | [a], n, h_gt => by
    have h_n_pos : n ≥ 1 := by simp at h_gt; omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show tagNSteps (emptyProdsTag k) [a] (m + 1) = none
    rfl
  | a :: b :: rest, n, h_gt => by
    have h_len : (a :: b :: rest).length = rest.length + 2 := by
      simp [List.length_cons]
    have h_div : (a :: b :: rest).length / 2 = rest.length / 2 + 1 := by
      rw [h_len]; omega
    rw [h_div] at h_gt
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h_m : m > rest.length / 2 := by omega
    show tagNSteps (emptyProdsTag k) (a :: b :: rest) (m + 1) = none
    show (match (emptyProdsTag k).step (a :: b :: rest) with
          | none => none
          | some c => tagNSteps (emptyProdsTag k) c m) = none
    have h_step : (emptyProdsTag k).step (a :: b :: rest) = some rest := by
      simp [Tag.step, emptyProdsTag]
    rw [h_step]
    exact emptyProdsTag_tagNSteps_eq_none_of_gt rest m h_m

/-- **`emptyProdsTag_tagNSteps_none_iff` (iter 604)**: the two-sided
    characterisation — `tagNSteps emptyProdsTag cfg n = none` iff
    `n > cfg.length / 2`.  Combines iter 602 and iter 604. -/
theorem emptyProdsTag_tagNSteps_none_iff {k : Nat}
    (cfg : TagConfig k) (n : Nat) :
    tagNSteps (emptyProdsTag k) cfg n = none ↔ n > cfg.length / 2 := by
  constructor
  · intro h_none
    rcases (Nat.lt_or_ge (cfg.length / 2) n) with h_lt | h_ge
    · exact h_lt
    · exfalso
      obtain ⟨result, h_some⟩ :=
        emptyProdsTag_tagNSteps_some_of_le cfg n h_ge
      rw [h_some] at h_none
      cases h_none
  · exact emptyProdsTag_tagNSteps_eq_none_of_gt cfg n

/-- **`emptyProdsTag_tagNSteps_isSome_iff` (iter 608)**: dual of iter
    604 — `tagNSteps emptyProdsTag cfg n` is `some _` iff `n ≤
    cfg.length / 2`.  Direct via Option dichotomy + iter 604. -/
theorem emptyProdsTag_tagNSteps_isSome_iff {k : Nat}
    (cfg : TagConfig k) (n : Nat) :
    (tagNSteps (emptyProdsTag k) cfg n).isSome ↔ n ≤ cfg.length / 2 := by
  rw [Option.isSome_iff_ne_none]
  rw [Ne, emptyProdsTag_tagNSteps_none_iff]
  exact ⟨fun h => by omega, fun h => by omega⟩

/-- **`emptyProdsTag_HaltsEmpty_imp_even` (iter 594)**: converse —
    if a cfg has HaltsEmpty under `emptyProdsTag`, its length is even.
    Each `emptyProdsTag` step shrinks length by 2 (so preserves
    parity); reaching the empty (length-0) cfg therefore requires
    starting from even length.  Proven by `Tag_HaltsEmpty_induction`. -/
theorem emptyProdsTag_HaltsEmpty_imp_even {k : Nat} (cfg : TagConfig k)
    (h : (emptyProdsTag k).HaltsEmpty cfg) :
    cfg.length % 2 = 0 := by
  apply Tag_HaltsEmpty_induction (emptyProdsTag k)
    (fun c => c.length % 2 = 0) ?_ ?_ cfg h
  · rfl
  · intro c c' h_step _ ih
    match c, h_step with
    | a :: b :: rest, h_step =>
      have h_eq : c' = rest := by
        have : (emptyProdsTag k).step (a :: b :: rest) = some rest := by
          simp [Tag.step, emptyProdsTag]
        rw [this] at h_step
        injection h_step with h
        exact h.symm
      have h_ih : rest.length % 2 = 0 := h_eq ▸ ih
      show (a :: b :: rest).length % 2 = 0
      simp [List.length_cons]
      omega

/-- **`emptyProdsTag_HaltsEmpty_iff_even` (iter 594)**: combining
    iter 592 with iter 594 — `HaltsEmpty` under `emptyProdsTag` is
    exactly the even-length predicate. -/
theorem emptyProdsTag_HaltsEmpty_iff_even {k : Nat} (cfg : TagConfig k) :
    (emptyProdsTag k).HaltsEmpty cfg ↔ cfg.length % 2 = 0 :=
  ⟨emptyProdsTag_HaltsEmpty_imp_even cfg,
   emptyProdsTag_HaltsEmpty_of_even cfg⟩

/-- A CTS has all-empty appendants if every appendant in the cyclic
    list is the empty bit-string. -/
def AllEmptyAppendants (cts : CTS) : Prop :=
  ∀ a ∈ cts.appendants, a = ([] : List Bool)

/-- `AllEmptyAppendants` is decidable. -/
instance (cts : CTS) : Decidable (AllEmptyAppendants cts) :=
  inferInstanceAs (Decidable (∀ a ∈ cts.appendants, a = ([] : List Bool)))

/-- For an all-empty-appendants CTS, the current appendant at any
    phase is `[]`. -/
theorem AllEmptyAppendants_currentAppendant_nil
    (cts : CTS) (h : AllEmptyAppendants cts) (phase : Nat) :
    cts.currentAppendant phase = [] := by
  unfold CTS.currentAppendant
  exact h _ (List.get_mem _ _)

/-- **For all-empty-appendants CTS, every step strictly shrinks data
    by exactly 1.** -/
theorem AllEmptyAppendants_step_data_length
    (cts : CTS) (cfg cfg' : CTSConfig)
    (h_app : AllEmptyAppendants cts)
    (h_step : cts.step cfg = some cfg') :
    cfg'.data.length + 1 = cfg.data.length := by
  obtain ⟨data, phase⟩ := cfg
  cases data with
  | nil => simp [CTS.step] at h_step
  | cons head rest =>
    cases head with
    | false =>
      rw [CTS_step_false_head] at h_step
      injection h_step with h_eq
      rw [← h_eq]
      simp
    | true =>
      have h_app_nil : cts.currentAppendant phase = [] :=
        AllEmptyAppendants_currentAppendant_nil cts h_app phase
      rw [CTS_step_true_head] at h_step
      injection h_step with h_eq
      rw [← h_eq]
      simp [h_app_nil]

/-- **Explicit step form for all-empty-appendants CTS**. -/
theorem AllEmptyAppendants_step_explicit
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (head : Bool) (rest : List Bool) (phase : Nat) :
    cts.step { data := head :: rest, phase := phase }
    = some { data := rest,
             phase := (phase + 1) % cts.appendants.length } := by
  cases head with
  | false => exact CTS_step_false_head cts rest phase
  | true =>
    rw [CTS_step_true_head]
    rw [AllEmptyAppendants_currentAppendant_nil cts h_app phase]
    simp

/-- **Halt-timing for all-empty-appendants CTS**. -/
theorem AllEmptyAppendants_nSteps_halts
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (data : List Bool) (phase : Nat) :
    ∃ phase', cts.nSteps { data := data, phase := phase } data.length
              = some { data := [], phase := phase' } := by
  induction data generalizing phase with
  | nil => exact ⟨phase, rfl⟩
  | cons head rest ih =>
    have h_step := AllEmptyAppendants_step_explicit cts h_app head rest phase
    obtain ⟨phase', h_rest⟩ := ih ((phase + 1) % cts.appendants.length)
    refine ⟨phase', ?_⟩
    show cts.nSteps { data := head :: rest, phase := phase } (rest.length + 1)
        = some { data := [], phase := phase' }
    rw [CTS_nSteps_succ_unfold, h_step]
    exact h_rest

/-- **AllEmptyAppendants halts in `data.length + 1` steps**. -/
theorem AllEmptyAppendants_nSteps_succ_data_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (data : List Bool) (phase : Nat) :
    cts.nSteps { data := data, phase := phase } (data.length + 1) = none := by
  obtain ⟨phase', h_halt⟩ := AllEmptyAppendants_nSteps_halts cts h_app data phase
  exact CTS_nSteps_none_of_reaches_halted cts _ _ data.length h_halt rfl

/-- **`AllEmptyAppendants_nSteps_drop` (iter 598)**: for an
    all-empty-appendants CTS, after `n ≤ data.length` steps the data
    is exactly `data.drop n`.  Closed form for the trajectory along
    any prefix; generalises `AllEmptyAppendants_nSteps_halts`
    (which is the `n = data.length` boundary case).  Phase is
    existentially quantified — we don't track its mod-length form. -/
theorem AllEmptyAppendants_nSteps_drop
    (cts : CTS) (h_app : AllEmptyAppendants cts) :
    ∀ (data : List Bool) (phase n : Nat), n ≤ data.length →
      ∃ phase', cts.nSteps { data := data, phase := phase } n
                = some { data := data.drop n, phase := phase' } := by
  intro data phase n
  induction n generalizing data phase with
  | zero =>
    intro _
    refine ⟨phase, ?_⟩
    simp [CTS.nSteps]
  | succ m ih =>
    intro h_le
    cases data with
    | nil => simp at h_le
    | cons head rest =>
      have h_step := AllEmptyAppendants_step_explicit cts h_app head rest phase
      have h_le' : m ≤ rest.length := by
        have : (head :: rest).length = rest.length + 1 := by simp [List.length_cons]
        omega
      obtain ⟨phase', h_rest⟩ :=
        ih rest ((phase + 1) % cts.appendants.length) h_le'
      refine ⟨phase', ?_⟩
      rw [CTS_nSteps_succ_unfold, h_step]
      have h_drop_eq : (head :: rest).drop (m + 1) = rest.drop m := rfl
      rw [h_drop_eq]
      exact h_rest

/-- **`AllEmptyAppendants_nSteps_data_length` (iter 596)**: for an
    all-empty-appendants CTS, every `n`-step success exactly drops
    `n` from the data length.  Multi-step generalisation of
    `AllEmptyAppendants_step_data_length`.  Proof: induction on `n`
    using the per-step shrinkage. -/
theorem AllEmptyAppendants_nSteps_data_length
    (cts : CTS) (h_app : AllEmptyAppendants cts) :
    ∀ (cfg : CTSConfig) (n : Nat) (cfg' : CTSConfig),
      cts.nSteps cfg n = some cfg' →
      cfg'.data.length + n = cfg.data.length := by
  intro cfg n
  induction n generalizing cfg with
  | zero =>
    intro cfg' h
    change some cfg = some cfg' at h
    injection h with h_eq
    rw [← h_eq]; simp
  | succ m ih =>
    intro cfg' h
    rw [CTS_nSteps_succ_unfold] at h
    cases h_step : cts.step cfg with
    | none => rw [h_step] at h; cases h
    | some c =>
      rw [h_step] at h
      have h_one : c.data.length + 1 = cfg.data.length :=
        AllEmptyAppendants_step_data_length cts cfg c h_app h_step
      have h_rec : cfg'.data.length + m = c.data.length := ih c cfg' h
      omega

/-- **AllEmptyAppendants implies CTS.Halts**: every empty-appendant
    CTS halts on every config. -/
theorem AllEmptyAppendants_Halts
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig) :
    cts.Halts cfg := by
  apply CTS_nSteps_none_imp_halts
  refine ⟨cfg.data.length + 1, ?_⟩
  obtain ⟨data, phase⟩ := cfg
  exact AllEmptyAppendants_nSteps_succ_data_length cts h_app data phase

/-- **`AllEmptyAppendants_nSteps_none_iff` (iter 600)**: for an
    all-empty-appendants CTS, `nSteps cfg n = none` exactly characterises
    "ran out of data": equivalent to `n > cfg.data.length`.  Combines
    `AllEmptyAppendants_nSteps_drop` (some-on-prefix) with
    `AllEmptyAppendants_nSteps_data_length` (length contradicts) and
    `AllEmptyAppendants_nSteps_succ_data_length` + monotone propagation
    (none past the boundary). -/
theorem AllEmptyAppendants_nSteps_none_iff
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig) (n : Nat) :
    cts.nSteps cfg n = none ↔ n > cfg.data.length := by
  constructor
  · intro h_none
    rcases (Nat.lt_or_ge cfg.data.length n) with h_lt | h_ge
    · exact h_lt
    · exfalso
      obtain ⟨data, phase⟩ := cfg
      obtain ⟨phase', h_some⟩ :=
        AllEmptyAppendants_nSteps_drop cts h_app data phase n h_ge
      rw [h_some] at h_none
      cases h_none
  · intro h_gt
    obtain ⟨data, phase⟩ := cfg
    have h_base : cts.nSteps { data := data, phase := phase } (data.length + 1) = none :=
      AllEmptyAppendants_nSteps_succ_data_length cts h_app data phase
    have h_le : data.length + 1 ≤ n := h_gt
    exact CTS_nSteps_none_propagate cts _ (data.length + 1) n h_le h_base

/-- Constructor for an `AllEmptyAppendants` CTS with `n` empty
    appendants (n ≥ 1). -/
def emptyAppendantsCTS (n : Nat) (h : 0 < n) : CTS :=
  { appendants := List.replicate n []
    nonempty := by rw [List.length_replicate]; exact h }

/-- The constructed CTS is `AllEmptyAppendants`. -/
theorem emptyAppendantsCTS_AllEmpty (n : Nat) (h : 0 < n) :
    AllEmptyAppendants (emptyAppendantsCTS n h) := by
  intro a h_mem
  exact List.eq_of_mem_replicate h_mem

/-- **`emptyAppendantsCTS_Halts` (iter 591)**: any cfg halts under
    `emptyAppendantsCTS n`.  Direct composition of
    `AllEmptyAppendants_Halts` with `emptyAppendantsCTS_AllEmpty`. -/
theorem emptyAppendantsCTS_Halts (n : Nat) (h : 0 < n) (cfg : CTSConfig) :
    (emptyAppendantsCTS n h).Halts cfg :=
  AllEmptyAppendants_Halts (emptyAppendantsCTS n h)
    (emptyAppendantsCTS_AllEmpty n h) cfg

/-- The trivial halting CTS: a single empty appendant.  Every step
    deletes the data head and appends nothing, so after `data.length`
    steps the CTS halts. -/
def trivialHaltCTS : CTS where
  appendants := [[]]
  nonempty := by simp

/-- One step on `trivialHaltCTS` strictly shrinks `data` by 1. -/
theorem trivialHaltCTS_step_shrinks (cfg : CTSConfig)
    (h_active : ctsHalted cfg = false) :
    ∃ cfg', trivialHaltCTS.step cfg = some cfg'
            ∧ cfg'.data.length + 1 = cfg.data.length := by
  cases h_data : cfg.data with
  | nil =>
    simp [ctsHalted, h_data] at h_active
  | cons head tail =>
    refine ⟨{ data := tail,
              phase := (cfg.phase + 1) % trivialHaltCTS.appendants.length }, ?_, ?_⟩
    · simp [CTS.step, h_data, trivialHaltCTS, CTS.currentAppendant]
    · simp

/-- **`trivialHaltCTS_AllEmptyAppendants` (iter 606)**: trivialHaltCTS
    is an instance of the all-empty-appendants pattern.  Direct unfold:
    its only appendant is `[]`. -/
theorem trivialHaltCTS_AllEmptyAppendants : AllEmptyAppendants trivialHaltCTS := by
  intro a h_mem
  simp [trivialHaltCTS] at h_mem
  exact h_mem

/-- **`trivialHaltCTS_nSteps_none_iff` (iter 606)**: `nSteps cfg n = none`
    on `trivialHaltCTS` exactly when `n > cfg.data.length`.  Direct
    application of `AllEmptyAppendants_nSteps_none_iff` to
    `trivialHaltCTS_AllEmptyAppendants`. -/
theorem trivialHaltCTS_nSteps_none_iff (cfg : CTSConfig) (n : Nat) :
    trivialHaltCTS.nSteps cfg n = none ↔ n > cfg.data.length :=
  AllEmptyAppendants_nSteps_none_iff trivialHaltCTS
    trivialHaltCTS_AllEmptyAppendants cfg n

/-- `trivialHaltCTS` halts on any input config. -/
theorem trivialHaltCTS_halts : ∀ (data : List Bool) (phase : Nat),
    trivialHaltCTS.Halts { data := data, phase := phase }
  | [], phase => ⟨0, { data := [], phase := phase },
      by simp [CTS.eval, ctsHalted]⟩
  | head :: tail, phase => by
    have h_step : trivialHaltCTS.step { data := head :: tail, phase := phase }
        = some { data := tail,
                  phase := (phase + 1) % trivialHaltCTS.appendants.length } := by
      simp [CTS.step, trivialHaltCTS, CTS.currentAppendant]
    obtain ⟨fuel, result, h_eval⟩ :=
      trivialHaltCTS_halts tail ((phase + 1) % trivialHaltCTS.appendants.length)
    refine ⟨fuel + 1, result, ?_⟩
    dsimp [CTS.eval]
    have h_nh : ctsHalted { data := head :: tail, phase := phase } = false := by
      simp [ctsHalted]
    rw [if_neg (by simp [h_nh])]
    rw [h_step]
    exact h_eval

/-- **AllEmptyAppendants intermediate `nSteps` evolution (explicit
    phase)**: extension of iter 598's `_nSteps_drop` that pins down
    the phase as `(phase + k) % |append|` instead of leaving it
    existential.  Requires the additional hypothesis `phase < |append|`
    so that the mod normalisation is well-defined.  Strong shape lemma
    for the AllEmptyAppendants trajectory. -/
theorem AllEmptyAppendants_nSteps_drop_explicit
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (data : List Bool) (phase : Nat)
    (h_phase : phase < cts.appendants.length)
    (k : Nat) (h_k : k ≤ data.length) :
    cts.nSteps { data := data, phase := phase } k
    = some { data := data.drop k,
             phase := (phase + k) % cts.appendants.length } := by
  induction k generalizing data phase with
  | zero =>
    show CTS.nSteps cts { data := data, phase := phase } 0 = _
    rw [CTS.nSteps_zero, List.drop_zero, Nat.add_zero, Nat.mod_eq_of_lt h_phase]
  | succ k ih =>
    cases data with
    | nil => simp [List.length_nil] at h_k
    | cons head rest =>
      have h_step := AllEmptyAppendants_step_explicit cts h_app head rest phase
      have h_phase_next : (phase + 1) % cts.appendants.length
                        < cts.appendants.length :=
        Nat.mod_lt _ cts.nonempty
      have h_k_rest : k ≤ rest.length := by
        simp [List.length_cons] at h_k
        omega
      have h_ih := ih rest ((phase + 1) % cts.appendants.length)
                     h_phase_next h_k_rest
      show cts.nSteps { data := head :: rest, phase := phase } (k + 1) = _
      rw [CTS_nSteps_succ_unfold, h_step]
      show cts.nSteps { data := rest, phase := (phase + 1) % cts.appendants.length } k
        = some { data := (head :: rest).drop (k + 1),
                 phase := (phase + (k + 1)) % cts.appendants.length }
      rw [h_ih]
      have h_drop : (head :: rest).drop (k + 1) = rest.drop k := by
        simp [List.drop]
      have h_mod : ((phase + 1) % cts.appendants.length + k)
                    % cts.appendants.length
                = (phase + (k + 1)) % cts.appendants.length := by
        rw [Nat.mod_add_mod]
        congr 1
        omega
      rw [h_drop, h_mod]

/-- **Sharper version of iter 299**: with `phase < |appendants|`,
    `cts.nSteps cfg data.length = some {data := [], phase := (phase
    + data.length) % |append|}`.  Specializes iter 321 (drop-k
    evolution) at `k = data.length` using `data.drop data.length =
    []`.  The phase at halt is now explicit (whereas iter 299 only
    asserts existence of some phase'). -/
theorem AllEmptyAppendants_nSteps_data_length_explicit
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (data : List Bool) (phase : Nat)
    (h_phase : phase < cts.appendants.length) :
    cts.nSteps { data := data, phase := phase } data.length
    = some { data := [],
             phase := (phase + data.length) % cts.appendants.length } := by
  have h := AllEmptyAppendants_nSteps_drop_explicit cts h_app data phase h_phase
            data.length (Nat.le_refl _)
  rw [h]
  congr 1
  show ({ data := data.drop data.length,
          phase := (phase + data.length) % cts.appendants.length } : CTSConfig)
      = { data := [],
          phase := (phase + data.length) % cts.appendants.length }
  rw [List.drop_length]

/-- **`AllEmptyAppendants_nSteps_drop_explicit_data_length` (iter
    698)**: data length after `k` AllEmptyAppendants steps is exactly
    `data.length - k`.  Combines `_nSteps_drop_explicit` with
    `List.length_drop`.  Companion to iter 596's general
    `_nSteps_data_length` (which derives `cfg'.data.length + n =
    cfg.data.length` from any successful `nSteps`); this version just
    states the resulting absolute length under the explicit-phase
    drop form. -/
theorem AllEmptyAppendants_nSteps_drop_explicit_data_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (data : List Bool) (phase : Nat)
    (h_phase : phase < cts.appendants.length)
    (k : Nat) (h_k : k ≤ data.length) :
    ∃ result, cts.nSteps { data := data, phase := phase } k = some result
              ∧ result.data.length = data.length - k := by
  refine ⟨_, AllEmptyAppendants_nSteps_drop_explicit cts h_app data phase
                h_phase k h_k, ?_⟩
  show (data.drop k).length = data.length - k
  exact List.length_drop

/-- **AllEmptyAppendants halt for any `n ≥ data.length + 1`**:
    composing iter 320 (`nSteps cfg (data.length+1) = none`) with
    iter 326's monotone propagation gives `nSteps cfg n = none`
    for every `n ≥ data.length + 1`.  Direct corollary of
    `_nSteps_none_iff` with `n > data.length ↔ data.length + 1 ≤ n`. -/
theorem AllEmptyAppendants_nSteps_ge_data_length_succ
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (data : List Bool) (phase : Nat) (n : Nat)
    (h_n : data.length + 1 ≤ n) :
    cts.nSteps { data := data, phase := phase } n = none := by
  have h_halt :=
    AllEmptyAppendants_nSteps_succ_data_length cts h_app data phase
  exact CTS_nSteps_none_propagate cts _ (data.length + 1) n h_n h_halt

/-- **AllEmptyAppendants `nSteps = some` implies `n ≤ data.length`**:
    contrapositive of iter 327 — if `nSteps cfg n = some result` for
    AllEmptyAppendants, then `n` cannot exceed `cfg.data.length`
    (otherwise iter 327 forces `nSteps = none`, contradiction).
    Bridge lemma for using iter 345 with budget conditions stated in
    terms of `n` rather than `cfg.data.length`. -/
theorem AllEmptyAppendants_nSteps_some_imp_n_le_data_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (data : List Bool) (phase : Nat) (n : Nat) (result : CTSConfig)
    (h : cts.nSteps { data := data, phase := phase } n = some result) :
    n ≤ data.length := by
  rcases Nat.lt_or_ge data.length n with h_gt | h_le
  · exfalso
    have h_ge : data.length + 1 ≤ n := h_gt
    have h_none := AllEmptyAppendants_nSteps_ge_data_length_succ
      cts h_app data phase n h_ge
    rw [h_none] at h
    cases h
  · exact h_le

/-- **AllEmptyAppendants step yields `data.tail`**: regardless of
    head bit (false drops, true drops + appends `[]` = drops), the
    post-step data is `cfg.data.tail`.  Direct case-split via
    `_step_explicit`. -/
theorem AllEmptyAppendants_step_data_tail
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg cfg' : CTSConfig) (h_step : cts.step cfg = some cfg') :
    cfg'.data = cfg.data.tail := by
  obtain ⟨data, phase⟩ := cfg
  cases data with
  | nil => simp [CTS.step] at h_step
  | cons head rest =>
    have h_step' := AllEmptyAppendants_step_explicit cts h_app head rest phase
    rw [h_step'] at h_step
    injection h_step with h_eq
    rw [← h_eq]
    rfl

/-- **AllEmptyAppendants `eval` with insufficient fuel returns
    `none`**: for non-empty data, `eval cfg (data.length - 1)` does
    not have enough fuel to reach the halted state.  Induction on
    data: nil is vacuous (data.length = 0 contradicts `0 < length`);
    cons reduces by one step and recurses on the tail with fuel
    `rest.length - 1` (when `rest.length > 0`) or `eval cfg 0` on a
    non-empty cfg₁ (returns none).  Sharper minimum-fuel companion
    to iter 329's `_eval_data_length`. -/
theorem AllEmptyAppendants_eval_lt_data_length_none
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (data : List Bool) (phase : Nat) (h_pos : 0 < data.length) :
    cts.eval { data := data, phase := phase } (data.length - 1) = none := by
  induction data generalizing phase with
  | nil => simp [List.length_nil] at h_pos
  | cons head rest ih =>
    have h_step := AllEmptyAppendants_step_explicit cts h_app head rest phase
    show cts.eval { data := head :: rest, phase := phase } rest.length = none
    rcases Nat.eq_zero_or_pos rest.length with h_zero | h_pos'
    · -- rest is empty: eval at fuel 0 on cons cfg returns none.
      rw [h_zero]
      simp [CTS.eval, ctsHalted, List.isEmpty]
    · -- rest non-empty: step → cfg₁ = {data := rest, ...}, recurse with rest.length - 1.
      have h_eq : rest.length = (rest.length - 1) + 1 := by omega
      rw [h_eq]
      simp [CTS.eval, ctsHalted, List.isEmpty, h_step]
      exact ih ((phase + 1) % cts.appendants.length) h_pos'

/-- **AllEmptyAppendants `eval` with explicit fuel `data.length`**:
    eval-style fuel halt-witness.  Induction on `data`: nil case
    halts via the fuel-0 branch; cons case steps via `_step_explicit`
    and recurses with fuel `rest.length`. -/
theorem AllEmptyAppendants_eval_data_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (data : List Bool) (phase : Nat) :
    ∃ cfg', cts.eval { data := data, phase := phase } data.length
            = some cfg' := by
  induction data generalizing phase with
  | nil =>
    refine ⟨{ data := [], phase := phase }, ?_⟩
    show cts.eval { data := [], phase := phase } 0 = some _
    simp [CTS.eval, ctsHalted, List.isEmpty]
  | cons head rest ih =>
    obtain ⟨cfg', h_ih⟩ := ih ((phase + 1) % cts.appendants.length)
    refine ⟨cfg', ?_⟩
    have h_step := AllEmptyAppendants_step_explicit cts h_app head rest phase
    show cts.eval { data := head :: rest, phase := phase }
          (rest.length + 1) = some cfg'
    simp [CTS.eval, ctsHalted, List.isEmpty, h_step]
    exact h_ih

/-- **`AllEmptyAppendants_step_phase_explicit` (iter 708)**: under
    AllEmptyAppendants, every step from a non-empty-data cfg advances
    the phase by exactly 1 (mod |appendants|), regardless of head bit.
    Direct case-split via `_step_explicit`.  Companion to
    `_step_data_tail` which characterises the data side; this
    characterises the phase side. -/
theorem AllEmptyAppendants_step_phase_explicit
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (cfg cfg' : CTSConfig) (h_data : cfg.data ≠ [])
    (h_step : cts.step cfg = some cfg') :
    cfg'.phase = (cfg.phase + 1) % cts.appendants.length := by
  obtain ⟨data, phase⟩ := cfg
  cases data with
  | nil => exact absurd rfl h_data
  | cons head rest =>
    have h_step' := AllEmptyAppendants_step_explicit cts h_app head rest phase
    rw [h_step'] at h_step
    injection h_step with h_eq
    rw [← h_eq]


/-- **AllEmptyAppendants halt time = data.length (iter 420)**: any
    halt witness for an AllEmptyAppendants CTS at cfg `{data, phase}`
    must occur exactly at step `k = data.length`, with the halted
    result being `{data := [], phase := phase'}` for some phase'.
    Combines iter 299's `_nSteps_halts` (witness at data.length) with
    iter 406's halt-point uniqueness. -/
theorem AllEmptyAppendants_halt_time_eq_data_length
    (cts : CTS) (h_app : AllEmptyAppendants cts) (data : List Bool) (phase : Nat) :
    ∃ phase', ∀ k r,
        cts.nSteps { data := data, phase := phase } k = some r → ctsHalted r = true →
        k = data.length ∧ r = { data := [], phase := phase' } := by
  obtain ⟨phase', h_witness⟩ := AllEmptyAppendants_nSteps_halts cts h_app data phase
  refine ⟨phase', ?_⟩
  intro k r h_n h_halt
  have h_witness_halt : ctsHalted ({ data := [], phase := phase' } : CTSConfig) = true := by
    simp [ctsHalted]
  exact CTS_nSteps_halt_unique cts _ k data.length r _
    h_n h_halt h_witness h_witness_halt

/-- **AllEmptyAppendants eval at data.length (iter 421)**: composes
    iter 299's `_nSteps_halts` with iter 380's
    `_nSteps_some_halted_imp_eval` to give the eval-form witness:
    `eval cfg data.length = some {[], phase'}`. -/
theorem AllEmptyAppendants_eval_at_data_length
    (cts : CTS) (h_app : AllEmptyAppendants cts) (data : List Bool) (phase : Nat) :
    ∃ phase', cts.eval { data := data, phase := phase } data.length
              = some { data := [], phase := phase' } := by
  obtain ⟨phase', h_n⟩ := AllEmptyAppendants_nSteps_halts cts h_app data phase
  refine ⟨phase', ?_⟩
  apply CTS_nSteps_some_halted_imp_eval cts _ data.length _ h_n
  simp [ctsHalted]

/-- **AllEmptyAppendants has no period (iter 422)**: trivial
    consequence of `AllEmptyAppendants_Halts` + iter 414's
    `CTS_Halts_no_period`.  Any AllEmptyAppendants CTS at any cfg
    cannot have `nSteps cfg p = some cfg` for `p ≥ 1`. -/
theorem AllEmptyAppendants_no_period
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig)
    (p : Nat) (h_pos : p ≥ 1) :
    cts.nSteps cfg p ≠ some cfg :=
  CTS_Halts_no_period cts cfg (AllEmptyAppendants_Halts cts h_app cfg) p h_pos

/-- **AllEmptyAppendants halt time extract package (iter 423)**:
    full halt-witness package — at `data.length`, the halted state
    `{[], phase'}` is reached, AND at every earlier step, the
    intermediate is not halted.  Combines iter 299 (data.length
    witness) with iter 406 (halt-uniqueness) to pin down the halt
    time as data.length and rule out earlier halt points. -/
theorem AllEmptyAppendants_halt_time_extract
    (cts : CTS) (h_app : AllEmptyAppendants cts) (data : List Bool) (phase : Nat) :
    ∃ phase',
      cts.nSteps { data := data, phase := phase } data.length =
        some { data := [], phase := phase' } ∧
      ∀ m < data.length, ∀ r',
        cts.nSteps { data := data, phase := phase } m = some r' → ctsHalted r' = false := by
  obtain ⟨phase', h_witness⟩ := AllEmptyAppendants_nSteps_halts cts h_app data phase
  refine ⟨phase', h_witness, ?_⟩
  intro m h_lt r' h_m
  cases h_halt'_b : ctsHalted r' with
  | false => rfl
  | true =>
    exfalso
    have h_witness_halt : ctsHalted ({ data := [], phase := phase' } : CTSConfig) = true := by
      simp [ctsHalted]
    obtain ⟨h_eq, _⟩ := CTS_nSteps_halt_unique cts _ m data.length r' _
                          h_m h_halt'_b h_witness h_witness_halt
    omega

/-- **AllEmptyAppendants halt time is uniquely data.length (iter
    424)**: if `nSteps cfg k = some r ∧ ctsHalted r`, then `k =
    cfg.data.length`.  Direct extraction of the halt-time field from
    iter 420's uniqueness witness. -/
theorem AllEmptyAppendants_halt_time_is_data_length
    (cts : CTS) (h_app : AllEmptyAppendants cts) (data : List Bool) (phase : Nat)
    (k : Nat) (r : CTSConfig)
    (h_n : cts.nSteps { data := data, phase := phase } k = some r)
    (h_halt : ctsHalted r = true) :
    k = data.length := by
  obtain ⟨_, h_unique⟩ := AllEmptyAppendants_halt_time_eq_data_length cts h_app data phase
  exact (h_unique k r h_n h_halt).1


-- iter 426 System5 Halts step lemmas placed after `System5.Halts` def below.

-- BiTM iter 419 analogue is placed after `BiTM_nSteps_some_halted_imp_eval`
-- below (matching the same forward-reference pattern as iter 394).

/-- **Smoke test for iter 375's Halts-nSteps-succ propagation** using
    `emptyAppendantsCTS 3` and AllEmptyAppendants_Halts.  For data
    `[false, true, false]`, after any `nSteps cfg n = some result`,
    `cts.Halts result` holds (since result is itself an
    AllEmptyAppendants config). -/
example : ∀ n result,
    (emptyAppendantsCTS 3 (by decide)).nSteps
      { data := [false, true, false], phase := 0 } n = some result →
    (emptyAppendantsCTS 3 (by decide)).Halts result := by
  intro n result h
  exact CTS_Halts_nSteps_succ
    (emptyAppendantsCTS 3 (by decide))
    { data := [false, true, false], phase := 0 } n
    (AllEmptyAppendants_Halts _ (emptyAppendantsCTS_AllEmpty 3 _) _)
    result h


/-- **AllEmptyAppendants `nSteps` result data length**: starting from
    `{data, phase}` with `phase < |append|`, after `n` steps with
    `nSteps cfg n = some result`, the result has data length
    `data.length - n`.  Composes iter 321's drop-k evolution with
    `List.length_drop`. -/
theorem AllEmptyAppendants_nSteps_some_data_length
    (cts : CTS) (h_app : AllEmptyAppendants cts)
    (data : List Bool) (phase : Nat) (h_phase : phase < cts.appendants.length)
    (n : Nat) (result : CTSConfig)
    (h : cts.nSteps { data := data, phase := phase } n = some result) :
    result.data.length = data.length - n := by
  have h_n : n ≤ data.length :=
    AllEmptyAppendants_nSteps_some_imp_n_le_data_length cts h_app data phase n result h
  have h_drop := AllEmptyAppendants_nSteps_drop_explicit cts h_app data phase h_phase n h_n
  rw [h] at h_drop
  injection h_drop with h_eq
  rw [h_eq]
  exact List.length_drop

/-- **`AllEmptyAppendants_no_self_loop_step` (iter 710)**: under
    AllEmptyAppendants, no config can step to itself.  Direct
    consequence of `_step_data_length`: a successful step strictly
    decreases data length by 1, but `cfg'.data = cfg.data` would
    force `cfg.data.length = cfg.data.length + 1`, contradiction.
    Companion to iter 422's `_no_period` (which rules out `nSteps p`
    self-loops); this is the sharpened single-step version. -/
theorem AllEmptyAppendants_no_self_loop_step
    (cts : CTS) (h_app : AllEmptyAppendants cts) (cfg : CTSConfig) :
    cts.step cfg ≠ some cfg := by
  intro h_step
  have h_len :=
    AllEmptyAppendants_step_data_length cts cfg cfg h_app h_step
  omega

end TagSystem
