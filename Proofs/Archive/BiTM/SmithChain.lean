/-
  BiTM.SmithChain

  Smith 2007's universality proof of Wolfram's (2,3) TM:
  CTS → System5 → System4 → System3 → System2 → System1 → wolfram23.

  Extracted from `BiTM.CockeMinskyConstruction` in iter 643.
  Originally bundled with Cocke-Minsky 1964 (TM → 2-tag) since both
  share the wolfram23 ground floor; now separated for clarity.

  Cocke-Minsky proper (TM → 2-tag → CTS) lives in
  `BiTM.CockeMinskyConstruction`.  This file picks up where that
  leaves off, defining `SmithReducesFaithful`, the chain emulators,
  and the wolfram23-specific bridges (TM_to_CTS_reduction,
  TM_to_wolfram23_reduction).

  Universality predicates and their abstract closure lemmas
  (`IsUniversal`, `IsSubstantiallyUniversal`, `EmulatesPerStep`,
  `PreservesHalt`, `HaltReduces`) live in `BiTM.CockeMinsky`.

  Contents:
    * `SmithReducesFaithful` / `SmithReducesStepFaithful` predicates
    * Concrete Cocke-Minsky witnesses (trivialHaltTM, twoStepHaltTM,
      threeStepHaltTM, leftMoveHaltTM, linearChainTM)
    * `ctsToSystem5_emulates_with_budget` (Smith Conjecture 0 sorry)
    * `SmithChainEmulators` — bundle of three link-level emulators
    * 2- and 3-link halt-preservation chains
    * Universality of wolfram23 conditioned on `SmithChainEmulators`
    * Wolfram23 periodicity obstructions
-/

import BiTM.Basic
import TagSystem.Basic
import TagSystem.TagToCTS
import TagSystem.HaltsEmpty
import BiTM.HaltInduction
import BiTM.Wolfram23Valid
import BiTM.Wolfram23Periodic
import BiTM.Smith
import BiTM.XorMerge
import BiTM.System5
import BiTM.System4
import BiTM.System5ToSystem4
import BiTM.CTSToSystem5
import BiTM.GeneralizedTM
import BiTM.System1
import BiTM.CockeMinsky
import BiTM.CockeMinskyConstruction

namespace BiTM
namespace CockeMinskyConstruction

open TM
open TagSystem
open BiTM (Config Halts halted step eval CockeMinskyReduces)

-- ============================================================================
-- Smith reduction: faithful strengthening (TODO: prove)
-- ============================================================================

/-- **Faithful** Smith reduction.  Strengthens the weak `SmithReduces`
    (which the trivial halt-collapse encoder discharges) with two extra
    demands:

    1. **Halted-encodes-halted**: halted CTS configs encode to a
       wolfram23 cfg that's already in the halt state.
    2. **Step simulation**: every CTS step is mirrored by a non-trivial
       (n ≥ 1) wolfram23 computation that reaches the encoded next config.

    Following the Cocke-Minsky pattern: the trivial `encode := fun _ _ =>
    halt-cfg` cannot satisfy clause (2) for CTSs that take ≥ 2 non-halt
    steps, since wolfram23 cannot "leave" the halt state once entered.

    **PREDICATE-WEAKNESS NOTE (iter 789)**: clause (1) requires the
    encoder to produce wolfram23 cfgs in state 0.  But
    `not_halts_wolfram23_valid` shows wolfram23 from valid (state ∈
    {1,2}) cfgs never reaches state 0 — so any encoder producing
    valid trajectories fails clause (1).  Equivalently:
    `SmithReducesFaithful` as written REQUIRES the encoder to produce
    state-0 wolfram23 cfgs, but a "faithful" encoder mirroring CTS
    dynamics necessarily produces valid trajectories.  Resolving this
    requires either (a) replacing clause (1) with a tape-pattern
    recognition criterion (e.g., a specific tape sub-pattern denoting
    "halt"), or (b) modeling a "halted" state distinct from state 0.
    Both are research-level reformulations. -/
def SmithReducesFaithful : Prop :=
  ∃ (encode : CTS → CTSConfig → Config),
    (∀ cts ctsCfg, ctsHalted ctsCfg = true → halted (encode cts ctsCfg) = true) ∧
    (∀ cts ctsCfg ctsCfg',
      cts.step ctsCfg = some ctsCfg' →
      ∃ n, n ≥ 1 ∧ nSteps wolfram23 (encode cts ctsCfg) n = some (encode cts ctsCfg'))

/-- **Iter 877: halting-only variant of `SmithReducesFaithful`**.

    The per-step clause is restricted to CTS configs on a halting
    trajectory.  This bypasses the iter 875 termination obstruction:
    System5 (and the rest of the chain to wolfram23) ALWAYS halts,
    so per-step emulation cannot mirror infinite CTS trajectories.
    By restricting to halting CTS configs, the predicate becomes
    satisfiable without requiring an unbounded-tape wolfram23
    construction.

    This variant suffices to imply `SmithReduces` (the weak form
    used by `wolfram23_universal`) — `SmithReducesFaithful_implies_weak`'s
    proof only invokes the per-step clause inside a fuel-bounded
    induction over a halting trajectory, where `cts.Halts ctsCfg`
    is automatically available. -/
def SmithReducesFaithfulHalting : Prop :=
  ∃ (encode : CTS → CTSConfig → Config),
    (∀ cts ctsCfg, ctsHalted ctsCfg = true → halted (encode cts ctsCfg) = true) ∧
    (∀ cts ctsCfg ctsCfg',
      cts.Halts ctsCfg →
      cts.step ctsCfg = some ctsCfg' →
      ∃ n, n ≥ 1 ∧ nSteps wolfram23 (encode cts ctsCfg) n = some (encode cts ctsCfg'))

/-- **Iter 877**: the strong predicate implies the halting variant
    (drop the unused `cts.Halts` hypothesis). -/
theorem SmithReducesFaithful_implies_halting (h : SmithReducesFaithful) :
    SmithReducesFaithfulHalting := by
  obtain ⟨encode, h_halt, h_step⟩ := h
  exact ⟨encode, h_halt, fun cts ctsCfg ctsCfg' _ h_step_eq =>
    h_step cts ctsCfg ctsCfg' h_step_eq⟩

/-- **Iter 878**: the halting variant implies the weak `SmithReduces`.
    Same proof structure as `SmithReducesFaithful_implies_weak` but
    threads `cts.Halts ctsCfg` through the per-step invocation —
    available from the outer `Halts` hypothesis at every inductive
    step (the trajectory remains halting after each step via
    `Halts_step_propagates`-style reasoning).

    This gives the practical path forward: build a halting-only
    encoder satisfying `SmithReducesFaithfulHalting`, then apply
    this theorem to obtain the meaningful `SmithReduces`. -/
theorem SmithReducesFaithfulHalting_implies_weak
    (h : SmithReducesFaithfulHalting) : SmithReduces := by
  obtain ⟨encode, h_halt, h_step⟩ := h
  refine ⟨encode, ?_⟩
  intro cts ctsCfg h_halts
  obtain ⟨fuel, result, h_eval⟩ := h_halts
  induction fuel generalizing ctsCfg with
  | zero =>
    dsimp [CTS.eval] at h_eval
    split at h_eval
    · rename_i h_h
      injection h_eval with h_eq; subst h_eq
      have h_halted := h_halt cts ctsCfg h_h
      exact ⟨0, encode cts ctsCfg, by simp [eval, h_halted]⟩
    · contradiction
  | succ fuel ih =>
    dsimp [CTS.eval] at h_eval
    split at h_eval
    · rename_i h_h
      injection h_eval with h_eq; subst h_eq
      have h_halted := h_halt cts ctsCfg h_h
      exact ⟨0, encode cts ctsCfg, by simp [eval, h_halted]⟩
    · rename_i h_nh
      cases h_step_eq : cts.step ctsCfg with
      | none =>
        have h_halted := (cts_step_none_iff_halted cts ctsCfg).mp h_step_eq
        rw [h_halted] at h_nh
        contradiction
      | some ctsCfg' =>
        rw [h_step_eq] at h_eval
        have h_halts_cfg : cts.Halts ctsCfg := ⟨fuel + 1, result, by
          dsimp [CTS.eval]
          rw [if_neg (by simp [h_nh])]
          rw [h_step_eq]
          exact h_eval⟩
        have ⟨n, _, hn⟩ := h_step cts ctsCfg ctsCfg' h_halts_cfg h_step_eq
        exact BiTM_Halts_nSteps_pred wolfram23 _ n _ hn (ih ctsCfg' h_eval)

/-- The faithful Smith predicate implies the weak one (analogous to
    Cocke-Minsky's case): if every step is simulated and halted CTS
    encodes to halted wolfram23, then by induction on fuel, halting
    CTSs map to halting wolfram23 configs. -/
theorem SmithReducesFaithful_implies_weak (h : SmithReducesFaithful) :
    SmithReduces := by
  obtain ⟨encode, h_halt, h_step⟩ := h
  refine ⟨encode, ?_⟩
  intro cts ctsCfg ⟨fuel, result, h_eval⟩
  induction fuel generalizing ctsCfg with
  | zero =>
    dsimp [CTS.eval] at h_eval
    split at h_eval
    · rename_i h_h
      injection h_eval with h_eq; subst h_eq
      have h_halted := h_halt cts ctsCfg h_h
      exact ⟨0, encode cts ctsCfg, by simp [eval, h_halted]⟩
    · contradiction
  | succ fuel ih =>
    dsimp [CTS.eval] at h_eval
    split at h_eval
    · rename_i h_h
      injection h_eval with h_eq; subst h_eq
      have h_halted := h_halt cts ctsCfg h_h
      exact ⟨0, encode cts ctsCfg, by simp [eval, h_halted]⟩
    · rename_i h_nh
      cases h_step_eq : cts.step ctsCfg with
      | none =>
        have h_halted := (cts_step_none_iff_halted cts ctsCfg).mp h_step_eq
        rw [h_halted] at h_nh
        contradiction
      | some ctsCfg' =>
        rw [h_step_eq] at h_eval
        have ⟨n, _, hn⟩ := h_step cts ctsCfg ctsCfg' h_step_eq
        exact BiTM_Halts_nSteps_pred wolfram23 _ n _ hn (ih ctsCfg' h_eval)

/-- **SORRY[smith-faithful]**: the substantive Smith 2007 simulation.
    Smith's construction uses a hierarchy of intermediate systems
    (system 0..4 in his numbering); formalizing it is a substantial
    multi-iteration project — the BiTM/CockeMinsky.lean WEAK-PREDICATE
    NOTE describes the full chain. -/
theorem smith_reduces_faithful : SmithReducesFaithful := by
  sorry

/-- The *non-trivial* discharge of `BiTM.SmithReduces`: derived from
    the faithful predicate (currently sorry).  When
    `smith_reduces_faithful` is closed, this becomes meaningful. -/
theorem smith_reduces_via_faithful : SmithReduces :=
  SmithReducesFaithful_implies_weak smith_reduces_faithful

-- ============================================================================
-- Trivial witness (for the WEAK predicate only)
-- ============================================================================

/-- **Trivial witness** for `CockeMinskyReduces tm`.

    The predicate `CockeMinskyReduces` only asks that there *exist* some
    `(k, ts, encode)` such that `Halts tm cfg → ts.HaltsEmpty (encode cfg)`.
    Setting `encode := fun _ => []` makes the conclusion trivially true,
    since the empty tag word always halts-empty (`Tag.haltsEmpty_nil`).

    This **closes** `cocke_minsky_reduces` as a theorem rather than an axiom,
    but it does **not** witness a faithful Cocke-Minsky simulation — it
    exposes the fact that `CockeMinskyReduces` as currently defined is too
    weak to capture "TM ⇒ 2-tag system simulation".  A meaningful predicate
    would additionally require the encoding to preserve cfg-distinguishing
    information (e.g. `¬ Halts tm cfg → ¬ ts.HaltsEmpty (encode cfg)` —
    the converse direction).

    See `cocke_minsky_reduces_concrete` for the (incomplete, sorry-stubbed)
    faithful variant. -/
theorem cocke_minsky_reduces_trivial (tm : Machine) :
    CockeMinskyReduces tm :=
  ⟨1, Nat.one_pos, ⟨fun _ => []⟩, fun _ => [],
    fun _ _ => Tag.haltsEmpty_nil _⟩

-- ============================================================================
-- Concrete smoke tests on a trivial halt TM
-- ============================================================================

/-- Smallest possible TM: 1 active state, 1 tape symbol, halts on first step. -/
def trivialHaltTM : Machine where
  numStates := 1
  numSymbols := 1
  transition := fun _ _ => { nextState := 0, write := 0, dir := Dir.R }

def trivialInit : Config := { state := 1, left := [], head := 0, right := [] }

/-- The alphabet for `trivialHaltTM` has 6 symbols
    (1 A-class + 4 B/B'/C/C'-class + 1 S = 6). -/
example : cmSize trivialHaltTM = 6 := rfl

/-- The S marker for `trivialHaltTM` lands at index 5. -/
example : (mkS trivialHaltTM).val = 5 := rfl

/-- The encoding of the empty-tape initial config has length 2. -/
example : (cmEncode trivialHaltTM trivialInit).length = 2 := by
  rw [cmEncode_length trivialHaltTM trivialInit
        (by decide) ⟨by decide, by decide⟩]
  rfl

/-- The post-step config is halted (state 0). -/
example : ∃ cfg', step trivialHaltTM trivialInit = some cfg' ∧ cfg'.state = 0 := by
  refine ⟨_, rfl, ?_⟩
  rfl

/-- One tag step on the encoded `trivialInit` reaches the empty word —
    i.e. `cmStep_sim_empty_halt` instantiates correctly on this TM. -/
example :
    tagNSteps (cmTagSystem trivialHaltTM) (cmEncode trivialHaltTM trivialInit) 1
      = some (cmEncode trivialHaltTM
          { state := 0, left := [0], head := 0, right := [] }) :=
  cmStep_sim_empty_halt trivialHaltTM trivialInit _
    (by decide) ⟨by decide, by decide⟩ (by decide) rfl rfl (by decide) rfl

/-- The full `HaltsEmpty` conclusion holds for `trivialHaltTM` on the
    initial empty-tape config — composing `cmStep_sim_empty_halt`
    (concrete simulation step) with `cmEncode_halted` (cfg' encodes
    to `[]`) and `tagNSteps_eq_nil_implies_haltsEmpty` (the bridge). -/
example : (cmTagSystem trivialHaltTM).HaltsEmpty
            (cmEncode trivialHaltTM trivialInit) := by
  apply tagNSteps_eq_nil_implies_haltsEmpty (cmTagSystem trivialHaltTM) _ 1
  have h_step := cmStep_sim_empty_halt trivialHaltTM trivialInit
    { state := 0, left := [0], head := 0, right := [] }
    (by decide) ⟨by decide, by decide⟩ (by decide) rfl rfl (by decide) rfl
  have h_enc : cmEncode trivialHaltTM
      { state := 0, left := [0], head := 0, right := [] } = [] :=
    cmEncode_halted _ _ rfl
  rw [h_step, h_enc]

/-- The construction is provably correct on configurations of this
    class (the largest class supported by the present alphabet design):
    empty tape, valid head, well-formed state, halting transition. -/
structure IsEmptyTapeHaltConfig (tm : Machine) (cfg : Config) : Prop where
  hk        : 0 < tm.numSymbols
  hq_lo     : 1 ≤ cfg.state
  hq_hi     : cfg.state ≤ tm.numStates
  h_head    : cfg.head < tm.numSymbols
  h_right   : cfg.right = []
  h_left    : cfg.left = []
  h_halt    : (tm.transition cfg.state cfg.head).nextState = 0

/-- Wrapper around `cmStep_sim_empty_halt` keyed by `IsEmptyTapeHaltConfig`. -/
theorem cmStep_sim_of_emptyHalt (tm : Machine) (cfg cfg' : Config)
    (h_cls : IsEmptyTapeHaltConfig tm cfg)
    (h_step : step tm cfg = some cfg') :
    tagNSteps (cmTagSystem tm) (cmEncode tm cfg) 1
      = some (cmEncode tm cfg') :=
  cmStep_sim_empty_halt tm cfg cfg' h_cls.hk
    ⟨h_cls.hq_lo, h_cls.hq_hi⟩ h_cls.h_head
    h_cls.h_right h_cls.h_left h_cls.h_halt h_step

/-- And the corresponding `HaltsEmpty` conclusion. -/
theorem cmHaltsEmpty_of_emptyHalt (tm : Machine) (cfg : Config)
    (h_cls : IsEmptyTapeHaltConfig tm cfg) :
    ∀ cfg', step tm cfg = some cfg' →
      (cmTagSystem tm).HaltsEmpty (cmEncode tm cfg) := by
  intro cfg' h_step
  apply tagNSteps_eq_nil_implies_haltsEmpty (cmTagSystem tm) _ 1
  rw [cmStep_sim_of_emptyHalt tm cfg cfg' h_cls h_step]
  -- cfg'.state = 0 because the transition's nextState = 0
  have h_cfg'_state : cfg'.state = 0 := by
    rw [step_active_state tm cfg cfg' h_step]; exact h_cls.h_halt
  have h_enc : cmEncode tm cfg' = [] :=
    cmEncode_halted _ _ (by simp [halted, h_cfg'_state])
  rw [h_enc]

/-- For any `IsEmptyTapeHaltConfig`, the step result exists. -/
theorem step_exists_emptyTapeHalt (tm : Machine) (cfg : Config)
    (h_cls : IsEmptyTapeHaltConfig tm cfg) :
    ∃ cfg', step tm cfg = some cfg' := by
  apply step_some_of_active
  intro h_zero
  have := h_cls.hq_lo
  omega

/-- Cleaner version: derives `cfg'` internally via `step_some_of_active`. -/
theorem cmHaltsEmpty_emptyTapeHalt (tm : Machine) (cfg : Config)
    (h_cls : IsEmptyTapeHaltConfig tm cfg) :
    (cmTagSystem tm).HaltsEmpty (cmEncode tm cfg) := by
  obtain ⟨cfg', h_step⟩ := step_exists_emptyTapeHalt tm cfg h_cls
  exact cmHaltsEmpty_of_emptyHalt tm cfg h_cls cfg' h_step

/-- 2-state, 1-symbol TM that takes 2 steps before halting:
    `(1, 0) → (2, 0, R)`, `(2, 0) → (0, 0, R)`. -/
def twoStepHaltTM : Machine where
  numStates := 2
  numSymbols := 1
  transition := fun s _ =>
    if s = 1 then { nextState := 2, write := 0, dir := Dir.R }
    else { nextState := 0, write := 0, dir := Dir.R }

def twoStepInit : Config := { state := 1, left := [], head := 0, right := [] }

example : cmSize twoStepHaltTM = 7 := rfl

example : (cmEncode twoStepHaltTM twoStepInit).length = 2 := by
  rw [cmEncode_length twoStepHaltTM twoStepInit
        (by decide) ⟨by decide, by decide⟩]
  rfl

/-- After one TM step, cfg' has state 2 and left tape `[0]`. -/
example :
    step twoStepHaltTM twoStepInit
      = some { state := 2, left := [0], head := 0, right := [] } := rfl

/-- The encoding of the post-step config has length 3 — but the active
    tag production [B(w), A(q', a)] preserves word length (-2 + 2 = 0),
    so one tag step from the length-2 initial encoding cannot reach a
    length-3 word.  This is the concrete witness of the design gap. -/
example :
    (cmEncode twoStepHaltTM
        { state := 2, left := [0], head := 0, right := [] }).length = 3 := by
  rw [cmEncode_length _ _ (by decide) ⟨by decide, by decide⟩]
  rfl

/-- **Faithful** Cocke-Minsky simulation for `twoStepHaltTM`, which takes
    2 TM steps before halting.  Methodology: encode each active config by
    a tag word whose length encodes "TM-steps remaining":
      - state 1 (2 steps to halt) → length-3 word `[a, b, d]`.
      - state ≥ 2 active (1 step to halt) → length-2 word `[d, e]`.
      - halted → `[]`.
    Productions: `a → [e]` (length 1, shrinks word by 1, propagates `e`);
    `d → []` (length 0, shrinks word by 2 to reach `[]`).  Each TM step
    corresponds to one tag step. -/
theorem cocke_minsky_reduces_faithful_twoStepHaltTM :
    CockeMinskyReducesFaithful twoStepHaltTM := by
  let prods : Fin 4 → List (Fin 4) := fun i =>
    if i.val = 0 then [⟨3, by omega⟩]
    else if i.val = 2 then []
    else []
  let enc : Config → TagConfig 4 := fun cfg =>
    if cfg.state = 0 then []
    else if cfg.state = 1 then
      [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩]
    else
      [⟨2, by omega⟩, ⟨3, by omega⟩]
  refine ⟨4, by omega, { productions := prods }, enc, ?_, ?_⟩
  · intro cfg h_halt
    have h_state : cfg.state = 0 := by simp [halted] at h_halt; exact h_halt
    simp [enc, h_state]
  · intro cfg cfg' h_step
    have h_active : cfg.state ≠ 0 := by
      intro h_zero
      have h_n : step twoStepHaltTM cfg = none :=
        (step_none_iff_halted _ _).mpr h_zero
      rw [h_n] at h_step; cases h_step
    have h_cfg'_state := step_active_state twoStepHaltTM cfg cfg' h_step
    by_cases h_s1 : cfg.state = 1
    · -- state 1 → state 2
      have h_cfg'_s : cfg'.state = 2 := by
        rw [h_cfg'_state, h_s1]; rfl
      have h_cfg'_ne0 : cfg'.state ≠ 0 := by rw [h_cfg'_s]; omega
      have h_cfg'_ne1 : cfg'.state ≠ 1 := by rw [h_cfg'_s]; omega
      refine ⟨1, Nat.le_refl _, ?_⟩
      simp [enc, h_s1, h_cfg'_ne0, h_cfg'_ne1, tagNSteps, Tag.step, prods]
    · -- state ≥ 2 → state 0
      have h_cfg'_s : cfg'.state = 0 := by
        rw [h_cfg'_state]
        -- transition (cfg.state, _) for state ≠ 1 returns nextState = 0
        unfold twoStepHaltTM
        simp [h_s1]
      have h_cfg'_halt : halted cfg' = true := by simp [halted, h_cfg'_s]
      refine ⟨1, Nat.le_refl _, ?_⟩
      simp [enc, h_active, h_s1, h_cfg'_s, tagNSteps, Tag.step, prods]

/-- `step` on an already-halted config reduces by `rfl`. -/
example : step trivialHaltTM
    { state := 0, left := [], head := 0, right := [] } = none := rfl

/-- `cmEncode` of any halted config reduces directly by `rfl`,
    even for non-trivial tape contents (the `1 ≤ state` guard fails). -/
example : cmEncode trivialHaltTM
    { state := 0, left := [0, 0], head := 5, right := [1, 2] } = [] := rfl

/-- The same fact via the structural lemma. -/
example : step trivialHaltTM
    { state := 0, left := [], head := 0, right := [] } = none :=
  (step_none_iff_halted _ _).mpr rfl

/-- `trivialInit` satisfies `IsEmptyTapeHaltConfig trivialHaltTM`. -/
def trivialHaltTM_isEmptyHalt :
    IsEmptyTapeHaltConfig trivialHaltTM trivialInit where
  hk := by decide
  hq_lo := by decide
  hq_hi := by decide
  h_head := by decide
  h_right := rfl
  h_left := rfl
  h_halt := by decide

/-- One-liner `HaltsEmpty` proof using the named witness. -/
example : (cmTagSystem trivialHaltTM).HaltsEmpty
            (cmEncode trivialHaltTM trivialInit) :=
  cmHaltsEmpty_emptyTapeHalt _ _ trivialHaltTM_isEmptyHalt

/-- **Faithful** Cocke-Minsky simulation for `trivialHaltTM`.

    Encoding: halted cfg → `[]`; non-halted cfg → length-2 word
    `[⟨0, _⟩, ⟨0, _⟩]`.  The tag system has `productions := fun _ => []`,
    so one tag step on the length-2 word reaches `[]`.

    For `trivialHaltTM` every active cfg halts in one TM step (the
    transition's nextState is always 0), so `encode cfg' = []` matches.
    This proves `CockeMinskyReducesFaithful` is *satisfiable* on at least
    one concrete TM. -/
theorem cocke_minsky_reduces_faithful_trivialHaltTM :
    CockeMinskyReducesFaithful trivialHaltTM := by
  refine ⟨1, Nat.one_pos, { productions := fun _ => [] },
          fun cfg => if halted cfg then ([] : TagConfig 1)
                     else [⟨0, Nat.one_pos⟩, ⟨0, Nat.one_pos⟩], ?_, ?_⟩
  · intro cfg h_halt
    simp [h_halt]
  · intro cfg cfg' h_step
    have h_active : ¬ halted cfg = true := by
      intro h_h
      have h_state : cfg.state = 0 := by simp [halted] at h_h; exact h_h
      have h_n : step trivialHaltTM cfg = none :=
        (step_none_iff_halted _ _).mpr h_state
      rw [h_n] at h_step; cases h_step
    have h_cfg'_state : cfg'.state = 0 := by
      rw [step_active_state trivialHaltTM cfg cfg' h_step]; rfl
    have h_cfg'_halt : halted cfg' = true := by
      simp [halted, h_cfg'_state]
    refine ⟨1, Nat.le_refl _, ?_⟩
    simp [h_active, h_cfg'_halt, tagNSteps, Tag.step]

/-- `trivialHaltTM` halts in one step from every active state. -/
theorem trivialHaltTM_immediate_halt :
    ∀ q s, q ≥ 1 → (trivialHaltTM.transition q s).nextState = 0 :=
  fun _ _ _ => rfl

/-- Same conclusion via the *generic* immediate-halt theorem (one-liner). -/
example : CockeMinskyReducesFaithful trivialHaltTM :=
  cocke_minsky_reduces_faithful_of_immediate_halt trivialHaltTM
    trivialHaltTM_immediate_halt

/-- 1-state, 1-symbol TM that halts immediately on an L-move.
    After step, cfg' = {state=0, left=[], head=0, right=[0]}. -/
def leftMoveHaltTM : Machine where
  numStates := 1
  numSymbols := 1
  transition := fun _ _ => { nextState := 0, write := 0, dir := Dir.L }

def leftMoveInit : Config := { state := 1, left := [], head := 0, right := [] }

example :
    step leftMoveHaltTM leftMoveInit
      = some { state := 0, left := [], head := 0, right := [0] } := rfl

/-- Same simulation property holds for the L-direction halt:
    the post-step cfg' is halted (state 0), so cmEncode cfg' = [],
    and one tag step on the encoded `[A, S]` reaches `[]`. -/
example :
    tagNSteps (cmTagSystem leftMoveHaltTM)
        (cmEncode leftMoveHaltTM leftMoveInit) 1
      = some (cmEncode leftMoveHaltTM
          { state := 0, left := [], head := 0, right := [0] }) :=
  cmStep_sim_empty_halt leftMoveHaltTM leftMoveInit _
    (by decide) ⟨by decide, by decide⟩ (by decide) rfl rfl (by decide) rfl

/-- `leftMoveInit` satisfies `IsEmptyTapeHaltConfig leftMoveHaltTM`. -/
def leftMoveHaltTM_isEmptyHalt :
    IsEmptyTapeHaltConfig leftMoveHaltTM leftMoveInit where
  hk := by decide
  hq_lo := by decide
  hq_hi := by decide
  h_head := by decide
  h_right := rfl
  h_left := rfl
  h_halt := by decide

/-- One-liner `HaltsEmpty` for the L-direction halt. -/
example : (cmTagSystem leftMoveHaltTM).HaltsEmpty
            (cmEncode leftMoveHaltTM leftMoveInit) :=
  cmHaltsEmpty_emptyTapeHalt _ _ leftMoveHaltTM_isEmptyHalt

/-- `leftMoveHaltTM` halts in one step from every active state. -/
theorem leftMoveHaltTM_immediate_halt :
    ∀ q s, q ≥ 1 → (leftMoveHaltTM.transition q s).nextState = 0 :=
  fun _ _ _ => rfl

/-- Faithful predicate for `leftMoveHaltTM` via the generic theorem. -/
example : CockeMinskyReducesFaithful leftMoveHaltTM :=
  cocke_minsky_reduces_faithful_of_immediate_halt leftMoveHaltTM
    leftMoveHaltTM_immediate_halt

/-- 3-state, 1-symbol TM that takes 3 TM steps before halting:
    `1 → 2 → 3 → 0`.  Demonstrates the level-encoding methodology
    extended one more step. -/
def threeStepHaltTM : Machine where
  numStates := 3
  numSymbols := 1
  transition := fun s _ =>
    if s = 1 then { nextState := 2, write := 0, dir := Dir.R }
    else if s = 2 then { nextState := 3, write := 0, dir := Dir.R }
    else { nextState := 0, write := 0, dir := Dir.R }

/-- **Faithful** Cocke-Minsky simulation for `threeStepHaltTM`.
    Encoding (alphabet Fin 6):
      - state 1 → `[a, b, c, d]` (length 4).
      - state 2 → `[c, d, e]`    (length 3).
      - state 3 → `[e, f]`        (length 2).
      - halted → `[]`.
    Productions: `a → [e]`, `c → [f]`, `e → []`; others empty.
    Each TM step = exactly one tag step, shrinking by 1 (until the
    final step, which shrinks by 2). -/
theorem cocke_minsky_reduces_faithful_threeStepHaltTM :
    CockeMinskyReducesFaithful threeStepHaltTM := by
  let prods : Fin 6 → List (Fin 6) := fun i =>
    if i.val = 0 then [⟨4, by omega⟩]
    else if i.val = 2 then [⟨5, by omega⟩]
    else if i.val = 4 then []
    else []
  let enc : Config → TagConfig 6 := fun cfg =>
    if cfg.state = 0 then []
    else if cfg.state = 1 then
      [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]
    else if cfg.state = 2 then
      [⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩]
    else
      [⟨4, by omega⟩, ⟨5, by omega⟩]
  refine ⟨6, by omega, { productions := prods }, enc, ?_, ?_⟩
  · intro cfg h_halt
    have h_state : cfg.state = 0 := by simp [halted] at h_halt; exact h_halt
    simp [enc, h_state]
  · intro cfg cfg' h_step
    have h_active : cfg.state ≠ 0 := by
      intro h_zero
      have h_n : step threeStepHaltTM cfg = none :=
        (step_none_iff_halted _ _).mpr h_zero
      rw [h_n] at h_step; cases h_step
    have h_cfg'_state := step_active_state threeStepHaltTM cfg cfg' h_step
    by_cases h_s1 : cfg.state = 1
    · have h_cfg'_s : cfg'.state = 2 := by
        rw [h_cfg'_state, h_s1]; rfl
      have h_cfg'_ne0 : cfg'.state ≠ 0 := by rw [h_cfg'_s]; omega
      have h_cfg'_ne1 : cfg'.state ≠ 1 := by rw [h_cfg'_s]; omega
      refine ⟨1, Nat.le_refl _, ?_⟩
      simp [enc, h_s1, h_cfg'_s, tagNSteps, Tag.step, prods]
    · by_cases h_s2 : cfg.state = 2
      · have h_cfg'_s : cfg'.state = 3 := by
          rw [h_cfg'_state, h_s2]; rfl
        refine ⟨1, Nat.le_refl _, ?_⟩
        simp [enc, h_s2, h_cfg'_s, tagNSteps, Tag.step, prods]
      · -- state ≥ 3 → state 0
        have h_cfg'_s : cfg'.state = 0 := by
          rw [h_cfg'_state]
          unfold threeStepHaltTM
          simp [h_s1, h_s2]
        refine ⟨1, Nat.le_refl _, ?_⟩
        simp [enc, h_active, h_s1, h_s2, h_cfg'_s, tagNSteps, Tag.step, prods]
        decide

-- ============================================================================
-- Generic linear-chain TM family and its uniform faithful witness
-- ============================================================================

/-- The "linear chain" TM with `D` active states: every active state `q`
    transitions to `q + 1` (or to halt when `q = D`).  Uniform halting in
    `D - q + 1` steps from state `q`.  Generalizes `trivialHaltTM` (D=1),
    `twoStepHaltTM` (D=2), `threeStepHaltTM` (D=3). -/
def linearChainTM (D : Nat) : Machine where
  numStates := D
  numSymbols := 1
  transition := fun q _ =>
    if q < D then { nextState := q + 1, write := 0, dir := Dir.R }
    else { nextState := 0, write := 0, dir := Dir.R }

/-- Build a contiguous run via `n`-recursion (reduces by direct
    pattern match on `n`, not by Nat subtraction or `List.finRange`). -/
def buildRun (m : Nat) (start : Nat) : Nat → List (Fin m)
  | 0 => []
  | n + 1 =>
    if h : start < m then ⟨start, h⟩ :: buildRun m (start + 1) n
    else []

/-- Cons: head equation when `start < m`. -/
theorem buildRun_succ (m start n : Nat) (h : start < m) :
    buildRun m start (n + 1) = ⟨start, h⟩ :: buildRun m (start + 1) n := by
  show (if h : start < m then ⟨start, h⟩ :: buildRun m (start + 1) n else []) = _
  rw [dif_pos h]

/-- Snoc: appending the next element extends a `buildRun` by one. -/
theorem buildRun_snoc (m : Nat) :
    ∀ (n start : Nat) (h : start + n < m),
      buildRun m start (n + 1) = buildRun m start n ++ [⟨start + n, h⟩]
  | 0, start, h => by
    have h0 : start < m := by omega
    show buildRun m start 1 = [] ++ [⟨start + 0, h⟩]
    simp [buildRun, h0]
  | n + 1, start, h => by
    have h0 : start < m := by omega
    have h1 : start + 1 + n < m := by omega
    have ih := buildRun_snoc m n (start + 1) h1
    unfold buildRun
    rw [dif_pos h0, dif_pos h0, List.cons_append, ih]
    have h_eq : start + 1 + n = start + (n + 1) := by omega
    simp [h_eq]

/-- A contiguous run of `n` Fin elements starting at `start`, given a
    bound `start + n ≤ 2 * D`.  Non-dependent on `q` — easier to
    rewrite. -/
def linearChainEncodeRun (D n start : Nat) (_h_bound : start + n ≤ 2 * D) :
    TagConfig (2 * D) :=
  buildRun (2 * D) start n

/-- The level-d word for state `q` in the linear chain: a length-(D+2-q)
    word at positions `2(q-1) .. q+D-1`.  Now defined via the
    non-dependent helper `linearChainEncodeRun`. -/
def linearChainEncodeAtQ (D q : Nat) (h_lo : 1 ≤ q) (h_hi : q ≤ D) :
    TagConfig (2 * D) :=
  linearChainEncodeRun D (D + 2 - q) (2 * (q - 1)) (by omega)

/-- Unfold the level-d encoding twice (head + second + rest) when
    `q < D` (so the word has length ≥ 3). -/
theorem linearChainEncodeAtQ_unfold_two (D q : Nat)
    (h_lo : 1 ≤ q) (h_hi : q ≤ D) (h_q_lt : q < D) :
    linearChainEncodeAtQ D q h_lo h_hi
      = ⟨2 * (q - 1), by omega⟩ :: ⟨2 * (q - 1) + 1, by omega⟩ ::
        buildRun (2 * D) (2 * (q - 1) + 2) (D - q) := by
  unfold linearChainEncodeAtQ linearChainEncodeRun
  rw [show D + 2 - q = (D - q + 1) + 1 from by omega]
  rw [buildRun_succ (2 * D) (2 * (q - 1)) (D - q + 1) (by omega)]
  rw [show D - q + 1 = (D - q) + 1 from rfl]
  rw [buildRun_succ (2 * D) (2 * (q - 1) + 1) (D - q) (by omega)]

/-- For `q = D`, encoding is the length-2 word.  Proof goes through
    after refactoring via `buildRun` (which recurses on `n` directly,
    avoiding `List.finRange`'s dependent-type machinery): `rw [D+2-D=2]`
    rewrites a plain Nat argument, then unfolding `buildRun` twice
    builds the explicit list. -/
theorem linearChainEncodeAtQ_at_D (D : Nat) (hD : 1 ≤ D) :
    linearChainEncodeAtQ D D hD (Nat.le_refl _)
      = [⟨2 * (D - 1), by omega⟩, ⟨2 * (D - 1) + 1, by omega⟩] := by
  unfold linearChainEncodeAtQ linearChainEncodeRun
  have h_diff : D + 2 - D = 2 := by omega
  rw [h_diff]
  unfold buildRun
  rw [dif_pos (by omega : 2 * (D - 1) < 2 * D)]
  unfold buildRun
  rw [dif_pos (by omega : 2 * (D - 1) + 1 < 2 * D)]
  rfl

/-- Congruence: equal `q` arguments give equal encodings (modulo
    proof-irrelevant bound proofs). -/
theorem linearChainEncodeAtQ_congr (D q q' : Nat)
    (h_lo : 1 ≤ q) (h_hi : q ≤ D)
    (h_lo' : 1 ≤ q') (h_hi' : q' ≤ D) (h_eq : q = q') :
    linearChainEncodeAtQ D q h_lo h_hi = linearChainEncodeAtQ D q' h_lo' h_hi' := by
  subst h_eq
  rfl


/-- The level-d word for the linear chain.  States `> D` are treated as
    state `D` (level-1 word).  Uniform across `D ≥ 1`. -/
def linearChainEncode (D : Nat) (cfg : Config) : TagConfig (2 * D) :=
  if cfg.state = 0 then ([] : TagConfig (2 * D))
  else if h_le : cfg.state ≤ D then
    if h_lo : 1 ≤ cfg.state then
      linearChainEncodeAtQ D cfg.state h_lo h_le
    else
      ([] : TagConfig (2 * D))
  else if hD : 1 ≤ D then
    linearChainEncodeAtQ D D hD (Nat.le_refl _)
  else
    ([] : TagConfig (2 * D))

/-- For an active config with state ≥ D, `linearChainEncode D cfg`
    is the level-1 (state-D) encoding. -/
theorem linearChainEncode_at_state_geD (D : Nat) (hD : 1 ≤ D)
    (cfg : Config) (h_active : cfg.state ≠ 0) (h_geD : D ≤ cfg.state) :
    linearChainEncode D cfg = linearChainEncodeAtQ D D hD (Nat.le_refl _) := by
  unfold linearChainEncode
  rw [if_neg h_active]
  by_cases h_le : cfg.state ≤ D
  · -- state = D
    have h_eq : cfg.state = D := by omega
    have h_lo : 1 ≤ cfg.state := by omega
    rw [dif_pos h_le, dif_pos h_lo]
    exact linearChainEncodeAtQ_congr D cfg.state D h_lo h_le hD (Nat.le_refl _) h_eq
  · -- state > D
    rw [dif_neg h_le, dif_pos hD]

/-- For an active config with state in `[1, D]`, the encoding is the
    canonical level-d word. -/
theorem linearChainEncode_at_state_inrange (D : Nat) (cfg : Config)
    (h_lo : 1 ≤ cfg.state) (h_hi : cfg.state ≤ D) :
    linearChainEncode D cfg = linearChainEncodeAtQ D cfg.state h_lo h_hi := by
  unfold linearChainEncode
  have h_active : cfg.state ≠ 0 := by omega
  rw [if_neg h_active, dif_pos h_hi, dif_pos h_lo]

/-- Productions for the linear-chain construction.
    Position `p`:
      - If `p` is even and `p + 4 ≤ 2D`: head of level d ≥ 2.
        Production = `[⟨D + p/2 + 1, _⟩]` — chains to the next level's
        last cell.
      - Otherwise (odd, or p = 2D-2 the level-1 head, or out-of-range):
        production = `[]`. -/
def linearChainProds (D : Nat) : Fin (2 * D) → List (Fin (2 * D)) :=
  fun p =>
    if h : p.val % 2 = 0 ∧ p.val + 4 ≤ 2 * D then
      [⟨D + p.val / 2 + 1, by
        have h_le : p.val + 4 ≤ 2 * D := h.2
        have h_mod : p.val % 2 = 0 := h.1
        have h_pv : p.val / 2 ≤ D - 2 := by
          have h_pv_eq : p.val = 2 * (p.val / 2) := by omega
          omega
        omega⟩]
    else
      ([] : List (Fin (2 * D)))

/-- **SORRY[linear-chain-faithful-step]**: the parametric step-simulation
    proof.  Uniformly closes the chain-step case for every state `q` in
    `[1, D-1]`: tag step on level-d word yields level-(d-1) word.
    Currently scaffolded; halt case (state ≥ D) closed below. -/
theorem cocke_minsky_reduces_faithful_linearChain (D : Nat) (hD : 0 < D) :
    CockeMinskyReducesFaithful (linearChainTM D) := by
  refine ⟨2 * D, by omega, { productions := linearChainProds D },
          linearChainEncode D, ?_, ?_⟩
  · -- halt clause
    intro cfg h_halt
    have h_state : cfg.state = 0 := by simp [halted] at h_halt; exact h_halt
    simp [linearChainEncode, h_state]
  · -- step clause
    intro cfg cfg' h_step
    have h_active : cfg.state ≠ 0 := by
      intro h_zero
      have h_n : step (linearChainTM D) cfg = none :=
        (step_none_iff_halted _ _).mpr h_zero
      rw [h_n] at h_step; cases h_step
    by_cases h_qlt : cfg.state < D
    · -- chain step: cfg.state ∈ [1, D-1]
      have h_lo : 1 ≤ cfg.state := by omega
      have h_le : cfg.state ≤ D := by omega
      have h_cfg'_s : cfg'.state = cfg.state + 1 := by
        rw [step_active_state (linearChainTM D) cfg cfg' h_step]
        unfold linearChainTM
        simp [h_qlt]
      have h_cfg'_lo : 1 ≤ cfg'.state := by omega
      have h_cfg'_le : cfg'.state ≤ D := by omega
      refine ⟨1, Nat.le_refl _, ?_⟩
      rw [tagNSteps_one]
      rw [linearChainEncode_at_state_inrange D cfg h_lo h_le]
      rw [linearChainEncode_at_state_inrange D cfg' h_cfg'_lo h_cfg'_le]
      rw [linearChainEncodeAtQ_unfold_two D cfg.state h_lo h_le h_qlt]
      -- Goal: Tag.step (head :: second :: rest) = some (linearChainEncodeAtQ D cfg'.state ...)
      show some (buildRun (2 * D) (2 * (cfg.state - 1) + 2) (D - cfg.state) ++
                  linearChainProds D ⟨2 * (cfg.state - 1), by omega⟩)
           = some (linearChainEncodeAtQ D cfg'.state h_cfg'_lo h_cfg'_le)
      -- Compute production at position 2(cfg.state - 1)
      have h_pred : (⟨2 * (cfg.state - 1), by omega⟩ : Fin (2 * D)).val % 2 = 0
                    ∧ (⟨2 * (cfg.state - 1), by omega⟩ : Fin (2 * D)).val + 4 ≤ 2 * D := by
        refine ⟨?_, ?_⟩ <;> simp <;> omega
      have h_prod : linearChainProds D ⟨2 * (cfg.state - 1), by omega⟩
                  = [⟨D + cfg.state, by omega⟩] := by
        unfold linearChainProds
        rw [dif_pos h_pred]
        congr 1
        ext
        simp; omega
      rw [h_prod]
      -- RHS: linearChainEncodeAtQ D cfg'.state ... = buildRun (2D) (2*(cfg'.state-1)) (D+2-cfg'.state)
      unfold linearChainEncodeAtQ linearChainEncodeRun
      have h_start_eq : 2 * (cfg'.state - 1) = 2 * (cfg.state - 1) + 2 := by omega
      have h_n_eq : D + 2 - cfg'.state = (D - cfg.state) + 1 := by omega
      rw [h_start_eq, h_n_eq]
      rw [buildRun_snoc (2 * D) (D - cfg.state) (2 * (cfg.state - 1) + 2) (by omega)]
      -- Goal: ... ++ [⟨D + cfg.state, _⟩] = ... ++ [⟨2*(cfg.state-1)+2 + (D-cfg.state), _⟩]
      have h_fin_eq : (⟨D + cfg.state, by omega⟩ : Fin (2 * D)) =
                      ⟨2 * (cfg.state - 1) + 2 + (D - cfg.state), by omega⟩ := by
        apply Fin.ext
        simp; omega
      rw [h_fin_eq]
    · -- halt step: cfg.state ≥ D, transition gives nextState = 0
      have h_qge : D ≤ cfg.state := Nat.le_of_not_lt h_qlt
      have h_cfg'_s : cfg'.state = 0 := by
        rw [step_active_state (linearChainTM D) cfg cfg' h_step]
        unfold linearChainTM
        simp [h_qlt]
      refine ⟨1, Nat.le_refl _, ?_⟩
      rw [tagNSteps_one]
      have h_enc' : linearChainEncode D cfg' = [] := by
        simp [linearChainEncode, h_cfg'_s]
      rw [h_enc']
      rw [linearChainEncode_at_state_geD D hD cfg h_active h_qge]
      rw [linearChainEncodeAtQ_at_D D hD]
      -- Goal: Tag.step ... [⟨2(D-1), _⟩, ⟨2(D-1)+1, _⟩] = some []
      show some (([] : List (Fin (2 * D))) ++
            linearChainProds D ⟨2 * (D - 1), by omega⟩) = some []
      simp [linearChainProds]
      omega

/-- `linearChainTM 1` is itself an immediate-halt TM (only state 1
    is active, and it transitions to 0).  So the immediate-halt
    theorem provides a *second* faithful witness for `linearChainTM 1`
    independently of the parametric proof. -/
theorem linearChainTM_one_immediate_halt :
    ∀ q s, q ≥ 1 → ((linearChainTM 1).transition q s).nextState = 0 := by
  intros q s h_pos
  unfold linearChainTM
  have h_neg : ¬ q < 1 := by omega
  simp [h_neg]

example : CockeMinskyReducesFaithful (linearChainTM 1) :=
  cocke_minsky_reduces_faithful_of_immediate_halt (linearChainTM 1)
    linearChainTM_one_immediate_halt

/-- Re-derivation of `cocke_minsky_reduces_faithful_linearChain` via the
    iter-96 depth abstraction.  Depth function:
    * halted → 0,
    * state `q` with `1 ≤ q ≤ D` → `D + 1 - q` (chain length to halt),
    * state `q > D` → 1 (out-of-range halts immediately).

    For each step, depth decreases by exactly 1 by case analysis on
    `q < D` vs `q ≥ D`.  This validates iter 96 against the third
    universal class — adding `linearChain D` to the immediate-halt and
    two-step-halt cases. -/
theorem cocke_minsky_reduces_faithful_linearChain' (D : Nat) (_hD : 0 < D) :
    CockeMinskyReducesFaithful (linearChainTM D) := by
  apply cocke_minsky_reduces_faithful_of_depth_decreasing (linearChainTM D)
    (fun cfg =>
      if cfg.state = 0 then 0
      else if cfg.state ≤ D then D + 1 - cfg.state
      else 1)
  · intro cfg h_halt
    have h_state : cfg.state = 0 := by simp [halted] at h_halt; exact h_halt
    simp [h_state]
  · intro cfg cfg' h_step
    have h_active : cfg.state ≠ 0 := by
      intro h_z
      have h_n : step (linearChainTM D) cfg = none :=
        (step_none_iff_halted _ _).mpr h_z
      rw [h_n] at h_step; cases h_step
    have h_pos : 1 ≤ cfg.state := by omega
    by_cases h_qlt : cfg.state < D
    · -- Chain step: q < D ⇒ cfg'.state = q + 1.
      have h_cfg'_s : cfg'.state = cfg.state + 1 := by
        rw [step_active_state (linearChainTM D) cfg cfg' h_step]
        unfold linearChainTM; simp [h_qlt]
      have h_cfg'_pos : cfg'.state ≠ 0 := by omega
      have h_cfg'_le : cfg'.state ≤ D := by omega
      simp [h_active, h_cfg'_pos, h_cfg'_le]
      have h_le : cfg.state ≤ D := by omega
      simp [h_le, h_cfg'_s]; omega
    · -- Halt step: q ≥ D ⇒ cfg'.state = 0.
      have h_qge : D ≤ cfg.state := Nat.le_of_not_lt h_qlt
      have h_cfg'_s : cfg'.state = 0 := by
        rw [step_active_state (linearChainTM D) cfg cfg' h_step]
        unfold linearChainTM; simp [h_qlt]
      simp [h_active, h_cfg'_s]
      by_cases h_qD : cfg.state ≤ D
      · -- cfg.state = D (since q ≥ D ∧ q ≤ D)
        have h_eq : cfg.state = D := by omega
        simp [h_eq]
      · simp [h_qD]

/-- 1-state, 3-symbol TM that halts immediately.  Alphabet size scales:
    `cmSize = 1*3 + 4*3 + 1 = 16`. -/
def threeSymbolHaltTM : Machine where
  numStates := 1
  numSymbols := 3
  transition := fun _ _ => { nextState := 0, write := 0, dir := Dir.R }

example : cmSize threeSymbolHaltTM = 16 := rfl

example : (mkS threeSymbolHaltTM).val = 15 := rfl

-- ============================================================================
-- Concrete CTS examples (Smith side)
-- ============================================================================



-- ============================================================================
-- WOLFRAM23 STRUCTURAL NOTE (iter 77 finding)
-- ============================================================================
--
-- `wolfram23.transition 2 2 = {nextState := 1, write := 0, dir := R}`.
-- The comment `B,2 → 0,R,A` in `BiTM/Basic.lean` means "write 0,
-- move R, go to A" (state 1), NOT "go to halt-state 0".
--
-- WOLFRAM23 NEVER REACHES HALT STATE 0 via its declared 6 transitions;
-- only the unreachable `_, _` fall-through has `nextState := 0`.
-- Therefore `Halts wolfram23 cfg` is true ONLY for cfgs that already
-- have `state = 0` — wolfram23's computation never literally halts.
--
-- CONSEQUENCE for `SmithReducesFaithful`:
-- The step-sim clause requires
-- `nSteps wolfram23 (encode ctsCfg) n = some (encode ctsCfg')`.
-- If `ctsCfg` is active and `ctsCfg'` is halted, `encode ctsCfg'`
-- must satisfy `halted (encode ctsCfg') = true` (state 0), but
-- `nSteps` from a non-halted starting cfg never reaches state 0.
-- Hence the FAITHFUL predicate is STRUCTURALLY UNSATISFIABLE for
-- wolfram23 with our current notion of `Halts`.
--
-- Smith's actual universality result is about COMPUTATIONAL
-- simulation (tape pattern), not literal halting.  Capturing it
-- faithfully requires:
--   (a) a different "halts" notion for wolfram23 (e.g., "reaches a
--       specific tape pattern" or "enters a recurring cycle"), OR
--   (b) embedding the CTS halt signal as a tape marker recognizable
--       by some external observer.
-- See the WEAK-PREDICATE NOTE in `BiTM/CockeMinsky.lean` for the
-- broader discussion.

example : (wolfram23.transition 2 2).nextState = 1 := by native_decide
example : (wolfram23.transition 2 2).write = 0 := by native_decide
example : (wolfram23.transition 2 2).dir = Dir.R := by native_decide





-- ============================================================================
-- STATUS SUMMARY
-- ============================================================================
--
-- WEAK PREDICATES (closed via trivial halt-collapse in `BiTM.CockeMinsky`).
-- FAITHFUL PREDICATES: closed via `cocke_minsky_reduces_faithful_universal`
-- (any TM, via 2-symbol self-loop tag system).  Plus parametric depth
-- abstractions for sub-classes.  Open: `cmStep_sim` active case (alphabet
-- redesign — off critical path), `smith_reduces_faithful` (multi-month).
-- See `git log` for granular iter history.

-- ============================================================================
-- SMITH'S CONSTRUCTION: System 5 (PDF `TM23Proof.pdf` p. 30, `system5.pl`)
-- ============================================================================
--
-- A System 5 configuration is a `bag` (multiset of integers, parity-XOR
-- semantics) and a queue of `rules` (each a multiset of integers).
--
-- Step (from the perl interpreter):
--   1. Normalise `bag`: drop entries with even multiplicity.
--   2. Decrement every integer in `bag`.
--   3. Increment every integer in every rule.
--   4. If `0 ∈ bag` (after decrement): pop the first rule, XOR-merge its
--      contents into `bag`.
--   5. Halt if `bag` empty OR no rules left.

-- `xorInsert`, `xorMerge`, and their lemmas live in `BiTM.XorMerge`.


-- ============================================================================
-- CTS → System 5 encoder (PDF p. 28, `cy2s5.pl`)
-- ============================================================================
--
-- The Smith encoder doubles a 2-color CTS into a System 5 program:
-- * Each bit of the CTS working string contributes a pair of integers
--   (4 integers per bit total) at positions determined by a counter
--   that advances by 4 (for '0') or 6 (for '1') per bit.
-- * Each CTS rule (a binary string) is similarly doubled into a System 5
--   rule (a multiset of integers).
-- * For an n-step CTS emulation, n CTS rules are repeated cyclically.
--
-- The encoder takes (cts : CTS, ctsCfg : CTSConfig, n : Nat) and produces
-- a System5Config whose `n`-step evolution corresponds to the n-step CTS
-- evolution from `ctsCfg`.





/-- **`smith_per_step_extension` (iter 803 stub)**: the key Smith
    Conjecture 0 sub-claim, factored out for clarity.  From any
    System 5 state `s5'` whose bag matches the encoder of a non-halted
    CTS `result'`, a single CTS step `result' → result` (with `result`
    also non-halted) is mirrored by some `j ≥ 1` System 5 steps
    yielding a state with bag = `ctsConfigToSystem5Bag result`.

    **PDF reference (Smith 2007 p. 3, Conjecture 0)**: "system 0 can
    emulate any two-colour cyclic tag system for an arbitrary number
    of steps, using a finite-length initial condition...".  The
    emulation goes through `cy2s5.pl` (CTS → system 5 encoder, p. 28),
    then through systems 4, 3, 2, 1 down to system 0 = wolfram23.
    The system 5 step rules (Conjecture 5, p. 15) are:
      1. remove duplicates in pairs from bag,
      2. decrement bag, increment rules,
      3. if 0 ∈ bag, replace with first rule's contents, pop rule.
    Iter 821's `native_decide` verified this emulation is satisfiable
    for `cts := {[[true]]}, cfg := {[false, false]}, N := 3` with the
    iter 818-corrected 4-rules-per-appendant encoder.  Generalising to
    a Lean proof for ALL CTSs is the multi-month research goal.

    The current encoder `ctsToSystem5` would need to satisfy this for
    arbitrary CTSs.  For `AllEmptyAppendants` CTSs the result holds
    via `BiTM.AllEmptyAppendants_System5_per_step_emulation`. -/
theorem smith_per_step_extension
    (cts : CTS) (cfg : CTSConfig) (N : Nat)
    (s5' : System5Config) (m : Nat)
    (h_s5 : System5.nSteps (ctsToSystem5 cts cfg N) m = some s5')
    (result' result : CTSConfig)
    (h_bag : s5'.bag = ctsConfigToSystem5Bag result')
    (h_step : cts.step result' = some result)
    (h_nh' : ctsHalted result' = false)
    (h_nh : ctsHalted result = false) :
    ∃ (j : Nat) (s5_result : System5Config),
      System5.nSteps (ctsToSystem5 cts cfg N) (m + j) = some s5_result
      ∧ s5_result.bag = ctsConfigToSystem5Bag result := by
  -- Dispatch on `result'.data` head (which exists since `ctsHalted result' = false`).
  obtain ⟨data', phase'⟩ := result'
  cases h_data' : data' with
  | nil =>
    exfalso
    simp [ctsHalted, h_data'] at h_nh'
  | cons head' rest' =>
    cases head' with
    | false =>
      -- SORRY[smith-conjecture-0-false-head]: 4-step false-head extension
      -- under arbitrary rules.
      --
      -- AllEmptyAppendants case: `AllEmptyAppendants_System5_4steps_false_head`.
      -- General case: each of 4 D-steps pops a rule (0 ∈ decremented bag),
      -- xor-merges popped rule into bag-after-erase.  The 4 popped rules'
      -- cumulative xor contribution must equal zero (mod parity) for the
      -- bag to reach `aux rest' 1`.  Smith's encoder
      -- (`processCycle`/`encodeAppendant` per `cy2s5.pl` PDF p. 28) is
      -- designed for exactly this cancellation.
      --
      -- VERIFICATION (iter 850-851, BiTM/CTSToSystem5.lean):
      -- m = 4 specifically gives bag = `aux rest' 1` for THREE
      -- different appendant shapes (`[[true]]`, `[[false]]`,
      -- `[[true, false]]`).  Confirms the 4-step pattern is robust
      -- across appendant variations.
      --
      -- **Iter 860 STATUS**: false-head case satisfies the RIGID
      -- predicate `s5_result.bag = ctsConfigToSystem5Bag result`
      -- across 1-bit, 2-bit, 3-bit data (machine-checked via
      -- native_decide for cfg ∈ {[false,false], [false,true],
      -- [false,true,false]} with appendant [[true]], all at m=4,
      -- N=10, all giving the rigid encoder).
      --
      -- **Iter 864 helper**: see `BiTM.schematicFalseHeadBag` in
      -- BiTM/CTSToSystem5.lean = `ctsConfigToSystem5BagAux data 1`.
      -- Concrete target: prove
      --   (System5.nSteps ... 4).map (·.bag.mergeSort)
      --     = some (schematicFalseHeadBag result.data)
      --
      -- **Iter 884-924 cumulative infrastructure (37+ lemmas)**:
      -- - Rules-length tracking (System5_step_rules_length_le, _eq_pop, _eq_dec
      --   in System5.lean) — characterizes when each step is P vs D.
      -- - Encoder cancellation (encodeAppendant_r1_eq_r2_add_2 in
      --   CTSToSystem5.lean) — `firstRule = secondRule.map(·+2)`, the
      --   fundamental algebraic identity behind the iter 871 timed
      --   cancellation pattern.
      -- - Cancellation lifted through processCycle, nCycles,
      --   ctsRulesToSystem5Rules — the first two emitted rules of any
      --   ctsToSystem5 encoder satisfy the cancellation property.
      -- - Cancellation algebra (encodeAppendant_cancellation_algebra) —
      --   `(r1.map(·+1)).map(·-1) = r2.map(·+2)`, capturing the
      --   "decrement-then-pop = pop-incremented-r2" identity at step 2.
      -- - Decrement-erase helpers (decrement_erase_*_cons_aux in
      --   CTSToSystem5.lean) — bag transformation under decrement+erase.
      -- - System5_one_mem_iff_zero_in_decremented (System5.lean) —
      --   bridge `1 ∈ bag ↔ 0 ∈ bag.map(·-1)`.
      --
      -- **Remaining gap (~30-50 lines)**: chain the 4 P-steps abstractly
      -- using the above infrastructure: step 1 pops r1+1, step 2 pops
      -- r2+2 (cancels), steps 3-4 pop empty rules (just decrement).
      -- Net: bag transitions from `aux (false :: rest) 1` to `aux rest 1`.
      sorry
    | true =>
      -- SORRY[smith-conjecture-0-true-head]: 6-step true-head extension
      -- under arbitrary rules.
      --
      -- AllEmptyAppendants case: `AllEmptyAppendants_System5_6steps_true_head`.
      -- General case: 4 D-steps + 2 P-steps, with the 4 popped rules'
      -- xor contribution producing exactly `[1, 3, 4, 6]` minus
      -- `[1, 2, 3, 4]` = ... (the encoded appendant transformation).
      --
      -- CAVEAT (iter 834): for `cts := {[[false]]}, cfg := {[true,
      -- false]}, N ≤ 10, m ≤ 200`, exact bag-match never reached
      -- (verified via native_decide).  Per iter 836 PDF re-reading,
      -- Smith's actual claim may be halt-preservation, not exact
      -- bag-match — so this sorry's CURRENT statement may be too
      -- strong.  See top-level `_emulates_with_budget` doc + iter
      -- 836 comment in CTSToSystem5.lean for predicate-weakness note.
      --
      -- **Iter 859 ROOT-CAUSE PINPOINT** (machine-checked in
      -- BiTM/CTSToSystem5.lean): for `cts := {[[true]]}, cfg :=
      -- {[true, false]}, N := 10`, the bag at m=6 IS the encoder of
      -- `[false, true]`, but with NON-CONTIGUOUS counter offsets:
      -- bag = `ctsConfigToSystem5BagAux [false] 1 ++
      -- ctsConfigToSystem5BagAux [true] 11`.
      --
      -- **Iter 861-863 UNIVERSAL PATTERN** (verified across 5 cases
      -- in CTSToSystem5.lean): true-head step at m=6 universally
      -- gives `bag.mergeSort = schematicTrueHeadBag pre appended`
      -- where pre = result.data.dropLast(|appendant|) and
      -- appended = currentAppendant.
      --
      -- See `BiTM.schematicTrueHeadBag` in CTSToSystem5.lean:
      --   schematicTrueHeadBag pre appended :=
      --     aux pre 1 ++ aux appended (counterAfterWorkingString pre + 6)
      --
      -- The 6-counter gap is CONSTANT (= 2 P-step counter advancement
      -- per Conjecture 5).  Validated across 5 distinct configurations.
      --
      -- **Closure path** (iter 864 status):
      -- 1. Reformulate `_emulates_with_budget` from rigid
      --    `s5_result.bag = ctsConfigToSystem5Bag result` to either:
      --    (a) schematic equality `bag.mergeSort = schematicTrueHeadBag
      --        (result.data.take ...) (currentAppendant)`, OR
      --    (b) halt-preservation only (drop the bag-match conjunct
      --        entirely, per iter 836 reformulation option (a)).
      -- 2. Prove the schematic equality holds at m=6 via concrete
      --    System 5 step-by-step bag tracking (4 D-steps + 2 P-steps).
      sorry

/-- **Iter 1015: Perm-based per-step extension predicate**.  Alternative
    formulation of `smith_per_step_extension` using `List.Perm` instead
    of list equality for the bag predicate.  This captures the parity-
    multiset semantics System5's bag actually represents (orderings
    are not meaningful — only membership/multiset content).

    Iter 1014's `ctsToSystem5_false_head_bag4_perm` directly closes the
    `m = 0, false-head` case of this predicate at the cfg5 trajectory
    level.  However, for `m > 0`, the chain hypothesis `s5'.bag` arises
    from a non-fresh encoder trajectory, where iter 873's negative
    finding shows `s5'.rules` has DIFFERENT counter offsets than a
    fresh `ctsToSystem5 cts result' ?`, so the next 4 steps' popped
    rules differ.  Closure for arbitrary `m` requires either:
    - extending the trajectory analysis to characterize `s5'.rules` at
      step `m` when bag matches (the trajectory invariant gap), OR
    - using a Classical.choose-based encoder akin to
      `cocke_minsky_reduces_faithful_universal`.

    This `Prop` is committed without a proof obligation — it documents
    the alternative formulation that iter 1014 closes at the cfg5
    level, and is the natural target for the Perm-predicate
    reformulation path. -/
def SmithPerStepExtensionPerm : Prop :=
  ∀ (cts : CTS) (cfg : CTSConfig) (N : Nat) (s5' : System5Config) (m : Nat),
    System5.nSteps (ctsToSystem5 cts cfg N) m = some s5' →
    ∀ (result' result : CTSConfig),
      List.Perm s5'.bag (ctsConfigToSystem5Bag result') →
      cts.step result' = some result →
      ctsHalted result' = false →
      ctsHalted result = false →
      ∃ (j : Nat) (s5_result : System5Config),
        System5.nSteps (ctsToSystem5 cts cfg N) (m + j) = some s5_result
        ∧ List.Perm s5_result.bag (ctsConfigToSystem5Bag result)

/-- **Iter 1016: m=0 false-head case of `SmithPerStepExtensionPerm`**.
    At the START of the chain (m=0, fresh encoder), iter 1014's
    `ctsToSystem5_false_head_bag4_perm` directly closes the false-head
    case of `SmithPerStepExtensionPerm`: after `j = 4` System5 steps,
    `s5_result.bag` is a `List.Perm` of `ctsConfigToSystem5Bag result`
    (the encoder bag of the post-CTS-step state).

    This is the strongest cfg5-trajectory closure achievable.  For
    `m > 0` the obstruction is that `s5'.rules` differs from a fresh
    encoder's rules (iter 873).  The chain hypothesis at general `m`
    would require either a trajectory invariant for `s5'.rules` at
    step `m` when bag matches `result'` (the iter 956 algebraic form
    + the cycle-boundary correctness), or a Classical.choose-based
    encoder. -/
theorem smith_per_step_extension_perm_false_head_at_zero
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (result : CTSConfig)
    (h_step : cts.step { data := false :: rest, phase := phase } = some result) :
    ∃ (j : Nat) (s5_result : System5Config),
      System5.nSteps (ctsToSystem5 cts { data := false :: rest, phase := phase } N) j
        = some s5_result
      ∧ List.Perm s5_result.bag (ctsConfigToSystem5Bag result) := by
  have h_result : result.data = rest := by
    unfold CTS.step at h_step
    simp at h_step
    rw [← h_step]
  obtain ⟨r1, r2, tail, h_rules, _, _⟩ :=
    ctsToSystem5_false_head_first_two_rules_ge_seven cts rest phase N h_N
  obtain ⟨s5_4, h_step4, h_perm⟩ :=
    ctsToSystem5_false_head_bag4_perm cts rest phase N h_N r1 r2 tail h_rules
  refine ⟨4, s5_4, h_step4, ?_⟩
  have h_target : ctsConfigToSystem5Bag result = ctsConfigToSystem5BagAux rest 1 := by
    unfold ctsConfigToSystem5Bag
    rw [h_result]
  rw [h_target]
  exact h_perm

/-- **Iter 1088: false-head CTS step's data is the tail**.  Small
    extraction of the false-head step computation: when `cts.step
    {data := false :: rest, phase} = some result`, `result.data = rest`.
    Direct via `unfold CTS.step` + `simp`.  **Reusable helper** —
    the inline computation appearing in iters 1016 and 1087, extracted
    for cleanliness in downstream chain-induction proofs. -/
theorem CTS_step_false_head_data
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := false :: rest, phase := phase } = some result) :
    result.data = rest := by
  unfold CTS.step at h_step
  simp at h_step
  rw [← h_step]

/-- **Iter 1096: ctsConfigToSystem5Bag in terms of data**.  Trivial
    unfolding: `cfg.data = data → ctsConfigToSystem5Bag cfg =
    ctsConfigToSystem5BagAux data 1`.  Direct via the def + rw.
    **Uniform interface** for false-head and true-head step results
    (iters 1094, 1095) and any other place where `cfg.data` is
    explicitly known. -/
theorem ctsConfigToSystem5Bag_data_eq
    (cfg : CTSConfig) (data : List Bool) (h : cfg.data = data) :
    ctsConfigToSystem5Bag cfg = ctsConfigToSystem5BagAux data 1 := by
  unfold ctsConfigToSystem5Bag
  rw [h]

/-- **Iter 1094: encoder bag of false-head step result**.  Direct
    consequence of iter 1088: when `cts.step false-head = some result`,
    `ctsConfigToSystem5Bag result = ctsConfigToSystem5BagAux rest 1`.
    This extracts the `h_target` computation appearing in iter 1087's
    body as a reusable helper.  Refactored (iter 1097) to use iter 1096. -/
theorem ctsConfigToSystem5Bag_false_head_step_result_eq
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := false :: rest, phase := phase } = some result) :
    ctsConfigToSystem5Bag result = ctsConfigToSystem5BagAux rest 1 :=
  ctsConfigToSystem5Bag_data_eq result rest
    (CTS_step_false_head_data cts rest phase result h_step)

/-- **Iter 1089: true-head CTS step's data is tail ++ current appendant**.
    Companion to iter 1088 for the true-head case: when `cts.step
    {data := true :: rest, phase} = some result`, `result.data = rest
    ++ cts.currentAppendant phase`.  Direct via `unfold CTS.step` +
    `simp`.  **Reusable helper** for downstream true-head chain-
    induction proofs. -/
theorem CTS_step_true_head_data
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := true :: rest, phase := phase } = some result) :
    result.data = rest ++ cts.currentAppendant phase := by
  unfold CTS.step at h_step
  simp at h_step
  rw [← h_step]

/-- **Iter 1229: post-step false-head encoder bag length**.  Direct
    from iter 1094 + `_length`: `(ctsConfigToSystem5Bag result).length
    = 4 * rest.length` for `result = cts.step (false-head config)`. -/
theorem ctsConfigToSystem5Bag_false_head_step_result_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := false :: rest, phase := phase } = some result) :
    (ctsConfigToSystem5Bag result).length = 4 * rest.length := by
  rw [ctsConfigToSystem5Bag_false_head_step_result_eq cts rest phase result h_step]
  exact ctsConfigToSystem5BagAux_length rest 1

/-- **Iter 1230: post-step false-head bag non-empty iff rest non-empty**.
    Direct from iter 1229 + `length_eq_zero_iff`. -/
theorem ctsConfigToSystem5Bag_false_head_step_result_nonempty_iff
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := false :: rest, phase := phase } = some result) :
    ctsConfigToSystem5Bag result ≠ [] ↔ rest ≠ [] := by
  constructor
  · intro h h_rest
    apply h
    have h_len := ctsConfigToSystem5Bag_false_head_step_result_length cts rest phase result h_step
    rw [h_rest] at h_len
    simp at h_len
    exact h_len
  · intro h_rest h_bag
    have h_len := ctsConfigToSystem5Bag_false_head_step_result_length cts rest phase result h_step
    rw [h_bag, List.length_nil] at h_len
    have : rest.length = 0 := by omega
    exact h_rest (List.length_eq_zero_iff.mp this)

/-- **Iter 1231: post-step true-head bag non-empty iff rest or appendant
    non-empty**.  Direct from iter 1228 (length = 4 * (rest.length +
    appendant.length)) — bag empty iff length = 0 iff both rest and
    appendant empty.  **Useful for halt analysis at the true-head
    branch.** -/
theorem ctsConfigToSystem5Bag_true_head_step_result_nonempty_iff
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := true :: rest, phase := phase } = some result) :
    ctsConfigToSystem5Bag result ≠ [] ↔
      rest ≠ [] ∨ cts.currentAppendant phase ≠ [] := by
  have h_len := ctsConfigToSystem5Bag_true_head_step_result_length cts rest phase result h_step
  constructor
  · intro h
    cases h_rest : rest with
    | nil =>
      cases h_app : cts.currentAppendant phase with
      | nil =>
        exfalso; apply h
        rw [h_rest, h_app, List.length_nil, Nat.add_zero, Nat.mul_zero] at h_len
        exact List.length_eq_zero_iff.mp h_len
      | cons hd tl =>
        right
        exact List.cons_ne_nil hd tl
    | cons hd tl =>
      left
      exact List.cons_ne_nil hd tl
  · intro h_or h_bag
    rw [h_bag, List.length_nil] at h_len
    have h_rest_zero : rest.length = 0 := by omega
    have h_app_zero : (cts.currentAppendant phase).length = 0 := by omega
    have h_rest_nil : rest = [] := List.length_eq_zero_iff.mp h_rest_zero
    have h_app_nil : cts.currentAppendant phase = [] := List.length_eq_zero_iff.mp h_app_zero
    rcases h_or with h | h
    · exact h h_rest_nil
    · exact h h_app_nil

/-- **Iter 1296: cts.step true-head result data length**.
    `result.data.length = rest.length + (cts.currentAppendant phase).length`.
    Direct from iter 1089 + `List.length_append`. -/
theorem CTS_step_true_head_data_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := true :: rest, phase := phase } = some result) :
    result.data.length = rest.length + (cts.currentAppendant phase).length := by
  rw [CTS_step_true_head_data cts rest phase result h_step, List.length_append]

/-- **Iter 1297: cts.step false-head result data length**.
    `result.data.length = rest.length`.  Direct from iter 1088. -/
theorem CTS_step_false_head_data_length
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := false :: rest, phase := phase } = some result) :
    result.data.length = rest.length := by
  rw [CTS_step_false_head_data cts rest phase result h_step]

/-- **Iter 1298: false-head cts.step decreases data length by 1**.
    `result.data.length = cfg.data.length - 1` for false-head.
    Direct from iter 1297. -/
theorem CTS_step_false_head_data_length_pred
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := false :: rest, phase := phase } = some result) :
    result.data.length + 1 = (false :: rest).length := by
  rw [CTS_step_false_head_data_length cts rest phase result h_step]
  simp [List.length_cons]

/-- **Iter 1299: true-head cts.step changes data length by appendant.length - 1**.
    `result.data.length = cfg.data.length - 1 + appendant.length`.
    Direct from iter 1296. -/
theorem CTS_step_true_head_data_length_diff
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := true :: rest, phase := phase } = some result) :
    result.data.length + 1 = (true :: rest).length + (cts.currentAppendant phase).length := by
  rw [CTS_step_true_head_data_length cts rest phase result h_step]
  simp [List.length_cons]
  omega

/-- **Iter 1304: cts.step false-head result halted iff rest empty**. -/
theorem CTS_step_false_head_result_halted_iff
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := false :: rest, phase := phase } = some result) :
    ctsHalted result = true ↔ rest = [] := by
  rw [ctsHalted_true_iff_data_eq_nil,
      CTS_step_false_head_data cts rest phase result h_step]

/-- **Iter 1305: cts.step true-head result halted iff rest and
    appendant both empty**. -/
theorem CTS_step_true_head_result_halted_iff
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := true :: rest, phase := phase } = some result) :
    ctsHalted result = true ↔ rest = [] ∧ cts.currentAppendant phase = [] := by
  rw [ctsHalted_true_iff_data_eq_nil,
      CTS_step_true_head_data cts rest phase result h_step]
  constructor
  · intro h
    have h_len : (rest ++ cts.currentAppendant phase).length = 0 := by
      rw [h]; rfl
    rw [List.length_append] at h_len
    have h_rest_zero : rest.length = 0 := by omega
    have h_app_zero : (cts.currentAppendant phase).length = 0 := by omega
    exact ⟨List.length_eq_zero_iff.mp h_rest_zero,
           List.length_eq_zero_iff.mp h_app_zero⟩
  · intro ⟨h_rest, h_app⟩
    rw [h_rest, h_app]
    rfl

/-- **Iter 1323: cts.step full-structure decomposition**.  When
    `cts.step cfg = some result`, the result has explicit data/phase
    structure parameterized by the head bit. -/
theorem CTS_step_full_decomp (cts : CTS) (cfg result : CTSConfig)
    (h_step : cts.step cfg = some result) :
    ∃ head rest, cfg.data = head :: rest
              ∧ result.data = (if head then rest ++ cts.currentAppendant cfg.phase else rest)
              ∧ result.phase = (cfg.phase + 1) % cts.appendants.length := by
  unfold CTS.step at h_step
  cases h_data : cfg.data with
  | nil => rw [h_data] at h_step; simp at h_step
  | cons head rest =>
    rw [h_data] at h_step
    simp at h_step
    refine ⟨head, rest, ?_, ?_, ?_⟩
    · rfl
    · rw [← h_step]
    · rw [← h_step]

/-- **Iter 1095: encoder bag of true-head step result**.  Companion
    to iter 1094 for the true-head case: when `cts.step true-head =
    some result`, `ctsConfigToSystem5Bag result = ctsConfigToSystem5BagAux
    (rest ++ cts.currentAppendant phase) 1`.  Direct via iter 1089
    + `unfold + rw`.  **Reusable helper** for downstream true-head
    chain-induction proofs. -/
theorem ctsConfigToSystem5Bag_true_head_step_result_eq
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := true :: rest, phase := phase } = some result) :
    ctsConfigToSystem5Bag result
      = ctsConfigToSystem5BagAux (rest ++ cts.currentAppendant phase) 1 :=
  ctsConfigToSystem5Bag_data_eq result _
    (CTS_step_true_head_data cts rest phase result h_step)

/-- **Iter 1092: ctsHalted ⇔ data is empty**.  Definitional unfolding
    of `ctsHalted = data.isEmpty` as an iff: `ctsHalted cfg = false
    ↔ cfg.data ≠ []`.  Direct via `unfold + simp`.  **Reusable helper**
    for chain-induction proofs that need to convert between halt
    hypotheses and data-non-empty hypotheses. -/
theorem ctsHalted_eq_false_iff (cfg : CTSConfig) :
    ctsHalted cfg = false ↔ cfg.data ≠ [] := by
  unfold ctsHalted
  simp

/-- **Iter 1091: false-head CTS step preserves non-halted via rest**.
    When `cts.step false-head = some result` and `ctsHalted result = false`,
    `rest ≠ []`.  Composes iter 1088 (result.data = rest) + iter 1092
    (ctsHalted ⇔ data empty).  **Reusable helper** when applying
    iter 1087 in chain-induction contexts where the predicate
    `SmithPerStepExtensionPerm` provides `ctsHalted result = false`
    as a hypothesis. -/
theorem CTS_step_false_head_rest_nonempty
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := false :: rest, phase := phase } = some result)
    (h_not_halt : ctsHalted result = false) :
    rest ≠ [] := by
  have h_data : result.data = rest :=
    CTS_step_false_head_data cts rest phase result h_step
  have h_ne : result.data ≠ [] := (ctsHalted_eq_false_iff result).mp h_not_halt
  rw [h_data] at h_ne
  exact h_ne

/-- **Iter 1098: true-head CTS step preserves non-halted via tail++app**.
    When `cts.step true-head = some result` and `ctsHalted result = false`,
    `rest ++ cts.currentAppendant phase ≠ []`.  Composes iter 1089
    (result.data = rest ++ appendant) + iter 1092 (ctsHalted ⇔ data
    empty).  **Reusable helper** for true-head chain-induction
    contexts. -/
theorem CTS_step_true_head_data_nonempty
    (cts : CTS) (rest : List Bool) (phase : Nat) (result : CTSConfig)
    (h_step : cts.step { data := true :: rest, phase := phase } = some result)
    (h_not_halt : ctsHalted result = false) :
    rest ++ cts.currentAppendant phase ≠ [] := by
  have h_data : result.data = rest ++ cts.currentAppendant phase :=
    CTS_step_true_head_data cts rest phase result h_step
  have h_ne : result.data ≠ [] := (ctsHalted_eq_false_iff result).mp h_not_halt
  rw [h_data] at h_ne
  exact h_ne


/-- **Iter 1087: Per-step extension for arbitrary false-head Perm-chain
    points (FULL CHAIN-INDUCTION STEP)**.  Generalizes iter 1016 from
    the cfg5 starting point (m=0) to any starting `bag` Perm-equivalent
    to the false-head encoder bag.  Composes iter 1086's
    `ctsConfigToSystem5Bag_false_head_perm_step4_bag4_perm` with the
    false-head step characterization (cts.step on false-head config
    yields data = rest).  **The Perm-based per-step extension is now
    provable for arbitrary chain points in the false-head case** — the
    `SmithPerStepExtensionPerm` predicate's false-head branch is
    discharged at any chain point (not just m=0). -/
theorem smith_per_step_extension_perm_false_head_general
    (cts : CTS) (rest : List Bool) (phase : Nat) (N : Nat) (h_N : N ≥ 1)
    (bag : List Int)
    (h_perm : List.Perm bag (ctsConfigToSystem5Bag
                  { data := false :: rest, phase := phase }))
    (result : CTSConfig)
    (h_step : cts.step { data := false :: rest, phase := phase } = some result) :
    ∃ (s5_result : System5Config),
      System5.nSteps ⟨bag, ctsRulesToSystem5Rules cts
        { data := false :: rest, phase := phase } N⟩ 4 = some s5_result
      ∧ List.Perm s5_result.bag (ctsConfigToSystem5Bag result) := by
  obtain ⟨s5_4, h_step4, h_perm_aux⟩ :=
    ctsConfigToSystem5Bag_false_head_perm_step4_bag4_perm cts rest phase N h_N bag h_perm
  refine ⟨s5_4, h_step4, ?_⟩
  rw [ctsConfigToSystem5Bag_false_head_step_result_eq cts rest phase result h_step]
  exact h_perm_aux

/-- **Iter 1099: worked example of iter 1087 at a concrete CTS**.
    Demonstrates that `smith_per_step_extension_perm_false_head_general`
    closes a specific CTS chain.  For `exampleCTS = {appendants := [[true]]}`
    and false-head config `{data := [false, false], phase := 0}`,
    the post-step CTS state is `{data := [false], phase := 0}`, and
    iter 1087 gives a 4-step System5 trajectory ending at a bag
    Perm-equivalent to the post-step encoder bag. -/
example (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_result,
      System5.nSteps ⟨ctsConfigToSystem5Bag { data := [false, false], phase := 0 },
        ctsRulesToSystem5Rules exampleCTS { data := [false, false], phase := 0 } N⟩ 4
        = some s5_result
      ∧ List.Perm s5_result.bag
          (ctsConfigToSystem5Bag { data := [false], phase := 0 }) := by
  apply smith_per_step_extension_perm_false_head_general exampleCTS [false] 0 N h_N _
    (List.Perm.refl _)
  native_decide

/-- **Iter 1100: worked example of iter 1087 with a non-trivial Perm**.
    Companion to iter 1099 demonstrating iter 1087 also works with a
    Perm that's NOT `Perm.refl` — here the bag is the reversed encoder
    bag, related via `List.reverse_perm`.  This confirms iter 1087's
    full generality: the chain hypothesis can be any Perm-equivalent
    bag, not just the encoder bag itself. -/
example (N : Nat) (h_N : N ≥ 1) :
    ∃ s5_result,
      System5.nSteps ⟨(ctsConfigToSystem5Bag
          { data := [false, false], phase := 0 }).reverse,
        ctsRulesToSystem5Rules exampleCTS { data := [false, false], phase := 0 } N⟩ 4
        = some s5_result
      ∧ List.Perm s5_result.bag
          (ctsConfigToSystem5Bag { data := [false], phase := 0 }) := by
  apply smith_per_step_extension_perm_false_head_general exampleCTS [false] 0 N h_N _
    (List.reverse_perm _)
  native_decide

/-- **REFACTOR: trajectory-relative false-head per-step extension**.
    Bridges iter 1087 (`smith_per_step_extension_perm_false_head_general`)
    to the chain-induction signature of `SmithPerStepExtensionPerm`,
    given the trajectory rules invariant `s5'.rules =
    ctsRulesToSystem5Rules cts {false :: rest', phase'} N` as an explicit
    hypothesis.

    With this hypothesis, the false-head per-step extension at any
    chain point `m` is unconditional.  The remaining gap is proving the
    rules invariant itself (the cycle-boundary correctness gap noted in
    the plan doc) — which is a SEPARATE, focused obligation, not buried
    inside the per-step extension itself. -/
theorem smith_per_step_extension_perm_false_head_via_rules_invariant
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1)
    (s5' : System5Config) (m : Nat)
    (h_s5 : System5.nSteps (ctsToSystem5 cts cfg N) m = some s5')
    (rest' : List Bool) (phase' : Nat) (result : CTSConfig)
    (h_perm : List.Perm s5'.bag
       (ctsConfigToSystem5Bag { data := false :: rest', phase := phase' }))
    (h_step : cts.step { data := false :: rest', phase := phase' } = some result)
    (h_rules : s5'.rules = ctsRulesToSystem5Rules cts
                  { data := false :: rest', phase := phase' } N) :
    ∃ s5_result,
      System5.nSteps (ctsToSystem5 cts cfg N) (m + 4) = some s5_result
      ∧ List.Perm s5_result.bag (ctsConfigToSystem5Bag result) := by
  obtain ⟨s5_result, h_step4, h_perm_result⟩ :=
    smith_per_step_extension_perm_false_head_general cts rest' phase' N h_N
      s5'.bag h_perm result h_step
  refine ⟨s5_result, ?_, h_perm_result⟩
  rw [System5.nSteps_add, h_s5]
  have h_s5_unfold : s5' = ⟨s5'.bag, ctsRulesToSystem5Rules cts
        { data := false :: rest', phase := phase' } N⟩ := by
    cases s5' with
    | mk bag rules =>
      simp only at h_rules
      simp [h_rules]
  rw [h_s5_unfold]
  exact h_step4

/-- **Smith's emulation claim, generalised form** (PDF Conjecture 0):
    with separate System 5 budget `N ≥ n`, the System 5 starting cfg
    `ctsToSystem5 cts cfg N` is fixed across the induction on `n`,
    making the proof tractable.  The original
    `ctsToSystem5_emulates` is recovered by setting `N := n`. -/
theorem ctsToSystem5_emulates_with_budget (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ∀ n result, n ≤ N → cts.nSteps cfg n = some result →
      ctsHalted result = false →
      ∃ (m : Nat) (s5_result : System5Config),
        System5.nSteps (ctsToSystem5 cts cfg N) m = some s5_result
        ∧ s5_result.bag = ctsConfigToSystem5Bag result := by
  intro n
  induction n with
  | zero =>
    intro result _ h _
    refine ⟨0, ctsToSystem5 cts cfg N, rfl, ?_⟩
    simp [CTS.nSteps] at h
    rw [← h]; rfl
  | succ n ih =>
    intro result h_le h h_not_halt
    obtain ⟨result', h_n, h_step⟩ := CTS_nSteps_succ_decompose cts cfg result n h
    have h_not_halt' : ctsHalted result' = false :=
      cts_step_some_not_halted cts result' result h_step
    obtain ⟨m, s5', h_s5_eq, h_bag⟩ :=
      ih result' (Nat.le_of_succ_le h_le) h_n h_not_halt'
    -- ITER 810 FINDING: this sorry may be UNCLOSEABLE as stated.
    -- For cts = {appendants := [[true]]}, cfg = {data := [false, false]},
    -- N = 10, no m ≤ 100 yields System 5 bag = ctsConfigToSystem5Bag
    -- {data := [false], _} = [1, 2, 3, 4].  See concrete native_decide
    -- counterexamples in BiTM/CTSToSystem5.lean.  Suggests the encoder
    -- `ctsToSystem5` doesn't faithfully implement Smith's `cy2s5.pl`,
    -- OR the predicate `ctsToSystem5_emulates_with_budget` is too
    -- strong (claims more than Smith's PDF establishes).  Resolution
    -- requires either fixing the encoder or weakening the predicate.
    obtain ⟨j, s5_result, h_j, h_j_bag⟩ :=
      smith_per_step_extension cts cfg N s5' m h_s5_eq result' result
        h_bag h_step h_not_halt' h_not_halt
    exact ⟨m + j, s5_result, h_j, h_j_bag⟩

/-- **Iter 1017: Perm-based ctsToSystem5_emulates_with_budget**.
    Conditional version of `ctsToSystem5_emulates_with_budget` using
    `List.Perm` for the bag predicate, conditional on
    `SmithPerStepExtensionPerm` (iter 1015).  Provable WITHOUT sorry
    given the per-step extension as a hypothesis.

    Inductive structure:
    - n = 0: trivial, m = 0, bag = ctsConfigToSystem5Bag cfg = ctsConfigToSystem5Bag result.
    - n + 1: by IH, get s5' with Perm bag-equivalent to result'.
      Then apply the per-step extension hypothesis to extend by j steps.

    Once `SmithPerStepExtensionPerm` is proven (via either trajectory
    invariant for arbitrary s5' or a Classical.choose-based encoder),
    this theorem becomes unconditional and gives a Perm-based emulation
    proof. -/
theorem ctsToSystem5_emulates_with_budget_perm
    (h_per_step : SmithPerStepExtensionPerm)
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ∀ n result, n ≤ N → cts.nSteps cfg n = some result →
      ctsHalted result = false →
      ∃ (m : Nat) (s5_result : System5Config),
        System5.nSteps (ctsToSystem5 cts cfg N) m = some s5_result
        ∧ List.Perm s5_result.bag (ctsConfigToSystem5Bag result) := by
  intro n
  induction n with
  | zero =>
    intro result _ h _
    refine ⟨0, ctsToSystem5 cts cfg N, rfl, ?_⟩
    simp [CTS.nSteps] at h
    rw [← h]
    exact List.Perm.refl _
  | succ n ih =>
    intro result h_le h h_not_halt
    obtain ⟨result', h_n, h_step⟩ := CTS_nSteps_succ_decompose cts cfg result n h
    have h_not_halt' : ctsHalted result' = false :=
      cts_step_some_not_halted cts result' result h_step
    obtain ⟨m, s5', h_s5_eq, h_bag⟩ :=
      ih result' (Nat.le_of_succ_le h_le) h_n h_not_halt'
    obtain ⟨j, s5_result, h_j, h_j_bag⟩ :=
      h_per_step cts cfg N s5' m h_s5_eq result' result
        h_bag h_step h_not_halt' h_not_halt
    exact ⟨m + j, s5_result, h_j, h_j_bag⟩

/-- **Smith's emulation claim** (PDF Conjecture 0 + the chain through
    Conjectures 1–5): for any CTS `cts` and starting cfg `ctsCfg`,
    System 5 emulation reproduces the n-step CTS evolution **on the
    non-halt prefix**.

    Iter-257 statement-flaw fix: requires `ctsHalted result = false`
    (the bag-equality at halt is unsatisfiable; halt-preservation is a
    separate question).  Derived from `_with_budget` by `N := n`. -/
theorem ctsToSystem5_emulates (cts : CTS) (cfg : CTSConfig) :
    ∀ n result, cts.nSteps cfg n = some result →
      ctsHalted result = false →
      ∃ (m : Nat) (s5_result : System5Config),
        System5.nSteps (ctsToSystem5 cts cfg n) m = some s5_result
        ∧ s5_result.bag = ctsConfigToSystem5Bag result :=
  fun n result h h_nh =>
    ctsToSystem5_emulates_with_budget cts cfg n n result (Nat.le_refl n) h h_nh

-- ============================================================================
-- SMITH'S CONSTRUCTION: System 4 (PDF `TM23Proof.pdf` p. 34, `system4.pl`)
-- ============================================================================
--
-- System 4 has a list of "elements" (each either a star `_` or a set of ints),
-- an `active` index, and a state ∈ {A, B, C}.
--
-- Step rules (5 total, per the `system4.pl` interpreter):
--   Rule 1 (set in A): active--; if at 0, state→B.
--   Rule 2 (star in A): remove the star (splice), state→B.
--   Rule 3 (set in B/C): decrement every int in the set; if 0 was present,
--       toggle state B↔C; active++.
--   Rule 4 (star in B): remove the star, active--, state→A.
--   Rule 5 (star in C): active++, toggle membership of `1` in elems[active].
--
-- `cy2s4.pl` (PDF p. 32) emulates System 5 with System 4 by encoding each
-- System 5 set as a System 4 set, with stars marking "boundaries".


-- ============================================================================
-- System 5 → System 4 encoder (PDF `TM23Proof.pdf` p. 32, `s52s4.pl`)
-- ============================================================================
--
-- The encoder takes a System 5 program (bag, rules) plus a parameter `f`
-- (the value of f to use in the emulation; controls amount of "padding").
-- It produces:
--   * Initial state = A.
--   * First element: bag set, with each entry `e` mapped to `e*2 - 2`.
--   * Then `f` star/empty-set pairs (padding).
--   * For each System 5 rule:
--     - Rule-encoded set: contains 0..f*3, XOR'd with each rule entry `k`
--       mapped to `k*2 + f + 3`.
--     - Then `f*2` star/empty-set pairs.
--     - Then a set containing all 0..3*f.
--     - Then `f*2 - 2` star/empty-set pairs.
--
-- Active starts at 0.


-- ============================================================================
-- Systems 1, 2, 3 (PDF `TM23Proof.pdf` p. 4-5)
-- ============================================================================
--
-- Smith's chain of equivalent systems:
--   * System 0 (= wolfram23) ↔ System 1 ↔ System 2 ↔ System 3
--     (equivalences via state/cell relabelings, PDF p. 4-5).
--   * System 5 ⇒ System 4 ⇒ System 3 (emulations via `s52s4.pl` etc.).
--
-- CHALLENGE: Systems 1, 2, 3 are NOT standard Turing machines in the
-- `BiTM.Machine` sense — their transition tables include "multi-cell
-- writes" (e.g. System 1's (B, 20) → write `00`, which writes BOTH the
-- active cell AND an adjacent cell in one step).  This generalises the
-- TM model and isn't directly representable by `BiTM.Machine`.
--
-- Two options for formalising:
--   (a) Define a `GeneralizedTM` type that allows multi-cell writes per
--       transition.  Define Systems 1-3 as instances.
--   (b) Encode each System-N step as multiple `BiTM` steps via an
--       intermediate construction that writes one cell per step.
--
-- Option (a) is cleaner mathematically but requires significant new
-- machinery.  Deferred to future iterations.










/-- Smoke test: post-decrement-erase of `{data := [false]}` is `[1, 2, 3]`. -/
example :
    ((ctsConfigToSystem5Bag { data := [false], phase := 0 }).map (· - 1)).erase 0
    = [1, 2, 3] := by decide

/-- Smoke test: post-decrement-erase of `{data := [true]}` is `[2, 3, 5]`. -/
example :
    ((ctsConfigToSystem5Bag { data := [true], phase := 0 }).map (· - 1)).erase 0
    = [2, 3, 5] := by decide

-- (Iter 818: removed several illustrative smoke tests with hard-coded
-- bag/rule values that were correct for the old 3-rules-per-appendant
-- encoder.  With the iter 818 fix to 4-rules-per-appendant, these
-- specific values are stale.  The tests were documentation, not
-- load-bearing for any proof.)

/-- CTS dynamics smoke test: one step from `{data := [false], phase := 0}`
    on a CTS with one false-only appendant gives `{data := [], phase := 0}`.
    The leading `false` bit drops without appending; phase advances mod 1. -/
example :
    let cts : CTS := { appendants := [[false]], nonempty := by decide }
    cts.nSteps { data := [false], phase := 0 } 1
    = some { data := [], phase := 0 } := by
  decide

/-- **PARTIAL REDEMPTION of iter 274**: with `cts = [[]]` (empty
    appendant) and `data := [false, false]`, **N = 2 does work** —
    after 4 System 5 steps, bag = `[1, 2, 3, 4]` = encoded `{data :=
    [false]}` (the post-CTS-step state).  Iter 274's "INSUFFICIENT"
    finding was specific to N = 1.  With sufficient budget, the
    bag-matching CAN succeed for trivial CTSs.  This suggests Smith's
    emulation needs a `N ≥ N_required(n)` precondition to be stated
    correctly. -/
example :
    System5.nSteps (ctsToSystem5
        { appendants := [[]], nonempty := by decide }
        { data := [false, false], phase := 0 } 2) 4
    = some { bag := [1, 2, 3, 4], rules := [[], [], [], []] } := by
  native_decide

/-- For non-empty appendant `[[false]]` with `data := [false, false]`,
    `N = 3`: bag reaches `[]` at m = 8 — i.e., System 5 reaches the
    encoded HALTED state (after CTS halts in 2 steps).  Validates that
    bag-matching works AT HALT for non-empty appendants too.  But
    intermediate states do NOT match (per iter 274 trace) — Smith's
    emulation is bag-matching only at halt-checkpoints, not all m. -/
example :
    (System5.nSteps (ctsToSystem5
        { appendants := [[false]], nonempty := by decide }
        { data := [false, false], phase := 0 } 3) 8).map (fun c => c.bag)
    = some [] := by
  native_decide

-- (Iter 818: removed iter 283's stale "negative result" — its specific
-- hard-coded values were valid for the old 3-rules-per-appendant
-- encoder and are now stale.)



/-- **Empty-rule encoding**: the empty appendant encodes to `([], [],
    i)` (counter unchanged).  Already stated as `encodeAppendant_nil`,
    repeated here for proximity. -/
private theorem encodeAppendant_empty (i : Int) :
    encodeAppendant [] i = ([], [], i) := rfl










/-- Witness that `{appendants := [[]]}` is `AllEmptyAppendants`,
    discharged by `decide` via iter 354's `Decidable` instance. -/
private theorem trivialEmptyAppCTS_AllEmpty :
    AllEmptyAppendants ({ appendants := [[]], nonempty := by decide } : CTS) := by
  decide

/-- **Smoke test for iter 345's AllEmptyAppendants Smith emulation**.
    For `cts := {appendants := [[]]}` (so `|append| = 1`),
    `cfg := {data := [false], phase := 0}`, `N = 4`: budget K =
    3 * 1 * 4 = 12 ≥ 4 * 1 = 4 (n = 1).  After 1 CTS step, `result
    := {data := [], phase := 0}`, and the bag-match emulation
    gives `∃ m s5_result, ...`. -/
example :
    let cts : CTS := { appendants := [[]], nonempty := by decide }
    let cfg : CTSConfig := { data := [false], phase := 0 }
    ∃ m s5_result,
      System5.nSteps (ctsToSystem5 cts cfg 4) m = some s5_result
      ∧ s5_result.bag = ctsConfigToSystem5Bag
                          { data := [], phase := (0 + 1) % 1 } := by
  have h_step : ({ appendants := [[]], nonempty := by decide } : CTS).nSteps
                  { data := [false], phase := 0 } 1
                = some { data := [], phase := (0 + 1) % 1 } :=
    AllEmptyAppendants_step_explicit _ trivialEmptyAppCTS_AllEmpty false [] 0
  exact AllEmptyAppendants_ctsToSystem5_emulates _ trivialEmptyAppCTS_AllEmpty
    { data := [false], phase := 0 } (by decide) 4 1 (by decide) (by decide)
    _ h_step










/-- **Smoke test for iter 358**: on `emptyAppendantsCTS 3` with data
    `[false, true, false]`, any `nSteps cfg 2 = some result` yields
    `result.data.length = 1`. -/
example : ∀ result,
    (emptyAppendantsCTS 3 (by decide)).nSteps
      { data := [false, true, false], phase := 0 } 2 = some result →
    result.data.length = 1 := by
  intro result h
  have := AllEmptyAppendants_nSteps_some_data_length
    (emptyAppendantsCTS 3 (by decide))
    (emptyAppendantsCTS_AllEmpty 3 (by decide))
    [false, true, false] 0 (by decide) 2 result h
  simpa using this









/-- **Smoke test for `AllEmptyAppendants_System5_Halts`** on a
    concrete CTS.  Validates that the meaningful halt-preservation
    composes cleanly with `System5.Halts`. -/
example :
    ∃ N, System5.Halts
      (ctsToSystem5 ({ appendants := [[]], nonempty := by decide } : CTS)
                    { data := [false, true, false], phase := 0 } N) :=
  AllEmptyAppendants_System5_Halts _ trivialEmptyAppCTS_AllEmpty _

/-- **Smoke test using `emptyAppendantsCTS` constructor (iter 357)**:
    a 5-appendant empty-appendants CTS with mixed data halts. -/
example : ∃ N, System5.Halts
    (ctsToSystem5 (emptyAppendantsCTS 5 (by decide))
                  { data := [true, false, true], phase := 0 } N) :=
  AllEmptyAppendants_System5_Halts _ (emptyAppendantsCTS_AllEmpty 5 _) _



-- iter 444's `_periodic_not_halts` lemmas are placed after the corresponding
-- `_extract_step_none_witness` extractors below to satisfy forward-reference
-- ordering.


-- iter 449's 2-link CTS → System5 → tm chain placed after
-- `system5Halts_imp_tmHalts_under_step_emulation` (iter 433) below.

/-- **CTS → System5 → System4 halt-preservation chain (iter 432)**:
    composes iter 428 (CTS → System5) with iter 431 (System5 →
    System4).  Two link-level emulations + halt-encodings yield
    end-to-end CTS → System4 halt-preservation through the
    composite encoder. -/
theorem ctsHalts_imp_system4Halts_chain
    (cts : CTS) (enc1 : CTSConfig → System5Config)
    (enc2 : System5Config → System4Config)
    (h₁_step : ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ System5.nSteps (enc1 ctsCfg) n = some (enc1 ctsCfg'))
    (h₁_halt : ∀ ctsCfg, ctsHalted ctsCfg = true → System5.Halts (enc1 ctsCfg))
    (h₂_step : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ System4.nSteps (enc2 cfg) n = some (enc2 cfg'))
    (h₂_halt : ∀ cfg, System5.step cfg = none → System4.Halts (enc2 cfg))
    (ctsCfg : CTSConfig) (h : cts.Halts ctsCfg) :
    System4.Halts (enc2 (enc1 ctsCfg)) :=
  system5Halts_imp_system4Halts_under_step_emulation enc2 h₂_step h₂_halt
    (enc1 ctsCfg)
    (ctsHalts_imp_system5Halts_under_step_emulation cts enc1 h₁_step h₁_halt
      ctsCfg h)


/-- **CTS → System5 → tm halt-preservation chain (iter 449)**:
    2-link variant skipping System4.  Composes iter 428 + iter 433
    to give CTS → BiTM halt-preservation through a System5
    intermediate.  Useful if a hypothetical `system5ToWolfram23`
    emulator is exhibited directly. -/
theorem ctsHalts_imp_tmHalts_chain_through_system5
    (cts : CTS) (tm : Machine)
    (enc1 : CTSConfig → System5Config) (enc2 : System5Config → Config)
    (h₁_step : ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ System5.nSteps (enc1 ctsCfg) n = some (enc1 ctsCfg'))
    (h₁_halt : ∀ ctsCfg, ctsHalted ctsCfg = true → System5.Halts (enc1 ctsCfg))
    (h₂_step : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (enc2 cfg) n = some (enc2 cfg'))
    (h₂_halt : ∀ cfg, System5.step cfg = none → Halts tm (enc2 cfg))
    (ctsCfg : CTSConfig) (h : cts.Halts ctsCfg) :
    Halts tm (enc2 (enc1 ctsCfg)) :=
  system5Halts_imp_tmHalts_under_step_emulation tm enc2 h₂_step h₂_halt _
    (ctsHalts_imp_system5Halts_under_step_emulation cts enc1 h₁_step h₁_halt
      ctsCfg h)






/-- **`SmithSimulatesCTS` via 3-link per-step chain (iter 438)**:
    instantiating iter 437 with `tm := wolfram23` and bundling into
    `SmithSimulatesCTS cts` predicate.  Provides a clean entry point:
    discharge three link-level per-step emulators (CTS → System5,
    System5 → System4, System4 → wolfram23) and obtain
    `SmithSimulatesCTS cts` (which then chains to
    `SmithReducesStepFaithful` via
    `smithReducesStepFaithful_of_per_cts_simulates`). -/
theorem smithSimulatesCTS_via_chain
    (cts : CTS)
    (enc1 : CTSConfig → System5Config) (enc2 : System5Config → System4Config)
    (enc3 : System4Config → Config)
    (h₁ : ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ System5.nSteps (enc1 ctsCfg) n = some (enc1 ctsCfg'))
    (h₂ : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ System4.nSteps (enc2 cfg) n = some (enc2 cfg'))
    (h₃ : ∀ cfg cfg', System4.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps wolfram23 (enc3 cfg) n = some (enc3 cfg')) :
    SmithSimulatesCTS cts :=
  ⟨fun ctsCfg => enc3 (enc2 (enc1 ctsCfg)),
   cts_step_emulation_compose_full_chain cts wolfram23 enc1 enc2 enc3 h₁ h₂ h₃⟩

/-- **`SmithReducesStepFaithful` via universal 3-link chain (iter
    439)**: directly bundles iter 437 into `SmithReducesStepFaithful`
    with universal (cts-dependent for `enc1`, cts-independent for
    `enc2`/`enc3`) encoders.  Bypasses the need for
    `Classical.choose` over per-CTS witnesses (cf. iter 438 +
    `smithReducesStepFaithful_of_per_cts_simulates`). -/
theorem smithReducesStepFaithful_via_universal_chain
    (enc1 : CTS → CTSConfig → System5Config)
    (enc2 : System5Config → System4Config)
    (enc3 : System4Config → Config)
    (h₁ : ∀ (cts : CTS) (ctsCfg ctsCfg' : CTSConfig),
        cts.step ctsCfg = some ctsCfg' →
        ∃ n, n ≥ 1 ∧ System5.nSteps (enc1 cts ctsCfg) n = some (enc1 cts ctsCfg'))
    (h₂ : ∀ cfg cfg', System5.step cfg = some cfg' →
        ∃ n, n ≥ 1 ∧ System4.nSteps (enc2 cfg) n = some (enc2 cfg'))
    (h₃ : ∀ cfg cfg', System4.step cfg = some cfg' →
        ∃ n, n ≥ 1 ∧ nSteps wolfram23 (enc3 cfg) n = some (enc3 cfg')) :
    SmithReducesStepFaithful := by
  refine ⟨fun cts ctsCfg => enc3 (enc2 (enc1 cts ctsCfg)), ?_⟩
  intro cts ctsCfg ctsCfg' h_step
  exact cts_step_emulation_compose_full_chain cts wolfram23
    (enc1 cts) enc2 enc3 (h₁ cts) h₂ h₃ ctsCfg ctsCfg' h_step

/-- **`SmithReducesFaithful` via universal 3-link chain (iter 440)**:
    closes both clauses of `SmithReducesFaithful` (per-step + halt-
    cfg encoding) using a universal 3-link chain.  The halt-cfg
    chain propagates step-none across each link: ctsHalted →
    System5.step = none → System4.step = none → halted.  Together
    with iter 437's per-step chain, this gives a direct entry point
    to `SmithReducesFaithful` modulo three link-level encoders +
    six emulator hypotheses. -/
theorem smithReducesFaithful_via_universal_chain
    (enc1 : CTS → CTSConfig → System5Config)
    (enc2 : System5Config → System4Config)
    (enc3 : System4Config → Config)
    (h₁_step : ∀ (cts : CTS) (ctsCfg ctsCfg' : CTSConfig),
        cts.step ctsCfg = some ctsCfg' →
        ∃ n, n ≥ 1 ∧ System5.nSteps (enc1 cts ctsCfg) n = some (enc1 cts ctsCfg'))
    (h₂_step : ∀ cfg cfg', System5.step cfg = some cfg' →
        ∃ n, n ≥ 1 ∧ System4.nSteps (enc2 cfg) n = some (enc2 cfg'))
    (h₃_step : ∀ cfg cfg', System4.step cfg = some cfg' →
        ∃ n, n ≥ 1 ∧ nSteps wolfram23 (enc3 cfg) n = some (enc3 cfg'))
    (h₁_halt : ∀ (cts : CTS) (ctsCfg : CTSConfig), ctsHalted ctsCfg = true →
        System5.step (enc1 cts ctsCfg) = none)
    (h₂_halt : ∀ cfg, System5.step cfg = none → System4.step (enc2 cfg) = none)
    (h₃_halt : ∀ cfg, System4.step cfg = none → halted (enc3 cfg) = true) :
    SmithReducesFaithful := by
  refine ⟨fun cts ctsCfg => enc3 (enc2 (enc1 cts ctsCfg)), ?_, ?_⟩
  · intro cts ctsCfg h_halted
    exact h₃_halt _ (h₂_halt _ (h₁_halt cts ctsCfg h_halted))
  · intro cts ctsCfg ctsCfg' h_step
    exact cts_step_emulation_compose_full_chain cts wolfram23
      (enc1 cts) enc2 enc3 (h₁_step cts) h₂_step h₃_step ctsCfg ctsCfg' h_step

/-- **`SmithReduces` (weak form) via universal 3-link chain (iter
    446)**: composes iter 440 with the existing
    `SmithReducesFaithful_implies_weak`.  Closes the trivial
    `SmithReduces` (used by `smith_reduces` axiom closure) from the
    same six link-level hypotheses.  Provides a SUBSTANTIVE closure
    of `SmithReduces` (rather than the existing trivial halt-collapse
    `smith_reduces`). -/
theorem smithReduces_via_universal_chain
    (enc1 : CTS → CTSConfig → System5Config)
    (enc2 : System5Config → System4Config)
    (enc3 : System4Config → Config)
    (h₁_step : ∀ (cts : CTS) (ctsCfg ctsCfg' : CTSConfig),
        cts.step ctsCfg = some ctsCfg' →
        ∃ n, n ≥ 1 ∧ System5.nSteps (enc1 cts ctsCfg) n = some (enc1 cts ctsCfg'))
    (h₂_step : ∀ cfg cfg', System5.step cfg = some cfg' →
        ∃ n, n ≥ 1 ∧ System4.nSteps (enc2 cfg) n = some (enc2 cfg'))
    (h₃_step : ∀ cfg cfg', System4.step cfg = some cfg' →
        ∃ n, n ≥ 1 ∧ nSteps wolfram23 (enc3 cfg) n = some (enc3 cfg'))
    (h₁_halt : ∀ (cts : CTS) (ctsCfg : CTSConfig), ctsHalted ctsCfg = true →
        System5.step (enc1 cts ctsCfg) = none)
    (h₂_halt : ∀ cfg, System5.step cfg = none → System4.step (enc2 cfg) = none)
    (h₃_halt : ∀ cfg, System4.step cfg = none → halted (enc3 cfg) = true) :
    SmithReduces :=
  SmithReducesFaithful_implies_weak
    (smithReducesFaithful_via_universal_chain enc1 enc2 enc3
      h₁_step h₂_step h₃_step h₁_halt h₂_halt h₃_halt)

/-- **`SmithChainEmulators` predicate (iter 450)**: bundles the six
    link-level hypotheses required by iter 440/446's chain framework
    into a single Prop.  Names the substantive Smith chain obligation
    cleanly, useful as a target for future research-level proofs.
    Parameters: existence of three link-level encoders (CTS→System5,
    System5→System4, System4→wolfram23) such that:
      - per-step emulation holds at each link,
      - step-none halt-cfg encoding propagates: ctsHalted → S5.step=none →
        S4.step=none → halted.

    **STRUCTURAL CAVEAT (iter 787)**: hypothesis 5 (`S5.step = none →
    S4.step = none`) is too strong for the canonical `system5ToSystem4`
    encoder.  When System 5 halts (bag = [] or rules = []), the encoded
    System 4 cfg has elems = `set [] :: starredEmptyPairs f ++ ...` with
    active = 0, state = A — System 4 rule 1 (set in A) takes a step
    without halting.  A relaxed `SmithChainEmulators_Halts` predicate
    using `S5.step = none → S4.Halts` would match the encoder's actual
    behaviour.  Closing the current predicate requires either (a) using
    a different `enc2` that satisfies it, or (b) generalising the chain
    framework to use halt-preservation at the predicate level.  Both
    are research-level redirections. -/
def SmithChainEmulators : Prop :=
  ∃ (enc1 : CTS → CTSConfig → System5Config)
    (enc2 : System5Config → System4Config)
    (enc3 : System4Config → Config),
    (∀ (cts : CTS) (ctsCfg ctsCfg' : CTSConfig),
        cts.step ctsCfg = some ctsCfg' →
        ∃ n, n ≥ 1 ∧ System5.nSteps (enc1 cts ctsCfg) n = some (enc1 cts ctsCfg'))
    ∧ (∀ cfg cfg', System5.step cfg = some cfg' →
        ∃ n, n ≥ 1 ∧ System4.nSteps (enc2 cfg) n = some (enc2 cfg'))
    ∧ (∀ cfg cfg', System4.step cfg = some cfg' →
        ∃ n, n ≥ 1 ∧ nSteps wolfram23 (enc3 cfg) n = some (enc3 cfg'))
    ∧ (∀ (cts : CTS) (ctsCfg : CTSConfig), ctsHalted ctsCfg = true →
        System5.step (enc1 cts ctsCfg) = none)
    ∧ (∀ cfg, System5.step cfg = none → System4.step (enc2 cfg) = none)
    ∧ (∀ cfg, System4.step cfg = none → halted (enc3 cfg) = true)

/-- **`SmithChainEmulators ⇒ SmithReducesFaithful` (iter 450)**:
    the predicate-form iter 440.  Reduces the substantive
    `SmithReducesFaithful` problem to exhibiting the six link-level
    hypotheses bundled in `SmithChainEmulators`. -/
theorem smithReducesFaithful_of_chain_emulators (h : SmithChainEmulators) :
    SmithReducesFaithful := by
  obtain ⟨enc1, enc2, enc3, h₁s, h₂s, h₃s, h₁h, h₂h, h₃h⟩ := h
  exact smithReducesFaithful_via_universal_chain enc1 enc2 enc3
    h₁s h₂s h₃s h₁h h₂h h₃h

/-- **`SmithChainEmulators ⇒ SmithReduces` (iter 450)**: weak-form
    composite. -/
theorem smithReduces_of_chain_emulators (h : SmithChainEmulators) :
    SmithReduces :=
  SmithReducesFaithful_implies_weak (smithReducesFaithful_of_chain_emulators h)

/-- **`SmithChainEmulators` forces wolfram23 periodic point (iter
    451)**: composes iter 439 (`smithReducesStepFaithful_via_universal_
    chain`) with `smithReducesStepFaithful_implies_wolfram23_periodic`
    via `selfLoopCTS`.  Documents that `SmithChainEmulators` is
    non-trivial — exhibiting it would force a periodic point of
    wolfram23, which is not known to exist. -/
theorem SmithChainEmulators_implies_wolfram23_periodic
    (h : SmithChainEmulators) :
    ∃ cfg : Config, ∃ n, n ≥ 1 ∧ nSteps wolfram23 cfg n = some cfg := by
  obtain ⟨enc1, enc2, enc3, h₁s, h₂s, h₃s, _, _, _⟩ := h
  exact smithReducesStepFaithful_implies_wolfram23_periodic
    (smithReducesStepFaithful_via_universal_chain enc1 enc2 enc3 h₁s h₂s h₃s)

/-- **TM → CTS reduction predicate (iter 452)**: there exists a CTS
    and an encoder of TM configs into CTS configs that preserves
    halting.  This is the natural composite of Cocke-Minsky (TM →
    Tag) with Cook (Tag → CTS), expressed at the CTS level. -/
def TM_to_CTS_reduction (tm : Machine) : Prop :=
  ∃ (cts : CTS) (encode : Config → CTSConfig),
    ∀ cfg, Halts tm cfg → cts.Halts (encode cfg)

/-- **TM → CTS via Cocke-Minsky + Cook (iter 452)**: substantive
    closure of `TM_to_CTS_reduction` for ANY TM.  Composes iter 105's
    `cocke_minsky_reduces_via_universal` (TM → Tag, substantive) with
    Cook's `tagToCTS_halting_forward` (Tag → CTS, fully proved).  No
    new axioms. -/
theorem TM_to_CTS_reduction_via_cocke_minsky (tm : Machine) :
    TM_to_CTS_reduction tm := by
  obtain ⟨k, hk, ts, encode, h_cm⟩ := cocke_minsky_reduces_via_universal tm
  refine ⟨tagToCTS ts hk, fun cfg => tagConfigToCTS k (encode cfg), ?_⟩
  intro cfg h_halts
  exact tagToCTS_halting_forward ts hk _ (h_cm cfg h_halts)

/-- **TM → wolfram23 reduction predicate (iter 453)**: an encoder of
    TM configs into wolfram23 configs that preserves halting.  This
    is exactly the `IsUniversal wolfram23` condition for a single TM. -/
def TM_to_wolfram23_reduction (tm : Machine) : Prop :=
  ∃ (encode : Config → Config),
    ∀ cfg, Halts tm cfg → Halts wolfram23 (encode cfg)

/-- **TM → wolfram23 via Cocke-Minsky + Cook + Smith chain (iter
    453)**: SUBSTANTIVE closure of `TM_to_wolfram23_reduction` for
    ANY TM, conditioned on `SmithChainEmulators`.  Composes iter 452
    (TM → CTS, substantive) with iter 450's
    `smithReduces_of_chain_emulators` (CTS → wolfram23, conditioned
    on the chain hypothesis).  When `SmithChainEmulators` is closed,
    this gives a substantive `IsUniversal wolfram23` directly. -/
theorem TM_to_wolfram23_reduction_via_chain
    (h : SmithChainEmulators) (tm : Machine) :
    TM_to_wolfram23_reduction tm := by
  obtain ⟨cts, encode_tm_to_cts, h_tm_to_cts⟩ :=
    TM_to_CTS_reduction_via_cocke_minsky tm
  obtain ⟨smith_encode, h_smith⟩ := smithReduces_of_chain_emulators h
  refine ⟨fun cfg => smith_encode cts (encode_tm_to_cts cfg), ?_⟩
  intro cfg h_halts
  exact h_smith cts (encode_tm_to_cts cfg) (h_tm_to_cts cfg h_halts)

/-- **Substantive `IsUniversal wolfram23` via SmithChainEmulators
    (iter 454)**: closes the global universality predicate for
    wolfram23 SUBSTANTIVELY (no halt-collapse encoder), conditioned
    only on `SmithChainEmulators`.  Direct generalization of iter
    453 over all TMs. -/
theorem isUniversal_wolfram23_via_chain (h : SmithChainEmulators) :
    IsUniversal wolfram23 :=
  fun tm => TM_to_wolfram23_reduction_via_chain h tm

/-- **`IsUniversal wolfram23 ↔ ∀ tm, TM_to_wolfram23_reduction tm`
    (iter 455)**: trivial bridge documenting that
    `TM_to_wolfram23_reduction` (the per-TM predicate) and
    `IsUniversal wolfram23` (the universal predicate) coincide
    definitionally.  Useful as a bridge to standardize naming
    between the per-TM and universal forms. -/
theorem isUniversal_wolfram23_iff_universal_TM_reduction :
    IsUniversal wolfram23 ↔ ∀ tm, TM_to_wolfram23_reduction tm :=
  Iff.rfl

/-- **TM → CTS unconditional reduction for total TMs (iter 456)**:
    if a TM halts on every config, the substantive Cocke-Minsky-Cook
    reduction yields a CTS where every encoded config halts (without
    the `Halts tm cfg` premise).  Direct strengthening of iter 452
    when the source TM is total. -/
theorem TM_to_CTS_reduction_total
    (tm : Machine) (h_total : ∀ cfg, Halts tm cfg) :
    ∃ (cts : CTS) (encode : Config → CTSConfig),
      ∀ cfg, cts.Halts (encode cfg) := by
  obtain ⟨cts, encode, h⟩ := TM_to_CTS_reduction_via_cocke_minsky tm
  exact ⟨cts, encode, fun cfg => h cfg (h_total cfg)⟩

/-- **TM → wolfram23 unconditional reduction for total TMs (iter
    456)**: BiTM analog.  Conditioned on `SmithChainEmulators`. -/
theorem TM_to_wolfram23_reduction_total
    (h_chain : SmithChainEmulators) (tm : Machine) (h_total : ∀ cfg, Halts tm cfg) :
    ∃ (encode : Config → Config), ∀ cfg, Halts wolfram23 (encode cfg) := by
  obtain ⟨encode, h⟩ := TM_to_wolfram23_reduction_via_chain h_chain tm
  exact ⟨encode, fun cfg => h cfg (h_total cfg)⟩

/-- **TM → wolfram23 reduction via SmithReducesFaithful directly
    (iter 457)**: alternative path bypassing `SmithChainEmulators`.
    Uses any direct `SmithReducesFaithful` hypothesis (perhaps
    proven without going through the System5/System4 chain) to
    obtain TM → wolfram23 reduction. -/
theorem TM_to_wolfram23_reduction_via_faithful
    (h_faithful : SmithReducesFaithful) (tm : Machine) :
    TM_to_wolfram23_reduction tm := by
  obtain ⟨cts, encode_tm_to_cts, h_tm_to_cts⟩ :=
    TM_to_CTS_reduction_via_cocke_minsky tm
  obtain ⟨smith_encode, h_smith⟩ := SmithReducesFaithful_implies_weak h_faithful
  refine ⟨fun cfg => smith_encode cts (encode_tm_to_cts cfg), ?_⟩
  intro cfg h_halts
  exact h_smith cts (encode_tm_to_cts cfg) (h_tm_to_cts cfg h_halts)

/-- **`IsUniversal wolfram23` via `SmithReducesFaithful` (iter 457)**:
    universal substantive form, alternative to iter 454.  Uses any
    direct `SmithReducesFaithful` proof (not necessarily via the
    chain framework). -/
theorem isUniversal_wolfram23_via_faithful (h : SmithReducesFaithful) :
    IsUniversal wolfram23 :=
  fun tm => TM_to_wolfram23_reduction_via_faithful h tm


/-- **`HaltReduces tm wolfram23 → TM_to_wolfram23_reduction tm`
    (iter 472)**: substantive halt-reduction implies the per-TM
    wolfram23 reduction predicate.  Bridges the abstract
    `HaltReduces` (per-step + halt-cfg) with the concrete
    `TM_to_wolfram23_reduction` (halt-preservation only).  Note:
    the converse fails since `TM_to_wolfram23_reduction` admits
    trivial halt-collapse encoders. -/
theorem HaltReduces_imp_TM_to_wolfram23_reduction
    (tm : Machine) (h : HaltReduces tm wolfram23) :
    TM_to_wolfram23_reduction tm := by
  obtain ⟨encode, h_step, h_halt⟩ := h
  refine ⟨encode, ?_⟩
  intro cfg h_halts
  exact EmulatesPerStep_PreservesHalt_imp_halt_preservation tm wolfram23
    encode h_step h_halt cfg h_halts

/-- **`IsSubstantiallyUniversal wolfram23 → ∀ tm,
    TM_to_wolfram23_reduction tm` (iter 472)**: substantive
    universality implies the universal TM-to-wolfram23 reduction
    (which equals `IsUniversal wolfram23`). -/
theorem IsSubstantiallyUniversal_wolfram23_imp_universal_TM_reduction
    (h : IsSubstantiallyUniversal wolfram23) :
    ∀ tm, TM_to_wolfram23_reduction tm :=
  fun tm => HaltReduces_imp_TM_to_wolfram23_reduction tm (h tm)

/-- **`IsSubstantiallyUniversal` summary (iter 473)**: documents
    the consequences of having `IsSubstantiallyUniversal wolfram23`.
    Trivially bundles iter 459 (weak universality), the per-TM
    per-step encoder existence, and iter 471's halt-preservation
    extractor (existence of halting wolfram23 cfg per halting source). -/
theorem IsSubstantiallyUniversal_wolfram23_summary
    (h : IsSubstantiallyUniversal wolfram23) :
    IsUniversal wolfram23
    ∧ (∀ tm, ∃ (encode : Config → Config), ∀ cfg cfg',
        step tm cfg = some cfg' →
        ∃ n, n ≥ 1 ∧ nSteps wolfram23 (encode cfg) n = some (encode cfg'))
    ∧ (∀ tm cfg, Halts tm cfg → ∃ encoded, Halts wolfram23 encoded) := by
  refine ⟨IsSubstantiallyUniversal_implies_IsUniversal wolfram23 h, ?_, ?_⟩
  · intro tm
    obtain ⟨encode, h_step, _⟩ := h tm
    exact ⟨encode, h_step⟩
  · intro tm cfg h_halts
    exact HaltReduces_imp_halt_preservation tm wolfram23 (h tm) cfg h_halts




/-- **`SmithChainEmulators` forces wolfram23 periodic with period ≥
    2 (iter 479)**: refined form of iter 451.  Since wolfram23 has
    no period-1 orbits (iter 477), the wolfram23-period forced by
    `SmithChainEmulators` (via `selfLoopCTS`) is at least 2. -/
theorem SmithChainEmulators_implies_wolfram23_periodic_at_least_2
    (h : SmithChainEmulators) :
    ∃ cfg : Config, ∃ n, n ≥ 2 ∧ nSteps wolfram23 cfg n = some cfg := by
  obtain ⟨cfg, n, hn_pos, h_period⟩ := SmithChainEmulators_implies_wolfram23_periodic h
  exact ⟨cfg, n, TM_period_ge_2 wolfram23 cfg n hn_pos h_period, h_period⟩


/-- **`SmithChainEmulators` forces wolfram23 active periodic orbit
    of period ≥ 2 (iter 482)**: combines iter 479 (period ≥ 2) with
    iter 482 (active source) to give the strongest available
    obstruction lemma.  Documents that `SmithChainEmulators`
    requires wolfram23 to have a non-trivially-active periodic
    point — a non-trivial open obligation. -/
theorem SmithChainEmulators_implies_wolfram23_periodic_active_at_least_2
    (h : SmithChainEmulators) :
    ∃ cfg : Config, cfg.state ≠ 0 ∧
      ∃ n, n ≥ 2 ∧ nSteps wolfram23 cfg n = some cfg := by
  obtain ⟨cfg, n, hn_ge_2, h_period⟩ :=
    SmithChainEmulators_implies_wolfram23_periodic_at_least_2 h
  refine ⟨cfg, ?_, n, hn_ge_2, h_period⟩
  exact periodic_source_active wolfram23 cfg n (by omega) h_period


/-- **`SmithChainEmulators` consequences summary (iter 484)**:
    one-shot summary of what `SmithChainEmulators` unlocks across
    the framework — substantive Smith reduction (faithful + weak),
    universal TM-to-wolfram23 reduction, and active wolfram23
    periodic orbit obligation. -/
theorem SmithChainEmulators_summary
    (h : SmithChainEmulators) :
    SmithReducesFaithful ∧
    SmithReduces ∧
    (∀ tm, TM_to_wolfram23_reduction tm) ∧
    (∃ cfg : Config, cfg.state ≠ 0 ∧
      ∃ n, n ≥ 2 ∧ nSteps wolfram23 cfg n = some cfg) := by
  refine ⟨smithReducesFaithful_of_chain_emulators h,
          smithReduces_of_chain_emulators h, ?_, ?_⟩
  · intro tm
    exact TM_to_wolfram23_reduction_via_chain h tm
  · exact SmithChainEmulators_implies_wolfram23_periodic_active_at_least_2 h

/-- **`SmithReducesFaithful` implies wolfram23 periodic ≥ 2 (iter
    485)**: alternative obstruction starting from
    `SmithReducesFaithful` directly (rather than the more
    constrained `SmithChainEmulators`).  Drops the halt-cfg clause
    of `SmithReducesFaithful` to get `SmithReducesStepFaithful`,
    then composes with `selfLoopCTS` obstruction + iter 477. -/
theorem SmithReducesFaithful_implies_wolfram23_periodic_at_least_2
    (h : SmithReducesFaithful) :
    ∃ cfg : Config, ∃ n, n ≥ 2 ∧ nSteps wolfram23 cfg n = some cfg := by
  obtain ⟨encode, _h_halt, h_step⟩ := h
  have h_stepfaithful : SmithReducesStepFaithful := ⟨encode, h_step⟩
  obtain ⟨cfg, n, hn_pos, h_period⟩ :=
    smithReducesStepFaithful_implies_wolfram23_periodic h_stepfaithful
  exact ⟨cfg, n, TM_period_ge_2 wolfram23 cfg n hn_pos h_period, h_period⟩

/-- **No-period contrapositives (iter 486)**: contrapositives of
    iter 482 / iter 485 / iter 451 — if wolfram23 is *known* to
    have no periodic orbits ≥ 2, then `SmithChainEmulators`,
    `SmithReducesFaithful`, and `SmithReducesStepFaithful` are all
    unsatisfiable.  Documents the obstruction direction.  Whether
    wolfram23 actually has such periodic orbits is an open
    question (Wolfram (2,3) dynamics are not fully understood). -/
theorem no_wolfram23_periodic_implies_no_SmithChainEmulators
    (h_no_period : ∀ cfg : Config, ∀ n, n ≥ 2 →
      nSteps wolfram23 cfg n ≠ some cfg) :
    ¬ SmithChainEmulators := by
  intro h_chain
  obtain ⟨cfg, _h_active, n, hn_ge_2, h_period⟩ :=
    SmithChainEmulators_implies_wolfram23_periodic_active_at_least_2 h_chain
  exact h_no_period cfg n hn_ge_2 h_period

/-- Same obstruction for `SmithReducesFaithful` (iter 486). -/
theorem no_wolfram23_periodic_implies_no_SmithReducesFaithful
    (h_no_period : ∀ cfg : Config, ∀ n, n ≥ 2 →
      nSteps wolfram23 cfg n ≠ some cfg) :
    ¬ SmithReducesFaithful := by
  intro h_faithful
  obtain ⟨cfg, n, hn_ge_2, h_period⟩ :=
    SmithReducesFaithful_implies_wolfram23_periodic_at_least_2 h_faithful
  exact h_no_period cfg n hn_ge_2 h_period






/-- **Three-link halt-preservation chain CTS → System5 → System4 →
    bridge CTS halts all the way to a BiTM machine target via a
    three-stage encoder.  Discharges the Smith chain's halt-
    preservation modulo per-step emulation hypotheses at each link.
    The actual Smith reduction `smith_reduces_faithful` would
    instantiate this with `tm := wolfram23` and concrete encoders
    `ctsToSystem5`, `system5ToSystem4`, and a (yet unwritten)
    `system4ToWolfram23`. -/
theorem ctsHalts_imp_tmHalts_full_chain
    (cts : CTS) (tm : Machine)
    (enc1 : CTSConfig → System5Config) (enc2 : System5Config → System4Config)
    (enc3 : System4Config → Config)
    (h₁_step : ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ System5.nSteps (enc1 ctsCfg) n = some (enc1 ctsCfg'))
    (h₁_halt : ∀ ctsCfg, ctsHalted ctsCfg = true → System5.Halts (enc1 ctsCfg))
    (h₂_step : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ System4.nSteps (enc2 cfg) n = some (enc2 cfg'))
    (h₂_halt : ∀ cfg, System5.step cfg = none → System4.Halts (enc2 cfg))
    (h₃_step : ∀ cfg cfg', System4.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (enc3 cfg) n = some (enc3 cfg'))
    (h₃_halt : ∀ cfg, System4.step cfg = none → Halts tm (enc3 cfg))
    (ctsCfg : CTSConfig) (h : cts.Halts ctsCfg) :
    Halts tm (enc3 (enc2 (enc1 ctsCfg))) :=
  system4Halts_imp_tmHalts_under_step_emulation tm enc3 h₃_step h₃_halt _
    (system5Halts_imp_system4Halts_under_step_emulation enc2 h₂_step h₂_halt _
      (ctsHalts_imp_system5Halts_under_step_emulation cts enc1
        h₁_step h₁_halt ctsCfg h))

end CockeMinskyConstruction
end BiTM


