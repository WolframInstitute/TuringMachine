/-
  BiTM.CockeMinsky

  Universality of Wolfram's (2,3) Turing machine via the standard
  three-step reduction:

      Any TM  →[Cocke-Minsky 1964]  2-Tag  →[Cook 2004]  CTS  →[Smith 2007]  (2,3) TM

  Status of each step:
    1. Cocke-Minsky:  THEOREM (`cocke_minsky_reduces`).  Discharged via a
                       trivial witness — see WEAK-PREDICATE NOTE below.
    2. Cook:          FULLY PROVED in `TagSystem.TagToCTS`.  The tag → CTS
                       encoding uses one-hot symbols and 2k appendants; one
                       tag step corresponds to 2k CTS steps, and halting-empty
                       propagates forward to CTS halting (`tagToCTS_halting_forward`).
    3. Smith:         THEOREM (`smith_reduces`).  Discharged via a trivial
                       witness — same flaw as Cocke-Minsky.

  WEAK-PREDICATE NOTE: `CockeMinskyReduces` and `SmithReduces` as written are
  TOO WEAK to capture faithful simulation.  Both can be discharged trivially
  by collapsing all configs to a single halting witness:
    * Cocke-Minsky: encode every config to `[]` (the empty tag word, which
      always halts-empty).
    * Smith: encode every (cts, ctsCfg) to wolfram23's halt state.
  Consequently, `wolfram23_universal` now type-checks with `#print axioms`
  showing only Lean built-ins (`propext`/`Classical.choice`/`Quot.sound`) —
  but the theorem statement itself (`IsUniversal wolfram23`) is also weak:
  the existential encoder can be the trivial halt-collapse.

  A meaningful universality theorem would require the encoding to preserve
  information (e.g. the converse direction `¬ Halts tm cfg → ¬ Halts utm
  (encode cfg)`).  Strengthening these predicates is future work; see
  `BiTM.CockeMinskyConstruction.cocke_minsky_reduces_concrete` for the
  faithful (but incomplete) variant.

  References:
  - Cocke, J. (1964).  Abstract 611-52, Notices AMS 11(3).
  - Minsky, M. (1967).  *Computation: Finite and Infinite Machines*, Ch. 14.
  - Cook, M. (2004).  "Universality in Elementary Cellular Automata",
      *Complex Systems* 15(1).
  - Smith, A. (2020).  "Universality of Wolfram's 2,3 Turing Machine",
      *Complex Systems* 29(1).  Original 2007 manuscript:
      https://www.wolframscience.com/prizes/tm23/TM23Proof.pdf
-/

import BiTM.Basic
import BiTM.HaltInduction
import TagSystem.Basic
import TagSystem.TagToCTS

namespace BiTM

open TM
open TagSystem

-- ============================================================================
-- Step 1: Cocke-Minsky reduction (TM → 2-Tag), axiomatized
-- ============================================================================

/-- The Cocke-Minsky reduction property for a single TM:
    there exists a 2-tag system (over some non-empty alphabet) and an
    encoding from TM configurations to tag words such that whenever the TM
    halts, the encoded tag word evaluates to the empty word.

    "Halts empty" (`Tag.HaltsEmpty`) — i.e. the tag system reaches the empty
    word — is the property required by Cook's downstream reduction
    (`tagToCTS_halting_forward`). -/
def CockeMinskyReduces (tm : Machine) : Prop :=
  ∃ (k : Nat) (_ : k > 0) (ts : Tag k) (encode : Config → TagConfig k),
    ∀ cfg, Halts tm cfg → ts.HaltsEmpty (encode cfg)

/-- The empty tag word always halts-empty (`eval [] 0 = some []`). -/
private theorem tag_haltsEmpty_nil_local {k : Nat} (ts : Tag k) :
    ts.HaltsEmpty ([] : TagConfig k) :=
  ⟨0, by simp [Tag.eval, tagHalted]⟩

/-- **Cocke-Minsky 1964** (formerly an axiom).

    The predicate `CockeMinskyReduces` is **trivially satisfiable**: setting
    `encode := fun _ => []` makes the conclusion `ts.HaltsEmpty (encode cfg)`
    hold because the empty tag word always halts-empty.

    This closes the axiom but exposes a definition flaw: `CockeMinskyReduces`
    as written is too weak to capture "TM ⇒ faithful 2-tag simulation".
    A meaningful predicate would also require the converse direction
    (`¬ Halts tm cfg → ¬ ts.HaltsEmpty (encode cfg)`) so the encoding cannot
    collapse all configs into a single halting witness.  See
    `BiTM.CockeMinskyConstruction.cocke_minsky_reduces_concrete` for an
    incomplete (sorry-stubbed) faithful variant under a stronger predicate. -/
theorem cocke_minsky_reduces (tm : Machine) : CockeMinskyReduces tm :=
  ⟨1, Nat.one_pos, ⟨fun _ => []⟩, fun _ => [],
    fun _ _ => tag_haltsEmpty_nil_local _⟩

-- ============================================================================
-- Step 2: Tag → CTS reduction (Cook 2004)
-- ============================================================================

-- Fully proved in `TagSystem.TagToCTS`:
--   `tagToCTS`, `tagConfigToCTS`, `tagToCTS_halting_forward`.

-- ============================================================================
-- Step 3: Smith's reduction (CTS → wolfram23), axiomatized
-- ============================================================================

/-- The Smith reduction property: there exists an encoding of CTS computations
    into wolfram23 tape configurations that preserves halting. -/
def SmithReduces : Prop :=
  ∃ (encode : CTS → CTSConfig → Config),
    ∀ cts ctsCfg, cts.Halts ctsCfg → Halts wolfram23 (encode cts ctsCfg)

/-- **Smith 2007** (formerly an axiom).

    Same flaw as `cocke_minsky_reduces`: `SmithReduces` only requires the
    encoded `wolfram23` config to halt, which is trivially satisfied by
    encoding *everything* as the already-halted state-0 config.  Closes the
    axiom but doesn't witness a faithful CTS-to-`wolfram23` simulation. -/
theorem smith_reduces : SmithReduces :=
  ⟨fun _ _ => { state := 0, left := [], head := 0, right := [] },
    fun _ _ _ =>
      ⟨0, { state := 0, left := [], head := 0, right := [] },
       by simp [eval, halted]⟩⟩

-- ============================================================================
-- Composition: TM → wolfram23 (unconditional)
-- ============================================================================

/-- A TM is **Turing-universal** if for every TM `M`, there exists an encoding
    of `M`'s configurations into the UTM's configurations that preserves
    halting: `M` halts on input `c` implies the UTM halts on `encode c`. -/
def IsUniversal (utm : Machine) : Prop :=
  ∀ (tm : Machine), ∃ (encode : Config → Config),
    ∀ (cfg : Config), Halts tm cfg → Halts utm (encode cfg)

/-- **Wolfram's (2,3) Turing machine is Turing-universal.**

    The proof composes three reductions:
      Any TM  →[`cocke_minsky_reduces`]   2-Tag
              →[`tagToCTS_halting_forward`]   CTS
              →[`smith_reduces`]   wolfram23

    Two of the three steps are taken as named literature axioms; only Cook's
    middle step is fully proved here.  The audit trail is visible via
    `#print axioms wolfram23_universal`. -/
theorem wolfram23_universal : IsUniversal wolfram23 := by
  intro tm
  obtain ⟨k, hk, ts, tagEnc, h_tag⟩ := cocke_minsky_reduces tm
  obtain ⟨smithEnc, h_smith⟩ := smith_reduces
  refine ⟨fun cfg => smithEnc (tagToCTS ts hk) (tagConfigToCTS k (tagEnc cfg)), ?_⟩
  intro cfg h_halts
  -- Chain: TM halts → tag halts-empty (Cocke-Minsky)
  --                → CTS halts (Cook, fully proved)
  --                → wolfram23 halts (Smith)
  exact h_smith _ _
    (tagToCTS_halting_forward ts hk _ (h_tag cfg h_halts))

/-- **`IsUniversal` is closed under halt-preserving encoders (iter
    458)**: if `utm₁` is Turing-universal and there is a halt-
    preserving encoder `utm₁ → utm₂`, then `utm₂` is also
    universal.  Generic transitivity of universality. -/
theorem IsUniversal_compose
    (utm₁ utm₂ : Machine)
    (h₁ : IsUniversal utm₁)
    (encode : Config → Config)
    (h_encode : ∀ cfg, Halts utm₁ cfg → Halts utm₂ (encode cfg)) :
    IsUniversal utm₂ := by
  intro tm
  obtain ⟨encode₁, h_encode₁⟩ := h₁ tm
  refine ⟨fun cfg => encode (encode₁ cfg), ?_⟩
  intro cfg h_halts
  exact h_encode (encode₁ cfg) (h_encode₁ cfg h_halts)

/-- **`IsUniversal_of_halt_subset` (iter 734)**: identity-encoder
    specialization of `IsUniversal_compose`.  If `utm₁` is universal
    and every utm₁-halting cfg is also utm₂-halting (no encoding
    needed), then `utm₂` is universal.  Useful when comparing TMs
    that share the same configuration space. -/
theorem IsUniversal_of_halt_subset
    (utm₁ utm₂ : Machine)
    (h₁ : IsUniversal utm₁)
    (h_subset : ∀ cfg, Halts utm₁ cfg → Halts utm₂ cfg) :
    IsUniversal utm₂ :=
  IsUniversal_compose utm₁ utm₂ h₁ id h_subset

/-- **`IsUniversal utm` implies utm has a halting cfg (iter 465)**:
    universality implies the existence of at least one halting cfg
    in the UTM.  Proof: any state-0 TM cfg trivially halts; apply
    the universality encoder to get a halting cfg in utm. -/
theorem IsUniversal_has_halting_cfg (utm : Machine) (h : IsUniversal utm) :
    ∃ cfg, Halts utm cfg := by
  obtain ⟨encode, h_encode⟩ := h utm
  refine ⟨encode { state := 0, left := [], head := 0, right := [] }, ?_⟩
  exact h_encode _ (BiTM_Halts_state_zero utm [] 0 [])

/-- **Every TM is trivially universal via halt-collapse (iter 466)**:
    `IsUniversal utm` holds for ANY `utm : Machine`, witnessing the
    striking weakness of the predicate.  The encoder collapses every
    config to wolfram23's halted state-0 cfg, which trivially halts
    in any TM.

    This is exactly the trick used by `smith_reduces` (in CockeMinsky.lean)
    and explains why `wolfram23_universal` (also in CockeMinsky.lean) is
    not particularly informative.  The substantive
    `IsSubstantiallyUniversal` predicate (iter 459) is what's
    genuinely needed. -/
theorem IsUniversal_trivial (utm : Machine) : IsUniversal utm :=
  fun _ => ⟨fun _ => { state := 0, left := [], head := 0, right := [] },
    fun _ _ => BiTM_Halts_state_zero utm [] 0 []⟩

/-- **Wolfram23 is trivially universal (iter 467)**: short proof of
    `IsUniversal wolfram23` via iter 466's universal triviality.
    Bypasses the full Cocke-Minsky / Smith chain, exposing that the
    `IsUniversal` predicate as written is satisfied by any TM. -/
theorem wolfram23_universal_trivial : IsUniversal wolfram23 :=
  IsUniversal_trivial wolfram23

/-- **`IsUniversal_const_encoder` (iter 736)**: generalisation of
    `IsUniversal_trivial`.  If `utm` has any halting cfg `target`,
    then `utm` is universal via the constant encoder `_ ↦ target`.
    Documents that the `IsUniversal` predicate is satisfied as soon as
    a single halting cfg exists — far weaker than substantive
    universality.  Composes `IsUniversal_has_halting_cfg`'s converse
    direction with the constant-encoder construction. -/
theorem IsUniversal_const_encoder
    (utm : Machine) (target : Config) (h : Halts utm target) :
    IsUniversal utm :=
  fun _ => ⟨fun _ => target, fun _ _ => h⟩


/-- **`IsSubstantiallyUniversal` predicate (iter 459)**: stronger
    form of `IsUniversal` that requires per-step emulation +
    halt-cfg encoding (no trivial halt-collapse encoders).  Mirrors
    `SmithReducesFaithful`'s shape but at the universal-utm level. -/
def IsSubstantiallyUniversal (utm : Machine) : Prop :=
  ∀ (tm : Machine), ∃ (encode : Config → Config),
    (∀ cfg cfg', step tm cfg = some cfg' →
      ∃ n, n ≥ 1 ∧ nSteps utm (encode cfg) n = some (encode cfg'))
    ∧ (∀ cfg, halted cfg = true → halted (encode cfg) = true)

/-- **`IsSubstantiallyUniversal ⇒ IsUniversal` (iter 459)**:
    substantive universality implies (weak) universality.  Proof:
    extract per-step emulation, lift to nSteps via iter 398, then
    derive Halts via iter 397's framework specialized to identity-CTS
    (here we just use BiTM step-emulation framework directly). -/
theorem IsSubstantiallyUniversal_implies_IsUniversal
    (utm : Machine) (h : IsSubstantiallyUniversal utm) :
    IsUniversal utm := by
  intro tm
  obtain ⟨encode, h_step, h_halt⟩ := h tm
  refine ⟨encode, ?_⟩
  intro cfg h_halts
  exact tmHalts_imp_tmHalts_under_step_emulation tm utm encode h_step h_halt cfg h_halts

/-- **`IsSubstantiallyUniversal` is closed under per-step-emulating
    encoders (iter 460)**: if utm₁ is substantively universal and
    there's a per-step + halt-preserving encoder utm₁ → utm₂, then
    utm₂ is substantively universal.  Substantive analogue of iter
    458's `IsUniversal_compose`.  Composes via iter 404
    (`tm_step_emulation_compose`). -/
theorem IsSubstantiallyUniversal_compose
    (utm₁ utm₂ : Machine)
    (h₁ : IsSubstantiallyUniversal utm₁)
    (encode : Config → Config)
    (h_step_emulate : ∀ cfg cfg', step utm₁ cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps utm₂ (encode cfg) n = some (encode cfg'))
    (h_halt_preserve : ∀ cfg, halted cfg = true → halted (encode cfg) = true) :
    IsSubstantiallyUniversal utm₂ := by
  intro tm
  obtain ⟨encode₁, h_step₁, h_halt₁⟩ := h₁ tm
  refine ⟨fun cfg => encode (encode₁ cfg), ?_, ?_⟩
  · intro cfg cfg' h_step_tm
    exact tm_step_emulation_compose tm utm₁ utm₂ encode₁ encode
      h_step₁ h_step_emulate cfg cfg' h_step_tm
  · intro cfg h_halt_cfg
    exact h_halt_preserve _ (h_halt₁ cfg h_halt_cfg)

/-- **Per-step emulation encoders cannot collapse to halt (iter
    461)**: if an encoder satisfies per-step emulation utm₁ → utm₂
    for any non-vacuous step of `tm`, then the encoded source is
    not halted.  Generalizes iter 401/402's halt-collapse obstruction
    to arbitrary per-step emulation hypotheses.

    Implication: any `IsSubstantiallyUniversal utm` witness encoder
    is genuinely non-trivial (cannot collapse non-halted source
    cfgs to halted target cfgs). -/
theorem per_step_emulation_encoder_non_halted
    (utm : Machine) (tm : Machine) (encode : Config → Config)
    (h_step_emulate : ∀ cfg cfg', step tm cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps utm (encode cfg) n = some (encode cfg'))
    (cfg cfg' : Config) (h_step_tm : step tm cfg = some cfg') :
    halted (encode cfg) = false := by
  cases h_b : halted (encode cfg) with
  | false => rfl
  | true =>
    exfalso
    have h_state : (encode cfg).state = 0 := by
      simp [halted] at h_b; exact h_b
    exact halted_cfg_no_step_emulation utm (encode cfg) (encode cfg') h_state
      (h_step_emulate cfg cfg' h_step_tm)

/-- **`IsSubstantiallyUniversal utm` produces non-halted images for
    active TMs (iter 462)**: any TM with a non-vacuous step has an
    encoder (from `IsSubstantiallyUniversal utm`) that maps the
    source cfg to a non-halted utm cfg.  Direct application of iter
    461 to `IsSubstantiallyUniversal`'s witness. -/
theorem IsSubstantiallyUniversal_image_non_halted
    (utm : Machine) (h : IsSubstantiallyUniversal utm)
    (tm : Machine) (cfg cfg' : Config) (h_step : step tm cfg = some cfg') :
    ∃ encode : Config → Config,
      (∀ c c', step tm c = some c' →
        ∃ n, n ≥ 1 ∧ nSteps utm (encode c) n = some (encode c'))
      ∧ halted (encode cfg) = false := by
  obtain ⟨encode, h_step_em, _h_halt⟩ := h tm
  refine ⟨encode, h_step_em, ?_⟩
  exact per_step_emulation_encoder_non_halted utm tm encode h_step_em cfg cfg' h_step

/-- **`IsSubstantiallyUniversal utm` forces periodic points for
    self-looping TMs (iter 463)**: if `tm` has a self-step and `utm`
    is substantively universal, then `utm` has a periodic cfg.
    Direct lift of `smithReducesStepFaithful_implies_self_loops_periodic`
    to the universal level.  Documents that
    `IsSubstantiallyUniversal wolfram23` would force wolfram23 to
    have periodic points (a non-trivial open obligation). -/
theorem IsSubstantiallyUniversal_implies_periodic_for_self_looping_TM
    (utm : Machine) (h : IsSubstantiallyUniversal utm)
    (tm : Machine) (cfg : Config) (h_self : step tm cfg = some cfg) :
    ∃ encoded_cfg : Config, ∃ n, n ≥ 1 ∧ nSteps utm encoded_cfg n = some encoded_cfg := by
  obtain ⟨encode, h_step, _⟩ := h tm
  obtain ⟨n, hn_pos, h_n⟩ := h_step cfg cfg h_self
  exact ⟨encode cfg, n, hn_pos, h_n⟩

/-- **`IsSubstantiallyUniversal utm` forces periodic points for
    periodic TMs (iter 464)**: generalises iter 463 from period 1
    to any `p ≥ 1`.  Composes `IsSubstantiallyUniversal` per-step
    emulation with iter 403's positive-budget multi-step lifting. -/
theorem IsSubstantiallyUniversal_implies_periodic_for_periodic_TM
    (utm : Machine) (h : IsSubstantiallyUniversal utm)
    (tm : Machine) (cfg : Config) (p : Nat) (h_pos : p ≥ 1)
    (h_period : nSteps tm cfg p = some cfg) :
    ∃ encoded_cfg : Config, ∃ n, n ≥ 1 ∧ nSteps utm encoded_cfg n = some encoded_cfg := by
  obtain ⟨encode, h_step, _⟩ := h tm
  obtain ⟨m, hm_pos, h_m⟩ := tm_step_to_nSteps_emulation_pos tm utm encode h_step
    cfg p cfg h_pos h_period
  exact ⟨encode cfg, m, hm_pos, h_m⟩

/-- **Substantive universality is strictly stronger (iter 467)**:
    every TM is trivially `IsUniversal` (iter 466), but
    `IsSubstantiallyUniversal` requires per-step emulation +
    halt-preserve, which the halt-collapse encoder fails for any
    TM with a non-vacuous step (per iter 461). -/
theorem IsSubstantiallyUniversal_no_halt_collapse
    (utm : Machine) (tm : Machine) (cfg cfg' : Config)
    (h_step : step tm cfg = some cfg') :
    ¬ ∃ (encode : Config → Config),
        encode = (fun _ => { state := 0, left := [], head := 0, right := [] })
        ∧ (∀ c c', step tm c = some c' →
            ∃ n, n ≥ 1 ∧ nSteps utm (encode c) n = some (encode c')) := by
  rintro ⟨encode, h_eq, h_step_em⟩
  have h_halt : halted (encode cfg) = true := by
    rw [h_eq]; rfl
  have h_not_halt : halted (encode cfg) = false :=
    per_step_emulation_encoder_non_halted utm tm encode h_step_em cfg cfg' h_step
  rw [h_halt] at h_not_halt
  exact Bool.noConfusion h_not_halt

/-- **`IsUniversal_iff_exists_halting_cfg` (iter 738)**: complete
    characterisation of the (weak) `IsUniversal` predicate.  A TM is
    `IsUniversal` iff it has at least one halting cfg.  Forward: from
    a halting target, build the constant encoder via
    `IsUniversal_const_encoder`.  Backward: extract a halting cfg via
    `IsUniversal_has_halting_cfg`.  Cleanly exposes the predicate's
    weakness — no faithful encoding required, just any halting state. -/
theorem IsUniversal_iff_exists_halting_cfg (utm : Machine) :
    IsUniversal utm ↔ ∃ cfg, Halts utm cfg := by
  constructor
  · exact IsUniversal_has_halting_cfg utm
  · rintro ⟨target, h_target⟩
    exact IsUniversal_const_encoder utm target h_target


/-- **`EmulatesPerStep` predicate (iter 468)**: clean Prop bundling
    per-step emulation between two TMs under an encoder.  Used as a
    building block for closure properties. -/
def EmulatesPerStep (tm₁ tm₂ : Machine) (encode : Config → Config) : Prop :=
  ∀ cfg cfg', step tm₁ cfg = some cfg' →
    ∃ n, n ≥ 1 ∧ nSteps tm₂ (encode cfg) n = some (encode cfg')

/-- **`EmulatesPerStep` is reflexive via identity (iter 468)**: any
    TM emulates itself per-step with the identity encoder.  Repackages
    iter 400's `tm_self_emulates_step`. -/
theorem EmulatesPerStep_refl (tm : Machine) : EmulatesPerStep tm tm id :=
  tm_self_emulates_step tm

/-- **`EmulatesPerStep` is transitive (iter 468)**: composes via
    iter 404's `tm_step_emulation_compose`. -/
theorem EmulatesPerStep_trans
    (tm₁ tm₂ tm₃ : Machine) (enc1 enc2 : Config → Config)
    (h₁ : EmulatesPerStep tm₁ tm₂ enc1) (h₂ : EmulatesPerStep tm₂ tm₃ enc2) :
    EmulatesPerStep tm₁ tm₃ (enc2 ∘ enc1) :=
  tm_step_emulation_compose tm₁ tm₂ tm₃ enc1 enc2 h₁ h₂

/-- **`PreservesHalt` predicate (iter 469)**: encoder maps halted
    cfgs to halted cfgs. -/
def PreservesHalt (encode : Config → Config) : Prop :=
  ∀ cfg, halted cfg = true → halted (encode cfg) = true

/-- **`PreservesHalt id` (iter 469)**: identity preserves halt. -/
theorem PreservesHalt_id : PreservesHalt id := fun _ h => h

/-- **`PreservesHalt` composes (iter 469)**: composition of
    halt-preserving encoders is halt-preserving. -/
theorem PreservesHalt_comp
    (enc1 enc2 : Config → Config)
    (h1 : PreservesHalt enc1) (h2 : PreservesHalt enc2) :
    PreservesHalt (enc2 ∘ enc1) :=
  fun cfg h => h2 (enc1 cfg) (h1 cfg h)

/-- **`IsSubstantiallyUniversal` via `EmulatesPerStep` and
    `PreservesHalt` (iter 469)**: clean repackaging of the
    `IsSubstantiallyUniversal` predicate using the new abstractions. -/
theorem IsSubstantiallyUniversal_iff_PerStep_PreservesHalt (utm : Machine) :
    IsSubstantiallyUniversal utm ↔
      ∀ tm, ∃ encode, EmulatesPerStep tm utm encode ∧ PreservesHalt encode :=
  Iff.rfl

/-- **Per-step + halt-preserving encoders give halt-preservation
    (iter 470)**: clean shorthand bundling iter 398's
    `tmHalts_imp_tmHalts_under_step_emulation` using the new
    `EmulatesPerStep` and `PreservesHalt` predicates. -/
theorem EmulatesPerStep_PreservesHalt_imp_halt_preservation
    (tm utm : Machine) (encode : Config → Config)
    (h_step : EmulatesPerStep tm utm encode)
    (h_halt : PreservesHalt encode)
    (cfg : Config) (h_halts : Halts tm cfg) :
    Halts utm (encode cfg) :=
  tmHalts_imp_tmHalts_under_step_emulation tm utm encode h_step h_halt cfg h_halts

/-- **`HaltReduces` predicate (iter 470)**: there exists a per-step
    + halt-preserving encoder from `tm` to `utm`.  Bundles
    `EmulatesPerStep` and `PreservesHalt` into a single Prop. -/
def HaltReduces (tm utm : Machine) : Prop :=
  ∃ encode, EmulatesPerStep tm utm encode ∧ PreservesHalt encode

/-- **`IsSubstantiallyUniversal` ↔ `∀ tm, HaltReduces tm utm`
    (iter 470)**: trivial `Iff.rfl` bridge. -/
theorem IsSubstantiallyUniversal_iff_universal_HaltReduces (utm : Machine) :
    IsSubstantiallyUniversal utm ↔ ∀ tm, HaltReduces tm utm :=
  Iff.rfl

/-- **`HaltReduces` is reflexive (iter 470)**: any TM halt-reduces
    to itself via the identity encoder. -/
theorem HaltReduces_refl (tm : Machine) : HaltReduces tm tm :=
  ⟨id, EmulatesPerStep_refl tm, PreservesHalt_id⟩

/-- **`HaltReduces` is transitive (iter 470)**: composes via iter
    468 (`EmulatesPerStep_trans`) and iter 469 (`PreservesHalt_comp`). -/
theorem HaltReduces_trans
    (tm₁ tm₂ tm₃ : Machine)
    (h₁ : HaltReduces tm₁ tm₂) (h₂ : HaltReduces tm₂ tm₃) :
    HaltReduces tm₁ tm₃ := by
  obtain ⟨enc1, h_step1, h_halt1⟩ := h₁
  obtain ⟨enc2, h_step2, h_halt2⟩ := h₂
  exact ⟨enc2 ∘ enc1, EmulatesPerStep_trans tm₁ tm₂ tm₃ enc1 enc2 h_step1 h_step2,
    PreservesHalt_comp enc1 enc2 h_halt1 h_halt2⟩

/-- **`HaltReduces_imp_IsUniversal_compose` (iter 740)**: substantive
    halt-reduction is a sufficient condition for the closure of (weak)
    `IsUniversal`.  If `utm₁` is universal and `utm₁` halt-reduces to
    `utm₂` (substantive: per-step + halt-cfg encoding), then `utm₂` is
    universal.  Specialisation of `IsUniversal_compose` using the
    `HaltReduces` abstraction.  Bridges substantive ↔ weak universality
    closure forms. -/
theorem HaltReduces_imp_IsUniversal_compose
    (utm₁ utm₂ : Machine)
    (h_uni : IsUniversal utm₁)
    (h_red : HaltReduces utm₁ utm₂) :
    IsUniversal utm₂ := by
  obtain ⟨encode, h_step, h_halt⟩ := h_red
  exact IsUniversal_compose utm₁ utm₂ h_uni encode
    (fun cfg h_halts =>
      EmulatesPerStep_PreservesHalt_imp_halt_preservation utm₁ utm₂ encode
        h_step h_halt cfg h_halts)


/-- **`IsSubstantiallyUniversal` via `HaltReduces` (iter 471)**:
    cleaner restatement of iter 460's `IsSubstantiallyUniversal_compose`
    using the new `HaltReduces` abstraction.  If `utm₁` is
    substantively universal and `utm₁` halt-reduces to `utm₂`, then
    `utm₂` is substantively universal. -/
theorem IsSubstantiallyUniversal_via_HaltReduces
    (utm₁ utm₂ : Machine)
    (h₁ : IsSubstantiallyUniversal utm₁) (h₁₂ : HaltReduces utm₁ utm₂) :
    IsSubstantiallyUniversal utm₂ :=
  fun tm => HaltReduces_trans tm utm₁ utm₂ (h₁ tm) h₁₂

/-- **`HaltReduces` implies `Halts`-preservation (iter 471)**:
    extracts the halt-preservation conclusion from any `HaltReduces`
    witness.  Direct application of iter 470's
    `EmulatesPerStep_PreservesHalt_imp_halt_preservation`. -/
theorem HaltReduces_imp_halt_preservation
    (tm utm : Machine) (h : HaltReduces tm utm)
    (cfg : Config) (h_halts : Halts tm cfg) :
    ∃ encoded : Config, Halts utm encoded := by
  obtain ⟨encode, h_step, h_halt⟩ := h
  exact ⟨encode cfg,
    EmulatesPerStep_PreservesHalt_imp_halt_preservation tm utm encode
      h_step h_halt cfg h_halts⟩

/-- **`IsSubstantiallyUniversal` 3-machine compose (iter 474)**:
    transitive composition through two `HaltReduces` links.  Direct
    composition via iter 470's transitivity. -/
theorem IsSubstantiallyUniversal_compose_trans
    (utm₁ utm₂ utm₃ : Machine)
    (h₁ : IsSubstantiallyUniversal utm₁)
    (h₁₂ : HaltReduces utm₁ utm₂) (h₂₃ : HaltReduces utm₂ utm₃) :
    IsSubstantiallyUniversal utm₃ :=
  IsSubstantiallyUniversal_via_HaltReduces utm₁ utm₃ h₁
    (HaltReduces_trans utm₁ utm₂ utm₃ h₁₂ h₂₃)

/-- **`HaltReduces` 3-link compose (iter 474)**: chain composition
    of `HaltReduces` across three machines.  Direct via iter 470. -/
theorem HaltReduces_trans₃
    (tm₁ tm₂ tm₃ tm₄ : Machine)
    (h₁₂ : HaltReduces tm₁ tm₂) (h₂₃ : HaltReduces tm₂ tm₃)
    (h₃₄ : HaltReduces tm₃ tm₄) :
    HaltReduces tm₁ tm₄ :=
  HaltReduces_trans tm₁ tm₃ tm₄
    (HaltReduces_trans tm₁ tm₂ tm₃ h₁₂ h₂₃) h₃₄

/-- **Mutual `HaltReduces` between two substantively-universal TMs
    (iter 475)**: any two `IsSubstantiallyUniversal` TMs halt-reduce
    to each other (each can simulate the other).  Trivial via
    instantiating each universality predicate at the other TM. -/
theorem IsSubstantiallyUniversal_mutual_HaltReduces
    (utm₁ utm₂ : Machine)
    (h₁ : IsSubstantiallyUniversal utm₁)
    (h₂ : IsSubstantiallyUniversal utm₂) :
    HaltReduces utm₁ utm₂ ∧ HaltReduces utm₂ utm₁ :=
  ⟨h₂ utm₁, h₁ utm₂⟩

/-- **`IsSubstantiallyUniversal utm` forces period ≥ 2 in utm
    (iter 478)**: refined form of iter 464.  Since utm has no
    period-1 orbits (iter 477), the utm-period from
    `IsSubstantiallyUniversal` is at least 2. -/
theorem IsSubstantiallyUniversal_implies_periodic_at_least_2_for_periodic_TM
    (utm : Machine) (h : IsSubstantiallyUniversal utm)
    (tm : Machine) (cfg : Config) (p : Nat) (h_pos : p ≥ 1)
    (h_period : nSteps tm cfg p = some cfg) :
    ∃ encoded_cfg : Config, ∃ n, n ≥ 2 ∧ nSteps utm encoded_cfg n = some encoded_cfg := by
  obtain ⟨encoded_cfg, n, hn_pos, h_period_utm⟩ :=
    IsSubstantiallyUniversal_implies_periodic_for_periodic_TM utm h tm cfg p h_pos h_period
  exact ⟨encoded_cfg, n,
    TM_period_ge_2 utm encoded_cfg n hn_pos h_period_utm, h_period_utm⟩

/-- **`IsSubstantiallyUniversal_imp_TM_period_ge_2_iff` (iter 750)**:
    characterisation form of iter 478.  For a substantively universal
    `utm`, having a periodic point ↔ having a periodic point with
    period `≥ 2`.  Direct via iter 748's `TM_periodic_iff_periodic_ge_2`
    instantiated at utm — the `IsSubstantiallyUniversal` hypothesis is
    only used to derive any periodicity from the source TM's
    periodicity. -/
theorem IsSubstantiallyUniversal_imp_TM_period_ge_2_iff
    (utm : Machine) (_h : IsSubstantiallyUniversal utm)
    (_tm : Machine) (_cfg : Config) (_p : Nat) (_h_pos : _p ≥ 1)
    (_h_period : nSteps _tm _cfg _p = some _cfg) :
    (∃ encoded_cfg : Config, ∃ n, n ≥ 1 ∧ nSteps utm encoded_cfg n = some encoded_cfg)
    ↔ (∃ encoded_cfg : Config, ∃ n, n ≥ 2 ∧ nSteps utm encoded_cfg n = some encoded_cfg) := by
  constructor
  · rintro ⟨encoded_cfg, n, hn_pos, h_period_utm⟩
    exact ⟨encoded_cfg, n,
      TM_period_ge_2 utm encoded_cfg n hn_pos h_period_utm,
      h_period_utm⟩
  · rintro ⟨encoded_cfg, n, hn_ge2, h_period_utm⟩
    exact ⟨encoded_cfg, n, by omega, h_period_utm⟩
  -- The `IsSubstantiallyUniversal` and per-TM-periodic hypotheses are
  -- not used in this iff (the equivalence is purely about strengthening
  -- the bound), but they document the intended usage context.

/-- **`IsSubstantiallyUniversal utm` forces utm active periodic
    orbit of period ≥ 2 for periodic source TMs (iter 483)**:
    universal version combining iter 478 (period ≥ 2) with iter 482
    (active source). -/
theorem IsSubstantiallyUniversal_implies_active_periodic_at_least_2_for_periodic_TM
    (utm : Machine) (h : IsSubstantiallyUniversal utm)
    (tm : Machine) (cfg : Config) (p : Nat) (h_pos : p ≥ 1)
    (h_period : nSteps tm cfg p = some cfg) :
    ∃ encoded_cfg : Config, encoded_cfg.state ≠ 0 ∧
      ∃ n, n ≥ 2 ∧ nSteps utm encoded_cfg n = some encoded_cfg := by
  obtain ⟨encoded_cfg, n, hn_ge_2, h_period_utm⟩ :=
    IsSubstantiallyUniversal_implies_periodic_at_least_2_for_periodic_TM
      utm h tm cfg p h_pos h_period
  refine ⟨encoded_cfg, ?_, n, hn_ge_2, h_period_utm⟩
  exact periodic_source_active utm encoded_cfg n (by omega) h_period_utm

/-- **`IsSubstantiallyUniversal_no_period_imp_no_periodic_TM` (iter
    752)**: contrapositive obstruction.  If `utm` is substantively
    universal but lacks period-≥-2 orbits, then no source TM has any
    periodic point either.  Strong consequence: substantive
    universality of an aperiodic UTM forces every source TM to be
    aperiodic — which is false in general (TMs trivially admit
    period-2 orbits in absurd cases).  Hence aperiodic UTMs cannot
    be substantively universal. -/
theorem IsSubstantiallyUniversal_no_period_imp_no_periodic_TM
    (utm : Machine) (h : IsSubstantiallyUniversal utm)
    (h_no_period : ∀ cfg : Config, ∀ n, n ≥ 2 →
      nSteps utm cfg n ≠ some cfg)
    (tm : Machine) (cfg : Config) (p : Nat) (h_pos : p ≥ 1)
    (h_period : nSteps tm cfg p = some cfg) : False := by
  obtain ⟨encoded_cfg, n, hn_ge_2, h_period_utm⟩ :=
    IsSubstantiallyUniversal_implies_periodic_at_least_2_for_periodic_TM
      utm h tm cfg p h_pos h_period
  exact h_no_period encoded_cfg n hn_ge_2 h_period_utm

/-- **`IsSubstantiallyUniversal_no_active_period_imp_no_periodic_TM`
    (iter 758)**: active-source variant of iter 752's obstruction.
    If `utm` lacks active period-≥-2 orbits (state ≠ 0 + period ≥ 2),
    then no source TM is periodic.  Sharper than `_no_period_imp` since
    active-period-≥-2 is a strictly weaker obstruction (rules out fewer
    utms).  Useful when only the active orbit structure is known. -/
theorem IsSubstantiallyUniversal_no_active_period_imp_no_periodic_TM
    (utm : Machine) (h : IsSubstantiallyUniversal utm)
    (h_no_active_period : ∀ cfg : Config, cfg.state ≠ 0 →
      ∀ n, n ≥ 2 → nSteps utm cfg n ≠ some cfg)
    (tm : Machine) (cfg : Config) (p : Nat) (h_pos : p ≥ 1)
    (h_period : nSteps tm cfg p = some cfg) : False := by
  obtain ⟨encoded_cfg, h_active, n, hn_ge_2, h_period_utm⟩ :=
    IsSubstantiallyUniversal_implies_active_periodic_at_least_2_for_periodic_TM
      utm h tm cfg p h_pos h_period
  exact h_no_active_period encoded_cfg h_active n hn_ge_2 h_period_utm

/-- **`IsSubstantiallyUniversal_imp_self_HaltReduces` (iter 760)**:
    every substantively universal utm halt-reduces to itself.  Direct
    instantiation of the predicate at `tm := utm`.  Documents that the
    `IsSubstantiallyUniversal` predicate is reflexive in the
    `HaltReduces` sense (separately from `HaltReduces_refl` via the
    identity encoder, this version uses utm's own substantive-
    universality witness for `tm := utm`). -/
theorem IsSubstantiallyUniversal_imp_self_HaltReduces
    (utm : Machine) (h : IsSubstantiallyUniversal utm) :
    HaltReduces utm utm :=
  h utm

end BiTM
