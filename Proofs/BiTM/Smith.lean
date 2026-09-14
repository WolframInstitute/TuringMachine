/-
  BiTM.Smith

  Step-faithful Smith-reduction predicates and their structural
  obstructions, extracted from `BiTM.CockeMinskyConstruction`.

  Contents:
    * `SmithReducesStepFaithful` — universal predicate
    * `SmithSimulatesCTS` — per-CTS variant
    * `smithReducesStepFaithful_of_per_cts_simulates` — Classical-choice
      bridge
    * `smithReducesStepFaithful_implies_self_loops_periodic` — CTS
      self-loops force wolfram23 periodic points
    * `smithReducesStepFaithful_implies_wolfram23_periodic` — concrete
      obstruction via `selfLoopCTS`
-/

import BiTM.Basic
import TagSystem.Basic
import TagSystem.HaltsEmpty

namespace BiTM

open TM
open TagSystem

/-- Step-faithful smith reduction: an encoder of (cts, ctsCfg) into
    wolfram23 cfgs that mirrors every CTS step by ≥ 1 wolfram23 steps.

    Captures Smith 2007's "System 0 emulates 2-color cyclic tag system"
    claim (PDF Conjecture 0, p. 3) at the per-step level.  Drops the
    halt-encodes-halted clause from the original `SmithReducesFaithful`
    since wolfram23 from a valid input never enters state 0
    (`not_halts_wolfram23_valid`). -/
def SmithReducesStepFaithful : Prop :=
  ∃ (encode : CTS → CTSConfig → Config),
    ∀ cts ctsCfg ctsCfg',
      cts.step ctsCfg = some ctsCfg' →
      ∃ n, n ≥ 1 ∧ nSteps wolfram23 (encode cts ctsCfg) n = some (encode cts ctsCfg')

/-- Per-CTS variant of `SmithReducesStepFaithful`.  Decoupling per-CTS
    decomposes the universal predicate: prove this for every `cts` and
    bundle via Classical choice to recover `SmithReducesStepFaithful`.

    For each CTS, the encoder is a function `CTSConfig → Config` (no
    `cts` dependency).  Step pairs `cfg → cfg'` of the GIVEN cts must
    be mirrored by some n ≥ 1 wolfram23 steps. -/
def SmithSimulatesCTS (cts : CTS) : Prop :=
  ∃ (encode : CTSConfig → Config),
    ∀ ctsCfg ctsCfg',
      cts.step ctsCfg = some ctsCfg' →
      ∃ n, n ≥ 1 ∧ nSteps wolfram23 (encode ctsCfg) n = some (encode ctsCfg')

/-- **Bridge**: per-CTS simulability ⇒ universal step-faithful Smith.
    Uses `Classical.choose` to bundle the per-CTS encoders into a single
    `(cts, ctsCfg) → Config` function. -/
theorem smithReducesStepFaithful_of_per_cts_simulates
    (h : ∀ cts, SmithSimulatesCTS cts) : SmithReducesStepFaithful := by
  classical
  refine ⟨fun cts => Classical.choose (h cts), ?_⟩
  intro cts ctsCfg ctsCfg' h_step
  exact Classical.choose_spec (h cts) ctsCfg ctsCfg' h_step

/-- **Obstruction lemma**: `SmithReducesStepFaithful` imposes that wolfram23
    has periodic points wherever a CTS has self-loops.  Specifically, if any
    CTS has a self-step `cfg → cfg`, then the encoded wolfram23 cfg must be
    a periodic point of wolfram23.

    This documents WHY the predicate is hard: wolfram23 has no proven
    periodic points (and likely none, given universality), so a CTS with
    self-loops obstructs the predicate.  Future work may need a different
    smith formulation. -/
theorem smithReducesStepFaithful_implies_self_loops_periodic
    (h : SmithReducesStepFaithful) (cts : CTS) (cfg : CTSConfig)
    (h_self : cts.step cfg = some cfg) :
    ∃ encode_cfg : Config, ∃ n, n ≥ 1
        ∧ nSteps wolfram23 encode_cfg n = some encode_cfg := by
  obtain ⟨encode, h_sim⟩ := h
  obtain ⟨n, hn_pos, h_eq⟩ := h_sim cts cfg cfg h_self
  exact ⟨encode cts cfg, n, hn_pos, h_eq⟩


/-- **Concrete obstruction**: `SmithReducesStepFaithful` ⇒ wolfram23 has
    a periodic point at the encoded `selfLoopCTS` cfg.

    Smith 2007 (PDF "How I constructed this proof", p. 55+) sidesteps this
    by encoding CTS *evolution history* into the wolfram23 tape pattern,
    not by requiring wolfram23 itself to cycle.  Future smith-side work
    must either reformulate this predicate (to allow Smith's evolving
    encoding) or prove the periodic point exists. -/
theorem smithReducesStepFaithful_implies_wolfram23_periodic
    (h : SmithReducesStepFaithful) :
    ∃ cfg : Config, ∃ n, n ≥ 1 ∧ nSteps wolfram23 cfg n = some cfg :=
  smithReducesStepFaithful_implies_self_loops_periodic h
    selfLoopCTS { data := [true, true], phase := 0 }
    selfLoopCTS_has_self_step

end BiTM
