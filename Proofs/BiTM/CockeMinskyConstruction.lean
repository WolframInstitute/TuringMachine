/-
  BiTM.CockeMinskyConstruction

  Two reductions toward Wolfram-(2,3) universality:

  COCKE-MINSKY (TM → 2-tag, Cocke 1964 / Minsky 1967 Ch. 14):
    * `cocke_minsky_reduces_faithful_universal` — meaningful proof of
      `CockeMinskyReducesFaithful tm` for ANY TM, via a 2-symbol tag system
      (halt-trajectory marker `a` with `prods a = []`, non-halt-trajectory
      marker `b` with `prods b = [b, b]` self-loop).  No structural
      hypotheses on the TM.
    * `cocke_minsky_reduces_via_universal` — closed downstream consumer of
      `CockeMinskyReduces tm` (replaces the trivial halt-collapse encoder
      in `BiTM.CockeMinsky`).
    * Parametric depth abstractions (`_of_depth_decreasing`,
      `_of_depth_weakly_decreasing`) and concrete sub-classes
      (immediate-halt, two- and three-step-halt, linear-chain,
      uniform-halt, eventual-halt).

  SMITH (CTS → wolfram23, Smith 2007 — `wolframscience.com/prizes/tm23/TM23Proof.pdf`):
    * Structural obstruction: `smithReducesStepFaithful_implies_self_loops_periodic`
      + `selfLoopCTS` show that any encoder faithful to CTS self-loops forces
      a periodic point of wolfram23.
    * `selfLoopCTS_periodic_all_m`: the obstruction's CTS witness is m-periodic
      for every m ≥ 0 (so the forced wolfram23 cycle can have any period).
    * Length monovariant (`step_total_length_nondecreasing`,
      `nSteps_total_length_nondecreasing`) and read-side constraints
      (`wolfram23_periodic_first_step_reads_nonempty`,
      `wolfram23_periodic_along_cycle_nonempty_read`,
      `wolfram23_periodic_state_and_head_valid`).
    * Period-1 ruled out from valid cfgs via `step_wolfram23_changes_cfg`.
    * `wolfram23_init` proven aperiodic (`wolfram23_from_init_not_periodic`).
    * CTS phase analysis: `cts_step_phase_changes` + `cts_cycle_phase_period_divides`.
    * System5Config (PDF p. 30) + `System5.step` + `System5.nSteps`
      faithfully implementing Smith's `system5.pl`: parity-mod-2 bag,
      decrement, conditional rule-pop with `xorMerge`.  Helpers:
      `xorInsert`, `xorMerge`.
    * `ctsConfigToSystem5Bag` per `cy2s5.pl` PDF p. 27 (verified
      against `test1.cy`'s working string `11011` via `decide`).
    * `ctsRulesToSystem5Rules` per `cy2s5.pl` PDF p. 28 (helpers:
      `counterAfterWorkingString`, `encodeAppendant`, `processCycle`,
      `nCycles`; each CTS appendant produces 3 System 5 rules).
    * `System5_step_pure_decrement` / `System5_step_pop_rule` /
      `System5_step_none_iff` characterise the step relation.
    * System 4 scaffold (PDF p. 34): `System4State`, `System4Elem`,
      `System4Config`, `System4.step`, `System4.nSteps`.
      `system5ToSystem4` encoder per PDF p. 32 (`s52s4.pl`).
    * `GeneralizedTM` type (multi-cell writes via `writes : List Sym`)
      enables System 1-3 transitions that aren't `BiTM.Machine`-
      representable.
    * System 0 ↔ 1 ↔ 2 ↔ 3 ↔ 4 ↔ 5 reduction chain partially built.
      Translation `wolfram23CfgToSystem1` + inverse + round-trip on
      valid cfgs + injectivity.  Halts/CTS bridges.  System 1
      transition table from PDF p. 4 deferred (`SORRY[system1-
      transition-table]`).
    * Halt-induction principles (Tag/CTS/BiTM/System5/System4):
      strong induction over halting cfgs from a halt-base + a
      backwards-step preservation hypothesis.  Used to derive
      `HaltsEmpty ↔ ∃ n, tagNSteps cfg n = some []` and friends.

  See `git log` for the granular iteration history.
  Remaining sorries: 2 substantive (`cmStep_sim` active case;
  `smith_reduces_faithful`) + 1 stub (`ctsToSystem5_emulates`'s
  per-step bag-match, with the predicate-weakness retained pending
  reformulation).
    1. `cmStep_sim` active case (alphabet redesign for the provisional
       Minsky-1967 sketch — off the critical path; superseded by
       `_universal` above).
    2. `smith_reduces_faithful` (multi-month work).
    3. `ctsToSystem5_emulates` (`smith-conjecture-0`) — Smith's main
       per-step emulation.  Closure path: implement the System 1-3
       multi-cell-write transitions, prove System 5 → 4 → 3 → 2 → 1 →
       0(=wolfram23) emulation chain, then derive that each CTS step is
       mirrored by some `j ≥ 1` System 5 steps reproducing the encoded
       next config.

  ---------------------------------------------------------------------------
  PLAN (provisional Cocke-Minsky sketch, superseded by `_universal`)
  ---------------------------------------------------------------------------
  We follow the Minsky 1967 construction (Ch. 14, Thm 14.6-1).

    Alphabet (size = s·k + 4k + 1, where s = numStates, k = numSymbols):
      A(q, a)     state-symbol pair         q ∈ 1..s, a ∈ 0..k-1   (s·k)
      B(a)        right-cell                a ∈ 0..k-1             (k)
      B'(a)       right-cell, primed        a ∈ 0..k-1             (k)
      C(a)        left-cell                 a ∈ 0..k-1             (k)
      C'(a)       left-cell, primed         a ∈ 0..k-1             (k)
      S           tape separator                                   (1)

    Encoding of cfg = ⟨q, left, h, right⟩:
      A(q, h) · B(r₀) · B'(r₁) · B(r₂) · ... · S · C(l₀) · C'(l₁) · C(l₂) · ...

    Production rules (sketch):
      A(q, a) ⟼  productions chosen by δ(q, a) that sweep one TM step
                 through the encoded tape, taking O(|tape|) tag steps.
                 The B/B' alternation pairs with 2-tag's "delete first 2"
                 to preserve granularity through the sweep.
      B(a)    ⟼  pass-through productions during the sweep
      C(a)    ⟼  pass-through productions during the sweep
      S       ⟼  identity-like, separating the two tape halves
      Halt:   A(0, _) ⟼ []   (once we artificially push state 0 into A)

    Key simulation lemma (target of subsequent iterations):
      ∀ tm cfg cfg', step tm cfg = some cfg' →
        ∃ n, tagNSteps (cmTagSystem tm) (cmEncode tm cfg) n
              = some (cmEncode tm cfg')

    Halting lemma (the form the final theorem needs):
      ∀ tm cfg, halted cfg → cmEncode tm cfg = []
      (so HaltsEmpty is automatic)

  ---------------------------------------------------------------------------
  REDESIGN NOTES (consolidated; toward closing `cmStep_sim` active case)
  ---------------------------------------------------------------------------
  The current 5k+1-symbol alphabet (A/B/B'/C/C'/S) is insufficient for a
  faithful Cocke-Minsky simulation.  The fundamental issues:

  1. PASS-THROUGH PRODUCTIONS LOSE INFO.
     `B(a) → [B'(a)]` (length 1) means 2-tag deletes the next symbol
     along with `B(a)` and only appends one symbol.  Information from
     the deleted next symbol is lost.  Cocke-Minsky's actual construction
     encodes each tape cell as MULTIPLE tag symbols (in unary), so
     delete-2-append-1 doesn't lose semantic info.

  2. ACTIVE PRODUCTION PUTS A AT THE END.
     `[B(w), A(q', a)]` places the new state-symbol marker at the END
     of the resulting word.  `cmEncode` of the post-step config has A at
     the FRONT.  No number of pass-through steps can rotate the word —
     pass-throughs only shrink it (-1 per step).

  3. HALT REACHES []` ONLY FOR THE EMPTY-TAPE CASE.
     `A(q, a) → []` (halt rule) gives `tag step` of length 2 → `[]`.
     For longer encodings, the residue is non-empty and pass-through
     drains shrink to length 1, NOT 0; `HaltsEmpty` fails.

  ---------------------------------------------------------------------------
  WHAT A FAITHFUL REDESIGN WOULD NEED
  ---------------------------------------------------------------------------
  - Unary cell encoding: each tape cell becomes a *block* of tag symbols
    so the simulation has the bandwidth to absorb 2-tag's deletions.
    Wang-style encoding represents the tape as `m · 2^n` and the
    simulation does multiplication/division by 2 via tag rules.
  - Multi-phase markers: each phase of the per-step sweep gets its own
    set of markers; productions transition between phases as the
    sweep advances through the tape.  Total alphabet ≈ O(s · k · phases).
  - Reduction to 2-symbol TMs first: Cocke-Minsky's original is for
    2-symbol TMs; general TMs reduce via standard binary encoding.

  ESTIMATED EFFORT: ~500–1500 additional lines of Lean across many
  iterations.  Out of scope for the present cron-loop pace.

  ---------------------------------------------------------------------------
  REFERENCES
  ---------------------------------------------------------------------------
  - Cocke, J. (1964).  Abstract 611-52, Notices AMS 11(3).
  - Minsky, M. (1967).  *Computation: Finite and Infinite Machines*, Ch. 14.
  - Rogozhin, Yu. (1996).  "Small Universal Turing Machines",
      *Theor. Comp. Sci.* 168(2) — cleaner small-alphabet variants.
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

namespace BiTM
namespace CockeMinskyConstruction

open TM
open TagSystem
open BiTM (Config Halts halted step eval CockeMinskyReduces)


-- ============================================================================
-- Alphabet size
-- ============================================================================

/-- Total alphabet size for the Cocke-Minsky tag system encoding of `tm`.
    Layout:
      [0, s·k)               : A(q, a)  with index (q-1)·k + a
      [s·k, s·k + k)         : B(a)     with index s·k + a
      [s·k + k, s·k + 2k)    : B'(a)    with index s·k + k + a
      [s·k + 2k, s·k + 3k)   : C(a)     with index s·k + 2k + a
      [s·k + 3k, s·k + 4k)   : C'(a)    with index s·k + 3k + a
      [s·k + 4k, s·k + 4k+1) : S        single symbol -/
def cmSize (tm : Machine) : Nat :=
  tm.numStates * tm.numSymbols + 4 * tm.numSymbols + 1

theorem cmSize_pos (tm : Machine) : cmSize tm > 0 := by
  unfold cmSize; omega

-- ============================================================================
-- Alphabet constructors
-- ============================================================================

/-- A(q, a): state-symbol marker.  Index = (q-1)·k + a.
    Requires `1 ≤ q ≤ s` and `a < k`. -/
def mkA {tm : Machine} (q a : Nat) (hq : 1 ≤ q) (hq' : q ≤ tm.numStates)
    (ha : a < tm.numSymbols) : Fin (cmSize tm) :=
  ⟨(q - 1) * tm.numSymbols + a, by
    unfold cmSize
    have h1 : q - 1 < tm.numStates := by omega
    have h2 : (q - 1) * tm.numSymbols < tm.numStates * tm.numSymbols :=
      Nat.mul_lt_mul_of_pos_right h1 (by omega)
    omega⟩

/-- B(a): right-tape cell marker.  Index = s·k + a. -/
def mkB {tm : Machine} (a : Nat) (ha : a < tm.numSymbols) :
    Fin (cmSize tm) :=
  ⟨tm.numStates * tm.numSymbols + a, by unfold cmSize; omega⟩

/-- B'(a): right-tape cell marker, primed copy.  Index = s·k + k + a. -/
def mkBP {tm : Machine} (a : Nat) (ha : a < tm.numSymbols) :
    Fin (cmSize tm) :=
  ⟨tm.numStates * tm.numSymbols + tm.numSymbols + a, by unfold cmSize; omega⟩

/-- C(a): left-tape cell marker.  Index = s·k + 2k + a. -/
def mkC {tm : Machine} (a : Nat) (ha : a < tm.numSymbols) :
    Fin (cmSize tm) :=
  ⟨tm.numStates * tm.numSymbols + 2 * tm.numSymbols + a, by unfold cmSize; omega⟩

/-- C'(a): left-tape cell marker, primed copy.  Index = s·k + 3k + a. -/
def mkCP {tm : Machine} (a : Nat) (ha : a < tm.numSymbols) :
    Fin (cmSize tm) :=
  ⟨tm.numStates * tm.numSymbols + 3 * tm.numSymbols + a, by unfold cmSize; omega⟩

/-- S: tape separator.  Index = s·k + 4k. -/
def mkS (tm : Machine) : Fin (cmSize tm) :=
  ⟨tm.numStates * tm.numSymbols + 4 * tm.numSymbols, by unfold cmSize; omega⟩

-- ============================================================================
-- Alphabet classifier
-- ============================================================================

/-- Classification of a tag-system symbol into its Cocke-Minsky alphabet class.
    Mirrors the six `mk*` constructors and lets production rules pattern-match
    on which class a symbol belongs to. -/
inductive CMKind (tm : Machine) where
  | A  (q a : Nat) (hq : 1 ≤ q) (hq' : q ≤ tm.numStates) (ha : a < tm.numSymbols)
  | B  (a : Nat) (ha : a < tm.numSymbols)
  | BP (a : Nat) (ha : a < tm.numSymbols)
  | C  (a : Nat) (ha : a < tm.numSymbols)
  | CP (a : Nat) (ha : a < tm.numSymbols)
  | S

/-- Decode a tag symbol back into its alphabet class. -/
def cmKind {tm : Machine} (sym : Fin (cmSize tm)) : CMKind tm :=
  if h_A : sym.val < tm.numStates * tm.numSymbols then
    have hk : 0 < tm.numSymbols := by
      cases hkz : tm.numSymbols with
      | zero => rw [hkz] at h_A; simp at h_A
      | succ _ => omega
    have h_div : sym.val / tm.numSymbols < tm.numStates :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h_A)
    CMKind.A (sym.val / tm.numSymbols + 1) (sym.val % tm.numSymbols)
      (Nat.le_add_left 1 _) h_div (Nat.mod_lt _ hk)
  else if h_B : sym.val < tm.numStates * tm.numSymbols + tm.numSymbols then
    CMKind.B (sym.val - tm.numStates * tm.numSymbols) (by omega)
  else if h_BP : sym.val < tm.numStates * tm.numSymbols + 2 * tm.numSymbols then
    CMKind.BP (sym.val - tm.numStates * tm.numSymbols - tm.numSymbols) (by omega)
  else if h_C : sym.val < tm.numStates * tm.numSymbols + 3 * tm.numSymbols then
    CMKind.C (sym.val - tm.numStates * tm.numSymbols - 2 * tm.numSymbols) (by omega)
  else if h_CP : sym.val < tm.numStates * tm.numSymbols + 4 * tm.numSymbols then
    CMKind.CP (sym.val - tm.numStates * tm.numSymbols - 3 * tm.numSymbols) (by omega)
  else
    CMKind.S

-- ============================================================================
-- Round-trip lemmas: `cmKind` recovers the constructor data
-- ============================================================================

/-- Smart-equality for `CMKind.A`: data equality implies kind equality
    (proof fields collapse via `subst` + proof irrelevance).  Used to dodge
    the dependent-motive issue when we rewrite `cmKind`'s A-branch output. -/
theorem CMKind.A_eq_of_data {tm : Machine}
    {q a q' a' : Nat}
    {hq : 1 ≤ q} {hq' : q ≤ tm.numStates} {ha : a < tm.numSymbols}
    {hq2 : 1 ≤ q'} {hq'2 : q' ≤ tm.numStates} {ha2 : a' < tm.numSymbols}
    (h_q : q = q') (h_a : a = a') :
    CMKind.A q a hq hq' ha = CMKind.A q' a' hq2 hq'2 ha2 := by
  subst h_q; subst h_a; rfl

@[simp] theorem mkA_val {tm : Machine} (q a : Nat) (hq : 1 ≤ q)
    (hq' : q ≤ tm.numStates) (ha : a < tm.numSymbols) :
    (mkA q a hq hq' ha).val = (q - 1) * tm.numSymbols + a := rfl

@[simp] theorem mkB_val {tm : Machine} (a : Nat) (ha : a < tm.numSymbols) :
    (mkB a ha (tm := tm)).val = tm.numStates * tm.numSymbols + a := rfl

@[simp] theorem mkBP_val {tm : Machine} (a : Nat) (ha : a < tm.numSymbols) :
    (mkBP a ha (tm := tm)).val =
      tm.numStates * tm.numSymbols + tm.numSymbols + a := rfl

@[simp] theorem mkC_val {tm : Machine} (a : Nat) (ha : a < tm.numSymbols) :
    (mkC a ha (tm := tm)).val =
      tm.numStates * tm.numSymbols + 2 * tm.numSymbols + a := rfl

@[simp] theorem mkCP_val {tm : Machine} (a : Nat) (ha : a < tm.numSymbols) :
    (mkCP a ha (tm := tm)).val =
      tm.numStates * tm.numSymbols + 3 * tm.numSymbols + a := rfl

@[simp] theorem mkS_val (tm : Machine) :
    (mkS tm).val = tm.numStates * tm.numSymbols + 4 * tm.numSymbols := rfl

theorem cmKind_mkA {tm : Machine} (q a : Nat) (hq : 1 ≤ q)
    (hq' : q ≤ tm.numStates) (ha : a < tm.numSymbols) :
    cmKind (mkA q a hq hq' ha) = CMKind.A q a hq hq' ha := by
  have hk : 0 < tm.numSymbols := Nat.lt_of_le_of_lt (Nat.zero_le a) ha
  have h_A : (q - 1) * tm.numSymbols + a < tm.numStates * tm.numSymbols := by
    have hq_step : (q - 1) * tm.numSymbols + tm.numSymbols = q * tm.numSymbols := by
      have h1 : (q - 1 + 1) * tm.numSymbols
                  = (q - 1) * tm.numSymbols + tm.numSymbols := by
        rw [Nat.add_mul, Nat.one_mul]
      have h2 : q - 1 + 1 = q := Nat.sub_add_cancel hq
      rw [← h1, h2]
    have h_qk : q * tm.numSymbols ≤ tm.numStates * tm.numSymbols :=
      Nat.mul_le_mul_right _ hq'
    omega
  have h_div : ((q - 1) * tm.numSymbols + a) / tm.numSymbols = q - 1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right a (q - 1) hk,
        Nat.div_eq_of_lt ha, Nat.zero_add]
  have h_mod : ((q - 1) * tm.numSymbols + a) % tm.numSymbols = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt ha
  unfold cmKind
  simp only [mkA_val]
  rw [dif_pos h_A]
  exact CMKind.A_eq_of_data
    (by rw [h_div]; exact Nat.sub_add_cancel hq) h_mod

theorem cmKind_mkB {tm : Machine} (a : Nat) (ha : a < tm.numSymbols) :
    cmKind (mkB a ha (tm := tm)) = CMKind.B a ha := by
  unfold cmKind
  simp only [mkB_val]
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 1
  omega

theorem cmKind_mkBP {tm : Machine} (a : Nat) (ha : a < tm.numSymbols) :
    cmKind (mkBP a ha (tm := tm)) = CMKind.BP a ha := by
  unfold cmKind
  simp only [mkBP_val]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  congr 1
  omega

theorem cmKind_mkC {tm : Machine} (a : Nat) (ha : a < tm.numSymbols) :
    cmKind (mkC a ha (tm := tm)) = CMKind.C a ha := by
  unfold cmKind
  simp only [mkC_val]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  congr 1
  omega

theorem cmKind_mkCP {tm : Machine} (a : Nat) (ha : a < tm.numSymbols) :
    cmKind (mkCP a ha (tm := tm)) = CMKind.CP a ha := by
  unfold cmKind
  simp only [mkCP_val]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
      dif_neg (by omega), dif_pos (by omega)]
  congr 1
  omega

theorem cmKind_mkS (tm : Machine) :
    cmKind (mkS tm) = CMKind.S := by
  unfold cmKind
  simp only [mkS_val]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
      dif_neg (by omega), dif_neg (by omega)]

-- ============================================================================
-- Production-rule helpers (one per kind; sorry-stubbed)
-- ============================================================================

/-- Production for `A(q,a)` when `δ(q,a)` is active (next state ≠ 0).

    PROVISIONAL: this is a structural sketch.  For valid transition data
    (`1 ≤ r.nextState ≤ numStates`, `r.write < numSymbols`):
      R-move:  `A(q,a) → [B(w), A(q', a)]`
      L-move:  `A(q,a) → [C(w), A(q', a)]`
    Otherwise (malformed transition), produce `[]`.

    Note: a *faithful* Cocke-Minsky simulation requires a richer alphabet
    (auxiliary "sweep" markers carrying state info through the tape) that
    this construction does not provide.  Closing `cmStep_sim` against the
    present sketch will likely require redesigning the alphabet — that
    redesign is the topic of future iterations. -/
def cmAActive (tm : Machine) (q a : Nat)
    (_hq : 1 ≤ q) (_hq' : q ≤ tm.numStates) (ha : a < tm.numSymbols)
    (_h_active : (tm.transition q a).nextState ≠ 0) :
    List (Fin (cmSize tm)) :=
  let r := tm.transition q a
  if h_valid : 1 ≤ r.nextState ∧ r.nextState ≤ tm.numStates
                ∧ r.write < tm.numSymbols then
    match r.dir with
    | Dir.R =>
        [mkB r.write h_valid.2.2 (tm := tm),
         mkA r.nextState a h_valid.1 h_valid.2.1 ha (tm := tm)]
    | Dir.L =>
        [mkC r.write h_valid.2.2 (tm := tm),
         mkA r.nextState a h_valid.1 h_valid.2.1 ha (tm := tm)]
  else
    []

/-- Production for `B(a)`: alternating toggle to `B'(a)`. -/
def cmBProd (tm : Machine) (a : Nat) (ha : a < tm.numSymbols) :
    List (Fin (cmSize tm)) :=
  [mkBP a ha (tm := tm)]

/-- Production for `B'(a)`: alternating toggle back to `B(a)`. -/
def cmBPProd (tm : Machine) (a : Nat) (ha : a < tm.numSymbols) :
    List (Fin (cmSize tm)) :=
  [mkB a ha (tm := tm)]

/-- Production for `C(a)`: alternating toggle to `C'(a)`. -/
def cmCProd (tm : Machine) (a : Nat) (ha : a < tm.numSymbols) :
    List (Fin (cmSize tm)) :=
  [mkCP a ha (tm := tm)]

/-- Production for `C'(a)`: alternating toggle back to `C(a)`. -/
def cmCPProd (tm : Machine) (a : Nat) (ha : a < tm.numSymbols) :
    List (Fin (cmSize tm)) :=
  [mkC a ha (tm := tm)]

/-- Production for the separator `S`: identity. -/
def cmSProd (tm : Machine) : List (Fin (cmSize tm)) :=
  [mkS tm]

-- Production-length bookkeeping (used by length-driven simulation arguments).

@[simp] theorem cmBProd_length (tm : Machine) (a : Nat) (ha : a < tm.numSymbols) :
    (cmBProd tm a ha).length = 1 := rfl

@[simp] theorem cmBPProd_length (tm : Machine) (a : Nat) (ha : a < tm.numSymbols) :
    (cmBPProd tm a ha).length = 1 := rfl

@[simp] theorem cmCProd_length (tm : Machine) (a : Nat) (ha : a < tm.numSymbols) :
    (cmCProd tm a ha).length = 1 := rfl

@[simp] theorem cmCPProd_length (tm : Machine) (a : Nat) (ha : a < tm.numSymbols) :
    (cmCPProd tm a ha).length = 1 := rfl

@[simp] theorem cmSProd_length (tm : Machine) :
    (cmSProd tm).length = 1 := rfl

/-- Length of `cmAActive` is `2` when the transition data is well-formed
    (next state in `[1, numStates]`, write symbol `< numSymbols`). -/
theorem cmAActive_length_valid (tm : Machine) (q a : Nat)
    (hq : 1 ≤ q) (hq' : q ≤ tm.numStates) (ha : a < tm.numSymbols)
    (h_active : (tm.transition q a).nextState ≠ 0)
    (h_valid : 1 ≤ (tm.transition q a).nextState
               ∧ (tm.transition q a).nextState ≤ tm.numStates
               ∧ (tm.transition q a).write < tm.numSymbols) :
    (cmAActive tm q a hq hq' ha h_active).length = 2 := by
  unfold cmAActive
  rw [dif_pos h_valid]
  cases (tm.transition q a).dir <;> rfl

/-- Length of `cmAActive` is `0` when the transition data is malformed.
    (Acts like the halt rule in that pathological case.) -/
theorem cmAActive_length_invalid (tm : Machine) (q a : Nat)
    (hq : 1 ≤ q) (hq' : q ≤ tm.numStates) (ha : a < tm.numSymbols)
    (h_active : (tm.transition q a).nextState ≠ 0)
    (h_invalid : ¬ (1 ≤ (tm.transition q a).nextState
                    ∧ (tm.transition q a).nextState ≤ tm.numStates
                    ∧ (tm.transition q a).write < tm.numSymbols)) :
    (cmAActive tm q a hq hq' ha h_active).length = 0 := by
  unfold cmAActive
  rw [dif_neg h_invalid]
  rfl

-- ============================================================================
-- Tag system construction
-- ============================================================================

/-- The Cocke-Minsky tag system for `tm`.  Productions dispatch on the
    alphabet class of the symbol (via `cmKind`).  The halt rule is
    inlined; all other classes delegate to the named helpers above. -/
def cmTagSystem (tm : Machine) : Tag (cmSize tm) where
  productions := fun sym =>
    match cmKind sym with
    | .A q a hq hq' ha =>
        if h : (tm.transition q a).nextState = 0 then
          ([] : List (Fin (cmSize tm)))
        else
          cmAActive tm q a hq hq' ha h
    | .B  a ha => cmBProd  tm a ha
    | .BP a ha => cmBPProd tm a ha
    | .C  a ha => cmCProd  tm a ha
    | .CP a ha => cmCPProd tm a ha
    | .S       => cmSProd  tm

-- ============================================================================
-- Dispatch-level production lemmas: what `productions` returns on each
-- alphabet builder.  These are how a `Tag.step` proof actually computes.
-- ============================================================================

theorem productions_mkA_halt (tm : Machine) (q a : Nat)
    (hq : 1 ≤ q) (hq' : q ≤ tm.numStates) (ha : a < tm.numSymbols)
    (h_halt : (tm.transition q a).nextState = 0) :
    (cmTagSystem tm).productions (mkA q a hq hq' ha (tm := tm)) = [] := by
  show (match cmKind (mkA q a hq hq' ha (tm := tm)) with
        | .A q' a' hq2 hq'2 ha2 =>
            if h : (tm.transition q' a').nextState = 0 then
              ([] : List (Fin (cmSize tm)))
            else cmAActive tm q' a' hq2 hq'2 ha2 h
        | .B  a ha => cmBProd  tm a ha
        | .BP a ha => cmBPProd tm a ha
        | .C  a ha => cmCProd  tm a ha
        | .CP a ha => cmCPProd tm a ha
        | .S       => cmSProd  tm) = []
  rw [cmKind_mkA]
  exact dif_pos h_halt

theorem productions_mkA_active (tm : Machine) (q a : Nat)
    (hq : 1 ≤ q) (hq' : q ≤ tm.numStates) (ha : a < tm.numSymbols)
    (h_active : (tm.transition q a).nextState ≠ 0) :
    (cmTagSystem tm).productions (mkA q a hq hq' ha (tm := tm))
      = cmAActive tm q a hq hq' ha h_active := by
  show (match cmKind (mkA q a hq hq' ha (tm := tm)) with
        | .A q' a' hq2 hq'2 ha2 =>
            if h : (tm.transition q' a').nextState = 0 then
              ([] : List (Fin (cmSize tm)))
            else cmAActive tm q' a' hq2 hq'2 ha2 h
        | .B  a ha => cmBProd  tm a ha
        | .BP a ha => cmBPProd tm a ha
        | .C  a ha => cmCProd  tm a ha
        | .CP a ha => cmCPProd tm a ha
        | .S       => cmSProd  tm) = cmAActive tm q a hq hq' ha h_active
  rw [cmKind_mkA]
  exact dif_neg h_active

theorem productions_mkB (tm : Machine) (a : Nat) (ha : a < tm.numSymbols) :
    (cmTagSystem tm).productions (mkB a ha (tm := tm)) = cmBProd tm a ha := by
  show (match cmKind (mkB a ha (tm := tm)) with
        | .A q' a' hq2 hq'2 ha2 =>
            if h : (tm.transition q' a').nextState = 0 then
              ([] : List (Fin (cmSize tm)))
            else cmAActive tm q' a' hq2 hq'2 ha2 h
        | .B  a ha => cmBProd  tm a ha
        | .BP a ha => cmBPProd tm a ha
        | .C  a ha => cmCProd  tm a ha
        | .CP a ha => cmCPProd tm a ha
        | .S       => cmSProd  tm) = cmBProd tm a ha
  rw [cmKind_mkB]

theorem productions_mkBP (tm : Machine) (a : Nat) (ha : a < tm.numSymbols) :
    (cmTagSystem tm).productions (mkBP a ha (tm := tm)) = cmBPProd tm a ha := by
  show (match cmKind (mkBP a ha (tm := tm)) with
        | .A q' a' hq2 hq'2 ha2 =>
            if h : (tm.transition q' a').nextState = 0 then
              ([] : List (Fin (cmSize tm)))
            else cmAActive tm q' a' hq2 hq'2 ha2 h
        | .B  a ha => cmBProd  tm a ha
        | .BP a ha => cmBPProd tm a ha
        | .C  a ha => cmCProd  tm a ha
        | .CP a ha => cmCPProd tm a ha
        | .S       => cmSProd  tm) = cmBPProd tm a ha
  rw [cmKind_mkBP]

theorem productions_mkC (tm : Machine) (a : Nat) (ha : a < tm.numSymbols) :
    (cmTagSystem tm).productions (mkC a ha (tm := tm)) = cmCProd tm a ha := by
  show (match cmKind (mkC a ha (tm := tm)) with
        | .A q' a' hq2 hq'2 ha2 =>
            if h : (tm.transition q' a').nextState = 0 then
              ([] : List (Fin (cmSize tm)))
            else cmAActive tm q' a' hq2 hq'2 ha2 h
        | .B  a ha => cmBProd  tm a ha
        | .BP a ha => cmBPProd tm a ha
        | .C  a ha => cmCProd  tm a ha
        | .CP a ha => cmCPProd tm a ha
        | .S       => cmSProd  tm) = cmCProd tm a ha
  rw [cmKind_mkC]

theorem productions_mkCP (tm : Machine) (a : Nat) (ha : a < tm.numSymbols) :
    (cmTagSystem tm).productions (mkCP a ha (tm := tm)) = cmCPProd tm a ha := by
  show (match cmKind (mkCP a ha (tm := tm)) with
        | .A q' a' hq2 hq'2 ha2 =>
            if h : (tm.transition q' a').nextState = 0 then
              ([] : List (Fin (cmSize tm)))
            else cmAActive tm q' a' hq2 hq'2 ha2 h
        | .B  a ha => cmBProd  tm a ha
        | .BP a ha => cmBPProd tm a ha
        | .C  a ha => cmCProd  tm a ha
        | .CP a ha => cmCPProd tm a ha
        | .S       => cmSProd  tm) = cmCPProd tm a ha
  rw [cmKind_mkCP]

theorem productions_mkS (tm : Machine) :
    (cmTagSystem tm).productions (mkS tm) = cmSProd tm := by
  show (match cmKind (mkS tm) with
        | .A q' a' hq2 hq'2 ha2 =>
            if h : (tm.transition q' a').nextState = 0 then
              ([] : List (Fin (cmSize tm)))
            else cmAActive tm q' a' hq2 hq'2 ha2 h
        | .B  a ha => cmBProd  tm a ha
        | .BP a ha => cmBPProd tm a ha
        | .C  a ha => cmCProd  tm a ha
        | .CP a ha => cmCPProd tm a ha
        | .S       => cmSProd  tm) = cmSProd tm
  rw [cmKind_mkS]

-- ============================================================================
-- Single-step lemmas: what `Tag.step` returns when the head is class X
-- ============================================================================

theorem step_mkA_halt (tm : Machine) (q a : Nat)
    (hq : 1 ≤ q) (hq' : q ≤ tm.numStates) (ha : a < tm.numSymbols)
    (h_halt : (tm.transition q a).nextState = 0)
    (b : Fin (cmSize tm)) (rest : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkA q a hq hq' ha (tm := tm) :: b :: rest)
      = some rest := by
  show some (rest ++ (cmTagSystem tm).productions (mkA q a hq hq' ha (tm := tm)))
        = some rest
  rw [productions_mkA_halt tm q a hq hq' ha h_halt, List.append_nil]

theorem step_mkA_active (tm : Machine) (q a : Nat)
    (hq : 1 ≤ q) (hq' : q ≤ tm.numStates) (ha : a < tm.numSymbols)
    (h_active : (tm.transition q a).nextState ≠ 0)
    (b : Fin (cmSize tm)) (rest : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkA q a hq hq' ha (tm := tm) :: b :: rest)
      = some (rest ++ cmAActive tm q a hq hq' ha h_active) := by
  show some (rest ++ (cmTagSystem tm).productions (mkA q a hq hq' ha (tm := tm)))
        = some (rest ++ cmAActive tm q a hq hq' ha h_active)
  rw [productions_mkA_active tm q a hq hq' ha h_active]

theorem step_mkB (tm : Machine) (a : Nat) (ha : a < tm.numSymbols)
    (b : Fin (cmSize tm)) (rest : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkB a ha (tm := tm) :: b :: rest)
      = some (rest ++ cmBProd tm a ha) := by
  show some (rest ++ (cmTagSystem tm).productions (mkB a ha (tm := tm)))
        = some (rest ++ cmBProd tm a ha)
  rw [productions_mkB tm a ha]

theorem step_mkBP (tm : Machine) (a : Nat) (ha : a < tm.numSymbols)
    (b : Fin (cmSize tm)) (rest : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkBP a ha (tm := tm) :: b :: rest)
      = some (rest ++ cmBPProd tm a ha) := by
  show some (rest ++ (cmTagSystem tm).productions (mkBP a ha (tm := tm)))
        = some (rest ++ cmBPProd tm a ha)
  rw [productions_mkBP tm a ha]

theorem step_mkC (tm : Machine) (a : Nat) (ha : a < tm.numSymbols)
    (b : Fin (cmSize tm)) (rest : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkC a ha (tm := tm) :: b :: rest)
      = some (rest ++ cmCProd tm a ha) := by
  show some (rest ++ (cmTagSystem tm).productions (mkC a ha (tm := tm)))
        = some (rest ++ cmCProd tm a ha)
  rw [productions_mkC tm a ha]

theorem step_mkCP (tm : Machine) (a : Nat) (ha : a < tm.numSymbols)
    (b : Fin (cmSize tm)) (rest : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkCP a ha (tm := tm) :: b :: rest)
      = some (rest ++ cmCPProd tm a ha) := by
  show some (rest ++ (cmTagSystem tm).productions (mkCP a ha (tm := tm)))
        = some (rest ++ cmCPProd tm a ha)
  rw [productions_mkCP tm a ha]

theorem step_mkS (tm : Machine)
    (b : Fin (cmSize tm)) (rest : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkS tm :: b :: rest)
      = some (rest ++ cmSProd tm) := by
  show some (rest ++ (cmTagSystem tm).productions (mkS tm))
        = some (rest ++ cmSProd tm)
  rw [productions_mkS tm]

-- ============================================================================
-- Length changes: how each step_mkX shifts word length
-- ============================================================================

theorem step_mkA_halt_length (tm : Machine) (q a : Nat)
    (hq : 1 ≤ q) (hq' : q ≤ tm.numStates) (ha : a < tm.numSymbols)
    (h_halt : (tm.transition q a).nextState = 0)
    (b : Fin (cmSize tm)) (rest result : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkA q a hq hq' ha (tm := tm) :: b :: rest) = some result →
    result.length + 2 = (mkA q a hq hq' ha (tm := tm) :: b :: rest).length := by
  intro h
  rw [step_mkA_halt tm q a hq hq' ha h_halt b rest] at h
  injection h with h_eq
  subst h_eq
  simp

theorem step_mkB_length (tm : Machine) (a : Nat) (ha : a < tm.numSymbols)
    (b : Fin (cmSize tm)) (rest result : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkB a ha (tm := tm) :: b :: rest) = some result →
    result.length + 1 = (mkB a ha (tm := tm) :: b :: rest).length := by
  intro h
  rw [step_mkB tm a ha b rest] at h
  injection h with h_eq
  subst h_eq
  simp [List.length_append, cmBProd_length]

theorem step_mkBP_length (tm : Machine) (a : Nat) (ha : a < tm.numSymbols)
    (b : Fin (cmSize tm)) (rest result : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkBP a ha (tm := tm) :: b :: rest) = some result →
    result.length + 1 = (mkBP a ha (tm := tm) :: b :: rest).length := by
  intro h
  rw [step_mkBP tm a ha b rest] at h
  injection h with h_eq
  subst h_eq
  simp [List.length_append, cmBPProd_length]

theorem step_mkC_length (tm : Machine) (a : Nat) (ha : a < tm.numSymbols)
    (b : Fin (cmSize tm)) (rest result : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkC a ha (tm := tm) :: b :: rest) = some result →
    result.length + 1 = (mkC a ha (tm := tm) :: b :: rest).length := by
  intro h
  rw [step_mkC tm a ha b rest] at h
  injection h with h_eq
  subst h_eq
  simp [List.length_append, cmCProd_length]

theorem step_mkCP_length (tm : Machine) (a : Nat) (ha : a < tm.numSymbols)
    (b : Fin (cmSize tm)) (rest result : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkCP a ha (tm := tm) :: b :: rest) = some result →
    result.length + 1 = (mkCP a ha (tm := tm) :: b :: rest).length := by
  intro h
  rw [step_mkCP tm a ha b rest] at h
  injection h with h_eq
  subst h_eq
  simp [List.length_append, cmCPProd_length]

theorem step_mkS_length (tm : Machine)
    (b : Fin (cmSize tm)) (rest result : List (Fin (cmSize tm))) :
    (cmTagSystem tm).step (mkS tm :: b :: rest) = some result →
    result.length + 1 = (mkS tm :: b :: rest).length := by
  intro h
  rw [step_mkS tm b rest] at h
  injection h with h_eq
  subst h_eq
  simp [List.length_append, cmSProd_length]

/-- Recursive encoder for the right tape: alternating B/B' markers,
    starting from B (parity = false). -/
def encodeRightCells (tm : Machine) (hk : 0 < tm.numSymbols) :
    Bool → List Nat → List (Fin (cmSize tm))
  | _, [] => []
  | false, v :: rest =>
      mkB (v % tm.numSymbols) (Nat.mod_lt _ hk) (tm := tm)
        :: encodeRightCells tm hk true rest
  | true, v :: rest =>
      mkBP (v % tm.numSymbols) (Nat.mod_lt _ hk) (tm := tm)
        :: encodeRightCells tm hk false rest

/-- Recursive encoder for the left tape: alternating C/C' markers,
    starting from C (parity = false). -/
def encodeLeftCells (tm : Machine) (hk : 0 < tm.numSymbols) :
    Bool → List Nat → List (Fin (cmSize tm))
  | _, [] => []
  | false, v :: rest =>
      mkC (v % tm.numSymbols) (Nat.mod_lt _ hk) (tm := tm)
        :: encodeLeftCells tm hk true rest
  | true, v :: rest =>
      mkCP (v % tm.numSymbols) (Nat.mod_lt _ hk) (tm := tm)
        :: encodeLeftCells tm hk false rest

/-- Encoding of a TM configuration into the tag-system data word:
      `A(q, h) · B(r₀) · B'(r₁) · B(r₂) · ... · S · C(l₀) · C'(l₁) · ...`
    Halted state (`state = 0`) and degenerate alphabet (`numSymbols = 0`)
    both produce the empty word, so `HaltsEmpty` follows automatically. -/
def cmEncode (tm : Machine) (cfg : Config) : TagConfig (cmSize tm) :=
  if hk : 0 < tm.numSymbols then
    if hq : 1 ≤ cfg.state ∧ cfg.state ≤ tm.numStates then
      let head_sym := mkA cfg.state (cfg.head % tm.numSymbols)
        hq.1 hq.2 (Nat.mod_lt _ hk) (tm := tm)
      [head_sym]
        ++ encodeRightCells tm hk false cfg.right
        ++ [mkS tm]
        ++ encodeLeftCells tm hk false cfg.left
    else
      []
  else
    []

-- ============================================================================
-- Halting correspondence (will become trivial once cmEncode handles halt)
-- ============================================================================

-- ============================================================================
-- Structural lemmas about the encoding (infrastructure for `cmStep_sim`)
-- ============================================================================

/-- `encodeRightCells` preserves length. -/
theorem encodeRightCells_length (tm : Machine) (hk : 0 < tm.numSymbols) :
    ∀ (parity : Bool) (l : List Nat),
      (encodeRightCells tm hk parity l).length = l.length
  | _, [] => rfl
  | false, _ :: rest => by
      simp [encodeRightCells, encodeRightCells_length tm hk true rest]
  | true, _ :: rest => by
      simp [encodeRightCells, encodeRightCells_length tm hk false rest]

/-- `encodeLeftCells` preserves length. -/
theorem encodeLeftCells_length (tm : Machine) (hk : 0 < tm.numSymbols) :
    ∀ (parity : Bool) (l : List Nat),
      (encodeLeftCells tm hk parity l).length = l.length
  | _, [] => rfl
  | false, _ :: rest => by
      simp [encodeLeftCells, encodeLeftCells_length tm hk true rest]
  | true, _ :: rest => by
      simp [encodeLeftCells, encodeLeftCells_length tm hk false rest]

/-- Structural unfolding of `cmEncode` for an *active* config (state in
    `[1, numStates]`, alphabet non-empty). -/
theorem cmEncode_active (tm : Machine) (cfg : Config)
    (hk : 0 < tm.numSymbols) (hq : 1 ≤ cfg.state ∧ cfg.state ≤ tm.numStates) :
    cmEncode tm cfg =
      [mkA cfg.state (cfg.head % tm.numSymbols)
        hq.1 hq.2 (Nat.mod_lt _ hk) (tm := tm)]
      ++ encodeRightCells tm hk false cfg.right
      ++ [mkS tm]
      ++ encodeLeftCells tm hk false cfg.left := by
  unfold cmEncode
  rw [dif_pos hk, dif_pos hq]

/-- **`cmEncode_halt_state_eq_nil` (iter 644)**: a halted cfg
    (`cfg.state = 0`) encodes to the empty tag word.  Falls out of
    `cmEncode`'s guard chain since `1 ≤ 0` is false. -/
theorem cmEncode_halt_state_eq_nil (tm : Machine) (cfg : Config)
    (h : cfg.state = 0) :
    cmEncode tm cfg = [] := by
  unfold cmEncode
  by_cases hk : 0 < tm.numSymbols
  · rw [dif_pos hk]
    have h_not : ¬ (1 ≤ cfg.state ∧ cfg.state ≤ tm.numStates) := by
      intro ⟨h_ge, _⟩; rw [h] at h_ge; omega
    rw [dif_neg h_not]
  · rw [dif_neg hk]

/-- **`cmEncode_zero_numSymbols_eq_nil` (iter 644)**: degenerate
    alphabet (`tm.numSymbols = 0`) also yields the empty tag word. -/
theorem cmEncode_zero_numSymbols_eq_nil (tm : Machine) (cfg : Config)
    (h : tm.numSymbols = 0) :
    cmEncode tm cfg = [] := by
  unfold cmEncode
  rw [dif_neg (by rw [h]; exact Nat.lt_irrefl 0)]

/-- Length of the encoded word for an active config:
    `2 + |right| + |left|` (the `2` accounts for the leading `A` and the
    middle `S`). -/
theorem cmEncode_length (tm : Machine) (cfg : Config)
    (hk : 0 < tm.numSymbols) (hq : 1 ≤ cfg.state ∧ cfg.state ≤ tm.numStates) :
    (cmEncode tm cfg).length = 2 + cfg.right.length + cfg.left.length := by
  rw [cmEncode_active tm cfg hk hq]
  simp [encodeRightCells_length, encodeLeftCells_length]
  omega

/-- Active configs have encoded length ≥ 2 (so the tag system can always
    take at least one step). -/
theorem cmEncode_length_ge_two_active (tm : Machine) (cfg : Config)
    (hk : 0 < tm.numSymbols) (hq : 1 ≤ cfg.state ∧ cfg.state ≤ tm.numStates) :
    (cmEncode tm cfg).length ≥ 2 := by
  rw [cmEncode_length tm cfg hk hq]
  omega

/-- Uniform upper bound on encoded length — holds for any cfg. -/
theorem cmEncode_length_le (tm : Machine) (cfg : Config) :
    (cmEncode tm cfg).length ≤ 2 + cfg.right.length + cfg.left.length := by
  unfold cmEncode
  by_cases hk : 0 < tm.numSymbols
  · rw [dif_pos hk]
    by_cases hq : 1 ≤ cfg.state ∧ cfg.state ≤ tm.numStates
    · rw [dif_pos hq]
      simp [encodeRightCells_length, encodeLeftCells_length]
      omega
    · rw [dif_neg hq]; simp
  · rw [dif_neg hk]; simp

/-- A successful tag-step changes word length by `-2 + |production|`.
    Stated additively so we never traffic in `Nat` subtraction. -/
theorem Tag.step_length_eq {k : Nat} (ts : Tag k)
    (a b : Fin k) (rest : List (Fin k)) (cfg' : TagConfig k)
    (h_step : ts.step (a :: b :: rest) = some cfg') :
    cfg'.length + 2 = (a :: b :: rest).length + (ts.productions a).length := by
  simp [Tag.step] at h_step
  subst h_step
  simp [List.length_append]
  omega

/-- For an empty-tape active config, the encoded word is exactly `[A, S]`. -/
theorem cmEncode_empty_tape (tm : Machine) (cfg : Config)
    (hk : 0 < tm.numSymbols)
    (hq : 1 ≤ cfg.state ∧ cfg.state ≤ tm.numStates)
    (h_right : cfg.right = []) (h_left : cfg.left = []) :
    cmEncode tm cfg
      = [mkA cfg.state (cfg.head % tm.numSymbols)
            hq.1 hq.2 (Nat.mod_lt _ hk) (tm := tm),
         mkS tm] := by
  rw [cmEncode_active tm cfg hk hq, h_right, h_left]
  simp [encodeRightCells, encodeLeftCells]

/-- For a config with right tape `[r0]` and empty left tape:
    encoded word is `[A, B(r0%k), S]`. -/
theorem cmEncode_singleton_right (tm : Machine) (cfg : Config)
    (hk : 0 < tm.numSymbols)
    (hq : 1 ≤ cfg.state ∧ cfg.state ≤ tm.numStates)
    (r0 : Nat) (h_right : cfg.right = [r0]) (h_left : cfg.left = []) :
    cmEncode tm cfg
      = [mkA cfg.state (cfg.head % tm.numSymbols)
            hq.1 hq.2 (Nat.mod_lt _ hk) (tm := tm),
         mkB (r0 % tm.numSymbols) (Nat.mod_lt _ hk) (tm := tm),
         mkS tm] := by
  rw [cmEncode_active tm cfg hk hq, h_right, h_left]
  simp [encodeRightCells, encodeLeftCells]

/-- For a config with empty right tape and left tape `[l0]`:
    encoded word is `[A, S, C(l0%k)]`. -/
theorem cmEncode_singleton_left (tm : Machine) (cfg : Config)
    (hk : 0 < tm.numSymbols)
    (hq : 1 ≤ cfg.state ∧ cfg.state ≤ tm.numStates)
    (l0 : Nat) (h_right : cfg.right = []) (h_left : cfg.left = [l0]) :
    cmEncode tm cfg
      = [mkA cfg.state (cfg.head % tm.numSymbols)
            hq.1 hq.2 (Nat.mod_lt _ hk) (tm := tm),
         mkS tm,
         mkC (l0 % tm.numSymbols) (Nat.mod_lt _ hk) (tm := tm)] := by
  rw [cmEncode_active tm cfg hk hq, h_right, h_left]
  simp [encodeRightCells, encodeLeftCells]

/-- More general: any cfg with state outside `[1, numStates]` encodes to `[]`. -/
theorem cmEncode_state_invalid_is_nil (tm : Machine) (cfg : Config)
    (h : ¬ (1 ≤ cfg.state ∧ cfg.state ≤ tm.numStates)) :
    cmEncode tm cfg = [] := by
  unfold cmEncode
  by_cases hk : 0 < tm.numSymbols
  · rw [dif_pos hk, dif_neg h]
  · rw [dif_neg hk]

/-- TM halt ⟹ encoded word is empty.  Halted means `state = 0`, which
    fails the `1 ≤ state` guard inside `cmEncode`. -/
theorem cmEncode_halted (tm : Machine) (cfg : Config) :
    halted cfg = true → cmEncode tm cfg = [] := by
  intro h_halt
  have h_state : cfg.state = 0 := by
    simp [halted] at h_halt; exact h_halt
  exact cmEncode_state_invalid_is_nil tm cfg (by intro ⟨h1, _⟩; omega)

/-- The simulation lemma for the *empty-tape halt sub-case*: when the
    TM is about to halt (`δ(state, head).nextState = 0`) on a
    configuration with empty left/right tape and a valid head value,
    one tag step on the encoding reaches the empty word — which is
    exactly `cmEncode tm cfg'` since `cfg'` has state 0. -/
theorem cmStep_sim_empty_halt (tm : Machine) (cfg cfg' : Config)
    (hk : 0 < tm.numSymbols)
    (hq : 1 ≤ cfg.state ∧ cfg.state ≤ tm.numStates)
    (h_head : cfg.head < tm.numSymbols)
    (h_right : cfg.right = []) (h_left : cfg.left = [])
    (h_halt : (tm.transition cfg.state cfg.head).nextState = 0)
    (h_step : step tm cfg = some cfg') :
    tagNSteps (cmTagSystem tm) (cmEncode tm cfg) 1
      = some (cmEncode tm cfg') := by
  have h_cfg'_state : cfg'.state = 0 := by
    rw [step_active_state tm cfg cfg' h_step]
    exact h_halt
  have h_cfg'_enc : cmEncode tm cfg' = [] :=
    cmEncode_halted tm cfg' (by simp [halted, h_cfg'_state])
  have h_head_mod : cfg.head % tm.numSymbols = cfg.head :=
    Nat.mod_eq_of_lt h_head
  have h_halt_mod :
      (tm.transition cfg.state (cfg.head % tm.numSymbols)).nextState = 0 := by
    rw [h_head_mod]; exact h_halt
  rw [tagNSteps_one, cmEncode_empty_tape tm cfg hk hq h_right h_left, h_cfg'_enc]
  exact step_mkA_halt tm cfg.state (cfg.head % tm.numSymbols)
    hq.1 hq.2 (Nat.mod_lt _ hk) h_halt_mod (mkS tm) []

-- ============================================================================
-- Step simulation property (the heart of Cocke-Minsky)
-- ============================================================================

/-- One TM step is simulated by some bounded number of tag steps.

    Structure of the proof:
    - Vacuous case (`cfg.state = 0`): `step` returns `none`, contradicting `h`.
    - Active case (`cfg.state ≠ 0`): the heart of the simulation —
      currently SORRY[step-sim-active] because the present 5k+1-symbol
      alphabet/production design isn't faithful (see iter-11 caveat). -/
theorem cmStep_sim (tm : Machine) (cfg cfg' : Config)
    (h : step tm cfg = some cfg') :
    ∃ n, tagNSteps (cmTagSystem tm) (cmEncode tm cfg) n
          = some (cmEncode tm cfg') := by
  by_cases h_halt : cfg.state = 0
  · -- Vacuous: `step` of a halted config returns `none`.
    exfalso
    have h_step_none : step tm cfg = none := by
      unfold step
      have : (cfg.state == 0) = true := by simp [h_halt]
      simp [this]
    rw [h_step_none] at h
    cases h
  · -- SORRY[step-sim-active]: real simulation requires faithful productions.
    -- The current `s·k + 4k + 1` alphabet (A/B/B'/C/C'/S) cannot
    -- encode the multi-pass sweep that Cocke-Minsky 1964 needs.
    --
    -- Reference: Minsky 1967, *Computation: Finite and Infinite
    -- Machines*, Ch. 14, Theorem 14.6-1.  Minsky's construction
    -- simulates one TM step with multiple 2-tag passes that:
    --   1. Locate the head's neighborhood via marker symbols.
    --   2. Apply the TM transition (state, symbol → state', symbol', dir).
    --   3. Shift the tape representation accordingly.
    --
    -- The current alphabet conflates pass phases with cell markers.
    -- Faithful closure requires either:
    --   (a) Adding per-state-symbol phase markers (alphabet grows to
    --       `s·k·p + 4k + 1` for `p` phases per transition), and
    --       redesigning `cmAActive`/`cmBProd`/etc. to emit phase-
    --       specific productions per Minsky 1967 §14.6.
    --   (b) Using the simpler Wang 1957 / Hooper 1966 reduction to
    --       2-counter machines, then 2-counter → 2-tag, but that
    --       requires defining a counter machine intermediate.
    --
    -- Either path is multi-iteration research work.  Note: the
    -- WEAK predicate `CockeMinskyReduces` (in CockeMinsky.lean) is
    -- already trivially closed via `fun _ => []` — see iter-11
    -- caveat.  This sorry is for the FAITHFUL strengthening
    -- `CockeMinskyReducesFaithful`, which the current encoder cannot
    -- discharge.
    sorry

/-- TM halts ⟹ tag system reaches the empty word.
    Reduces to `cmStep_sim` plus `cmEncode_halted` by induction on fuel. -/
theorem cmHaltsEmpty (tm : Machine) (cfg : Config) :
    Halts tm cfg → (cmTagSystem tm).HaltsEmpty (cmEncode tm cfg) := by
  intro ⟨fuel, result, h_eval⟩
  have h_th : tagHalted ([] : TagConfig (cmSize tm)) = true := by rfl
  induction fuel generalizing cfg with
  | zero =>
    dsimp [eval] at h_eval
    split at h_eval
    · rename_i h_halt
      injection h_eval with h_eq; subst h_eq
      exact ⟨0, by simp [Tag.eval, h_th, cmEncode_halted tm cfg h_halt]⟩
    · contradiction
  | succ fuel ih =>
    dsimp [eval] at h_eval
    split at h_eval
    · rename_i h_halt
      injection h_eval with h_eq; subst h_eq
      exact ⟨0, by simp [Tag.eval, h_th, cmEncode_halted tm cfg h_halt]⟩
    · rename_i h_not_halt
      cases h_step : step tm cfg with
      | none =>
        -- `step = none` happens only at halted configs; contradicts h_not_halt
        have h_step_false : step tm cfg ≠ none := by
          intro h
          have h_f : (cfg.state == 0) = false := by
            cases h_t : cfg.state == 0 <;> simp_all [halted]
          dsimp [step, halted] at h
          simp [h_f] at h
          split at h <;> contradiction
        contradiction
      | some cfg' =>
        rw [h_step] at h_eval
        have ⟨n, hn⟩ := cmStep_sim tm cfg cfg' h_step
        exact tag_haltsEmpty_after_nSteps (cmTagSystem tm) _ _ n hn (ih cfg' h_eval)

-- ============================================================================
-- The packaged reduction (target: replace the axiom in CockeMinsky.lean)
-- ============================================================================

/-- Concrete witness for `CockeMinskyReduces tm` via the (provisional)
    Cocke-Minsky-style construction.  Depends on `cmStep_sim`, which
    is currently `sorry` for the active case (alphabet redesign needed).
    Provided here for documentation / future use. -/
theorem cocke_minsky_reduces_concrete (tm : Machine) :
    CockeMinskyReduces tm :=
  ⟨cmSize tm, cmSize_pos tm, cmTagSystem tm, cmEncode tm,
    fun cfg h => cmHaltsEmpty tm cfg h⟩

-- ============================================================================
-- Strengthened predicate (resists the trivial encoding)
-- ============================================================================

/-- **Faithful** Cocke-Minsky reduction.  Strengthens the weak
    `CockeMinskyReduces` (which the trivial `encode := fun _ => []`
    discharges) with two extra demands:

    1. **Halted-encodes-empty**: halted configs encode to `[]`.
    2. **Step simulation**: every TM step is mirrored by a non-trivial
       (n ≥ 1) tag-system computation that reaches the encoded next config.

    The trivial halt-collapse encoder *fails* this predicate because it
    cannot satisfy the step-simulation clause for TMs that take more than
    one non-halt step (the tag system can only "leave" a fixed value once,
    not return to it). -/
def CockeMinskyReducesFaithful (tm : Machine) : Prop :=
  ∃ (k : Nat) (_ : k > 0) (ts : Tag k) (encode : Config → TagConfig k),
    (∀ cfg, halted cfg = true → encode cfg = []) ∧
    (∀ cfg cfg', step tm cfg = some cfg' →
      ∃ n, n ≥ 1 ∧ tagNSteps ts (encode cfg) n = some (encode cfg'))

/-- The faithful predicate implies the weak one: if every step is
    simulated and halted configs encode to `[]`, then by induction on
    fuel, halting TMs encode to halt-empty tag words. -/
theorem CockeMinskyReducesFaithful_implies_weak (tm : Machine)
    (h : CockeMinskyReducesFaithful tm) : CockeMinskyReduces tm := by
  obtain ⟨k, hk, ts, encode, h_halt, h_step⟩ := h
  refine ⟨k, hk, ts, encode, ?_⟩
  intro cfg ⟨fuel, result, h_eval⟩
  induction fuel generalizing cfg with
  | zero =>
    dsimp [eval] at h_eval
    split at h_eval
    · rename_i h_h
      injection h_eval with h_eq; subst h_eq
      have h_enc : encode cfg = [] := h_halt cfg h_h
      exact ⟨0, by simp [Tag.eval, tagHalted, h_enc]⟩
    · contradiction
  | succ fuel ih =>
    dsimp [eval] at h_eval
    split at h_eval
    · rename_i h_h
      injection h_eval with h_eq; subst h_eq
      have h_enc : encode cfg = [] := h_halt cfg h_h
      exact ⟨0, by simp [Tag.eval, tagHalted, h_enc]⟩
    · rename_i h_nh
      cases h_step_eq : step tm cfg with
      | none =>
        rw [h_step_eq] at h_eval
        injection h_eval with h_eq; subst h_eq
        -- not halted but step returns none: contradiction via step_none_iff_halted
        have : cfg.state = 0 := (step_none_iff_halted tm cfg).mp h_step_eq
        simp [halted, this] at h_nh
      | some cfg' =>
        rw [h_step_eq] at h_eval
        obtain ⟨n, _, hn⟩ := h_step cfg cfg' h_step_eq
        exact tag_haltsEmpty_after_nSteps ts (encode cfg) (encode cfg') n hn
                (ih cfg' h_eval)

-- (Iter 132) The forward-declared `cocke_minsky_reduces_faithful` stub
-- and its consumer `cocke_minsky_reduces_via_faithful` were removed in
-- favour of the meaningful `cocke_minsky_reduces_faithful_universal`
-- (iter 105) and `cocke_minsky_reduces_via_universal` defined later in
-- this file.  Eliminating the stub eliminates the only sorry whose sole
-- justification was forward-reference ordering.

/-- **Faithful Cocke-Minsky for any TM that halts in one step from
    every active state**.  Encoder: halted → `[]`, active → `[a, a]`
    (a = `⟨0, _⟩ : Fin 1`).  Productions: `a → []`.  One tag step on
    `[a, a]` yields `[]`, matching the encoding of the post-step
    (halted) config.  Generalizes the trivialHaltTM and similar
    bespoke proofs to arbitrary alphabets/states. -/
theorem cocke_minsky_reduces_faithful_of_immediate_halt (tm : Machine)
    (h_imm : ∀ q s, q ≥ 1 → (tm.transition q s).nextState = 0) :
    CockeMinskyReducesFaithful tm := by
  refine ⟨1, Nat.one_pos, { productions := fun _ => [] },
          fun cfg => if halted cfg then ([] : TagConfig 1)
                     else [⟨0, Nat.one_pos⟩, ⟨0, Nat.one_pos⟩], ?_, ?_⟩
  · intro cfg h_halt
    simp [h_halt]
  · intro cfg cfg' h_step
    have h_active : cfg.state ≠ 0 := by
      intro h_z
      have h_n : step tm cfg = none := (step_none_iff_halted _ _).mpr h_z
      rw [h_n] at h_step; cases h_step
    have h_pos : 1 ≤ cfg.state := by omega
    have h_cfg'_s : cfg'.state = 0 := by
      rw [step_active_state tm cfg cfg' h_step]
      exact h_imm cfg.state cfg.head h_pos
    have h_cfg'_halt : halted cfg' = true := by simp [halted, h_cfg'_s]
    have h_active' : ¬ halted cfg = true := by
      intro h_h
      have : cfg.state = 0 := by simp [halted] at h_h; exact h_h
      exact h_active this
    refine ⟨1, Nat.le_refl _, ?_⟩
    simp [h_active', h_cfg'_halt, tagNSteps, Tag.step]

/-- **Faithful Cocke-Minsky for any TM that halts in at most two steps from
    every active state**.  Generalises `_of_immediate_halt`: the precondition
    only requires that any state reachable in one TM step from an active config
    halts immediately on every symbol (or that the original step itself halts).

    Encoder uses alphabet `Fin 1` (singleton `a := ⟨0, _⟩`):
    * halted → `[]`
    * active with immediate-halt transition → `[a, a]`
    * active without immediate-halt transition → `[a, a, a, a]`

    Productions: `a → []` (so each tag step removes the leading two-element block).

    Step coverage:
    * cfg one-step-halt → cfg' halted: tag step on `[a,a]` ⇒ `[]`. ✓
    * cfg two-step-halt → cfg' one-step-halt: tag step on `[a,a,a,a]` ⇒ `[a,a]`. ✓ -/
theorem cocke_minsky_reduces_faithful_of_two_step_halt (tm : Machine)
    (h_two : ∀ q s, q ≥ 1 →
      (tm.transition q s).nextState = 0 ∨
      ∀ s', (tm.transition (tm.transition q s).nextState s').nextState = 0) :
    CockeMinskyReducesFaithful tm := by
  let a : Fin 1 := ⟨0, Nat.one_pos⟩
  refine ⟨1, Nat.one_pos, { productions := fun _ => [] },
          fun cfg =>
            if halted cfg then ([] : TagConfig 1)
            else if (tm.transition cfg.state cfg.head).nextState = 0 then [a, a]
            else [a, a, a, a],
          ?_, ?_⟩
  · -- halted-encodes-empty clause
    intro cfg h_halt
    simp [h_halt]
  · -- step-simulation clause
    intro cfg cfg' h_step
    have h_active : cfg.state ≠ 0 := by
      intro h_z
      have h_n : step tm cfg = none := (step_none_iff_halted _ _).mpr h_z
      rw [h_n] at h_step; cases h_step
    have h_pos : 1 ≤ cfg.state := by omega
    have h_active' : ¬ halted cfg = true := by
      intro h_h
      have : cfg.state = 0 := by simp [halted] at h_h; exact h_h
      exact h_active this
    have h_cfg'_state : cfg'.state = (tm.transition cfg.state cfg.head).nextState :=
      step_active_state tm cfg cfg' h_step
    by_cases h_imm : (tm.transition cfg.state cfg.head).nextState = 0
    · -- Case A: immediate halt — encode cfg = [a, a], step yields []
      have h_cfg'_halt : halted cfg' = true := by
        simp [halted, h_cfg'_state, h_imm]
      refine ⟨1, Nat.le_refl _, ?_⟩
      -- LHS: tagNSteps on [a, a] gives []
      -- RHS: encode cfg' = [] (via h_cfg'_halt)
      simp [h_active', h_imm, h_cfg'_halt, tagNSteps, Tag.step]
    · -- Case B: cfg' is one-step-halt active.  encode cfg = [a,a,a,a], step → [a,a]
      have h_two_apply := h_two cfg.state cfg.head h_pos
      have h_cfg'_imm : ∀ s', (tm.transition cfg'.state s').nextState = 0 := by
        cases h_two_apply with
        | inl h => exact absurd h h_imm
        | inr h =>
          intro s'
          rw [h_cfg'_state]
          exact h s'
      have h_cfg'_active : cfg'.state ≠ 0 := by
        rw [h_cfg'_state]; exact h_imm
      have h_cfg'_active' : ¬ halted cfg' = true := by
        simp [halted, h_cfg'_active]
      have h_cfg'_imm_head : (tm.transition cfg'.state cfg'.head).nextState = 0 :=
        h_cfg'_imm cfg'.head
      refine ⟨1, Nat.le_refl _, ?_⟩
      -- LHS: tagNSteps on [a,a,a,a] gives [a,a]
      -- RHS: encode cfg' = [a, a] (via h_cfg'_active' ∧ h_cfg'_imm_head)
      simp [h_active', h_imm, h_cfg'_active', h_cfg'_imm_head,
            tagNSteps, Tag.step]

/-- **Faithful Cocke-Minsky for any TM admitting a depth function** that
    weakly decreases by exactly 1 per step.  This subsumes
    `_of_immediate_halt` and `_of_two_step_halt`: any concrete bound
    on halting depth gives a witness for `depth`.

    Encoder: alphabet `Fin 1` (singleton `a`); for each cfg, encode it as
    `List.replicate (2 * depth cfg) a`.  Productions: `a → []`.

    Step coverage: `step tm cfg = some cfg'` ⟹ `depth cfg = depth cfg' + 1`,
    so `encode cfg = a :: a :: encode cfg'` and one tag step pops the two
    leading `a`s, leaving exactly `encode cfg'`.

    Halted-encodes-empty follows from `depth cfg = 0` for halted cfgs. -/
theorem cocke_minsky_reduces_faithful_of_depth_decreasing (tm : Machine)
    (depth : Config → Nat)
    (h_halt_depth : ∀ cfg, halted cfg = true → depth cfg = 0)
    (h_step_depth : ∀ cfg cfg', step tm cfg = some cfg' →
      depth cfg = depth cfg' + 1) :
    CockeMinskyReducesFaithful tm := by
  let a : Fin 1 := ⟨0, Nat.one_pos⟩
  refine ⟨1, Nat.one_pos, { productions := fun _ => [] },
          fun cfg => List.replicate (2 * depth cfg) a, ?_, ?_⟩
  · -- Halted ⇒ encode = [].
    intro cfg h_halt
    have : depth cfg = 0 := h_halt_depth cfg h_halt
    simp [this]
  · -- Step ⇒ one tag step suffices.
    intro cfg cfg' h_step
    have h_d : depth cfg = depth cfg' + 1 := h_step_depth cfg cfg' h_step
    refine ⟨1, Nat.le_refl _, ?_⟩
    -- Reduce to: tagNSteps on `List.replicate (2*(d+1)) a` = some (replicate (2*d) a).
    have h_size : 2 * depth cfg = 2 * depth cfg' + 2 := by
      rw [h_d, Nat.mul_add, Nat.mul_one]
    -- Show encode cfg = a :: a :: encode cfg'.
    have h_encode : List.replicate (2 * depth cfg) a
                  = a :: a :: List.replicate (2 * depth cfg') a := by
      rw [h_size]
      simp [List.replicate_succ]
    -- Now compute tag step.  Beta-reduce the encoder application first.
    show tagNSteps { productions := fun _ => [] } (List.replicate (2 * depth cfg) a) 1
        = some (List.replicate (2 * depth cfg') a)
    rw [h_encode, tagNSteps_one]
    show Tag.step _ (a :: a :: List.replicate (2 * depth cfg') a)
        = some (List.replicate (2 * depth cfg') a)
    simp [Tag.step]

/-- Re-derivation of `cocke_minsky_reduces_faithful_of_immediate_halt`
    via the parametric `_of_depth_decreasing`.  The depth function is the
    indicator `if halted cfg then 0 else 1`: every active step lands in
    halt by hypothesis, so depth drops from 1 to 0.  This validates the
    iter-96 abstraction (the original is kept for documentation; this
    primed variant demonstrates the pattern). -/
theorem cocke_minsky_reduces_faithful_of_immediate_halt' (tm : Machine)
    (h_imm : ∀ q s, q ≥ 1 → (tm.transition q s).nextState = 0) :
    CockeMinskyReducesFaithful tm := by
  apply cocke_minsky_reduces_faithful_of_depth_decreasing tm
    (fun cfg => if halted cfg then 0 else 1)
  · intro cfg h_halt; simp [h_halt]
  · intro cfg cfg' h_step
    -- cfg active ⇒ depth cfg = 1; cfg' halted (since transition halts) ⇒ depth cfg' = 0.
    have h_active : cfg.state ≠ 0 := by
      intro h_z
      have h_n : step tm cfg = none := (step_none_iff_halted _ _).mpr h_z
      rw [h_n] at h_step; cases h_step
    have h_pos : 1 ≤ cfg.state := by omega
    have h_active' : ¬ halted cfg = true := by
      intro h_h
      have : cfg.state = 0 := by simp [halted] at h_h; exact h_h
      exact h_active this
    have h_cfg'_state : cfg'.state = (tm.transition cfg.state cfg.head).nextState :=
      step_active_state tm cfg cfg' h_step
    have h_cfg'_halt : halted cfg' = true := by
      simp [halted, h_cfg'_state, h_imm cfg.state cfg.head h_pos]
    simp [h_active', h_cfg'_halt]

/-- Re-derivation of `cocke_minsky_reduces_faithful_of_two_step_halt`
    via the parametric `_of_depth_decreasing`.  The depth function:
    halted → 0, one-step-halt → 1, two-step-halt → 2.  Each TM step
    drops depth by exactly 1 by case analysis on the transition's
    `nextState`.  Validates iter-96's abstraction on the harder
    two-step-halt case. -/
theorem cocke_minsky_reduces_faithful_of_two_step_halt' (tm : Machine)
    (h_two : ∀ q s, q ≥ 1 →
      (tm.transition q s).nextState = 0 ∨
      ∀ s', (tm.transition (tm.transition q s).nextState s').nextState = 0) :
    CockeMinskyReducesFaithful tm := by
  -- Depth: halted → 0; active with immediate-halt next → 1; otherwise → 2.
  apply cocke_minsky_reduces_faithful_of_depth_decreasing tm
    (fun cfg =>
      if halted cfg then 0
      else if (tm.transition cfg.state cfg.head).nextState = 0 then 1
      else 2)
  · intro cfg h_halt; simp [h_halt]
  · intro cfg cfg' h_step
    have h_active : cfg.state ≠ 0 := by
      intro h_z
      have h_n : step tm cfg = none := (step_none_iff_halted _ _).mpr h_z
      rw [h_n] at h_step; cases h_step
    have h_pos : 1 ≤ cfg.state := by omega
    have h_active' : ¬ halted cfg = true := by
      intro h_h
      have : cfg.state = 0 := by simp [halted] at h_h; exact h_h
      exact h_active this
    have h_cfg'_state : cfg'.state = (tm.transition cfg.state cfg.head).nextState :=
      step_active_state tm cfg cfg' h_step
    by_cases h_imm : (tm.transition cfg.state cfg.head).nextState = 0
    · -- Case A: cfg.depth = 1, cfg' halted ⇒ cfg'.depth = 0.
      have h_cfg'_halt : halted cfg' = true := by
        simp [halted, h_cfg'_state, h_imm]
      simp [h_active', h_imm, h_cfg'_halt]
    · -- Case B: cfg.depth = 2, cfg' active with imm-halt next ⇒ cfg'.depth = 1.
      have h_cfg'_active : cfg'.state ≠ 0 := by
        rw [h_cfg'_state]; exact h_imm
      have h_cfg'_active' : ¬ halted cfg' = true := by
        simp [halted, h_cfg'_active]
      have h_two_apply := h_two cfg.state cfg.head h_pos
      have h_cfg'_imm : (tm.transition cfg'.state cfg'.head).nextState = 0 := by
        cases h_two_apply with
        | inl h => exact absurd h h_imm
        | inr h => rw [h_cfg'_state]; exact h cfg'.head
      simp [h_active', h_imm, h_cfg'_active', h_cfg'_imm]

/-- Helper: applying `n` tag steps to `[a, ..., a]` (length `2*D`) under the
    `productions ≡ []` rule pops `n` leading `[a, a]` blocks, yielding
    `[a, ..., a]` of length `2 * (D - n)`. -/
private theorem tagNSteps_replicate_pop_pair {k : Nat} (a : Fin k) :
    ∀ (D n : Nat), n ≤ D →
      tagNSteps ({ productions := fun _ => [] } : Tag k)
        (List.replicate (2 * D) a) n
        = some (List.replicate (2 * (D - n)) a)
  | D, 0, _ => by
      show some (List.replicate (2 * D) a) = some (List.replicate (2 * (D - 0)) a)
      rw [Nat.sub_zero]
  | D, n + 1, h => by
      have h_D_pos : D ≥ 1 := by omega
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
      have h_n_le : n ≤ D' := by omega
      have h_pair : 2 * (D' + 1) = 2 * D' + 2 := by
        rw [Nat.mul_add, Nat.mul_one]
      have h_split : List.replicate (2 * (D' + 1)) a
                  = a :: a :: List.replicate (2 * D') a := by
        rw [h_pair]; simp [List.replicate_succ]
      -- One tag step pops [a, a]; recurse with `n` on length 2*D'.
      show tagNSteps _ (List.replicate (2 * (D' + 1)) a) (n + 1)
            = some (List.replicate (2 * (D' + 1 - (n + 1))) a)
      rw [h_split]
      have h_step :
          ({ productions := fun _ => [] } : Tag k).step
            (a :: a :: List.replicate (2 * D') a)
            = some (List.replicate (2 * D') a) := by
        simp [Tag.step]
      show (match ({ productions := fun _ => [] } : Tag k).step
              (a :: a :: List.replicate (2 * D') a) with
            | none => none
            | some cfg' => tagNSteps _ cfg' n)
            = some (List.replicate (2 * (D' + 1 - (n + 1))) a)
      rw [h_step]
      have h_idx : D' + 1 - (n + 1) = D' - n := by omega
      rw [h_idx]
      exact tagNSteps_replicate_pop_pair a D' n h_n_le

/-- **Faithful Cocke-Minsky for any TM admitting a depth function** that
    *weakly* decreases by at least 1 per step.  Generalises iter-96's
    `_of_depth_decreasing` by allowing each step to drop the depth by
    any positive amount (rather than exactly 1).

    Encoder: same as iter 96 — `List.replicate (2 * depth cfg) a` over
    `Fin 1`.  Each TM step is mirrored by exactly `depth cfg - depth cfg'`
    tag steps (≥ 1 by hypothesis), each popping a `[a, a]` block. -/
theorem cocke_minsky_reduces_faithful_of_depth_weakly_decreasing (tm : Machine)
    (depth : Config → Nat)
    (h_halt_depth : ∀ cfg, halted cfg = true → depth cfg = 0)
    (h_step_depth : ∀ cfg cfg', step tm cfg = some cfg' →
      depth cfg ≥ depth cfg' + 1) :
    CockeMinskyReducesFaithful tm := by
  let a : Fin 1 := ⟨0, Nat.one_pos⟩
  refine ⟨1, Nat.one_pos, { productions := fun _ => [] },
          fun cfg => List.replicate (2 * depth cfg) a, ?_, ?_⟩
  · -- Halted ⇒ encode = [].
    intro cfg h_halt
    have : depth cfg = 0 := h_halt_depth cfg h_halt
    simp [this]
  · -- Step ⇒ `n := depth cfg - depth cfg'` tag steps suffice.
    intro cfg cfg' h_step
    have h_d : depth cfg ≥ depth cfg' + 1 := h_step_depth cfg cfg' h_step
    let n := depth cfg - depth cfg'
    have h_n_pos : n ≥ 1 := by simp [n]; omega
    have h_n_le : n ≤ depth cfg := Nat.sub_le _ _
    have h_diff : depth cfg - n = depth cfg' := by simp [n]; omega
    refine ⟨n, h_n_pos, ?_⟩
    show tagNSteps { productions := fun _ => [] }
            (List.replicate (2 * depth cfg) a) n
        = some (List.replicate (2 * depth cfg') a)
    rw [tagNSteps_replicate_pop_pair a (depth cfg) n h_n_le, h_diff]

/-- **Faithful Cocke-Minsky for any TM that halts in at most three steps from
    every active state**.  Generalises `_of_two_step_halt`: the third disjunct
    `(c)` allows configurations where neither immediate-halt nor next-step-halt
    holds, but the next-of-next state always halts on every symbol.

    Proof goes via `_of_depth_weakly_decreasing` (NOT `_of_depth_decreasing`):
    at depth-3 the actual cfg' could be depth-1 (drop by 2) or depth-2 (drop
    by 1), depending on the actual head symbol — so a strict drop-by-1
    invariant fails, but the weakly-decreasing version succeeds.

    Depth function:
    * halted → 0,
    * `next-state = 0` (immediate halt) → 1,
    * `∀ s', next-of-next halts` (one-step-halt) → 2,
    * else → 3 (under the three-step hypothesis).

    Demonstrates the iter-98 weakly-decreasing relaxation paying off: a TM
    class previously inaccessible via the strict-drop primitive. -/
theorem cocke_minsky_reduces_faithful_of_three_step_halt (tm : Machine)
    (h_three : ∀ q s, q ≥ 1 →
      (tm.transition q s).nextState = 0 ∨
      (∀ s', (tm.transition (tm.transition q s).nextState s').nextState = 0) ∨
      (∀ s' s'', (tm.transition (tm.transition (tm.transition q s).nextState s').nextState s'').nextState = 0)) :
    CockeMinskyReducesFaithful tm := by
  classical
  apply cocke_minsky_reduces_faithful_of_depth_weakly_decreasing tm
    (fun cfg =>
      if halted cfg then 0
      else if (tm.transition cfg.state cfg.head).nextState = 0 then 1
      else if ∀ s', (tm.transition (tm.transition cfg.state cfg.head).nextState s').nextState = 0
        then 2
      else 3)
  · intro cfg h_halt; simp [h_halt]
  · intro cfg cfg' h_step
    have h_active : cfg.state ≠ 0 := by
      intro h_z
      have h_n : step tm cfg = none := (step_none_iff_halted _ _).mpr h_z
      rw [h_n] at h_step; cases h_step
    have h_pos : 1 ≤ cfg.state := by omega
    have h_active' : ¬ halted cfg = true := by
      intro h_h
      have : cfg.state = 0 := by simp [halted] at h_h; exact h_h
      exact h_active this
    have h_cfg'_state : cfg'.state = (tm.transition cfg.state cfg.head).nextState :=
      step_active_state tm cfg cfg' h_step
    have h_three_apply := h_three cfg.state cfg.head h_pos
    by_cases h_imm : (tm.transition cfg.state cfg.head).nextState = 0
    · -- depth cfg = 1, depth cfg' = 0.
      have h_cfg'_halt : halted cfg' = true := by
        simp [halted, h_cfg'_state, h_imm]
      simp [h_active', h_imm, h_cfg'_halt]
    · -- cfg' active.
      have h_cfg'_active : cfg'.state ≠ 0 := by
        rw [h_cfg'_state]; exact h_imm
      have h_cfg'_active' : ¬ halted cfg' = true := by
        simp [halted, h_cfg'_active]
      by_cases h_next_halts : ∀ s',
          (tm.transition (tm.transition cfg.state cfg.head).nextState s').nextState = 0
      · -- depth cfg = 2, cfg' has next-state halting (since cfg'.state = next-state and ∀ s'
        -- on the next-state has its next halt).  So depth cfg' = 1.
        have h_cfg'_imm : (tm.transition cfg'.state cfg'.head).nextState = 0 := by
          rw [h_cfg'_state]; exact h_next_halts cfg'.head
        simp [h_active', h_imm, h_next_halts, h_cfg'_active', h_cfg'_imm]
      · -- depth cfg = 3 (we're in case (c) of hypothesis).
        -- cfg' has depth ∈ {1, 2}.  Either way, depth cfg ≥ depth cfg' + 1.
        have h_case_c : ∀ s' s'',
            (tm.transition (tm.transition (tm.transition cfg.state cfg.head).nextState s').nextState s'').nextState = 0 := by
          rcases h_three_apply with h | h | h
          · exact absurd h h_imm
          · exact absurd h h_next_halts
          · exact h
        -- For ANY head of cfg', the next-of-next-state halts.
        -- depth cfg' is either 1 (if cfg's next halts immediately) or 2.
        simp [h_active', h_imm, h_next_halts, h_cfg'_active']
        -- Goal: 3 ≥ (if (next of cfg' active) halts immediately then 1
        --              else if ∀ s', halts then 2 else 3) + 1
        by_cases h_cfg'_imm : (tm.transition cfg'.state cfg'.head).nextState = 0
        · simp [h_cfg'_imm]
        · have h_cfg'_next_halts :
              ∀ s', (tm.transition (tm.transition cfg'.state cfg'.head).nextState s').nextState = 0 := by
            intro s'
            rw [h_cfg'_state]
            exact h_case_c cfg'.head s'
          simp [h_cfg'_imm, h_cfg'_next_halts]

-- ============================================================================
-- Bounded halt-depth construction for uniform-N-step-halt TMs (iter 102)
-- ============================================================================

/-- The number of TM steps until halt, capped at fuel `n`.  When `cfg` halts
    within `n` steps this matches the true halt time; otherwise it returns 0
    (but for our use case the cap is never hit). -/
def boundedHaltDepth (tm : Machine) : Nat → Config → Nat
  | 0, _ => 0
  | n + 1, cfg =>
    if halted cfg then 0
    else match step tm cfg with
      | none => 0
      | some cfg' => 1 + boundedHaltDepth tm n cfg'

@[simp] theorem boundedHaltDepth_halted (tm : Machine) (cfg : Config) (n : Nat)
    (h : halted cfg = true) : boundedHaltDepth tm n cfg = 0 := by
  cases n with
  | zero => rfl
  | succ m => simp [boundedHaltDepth, h]

theorem boundedHaltDepth_active_step (tm : Machine) (cfg cfg' : Config) (n : Nat)
    (h_active : halted cfg = false) (h_step : step tm cfg = some cfg') :
    boundedHaltDepth tm (n + 1) cfg = 1 + boundedHaltDepth tm n cfg' := by
  show (if halted cfg then 0
        else match step tm cfg with
          | none => 0
          | some cfg' => 1 + boundedHaltDepth tm n cfg') = 1 + boundedHaltDepth tm n cfg'
  rw [if_neg (by simp [h_active])]
  rw [h_step]

/-- If `cfg` halts within `M` fuel steps (i.e. eval succeeds), then
    `boundedHaltDepth` is monotone: more fuel doesn't change the answer.
    The proof inducts on `M`. -/
theorem boundedHaltDepth_extra_fuel (tm : Machine) :
    ∀ (M : Nat) (cfg : Config),
      (∃ result, eval tm cfg M = some result ∧ halted result = true) →
      ∀ (N : Nat), N ≥ M →
        boundedHaltDepth tm N cfg = boundedHaltDepth tm M cfg
  | 0, cfg, h, N, _ => by
      obtain ⟨result, h_eval, h_halt⟩ := h
      dsimp [eval] at h_eval
      split at h_eval
      · injection h_eval with h_eq
        subst h_eq
        rw [boundedHaltDepth_halted tm cfg N h_halt]
        rw [boundedHaltDepth_halted tm cfg 0 h_halt]
      · contradiction
  | M + 1, cfg, h, N, hN => by
      obtain ⟨result, h_eval, h_halt_result⟩ := h
      dsimp [eval] at h_eval
      split at h_eval
      · -- cfg already halted
        rename_i h_halt
        injection h_eval with h_eq; subst h_eq
        rw [boundedHaltDepth_halted tm cfg N h_halt]
        rw [boundedHaltDepth_halted tm cfg (M + 1) h_halt]
      · -- cfg active, step proceeds
        rename_i h_active
        have h_active' : halted cfg = false := by
          cases h_t : halted cfg
          · rfl
          · simp [h_t] at h_active
        cases h_step : step tm cfg with
        | none =>
          rw [h_step] at h_eval
          injection h_eval with h_eq; subst h_eq
          -- result = cfg, but halted cfg = false and h_halt_result says halted cfg = true: contradiction
          rw [h_active'] at h_halt_result
          cases h_halt_result
        | some cfg' =>
          rw [h_step] at h_eval
          -- N ≥ M + 1 ⇒ N = N' + 1 with N' ≥ M
          obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
          have hN' : N' ≥ M := by omega
          have h_ih := boundedHaltDepth_extra_fuel tm M cfg' ⟨result, h_eval, h_halt_result⟩ N' hN'
          rw [boundedHaltDepth_active_step tm cfg cfg' N' h_active' h_step]
          rw [boundedHaltDepth_active_step tm cfg cfg' M h_active' h_step]
          rw [h_ih]

/-- If `cfg` halts within `M+1` fuel steps and active, then `cfg'` (one step
    away) halts within `M` fuel steps.  Used for the strict-decreasing step. -/
theorem step_active_halts_in_one_less (tm : Machine) (cfg cfg' : Config) (M : Nat)
    (h_active : halted cfg = false) (h_step : step tm cfg = some cfg')
    (h_halt : ∃ result, eval tm cfg (M + 1) = some result ∧ halted result = true) :
    ∃ result, eval tm cfg' M = some result ∧ halted result = true := by
  obtain ⟨result, h_eval, h_halt_result⟩ := h_halt
  dsimp [eval] at h_eval
  rw [if_neg (by simp [h_active])] at h_eval
  rw [h_step] at h_eval
  exact ⟨result, h_eval, h_halt_result⟩

/-- **Faithful Cocke-Minsky for uniformly-halting TMs**: if every cfg halts
    within exactly `N` fuel steps, then `CockeMinskyReducesFaithful` holds.
    Goes via the bounded-halt-depth helper + `_of_depth_decreasing`. -/
theorem cocke_minsky_reduces_faithful_of_uniform_halt (tm : Machine) (N : Nat)
    (h_uni : ∀ cfg, ∃ result, eval tm cfg N = some result ∧ halted result = true) :
    CockeMinskyReducesFaithful tm := by
  apply cocke_minsky_reduces_faithful_of_depth_decreasing tm
    (fun cfg => boundedHaltDepth tm N cfg)
  · intro cfg h_halt
    exact boundedHaltDepth_halted tm cfg N h_halt
  · intro cfg cfg' h_step
    have h_active : halted cfg = false := by
      have h_active_state : cfg.state ≠ 0 := by
        intro h_z
        have h_n : step tm cfg = none := (step_none_iff_halted _ _).mpr h_z
        rw [h_n] at h_step; cases h_step
      simp [halted, h_active_state]
    -- depth cfg = boundedHaltDepth tm N cfg.  Pick N = M + 1.
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := by
      cases N with
      | zero =>
        -- contradiction: cfg active but halts in 0 fuel ⇒ contradiction
        obtain ⟨result, h_eval, h_halt_result⟩ := h_uni cfg
        dsimp [eval] at h_eval
        rw [if_neg (by simp [h_active])] at h_eval
        cases h_eval
      | succ M => exact ⟨M, rfl⟩
    rw [boundedHaltDepth_active_step tm cfg cfg' M h_active h_step]
    -- Now: 1 + boundedHaltDepth tm M cfg' = boundedHaltDepth tm (M+1) cfg' + 1
    -- Use boundedHaltDepth_extra_fuel: cfg' halts within M (via step_active_halts_in_one_less)
    have h_cfg'_halts : ∃ result, eval tm cfg' M = some result ∧ halted result = true :=
      step_active_halts_in_one_less tm cfg cfg' M h_active h_step (h_uni cfg)
    have h_eq := boundedHaltDepth_extra_fuel tm M cfg' h_cfg'_halts (M + 1) (by omega)
    rw [h_eq]; omega

/-- If `eval` returns `some result`, then `result` is halted.  Used to convert
    `Halts tm cfg` (which doesn't include the halted-result clause) into the
    eval-halt-witness form consumed by `boundedHaltDepth_extra_fuel`. -/
theorem eval_some_implies_halted_result (tm : Machine) :
    ∀ (cfg : Config) (fuel : Nat) (result : Config),
      eval tm cfg fuel = some result → halted result = true
  | cfg, 0, result, h => by
      dsimp [eval] at h
      split at h
      · rename_i h_h; injection h with h_eq; subst h_eq; exact h_h
      · cases h
  | cfg, fuel + 1, result, h => by
      dsimp [eval] at h
      split at h
      · rename_i h_h; injection h with h_eq; subst h_eq; exact h_h
      · cases h_step : step tm cfg with
        | none =>
          rw [h_step] at h
          injection h with h_eq; subst h_eq
          have h_halt_cfg : cfg.state = 0 := (step_none_iff_halted tm cfg).mp h_step
          simp [halted, h_halt_cfg]
        | some cfg' =>
          rw [h_step] at h
          exact eval_some_implies_halted_result tm cfg' fuel result h

/-- `Halts tm cfg` packaged as an eval-halt-witness with the halted-result
    clause.  Adapter for the bounded-halt machinery in iter 102. -/
theorem halts_iff_eval_witness (tm : Machine) (cfg : Config) :
    Halts tm cfg ↔ ∃ N, ∃ result, eval tm cfg N = some result
                                  ∧ halted result = true := by
  constructor
  · intro ⟨fuel, result, h_eval⟩
    exact ⟨fuel, result, h_eval,
            eval_some_implies_halted_result tm cfg fuel result h_eval⟩
  · intro ⟨N, result, h_eval, _⟩
    exact ⟨N, result, h_eval⟩

/-- For an active cfg with successful step, `Halts tm cfg ↔ Halts tm cfg'`. -/
theorem halts_step_propagates (tm : Machine) (cfg cfg' : Config)
    (h_active : halted cfg = false) (h_step : step tm cfg = some cfg') :
    Halts tm cfg ↔ Halts tm cfg' := by
  constructor
  · intro ⟨fuel, result, h_eval⟩
    -- cfg active so eval cfg 0 = none.  Hence fuel ≥ 1.
    cases fuel with
    | zero =>
      dsimp [eval] at h_eval
      rw [if_neg (by simp [h_active])] at h_eval
      cases h_eval
    | succ f =>
      dsimp [eval] at h_eval
      rw [if_neg (by simp [h_active])] at h_eval
      rw [h_step] at h_eval
      exact ⟨f, result, h_eval⟩
  · intro ⟨fuel, result, h_eval⟩
    refine ⟨fuel + 1, result, ?_⟩
    dsimp [eval]
    rw [if_neg (by simp [h_active])]
    rw [h_step]
    exact h_eval

/-- **Faithful Cocke-Minsky for TMs that halt on every input** (eventually,
    not necessarily uniformly).  STRONGEST cocke-side theorem so far:
    covers every TM that halts on every cfg regardless of how long it takes.
    Subsumes `_of_uniform_halt N` (uniform N), and via that subsumes the
    structural classes (immediate-halt, two-step-halt, three-step-halt,
    linearChain) up to existence of a halt-witness function. -/
theorem cocke_minsky_reduces_faithful_of_halts_eventually (tm : Machine)
    (h_halt : ∀ cfg, ∃ N, ∃ result, eval tm cfg N = some result
                                     ∧ halted result = true) :
    CockeMinskyReducesFaithful tm := by
  classical
  -- pickN cfg = a halt fuel for cfg; specs are then (Classical.choose_spec ...).
  apply cocke_minsky_reduces_faithful_of_depth_decreasing tm
    (fun cfg => boundedHaltDepth tm (Classical.choose (h_halt cfg)) cfg)
  · intro cfg h_h
    exact boundedHaltDepth_halted tm cfg _ h_h
  · intro cfg cfg' h_step
    -- cfg active, since step succeeded
    have h_active_state : cfg.state ≠ 0 := by
      intro h_z
      have h_n : step tm cfg = none := (step_none_iff_halted _ _).mpr h_z
      rw [h_n] at h_step; cases h_step
    have h_active : halted cfg = false := by simp [halted, h_active_state]
    have h_spec_cfg := Classical.choose_spec (h_halt cfg)
    have h_spec_cfg' := Classical.choose_spec (h_halt cfg')
    -- pickN cfg ≥ 1 (active config can't halt with 0 fuel).  Case-split.
    cases h_pick : Classical.choose (h_halt cfg) with
    | zero =>
      -- Contradiction: cfg active but halts in 0 fuel.
      exfalso
      rw [h_pick] at h_spec_cfg
      obtain ⟨_, h_eval, _⟩ := h_spec_cfg
      dsimp [eval] at h_eval
      rw [if_neg (by simp [h_active])] at h_eval
      cases h_eval
    | succ M =>
    rw [boundedHaltDepth_active_step tm cfg cfg' M h_active h_step]
    -- cfg' halts within M fuel via step_active_halts_in_one_less.
    have h_cfg'_halt_M : ∃ result, eval tm cfg' M = some result
                                    ∧ halted result = true := by
      have := h_spec_cfg
      rw [h_pick] at this
      exact step_active_halts_in_one_less tm cfg cfg' M h_active h_step this
    -- Both M and (pickN cfg') suffice for cfg'.  Use a common upper bound.
    let MAX := max M (Classical.choose (h_halt cfg'))
    have hM_le : M ≤ MAX := Nat.le_max_left _ _
    have hN'_le : Classical.choose (h_halt cfg') ≤ MAX := Nat.le_max_right _ _
    have h_eq_M : boundedHaltDepth tm M cfg' = boundedHaltDepth tm MAX cfg' := by
      exact (boundedHaltDepth_extra_fuel tm M cfg' h_cfg'_halt_M MAX hM_le).symm
    have h_eq_N' : boundedHaltDepth tm (Classical.choose (h_halt cfg')) cfg'
                  = boundedHaltDepth tm MAX cfg' :=
      (boundedHaltDepth_extra_fuel tm _ cfg' h_spec_cfg' MAX hN'_le).symm
    rw [h_eq_M, ← h_eq_N']
    omega

/-- Friendly form of `_of_halts_eventually`: the hypothesis is the natural
    `Halts tm cfg` predicate (the same one used by the weak reduction in
    `BiTM.CockeMinsky`), with the eval-witness conversion handled internally
    by `halts_iff_eval_witness`. -/
theorem cocke_minsky_reduces_faithful_of_total_halts (tm : Machine)
    (h_total : ∀ cfg, Halts tm cfg) :
    CockeMinskyReducesFaithful tm :=
  cocke_minsky_reduces_faithful_of_halts_eventually tm
    (fun cfg => (halts_iff_eval_witness tm cfg).mp (h_total cfg))

/-- **Universal faithful Cocke-Minsky** for ANY TM, halting or not.

    Uses a 2-symbol tag system:
    * Symbol `a` (= ⟨0, _⟩): halting-trajectory marker.  Productions `a → []`.
    * Symbol `b` (= ⟨1, _⟩): non-halting-trajectory marker.  Productions
      `b → [b, b]` (so `[b, b]` self-loops in the tag system).

    Encoder:
    * halted → `[]`.
    * active ∧ `Halts tm cfg` → `List.replicate (2 * boundedHaltDepth ...) a`.
    * active ∧ `¬ Halts tm cfg` → `[b, b]`.

    Step coverage uses `halts_step_propagates`: cfg ↔ cfg' agree on `Halts`,
    so the encoder dispatches consistently.  Halt branch reuses the
    `_of_halts_eventually` argument; non-halt branch uses the `[b, b]`
    self-loop.

    This closes `cocke_minsky_reduces_faithful` for the general case. -/
theorem cocke_minsky_reduces_faithful_universal (tm : Machine) :
    CockeMinskyReducesFaithful tm := by
  classical
  let a : Fin 2 := ⟨0, by omega⟩
  let b : Fin 2 := ⟨1, by omega⟩
  -- Productions: a (val=0) → [], b (val=1) → [b, b].
  let prods : Fin 2 → List (Fin 2) := fun s => if s.val = 0 then [] else [b, b]
  refine ⟨2, by omega, { productions := prods },
          fun cfg =>
            if halted cfg then ([] : TagConfig 2)
            else if h : Halts tm cfg then
              List.replicate (2 * boundedHaltDepth tm
                (Classical.choose ((halts_iff_eval_witness tm cfg).mp h)) cfg) a
            else
              [b, b], ?_, ?_⟩
  · -- halted clause
    intro cfg h_halt; simp [h_halt]
  · -- step clause
    intro cfg cfg' h_step
    have h_active_state : cfg.state ≠ 0 := by
      intro h_z
      have h_n : step tm cfg = none := (step_none_iff_halted _ _).mpr h_z
      rw [h_n] at h_step; cases h_step
    have h_active : halted cfg = false := by simp [halted, h_active_state]
    have h_active' : ¬ halted cfg = true := by simp [h_active]
    by_cases h_halts : Halts tm cfg
    · -- Halt branch: reuse the `_of_halts_eventually` style of proof.
      have h_halts' : Halts tm cfg' :=
        (halts_step_propagates tm cfg cfg' h_active h_step).mp h_halts
      have h_witness_cfg := (halts_iff_eval_witness tm cfg).mp h_halts
      have h_witness_cfg' := (halts_iff_eval_witness tm cfg').mp h_halts'
      have h_spec_cfg := Classical.choose_spec h_witness_cfg
      have h_spec_cfg' := Classical.choose_spec h_witness_cfg'
      cases h_pick : Classical.choose h_witness_cfg with
      | zero =>
        exfalso
        rw [h_pick] at h_spec_cfg
        obtain ⟨_, h_eval, _⟩ := h_spec_cfg
        dsimp [eval] at h_eval
        rw [if_neg h_active'] at h_eval
        cases h_eval
      | succ M =>
      have h_cfg'_halt_M : ∃ result, eval tm cfg' M = some result
                                      ∧ halted result = true := by
        have := h_spec_cfg
        rw [h_pick] at this
        exact step_active_halts_in_one_less tm cfg cfg' M h_active h_step this
      let MAX := max M (Classical.choose h_witness_cfg')
      have hM_le : M ≤ MAX := Nat.le_max_left _ _
      have hN'_le : Classical.choose h_witness_cfg' ≤ MAX := Nat.le_max_right _ _
      have h_eq_M : boundedHaltDepth tm M cfg' = boundedHaltDepth tm MAX cfg' :=
        (boundedHaltDepth_extra_fuel tm M cfg' h_cfg'_halt_M MAX hM_le).symm
      have h_eq_N' : boundedHaltDepth tm (Classical.choose h_witness_cfg') cfg'
                    = boundedHaltDepth tm MAX cfg' :=
        (boundedHaltDepth_extra_fuel tm _ cfg' h_spec_cfg' MAX hN'_le).symm
      refine ⟨1, Nat.le_refl _, ?_⟩
      -- Plan: rewrite LHS encoded length via `boundedHaltDepth_active_step`,
      -- split `replicate (2 + 2*d') a = a :: a :: replicate (2*d') a`, apply
      -- one tag step (popping `[a, a]` since prods a = []), then match RHS.
      show tagNSteps { productions := prods }
            (if halted cfg then ([] : TagConfig 2)
             else if h : Halts tm cfg then
               List.replicate (2 * boundedHaltDepth tm
                 (Classical.choose ((halts_iff_eval_witness tm cfg).mp h)) cfg) a
             else [b, b]) 1
          = some (if halted cfg' then ([] : TagConfig 2)
                  else if h' : Halts tm cfg' then
                    List.replicate (2 * boundedHaltDepth tm
                      (Classical.choose ((halts_iff_eval_witness tm cfg').mp h')) cfg') a
                  else [b, b])
      rw [if_neg h_active', dif_pos h_halts]
      -- LHS: replicate (2 * bdh (chooseN cfg) cfg) a.
      -- Substitute Classical.choose = M+1, then unfold via active-step.
      have h_choose_eq : Classical.choose ((halts_iff_eval_witness tm cfg).mp h_halts)
                        = M + 1 := h_pick
      rw [h_choose_eq]
      rw [boundedHaltDepth_active_step tm cfg cfg' M h_active h_step]
      -- LHS: replicate (2 * (1 + bdh M cfg')) a.
      have h_split_mul : 2 * (1 + boundedHaltDepth tm M cfg')
                        = (2 * boundedHaltDepth tm M cfg') + 2 := by omega
      rw [h_split_mul]
      have h_split_replicate :
          List.replicate ((2 * boundedHaltDepth tm M cfg') + 2) a
          = a :: a :: List.replicate (2 * boundedHaltDepth tm M cfg') a := by
        rw [show (2 * boundedHaltDepth tm M cfg') + 2
              = (2 * boundedHaltDepth tm M cfg') + 1 + 1 from by omega]
        simp [List.replicate_succ]
      rw [h_split_replicate, tagNSteps_one]
      -- LHS: Tag.step (a :: a :: replicate (2*bdh M cfg') a)
      --     = some (replicate (2*bdh M cfg') a ++ prods a)
      --     = some (replicate (2*bdh M cfg') a ++ [])
      --     = some (replicate (2*bdh M cfg') a)
      have h_step_pops :
          ({ productions := prods } : Tag 2).step
            (a :: a :: List.replicate (2 * boundedHaltDepth tm M cfg') a)
            = some (List.replicate (2 * boundedHaltDepth tm M cfg') a) := by
        show some (List.replicate (2 * boundedHaltDepth tm M cfg') a ++ prods a)
            = some (List.replicate (2 * boundedHaltDepth tm M cfg') a)
        have h_prods_a : prods a = [] := rfl
        rw [h_prods_a, List.append_nil]
      rw [h_step_pops]
      -- Now need: some (replicate (2*bdh M cfg') a) = some (encode cfg')
      -- Case-split on halted cfg'.
      by_cases h_cfg'_halt : halted cfg' = true
      · -- cfg' halted ⇒ encode cfg' = [], and bdh M cfg' = 0.
        rw [if_pos h_cfg'_halt]
        rw [boundedHaltDepth_halted tm cfg' M h_cfg'_halt]
        simp
      · -- cfg' active and Halts tm cfg' ⇒ encode cfg' = replicate (2*bdh (chooseN cfg') cfg') a.
        rw [if_neg (by simp [h_cfg'_halt])]
        rw [dif_pos h_halts']
        congr 2
        -- bdh M cfg' = bdh (Classical.choose witness_cfg') cfg' (both via MAX).
        rw [show (halts_iff_eval_witness tm cfg').mp h_halts'
              = h_witness_cfg' from rfl]
        rw [h_eq_M, ← h_eq_N']
    · -- Non-halt branch.
      have h_halts'_neg : ¬ Halts tm cfg' := by
        intro h_h
        exact h_halts ((halts_step_propagates tm cfg cfg' h_active h_step).mpr h_h)
      have h_cfg'_active_state : cfg'.state ≠ 0 := by
        -- cfg' must be active since ¬ Halts cfg' (halted ⇒ Halts).
        intro h_z
        have h_cfg'_halt : halted cfg' = true := by simp [halted, h_z]
        exact h_halts'_neg ⟨0, cfg', by simp [eval, h_cfg'_halt]⟩
      have h_cfg'_active : halted cfg' = false := by simp [halted, h_cfg'_active_state]
      have h_cfg'_active' : ¬ halted cfg' = true := by simp [h_cfg'_active]
      refine ⟨1, Nat.le_refl _, ?_⟩
      show tagNSteps { productions := prods }
            (if halted cfg then ([] : TagConfig 2)
             else if h : Halts tm cfg then _
             else [b, b]) 1
          = some (if halted cfg' then ([] : TagConfig 2)
                  else if h' : Halts tm cfg' then _
                  else [b, b])
      rw [if_neg h_active', dif_neg h_halts]
      rw [if_neg h_cfg'_active', dif_neg h_halts'_neg]
      -- tagNSteps prods [b, b] 1 = Tag.step prods [b, b] = some ([] ++ prods b)
      --   = some [b, b] (since prods b = [b, b]).
      rw [tagNSteps_one]
      show ({ productions := prods } : Tag 2).step ([b, b] : TagConfig 2) = some [b, b]
      simp [Tag.step, prods, b]

/-- **Closed downstream consumer** of `BiTM.CockeMinskyReduces` via the
    universal faithful theorem.  Replaces the trivial halt-collapse encoder
    (`cocke_minsky_reduces` in `BiTM.CockeMinsky`) with a meaningful proof:
    halting cfgs encode to halt-empty tag words via a faithful step-by-step
    simulation, not the all-collapsing `fun _ => []`. -/
theorem cocke_minsky_reduces_via_universal (tm : Machine) :
    CockeMinskyReduces tm :=
  CockeMinskyReducesFaithful_implies_weak tm
    (cocke_minsky_reduces_faithful_universal tm)


end CockeMinskyConstruction
end BiTM
