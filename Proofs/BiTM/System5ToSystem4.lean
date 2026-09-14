/-
  BiTM.System5ToSystem4

  Smith's System 5 → System 4 encoder (PDF `TM23Proof.pdf` p. 32,
  `s52s4.pl`).  Maps a System 5 (bag, rules) program plus a
  parameter `f` to a System 4 configuration whose evolution
  emulates the System 5 evolution.

  Extracted from `BiTM.CockeMinskyConstruction` in a refactor.

  Encoding outline:
    * State A; active 0
    * First elem: bag set with each entry `e ↦ e*2 - 2`
    * Then `f` star/empty-set pairs (padding)
    * For each System 5 rule:
      - Rule-encoded set: `0..f*3` XOR'd with each rule entry
        `k ↦ k*2 + f + 3`
      - `f*2` star/empty-set pairs
      - Set containing all of `0..3*f`
      - `f*2 - 2` star/empty-set pairs

  Contents:
    * `system5BagEntryToSystem4`, `encodeBag` — bag encoder
    * `starredEmptyPairs`, `allInts` — helpers
    * `encodeS5RuleToS4Set`, `encodeS5RuleToS4Elems` — per-rule encoder
    * `system5ToSystem4` — top-level encoder
    * Length lemmas + sanity-check examples
-/

import BiTM.XorMerge
import BiTM.System5
import BiTM.System4

namespace BiTM

open TM
open TagSystem

/-- Encode a System 5 bag entry into the corresponding System 4 set entry. -/
def system5BagEntryToSystem4 (e : Int) : Int := e * 2 - 2

/-- Encode the bag-to-System4-set transformation. -/
def encodeBag (bag : List Int) : List Int := bag.map system5BagEntryToSystem4

/-- A list `[*, {}, *, {}, ..., *, {}]` of `n` star + empty-set pairs (`2n` elems). -/
def starredEmptyPairs : Nat → List System4Elem
  | 0 => []
  | k + 1 => System4Elem.star :: System4Elem.set [] :: starredEmptyPairs k

/-- All integers from 0 to `n - 1` as a `List Int`. -/
def allInts (n : Nat) : List Int :=
  (List.range n).map (fun (i : Nat) => (i : Int))

/-- Encode one System 5 rule into a System 4 set: starts with all of `0..f*3`,
    then XOR-toggle each rule entry `k` mapped to `k*2 + f + 3`. -/
def encodeS5RuleToS4Set (rule : List Int) (f : Nat) : List Int :=
  rule.foldl (fun acc k => xorInsert (k * 2 + (f : Int) + 3) acc)
             (allInts (f * 3 + 1))

/-- Encode one System 5 rule into a sequence of System 4 elements:
    rule-set + 2f star/empty pairs + all-ints set + (2f - 2) star/empty pairs. -/
def encodeS5RuleToS4Elems (rule : List Int) (f : Nat) : List System4Elem :=
  System4Elem.set (encodeS5RuleToS4Set rule f) ::
    starredEmptyPairs (f * 2) ++
    [System4Elem.set (allInts (3 * f + 1))] ++
    starredEmptyPairs (f * 2 - 2)

/-- Full System 5 → System 4 encoder per `s52s4.pl`. -/
def system5ToSystem4 (cfg : System5Config) (f : Nat) : System4Config :=
  { elems := System4Elem.set (encodeBag cfg.bag) :: starredEmptyPairs f ++
             cfg.rules.flatMap (fun r => encodeS5RuleToS4Elems r f)
    active := 0
    state := System4State.A }

/-- `starredEmptyPairs n` has length `2 * n`. -/
theorem starredEmptyPairs_length (n : Nat) :
    (starredEmptyPairs n).length = 2 * n := by
  induction n with
  | zero => simp [starredEmptyPairs]
  | succ k ih =>
    show (System4Elem.star :: System4Elem.set [] :: starredEmptyPairs k).length
        = 2 * (k + 1)
    simp [ih]; omega

/-- `encodeBag` preserves length. -/
@[simp] theorem encodeBag_length (bag : List Int) :
    (encodeBag bag).length = bag.length := by
  simp [encodeBag]

/-- `allInts n` has length `n`. -/
@[simp] theorem allInts_length (n : Nat) : (allInts n).length = n := by
  simp [allInts]

/-- `encodeS5RuleToS4Elems rule f` has exactly `8f - 2` elements (when f ≥ 1).
    For `f = 0`, the formula gives 0 - 2 which is 0 in Nat (natural subtraction). -/
theorem encodeS5RuleToS4Elems_length (rule : List Int) (f : Nat) :
    (encodeS5RuleToS4Elems rule f).length = 1 + 2 * (f * 2) + 1 + 2 * (f * 2 - 2) := by
  show (System4Elem.set _ :: starredEmptyPairs (f * 2) ++
        [System4Elem.set _] ++ starredEmptyPairs (f * 2 - 2)).length = _
  simp [List.length_append, List.length_cons, starredEmptyPairs_length]
  omega

/-- **`system5ToSystem4_state_A` (iter 612)**: the encoder always
    initialises the System 4 cfg in state `A`.  Direct unfold. -/
@[simp] theorem system5ToSystem4_state_A (cfg : System5Config) (f : Nat) :
    (system5ToSystem4 cfg f).state = System4State.A := rfl

/-- **`system5ToSystem4_active_zero` (iter 612)**: the encoder always
    initialises `active` to 0. -/
@[simp] theorem system5ToSystem4_active_zero (cfg : System5Config) (f : Nat) :
    (system5ToSystem4 cfg f).active = 0 := rfl

/-- **`system5ToSystem4_elems_nonempty` (iter 612)**: the encoded
    config always has at least one element (the bag-encoded set is the
    head of `elems`).  Useful precondition for ruling out
    immediate-OOB halting in `System4.step`. -/
theorem system5ToSystem4_elems_nonempty (cfg : System5Config) (f : Nat) :
    (system5ToSystem4 cfg f).elems ≠ [] := by
  show (System4Elem.set (encodeBag cfg.bag) :: starredEmptyPairs f ++
        cfg.rules.flatMap (fun r => encodeS5RuleToS4Elems r f)) ≠ []
  intro h_eq
  cases h_eq

/-- **`system5ToSystem4_elems_head` (iter 612)**: the head of `elems`
    is exactly the bag-encoded set.  Direct unfold. -/
theorem system5ToSystem4_elems_head (cfg : System5Config) (f : Nat) :
    (system5ToSystem4 cfg f).elems.head?
      = some (System4Elem.set (encodeBag cfg.bag)) := rfl

/-- **`system5ToSystem4_active_lt_length` (iter 612)**: at the initial
    config, `active = 0 < elems.length` (since `elems` is non-empty).
    Composes `system5ToSystem4_elems_nonempty` with
    `List.length_pos_iff`. -/
theorem system5ToSystem4_active_lt_length (cfg : System5Config) (f : Nat) :
    (system5ToSystem4 cfg f).active < (system5ToSystem4 cfg f).elems.length := by
  rw [system5ToSystem4_active_zero]
  exact List.length_pos_iff.mpr (system5ToSystem4_elems_nonempty cfg f)

/-- **System5 step → System4 nSteps emulation lifting**: parallel of
    `step_to_nSteps_emulation_system5_to_tm` for the System5 → System4
    link.  Given a per-step emulator with `n ≥ 1` budget, lift to
    multi-step. -/
theorem step_to_nSteps_emulation_system5_to_system4
    (encode : System5Config → System4Config)
    (h_emulate : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ System4.nSteps (encode cfg) n = some (encode cfg'))
    (cfg : System5Config) (k : Nat) (result : System5Config)
    (h_steps : System5.nSteps cfg k = some result) :
    ∃ m, System4.nSteps (encode cfg) m = some (encode result) := by
  induction k generalizing cfg with
  | zero =>
    rw [System5.nSteps_zero] at h_steps
    injection h_steps with h_eq
    refine ⟨0, ?_⟩
    rw [h_eq]
    rfl
  | succ k ih =>
    rw [System5.nSteps_succ] at h_steps
    cases h_step : System5.step cfg with
    | none => rw [h_step] at h_steps; cases h_steps
    | some cfg₁ =>
      rw [h_step] at h_steps
      simp at h_steps
      obtain ⟨n, _hn_pos, h_n⟩ := h_emulate cfg cfg₁ h_step
      obtain ⟨m', h_m'⟩ := ih cfg₁ h_steps
      exact ⟨n + m',
        System4_nSteps_some_compose (encode cfg) (encode cfg₁)
          n m' (encode result) h_n h_m'⟩

/-- **System5 → System4 halt-preservation under step emulation**: if
    every System5 step is mirrored by `≥ 1` System4 steps and every
    System5 cfg with `step = none` encodes to a System4 `Halts` cfg,
    then `System5.Halts cfg → System4.Halts (encode cfg)`.  Composes
    `step_to_nSteps_emulation_system5_to_system4` with the System5
    step-none witness extractor and `System4_Halts_nSteps_pred`. -/
theorem system5Halts_imp_system4Halts_under_step_emulation
    (encode : System5Config → System4Config)
    (h_step_emulate : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ System4.nSteps (encode cfg) n = some (encode cfg'))
    (h_halt_preserve : ∀ cfg, System5.step cfg = none → System4.Halts (encode cfg))
    (cfg : System5Config) (h : System5.Halts cfg) :
    System4.Halts (encode cfg) := by
  obtain ⟨k, r, h_n, h_step_none⟩ := System5_Halts_extract_step_none_witness cfg h
  obtain ⟨m, h_m⟩ := step_to_nSteps_emulation_system5_to_system4
    encode h_step_emulate cfg k r h_n
  exact System4_Halts_nSteps_pred (encode cfg) m (encode r) h_m
    (h_halt_preserve r h_step_none)

/-- **System5 → System4 step-to-nSteps emulation positive bound**:
    stronger version tracking `m ≥ 1` when `k ≥ 1`.  Required for
    composing per-step emulation chains. -/
theorem step_to_nSteps_emulation_system5_to_system4_pos
    (encode : System5Config → System4Config)
    (h_emulate : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ System4.nSteps (encode cfg) n = some (encode cfg'))
    (cfg : System5Config) (k : Nat) (h_pos : k ≥ 1) (result : System5Config)
    (h_steps : System5.nSteps cfg k = some result) :
    ∃ m, m ≥ 1 ∧ System4.nSteps (encode cfg) m = some (encode result) := by
  cases k with
  | zero => omega
  | succ k =>
    rw [System5.nSteps_succ] at h_steps
    cases h_step : System5.step cfg with
    | none => rw [h_step] at h_steps; cases h_steps
    | some cfg₁ =>
      rw [h_step] at h_steps
      simp at h_steps
      obtain ⟨n, hn_pos, h_n⟩ := h_emulate cfg cfg₁ h_step
      obtain ⟨m', h_m'⟩ := step_to_nSteps_emulation_system5_to_system4
        encode h_emulate cfg₁ k result h_steps
      exact ⟨n + m', by omega,
        System4_nSteps_some_compose (encode cfg) (encode cfg₁)
          n m' (encode result) h_n h_m'⟩

/-- Bag `[1, 3, 4, 6]` (the test1.cy initial bag from iter 149) encodes to
    System 4 set `[0, 4, 6, 10]` via the `e*2 - 2` mapping. -/
example : encodeBag [1, 3, 4, 6] = [0, 4, 6, 10] := by decide

/-- `starredEmptyPairs 2` produces 2 stars + 2 empty sets, alternating. -/
example : starredEmptyPairs 2
    = [System4Elem.star, System4Elem.set [],
       System4Elem.star, System4Elem.set []] := by decide

/-- `allInts 5 = [0, 1, 2, 3, 4]`. -/
example : allInts 5 = [0, 1, 2, 3, 4] := by decide

/-- `encodeS5RuleToS4Set [1, 4] 16` removes `1*2 + 16 + 3 = 21` and
    `4*2 + 16 + 3 = 27` from `allInts 49`.  The result is everything
    in 0..48 except 21 and 27. -/
example :
    encodeS5RuleToS4Set [1, 4] 16
    = ((allInts 49).erase 21).erase 27 := by
  decide

/-- **Per-step emulation compose CTS → System5 → tm**: 2-link variant
    skipping System4.  Lets a System5 → BiTM-machine emulator
    (such as a hypothetical `system5ToWolfram23`) be composed directly
    with a CTS → System5 emulator, bypassing System4. -/
theorem cts_step_emulation_compose_through_system5_to_tm
    (cts : CTS) (tm : Machine)
    (enc1 : CTSConfig → System5Config) (enc2 : System5Config → Config)
    (h₁ : ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ System5.nSteps (enc1 ctsCfg) n = some (enc1 ctsCfg'))
    (h₂ : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (enc2 cfg) n = some (enc2 cfg')) :
    ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (enc2 (enc1 ctsCfg)) n = some (enc2 (enc1 ctsCfg')) := by
  intro ctsCfg ctsCfg' h_cts_step
  obtain ⟨k₁, hk₁_pos, h_k₁⟩ := h₁ ctsCfg ctsCfg' h_cts_step
  exact step_to_nSteps_emulation_system5_to_tm_pos tm enc2 h₂
    (enc1 ctsCfg) k₁ hk₁_pos (enc1 ctsCfg') h_k₁

/-- **Per-step emulation compose through System5: CTS → System5 →
    System4**: Two link-level per-step emulators at System5 and
    System4 levels compose into a CTS → System4 per-step emulator
    preserving the `n ≥ 1` budget. -/
theorem cts_step_emulation_compose_through_system5
    (cts : CTS) (enc1 : CTSConfig → System5Config)
    (enc2 : System5Config → System4Config)
    (h₁ : ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ System5.nSteps (enc1 ctsCfg) n = some (enc1 ctsCfg'))
    (h₂ : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ System4.nSteps (enc2 cfg) n = some (enc2 cfg')) :
    ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ System4.nSteps (enc2 (enc1 ctsCfg)) n = some (enc2 (enc1 ctsCfg')) := by
  intro ctsCfg ctsCfg' h_cts_step
  obtain ⟨k₁, hk₁_pos, h_k₁⟩ := h₁ ctsCfg ctsCfg' h_cts_step
  exact step_to_nSteps_emulation_system5_to_system4_pos enc2 h₂
    (enc1 ctsCfg) k₁ hk₁_pos (enc1 ctsCfg') h_k₁

/-- **Full per-step emulation chain compose CTS → System5 → System4 →
    BiTM**: three-link per-step emulation chain composition.  Lets
    the entire Smith chain's per-step emulation be discharged via
    three link-level per-step emulators. -/
theorem cts_step_emulation_compose_full_chain
    (cts : CTS) (tm : Machine)
    (enc1 : CTSConfig → System5Config) (enc2 : System5Config → System4Config)
    (enc3 : System4Config → Config)
    (h₁ : ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ System5.nSteps (enc1 ctsCfg) n = some (enc1 ctsCfg'))
    (h₂ : ∀ cfg cfg', System5.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ System4.nSteps (enc2 cfg) n = some (enc2 cfg'))
    (h₃ : ∀ cfg cfg', System4.step cfg = some cfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (enc3 cfg) n = some (enc3 cfg')) :
    ∀ ctsCfg ctsCfg', cts.step ctsCfg = some ctsCfg' →
       ∃ n, n ≥ 1 ∧ nSteps tm (enc3 (enc2 (enc1 ctsCfg))) n
                  = some (enc3 (enc2 (enc1 ctsCfg'))) := by
  intro ctsCfg ctsCfg' h_cts_step
  obtain ⟨k, hk_pos, h_k⟩ := cts_step_emulation_compose_through_system5
    cts enc1 enc2 h₁ h₂ ctsCfg ctsCfg' h_cts_step
  exact step_to_nSteps_emulation_system4_to_tm_pos tm enc3 h₃
    (enc2 (enc1 ctsCfg)) k hk_pos (enc2 (enc1 ctsCfg')) h_k

end BiTM
