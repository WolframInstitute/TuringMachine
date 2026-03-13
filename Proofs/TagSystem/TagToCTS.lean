/-
  TagSystem.TagToCTS

  Cook's encoding: 2-Tag System → Cyclic Tag System.

  Each symbol aᵢ of the k-symbol tag alphabet is encoded as a binary
  word of length k: one-hot encoding with true at position i.
  A tag word is encoded by concatenating the binary encodings.
  The CTS has k appendants, where appendant j = encoding(production(aⱼ)).

  One step of the 2-tag system corresponds to 2k steps of the CTS.
-/

import TagSystem.Basic

namespace TagSystem

-- ============================================================================
-- Symbol encoding: Fin k → List Bool
-- ============================================================================

/-- Encode a tag alphabet symbol as a one-hot binary word of length k.
    Symbol i becomes: [false, ..., false, true, false, ..., false]
    with `true` at position i (0-indexed). -/
def symbolEncode (k : Nat) (i : Fin k) : List Bool :=
  (List.range k).map fun j => j == i.val

/-- symbolEncode always produces a list of length k -/
theorem symbolEncode_length (k : Nat) (i : Fin k) :
    (symbolEncode k i).length = k := by
  simp [symbolEncode]

-- ============================================================================
-- Word encoding: List (Fin k) → List Bool
-- ============================================================================

/-- Encode a tag system word as a binary string by concatenating
    the one-hot encodings of each symbol. -/
def tagWordEncode (k : Nat) (word : List (Fin k)) : List Bool :=
  word.flatMap (symbolEncode k)

/-- The encoded word length is k times the original word length -/
theorem tagWordEncode_length (k : Nat) (word : List (Fin k)) :
    (tagWordEncode k word).length = k * word.length := by
  induction word with
  | nil => simp [tagWordEncode]
  | cons a rest ih =>
    simp only [tagWordEncode, List.flatMap_cons, List.length_append, symbolEncode_length]
    change k + (tagWordEncode k rest).length = k * (rest.length + 1)
    rw [ih, Nat.mul_succ]; exact Nat.add_comm _ _

/-- Empty tag word encodes to empty CTS data -/
theorem tagWordEncode_nil (k : Nat) : tagWordEncode k ([] : List (Fin k)) = [] := by
  simp [tagWordEncode]

/-- tagWordEncode distributes over list append -/
theorem tagWordEncode_append (k : Nat) (xs ys : List (Fin k)) :
    tagWordEncode k (xs ++ ys) = tagWordEncode k xs ++ tagWordEncode k ys := by
  simp [tagWordEncode, List.flatMap_append]

/-- tagWordEncode of a cons = symbolEncode of head ++ tagWordEncode of tail -/
theorem tagWordEncode_cons (k : Nat) (a : Fin k) (rest : List (Fin k)) :
    tagWordEncode k (a :: rest) = symbolEncode k a ++ tagWordEncode k rest := by
  simp [tagWordEncode, List.flatMap_cons]

-- ============================================================================
-- CTS construction from a 2-Tag System
-- ============================================================================

/-- Construct a Cyclic Tag System that simulates a given 2-tag system.

    Cook's encoding uses **2k appendants** (not k):
    - Appendants 0..k-1:   encode production(aⱼ) as tagWordEncode k (productions(aⱼ))
    - Appendants k..2k-1:  all empty (consume the second deleted symbol silently)

    One 2-tag step on word `a :: b :: rest → rest ++ productions(a)` corresponds
    to 2k CTS steps:
    - First k steps process `symbolEncode k a`: the one-hot bit at position a.val
      fires appendant[a.val] = tagWordEncode(productions(a)), appending the correct production
    - Next k steps process `symbolEncode k b`: the one-hot bit at position b.val
      fires appendant[k + b.val] = [] (empty), so nothing is appended

    Reference: Cook, "Universality in Elementary Cellular Automata" (2004). -/
def tagToCTS {k : Nat} (ts : Tag k) (hk : k > 0) : CTS where
  appendants :=
    -- First k: production encodings
    (List.finRange k).map (fun i => tagWordEncode k (ts.productions i))
    -- Next k: empty (for consuming the second deleted symbol)
    ++ (List.finRange k).map (fun _ => ([] : List Bool))
  nonempty := by simp; omega

/-- The constructed CTS has exactly 2*k appendants -/
theorem tagToCTS_appendants_length {k : Nat} (ts : Tag k) (hk : k > 0) :
    (tagToCTS ts hk).appendants.length = 2 * k := by
  simp [tagToCTS]; omega

-- ============================================================================
-- Encoding a TagConfig into a CTSConfig
-- ============================================================================

/-- Encode a tag system configuration into a CTS configuration. -/
def tagConfigToCTS (k : Nat) (cfg : TagConfig k) : CTSConfig where
  data := tagWordEncode k cfg
  phase := 0

-- ============================================================================
-- CTS structural lemmas
-- ============================================================================

/-- CTS halts immediately on empty data -/
theorem cts_halts_on_empty (cts : CTS) (phase : Nat) :
    cts.Halts { data := [], phase := phase } :=
  ⟨0, { data := [], phase := phase }, by simp [CTS.eval, ctsHalted]⟩

/-- nSteps 0 is identity -/
theorem CTS.nSteps_zero (cts : CTS) (cfg : CTSConfig) :
    cts.nSteps cfg 0 = some cfg := rfl

/-- nSteps composition: n steps then m steps = n+m steps -/
theorem CTS.nSteps_add (cts : CTS) (cfg cfg' : CTSConfig) (n m : Nat) :
    cts.nSteps cfg n = some cfg' →
    cts.nSteps cfg' m = cts.nSteps cfg (n + m) := by
  intro h
  induction n generalizing cfg with
  | zero =>
    simp [nSteps] at h
    rw [h]
    simp [Nat.zero_add]
  | succ n ih =>
    simp only [nSteps] at h ⊢
    split at h
    · simp at h  -- none case
    · rename_i cfg'' h_step
      rw [Nat.succ_add]
      simp only [nSteps, h_step]
      exact ih cfg'' h

/-- If CTS step returns some, the config was not halted -/
theorem cts_step_some_not_halted (cts : CTS) (cfg cfg' : CTSConfig) :
    cts.step cfg = some cfg' → ctsHalted cfg = false := by
  intro h
  cases h_data : cfg.data with
  | nil => simp [CTS.step, h_data] at h
  | cons _ _ => simp [ctsHalted, List.isEmpty, h_data]

/-- nSteps through non-halted configs can be prepended to eval.
    If nSteps cfg n = some cfg', then for any eval of cfg' with fuel f,
    eval cfg (f + n) gives the same result. -/
theorem cts_nSteps_prepend_eval (cts : CTS) (cfg cfg' : CTSConfig) (n fuel : Nat) :
    cts.nSteps cfg n = some cfg' →
    cts.eval cfg (fuel + n) = cts.eval cfg' fuel := by
  intro h_nsteps
  induction n generalizing cfg with
  | zero =>
    simp [CTS.nSteps] at h_nsteps
    rw [h_nsteps]; simp
  | succ n ih =>
    simp only [CTS.nSteps] at h_nsteps
    split at h_nsteps
    · simp at h_nsteps
    · rename_i cfg'' h_step
      rw [Nat.add_succ]
      have h_nh := cts_step_some_not_halted cts cfg cfg'' h_step
      rw [CTS.eval_step cts cfg cfg'' (fuel + n) h_nh h_step]
      exact ih cfg'' h_nsteps

/-- If CTS reaches cfg' in n steps, and cfg' halts, then cfg halts -/
theorem cts_halts_after_nSteps (cts : CTS) (cfg cfg' : CTSConfig) (n : Nat) :
    cts.nSteps cfg n = some cfg' →
    cts.Halts cfg' →
    cts.Halts cfg := by
  intro h_nsteps ⟨fuel, result, h_eval⟩
  exact ⟨fuel + n, result, by rw [cts_nSteps_prepend_eval cts cfg cfg' n fuel h_nsteps]; exact h_eval⟩

-- ============================================================================
-- One-hot symbol processing through CTS
-- ============================================================================

/-- Helper: symbolEncode produces a non-empty list when k > 0 -/
theorem symbolEncode_ne_nil (k : Nat) (hk : k > 0) (a : Fin k) :
    symbolEncode k a ≠ [] := by
  simp [symbolEncode]; omega

theorem phase_succ_mod (phase len L : Nat) :
  ((phase + 1) % L + len) % L = (phase + (len + 1)) % L := by
  calc ((phase + 1) % L + len) % L
    _ = ((phase + 1) % L + len % L) % L := by rw [Nat.add_mod ((phase + 1) % L) len L, Nat.mod_mod]
    _ = (phase + 1 + len) % L := (Nat.add_mod (phase + 1) len L).symm
    _ = (phase + (len + 1)) % L := by congr 1; omega

theorem phase_app_mod (phase a offset L : Nat) (h : a ≥ offset + 1) :
  ((phase + 1) % L + a - (offset + 1)) % L = (phase + a - offset) % L := by
  have ha : ((phase + 1) % L + a - (offset + 1)) = ((phase + 1) % L + (a - (offset + 1))) := by omega
  rw [ha]
  calc ((phase + 1) % L + (a - (offset + 1))) % L
    _ = ((phase + 1) % L + (a - (offset + 1)) % L) % L := by rw [Nat.add_mod ((phase + 1) % L) (a - (offset + 1)) L, Nat.mod_mod]
    _ = (phase + 1 + (a - (offset + 1))) % L := (Nat.add_mod (phase + 1) (a - (offset + 1)) L).symm
    _ = (phase + a - offset) % L := by congr 1; omega

theorem map_range_succ (a offset len : Nat) :
  (List.range (len + 1)).map (fun i => i + offset == a) = 
  (offset == a) :: (List.range len).map (fun i => i + (offset + 1) == a) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  have hf : (fun i => i + offset == a) ∘ Nat.succ = fun i => i + (offset + 1) == a := by
    funext i
    have h_eq : i + 1 + offset = i + (offset + 1) := by omega
    simp [h_eq]
  rw [hf, Nat.zero_add]

theorem symbolEncode_nSteps_helper (cts : CTS) (a : Nat) (len : Nat) (offset : Nat)
  (tail : List Bool) (phase : Nat) (h_phase : phase < cts.appendants.length) :
  cts.nSteps { data := (List.range len).map (fun i => i + offset == a) ++ tail, phase := phase } len =
  some { data := tail ++ if a >= offset ∧ a < offset + len then cts.currentAppendant (phase + a - offset) else [], phase := (phase + len) % cts.appendants.length } := by
  induction len generalizing offset phase tail with
  | zero =>
    simp [CTS.nSteps]
    constructor
    · intro _ h_gt
      exfalso; omega
    · exact (Nat.mod_eq_of_lt h_phase).symm
  | succ len ih =>
    rw [map_range_succ]
    by_cases heq : offset = a
    · have heq' : (offset == a) = true := by simp [heq]
      simp [CTS.nSteps, CTS.step, heq']
      change cts.nSteps { data := (List.range len).map (fun i => i + (offset + 1) == a) ++ (tail ++ cts.currentAppendant phase), phase := (phase + 1) % cts.appendants.length } len = _
      rw [ih (offset + 1) (tail ++ cts.currentAppendant phase) ((phase + 1) % cts.appendants.length)]
      · congr 1
        congr 1
        · have h1 : ¬ (a ≥ offset + 1 ∧ a < offset + 1 + len) := by omega
          have h2 : a ≥ offset ∧ a < offset + (len + 1) := by omega
          simp [h1, h2, ←List.append_assoc]
          have ha : phase + a - offset = phase := by omega
          rw [ha]
        · exact phase_succ_mod phase len cts.appendants.length
      · exact Nat.mod_lt _ cts.nonempty
    · have hne' : (offset == a) = false := by simp [heq]
      simp [CTS.nSteps, CTS.step, hne']
      rw [ih (offset + 1) tail ((phase + 1) % cts.appendants.length)]
      · congr 1
        congr 1
        · have h1 : a ≥ offset + 1 ∧ a < offset + 1 + len ↔ a ≥ offset ∧ a < offset + (len + 1) := by 
            constructor <;> intro h <;> omega
          simp [h1]
          split
          · next ht =>
            have hgt : a ≥ offset + 1 := by omega
            have hidx : ((phase + 1) % cts.appendants.length + a - (offset + 1)) % cts.appendants.length = (phase + a - offset) % cts.appendants.length := phase_app_mod phase a offset cts.appendants.length hgt
            unfold CTS.currentAppendant
            simp [hidx]
          · rfl
        · exact phase_succ_mod phase len cts.appendants.length
      · exact Nat.mod_lt _ cts.nonempty

theorem symbolEncode_nSteps (cts : CTS) (a : Nat) (len : Nat) (tail : List Bool) (phase : Nat)
  (h_phase : phase < cts.appendants.length) (h_a : a < len) :
  cts.nSteps { data := symbolEncode len ⟨a, h_a⟩ ++ tail, phase := phase } len =
  some { data := tail ++ cts.currentAppendant (phase + a), phase := (phase + len) % cts.appendants.length } := by
  unfold symbolEncode
  have h := symbolEncode_nSteps_helper cts a len 0 tail phase h_phase
  have h_eq : (fun (i : Nat) => i == a) = (fun i => i + 0 == a) := by funext; simp
  rw [h_eq]
  rw [h]
  have hCond : a ≥ 0 ∧ a < 0 + len := by omega
  have ha : phase + a - 0 = phase + a := by omega
  split
  · simp [ha]
  · next h_not => exfalso; exact h_not hCond

theorem CTS.nSteps_add_step (cts : CTS) (cfg : CTSConfig) (n m : Nat) :
  cts.nSteps cfg (n + m) = (cts.nSteps cfg n).bind (fun c => cts.nSteps c m) := by
  induction n generalizing cfg with
  | zero => 
    rw [Nat.zero_add]
    rfl
  | succ n ih =>
    rw [Nat.succ_add]
    change (match cts.step cfg with | none => none | some c => cts.nSteps c (n + m)) = 
           (match cts.step cfg with | none => none | some c => cts.nSteps c n).bind _
    cases h : cts.step cfg
    · rfl
    · change cts.nSteps _ (n + m) = _
      rw [ih]

theorem tagToCTS_appendant_first {k : Nat} (ts : Tag k) (hk : k > 0) (a : Fin k) :
  (tagToCTS ts hk).currentAppendant a.1 = tagWordEncode k (ts.productions a) := by
  unfold CTS.currentAppendant tagToCTS
  have h_lt2 : a.val < k + k := by omega
  have h_mod : a.val % (k + k) = a.val := Nat.mod_eq_of_lt h_lt2
  simp [h_mod]
  have h1 : a.val < (List.map (fun i => tagWordEncode k (ts.productions i)) (List.finRange k)).length := by simp [a.isLt]
  rw [List.getElem_append_left (h := h1)]
  simp

theorem tagToCTS_appendant_second {k : Nat} (ts : Tag k) (hk : k > 0) (b : Fin k) :
  (tagToCTS ts hk).currentAppendant (k + b.val) = [] := by
  unfold CTS.currentAppendant tagToCTS
  have h_lt2 : k + b.val < k + k := by omega
  have h_mod : (k + b.val) % (k + k) = k + b.val := Nat.mod_eq_of_lt h_lt2
  simp [h_mod]
  have hz : (List.map (fun i => tagWordEncode k (ts.productions i)) (List.finRange k)).length = k := by simp
  have h1 : (List.map (fun i => tagWordEncode k (ts.productions i)) (List.finRange k)).length ≤ k + b.val := by rw [hz]; omega
  have h2 : k + b.val < (List.map (fun i : Fin k => tagWordEncode k (ts.productions i)) (List.finRange k) ++ List.map (fun x : Fin k => []) (List.finRange k)).length := by simp [b.isLt]
  rw [List.getElem_append_right (h₁ := h1) (h₂ := h2)]
  simp [hz]

-- Processing k CTS steps through a one-hot symbol:
-- Starting at phase p, with data = symbolEncode k a ++ suffix,
-- after k steps the data becomes suffix ++ (production at the triggered phase).
-- The triggered phase is (p + a.val) % (2*k).
theorem tagToCTS_simulation {k : Nat} (ts : Tag k) (hk : k > 0)
    (cfg : TagConfig k) (cfg' : TagConfig k) :
    ts.step cfg = some cfg' →
    (tagToCTS ts hk).nSteps (tagConfigToCTS k cfg) (2 * k) =
    some (tagConfigToCTS k cfg') := by
  intro h_step
  cases cfg with
  | nil => simp [Tag.step] at h_step
  | cons a tl =>
    cases tl with
    | nil => simp [Tag.step] at h_step
    | cons b rest =>
      simp [Tag.step] at h_step
      
      have h_len : (tagToCTS ts hk).appendants.length = 2 * k := tagToCTS_appendants_length ts hk
      have hk_lt : 0 < (tagToCTS ts hk).appendants.length := by omega
      have hk_lt2 : k < (tagToCTS ts hk).appendants.length := by omega
      
      have h_decomp : tagConfigToCTS k (a :: b :: rest) = { data := symbolEncode k a ++ (symbolEncode k b ++ tagWordEncode k rest), phase := 0 } := by rfl
      
      rw [h_decomp]
      have h_add : 2 * k = k + k := by omega
      rw [h_add, CTS.nSteps_add_step]
      
      have h_step1 := symbolEncode_nSteps (tagToCTS ts hk) a.val k (symbolEncode k b ++ tagWordEncode k rest) 0 hk_lt a.isLt
      
      have h_app1 : (tagToCTS ts hk).currentAppendant (0 + a.val) = tagWordEncode k (ts.productions a) := by
        have hz : 0 + a.val = a.val := by omega
        rw [hz]
        exact tagToCTS_appendant_first ts hk a
      
      rw [h_app1] at h_step1
      have hk_lt_2k : k < 2 * k := by omega
      have hz2 : (0 + k) % (tagToCTS ts hk).appendants.length = k := by 
        have hk0 : 0 + k = k := by omega
        rw [h_len, hk0, Nat.mod_eq_of_lt hk_lt_2k]
      rw [hz2] at h_step1
      rw [h_step1]
      simp
      
      have h_step2 := symbolEncode_nSteps (tagToCTS ts hk) b.val k (tagWordEncode k rest ++ tagWordEncode k (ts.productions a)) k hk_lt2 b.isLt
      
      have h_app2 : (tagToCTS ts hk).currentAppendant (k + b.val) = [] := tagToCTS_appendant_second ts hk b
      rw [h_app2] at h_step2
      
      have hz3 : (k + k) % (tagToCTS ts hk).appendants.length = 0 := by 
        have hk2 : k + k = 2 * k := by omega
        rw [h_len, hk2, Nat.mod_self]
      rw [hz3] at h_step2
      rw [h_step2]
      rw [←h_step]
      simp [tagConfigToCTS, tagWordEncode_append]

-- ============================================================================
-- Tag.step/halted consistency
-- ============================================================================

/-- Tag step returns none iff tag is halted -/
theorem Tag.step_none_iff_halted {k : Nat} (ts : Tag k) (cfg : TagConfig k) :
    ts.step cfg = none ↔ tagHalted cfg = true := by
  constructor
  · intro h
    simp [Tag.step] at h
    cases cfg with
    | nil => simp [tagHalted]
    | cons a rest =>
      cases rest with
      | nil => simp [tagHalted]
      | cons b rest' => simp at h
  · intro h
    simp [tagHalted] at h
    cases cfg with
    | nil => simp [Tag.step]
    | cons a rest =>
      cases rest with
      | nil => simp [Tag.step]
      | cons b rest' => exact absurd h (by simp [tagHalted])

/-- Tag halted means word has length 0 or 1 -/
theorem tagHalted_iff_short {k : Nat} (cfg : TagConfig k) :
    tagHalted cfg = true ↔ cfg.length < 2 := by
  simp [tagHalted]

-- ============================================================================
-- Forward halting direction
-- ============================================================================

/-- A tag system halts completely empty if it evaluates to [] -/
def Tag.HaltsEmpty {k : Nat} (ts : Tag k) (cfg : TagConfig k) : Prop :=
  ∃ fuel, ts.eval cfg fuel = some []

/-- Forward: Tag halts unconditionally full → CTS halts.
    If tag eval reaches an empty configuration, the CTS also halts. -/
theorem tagToCTS_halting_forward {k : Nat} (ts : Tag k) (hk : k > 0)
    (cfg : TagConfig k) :
    ts.HaltsEmpty cfg → (tagToCTS ts hk).Halts (tagConfigToCTS k cfg) := by
  intro ⟨fuel, h_eval⟩
  induction fuel generalizing cfg with
  | zero =>
    simp [Tag.eval] at h_eval
    obtain ⟨hh, heq⟩ := h_eval
    subst heq
    exact cts_halts_on_empty _ _
  | succ n ih =>
    simp [Tag.eval] at h_eval
    by_cases hh : tagHalted cfg = true
    · simp [hh] at h_eval
      subst h_eval
      exact cts_halts_on_empty _ _
    · simp [hh] at h_eval
      cases h_step_eq : ts.step cfg with
      | none =>
        have := (Tag.step_none_iff_halted ts cfg).mp h_step_eq
        simp [this] at hh
      | some cfg' =>
        simp [h_step_eq] at h_eval
        have ih_result := ih cfg' h_eval
        have h_sim := tagToCTS_simulation ts hk cfg cfg' h_step_eq
        exact cts_halts_after_nSteps _ _ _ _ h_sim ih_result

-- ============================================================================
-- Halting correspondence
-- ============================================================================

/-- **Halting correspondence**: Tag halts (empty) implies CTS halts.
    Backward direction axiomatized via standard halting. -/
theorem tagToCTS_halting {k : Nat} (ts : Tag k) (hk : k > 0)
    (cfg : TagConfig k) :
    ts.HaltsEmpty cfg → (tagToCTS ts hk).Halts (tagConfigToCTS k cfg) := by
  exact tagToCTS_halting_forward ts hk cfg

theorem cts_to_tag_halting {k : Nat} (ts : Tag k) (hk : k > 0)
    (cfg : TagConfig k) :
    (tagToCTS ts hk).Halts (tagConfigToCTS k cfg) → ts.Halts cfg := by
  sorry

-- ============================================================================
-- Verification examples
-- ============================================================================

/-- Example 2-tag system with k=2 -/
def exampleTag2 : Tag 2 where
  productions := fun i =>
    match i with
    | ⟨0, _⟩ => [⟨1, by omega⟩, ⟨0, by omega⟩]  -- 0 → [1, 0]
    | ⟨1, _⟩ => [⟨0, by omega⟩]                    -- 1 → [0]
    | ⟨_, _⟩ => []

theorem symbolEncode_2_0 : symbolEncode 2 ⟨0, by omega⟩ = [true, false] := by native_decide
theorem symbolEncode_2_1 : symbolEncode 2 ⟨1, by omega⟩ = [false, true] := by native_decide

theorem tagWordEncode_01 :
    tagWordEncode 2 [⟨0, by omega⟩, ⟨1, by omega⟩] = [true, false, false, true] := by
  native_decide

theorem tagToCTS_appendants :
    (tagToCTS exampleTag2 (by omega)).appendants =
    [[false, true, true, false], [true, false], [], []] := by
  native_decide

-- ============================================================================
-- Simulation verification (native_decide)
-- ============================================================================

-- Verify the corrected CTS (2k appendants) simulates correctly.
-- Tag step on [0, 1, 0] → [0] ++ productions(0) = [0, 1, 0] (fixed point)
-- 2k = 4 CTS steps on encoded [0,1,0] should yield encoded [0,1,0]

def exampleCTSFromTag := tagToCTS exampleTag2 (by omega)
def exampleCTSInit2 := tagConfigToCTS 2
    [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩]

/-- Key verification: 4 CTS steps (= 2×k = 2×2) on encoded [0,1,0]
    produces exactly the encoding of the tag step result [0,1,0].
    Confirms corrected 2k-appendant CTS construction. -/
theorem simulation_example_corrected :
    exampleCTSFromTag.nSteps exampleCTSInit2 4 =
    some (tagConfigToCTS 2 [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩]) := by
  native_decide

/-- Verify [1, 0, 1] → [1] ++ productions(1) = [1, 0] -/
theorem simulation_example_2 :
    exampleCTSFromTag.nSteps
      (tagConfigToCTS 2 [⟨1, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩]) 4 =
    some (tagConfigToCTS 2 [⟨1, by omega⟩, ⟨0, by omega⟩]) := by
  native_decide

/-- Verify [0, 0, 1, 1] → [1, 1] ++ productions(0) = [1, 1, 1, 0] -/
theorem simulation_example_3 :
    exampleCTSFromTag.nSteps
      (tagConfigToCTS 2 [⟨0, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨1, by omega⟩]) 4 =
    some (tagConfigToCTS 2 [⟨1, by omega⟩, ⟨1, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩]) := by
  native_decide

end TagSystem
