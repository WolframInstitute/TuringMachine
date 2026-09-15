/-
  BiTM.CTSToSystem5

  Smith's cyclic-tag-system to System 5 encoder, a transcription of the
  Perl program `cy2s5.pl` (TM23Proof.pdf p. 28-29).  The working string is
  doubled bit by bit into a bag of integers, and each appendant is doubled
  into a block of four System 5 rules.

  Contents:
    * `ctsConfigToSystem5BagAux`, `ctsConfigToSystem5Bag`: the working
      string as a System 5 bag.
    * `counterAfterWorkingString`: the value of the Perl counter `i` after
      the working-string loop.
    * `encodeAppendant`, `processCycle`, `nCycles`: one appendant, one pass
      over all appendants, and n such passes, as System 5 rules.
    * `ctsRulesToSystem5Rules`, `ctsToSystem5`: the top-level encoder.
    * Structural lemmas: lengths, lower bounds, Nodup, the pair relation
      r1 = r2.map (+ 2) between the two rules of an appendant, and the
      characterisation of when the encoded System 5 config can step.

  Fidelity notes:
    * `cy2s5.pl` emits FOUR rules per appendant (`$temp`, `$temp2`, "", ""),
      not three; the Perl source is on PDF p. 28-29.
    * `cy2s5.pl` has no notion of CTS phase: it always starts the rule stream
      at appendant 0.  `ctsRulesToSystem5Rules` rotates the appendant list by
      `cfg.phase % |appendants|`, the index `CTS.currentAppendant` reads, so
      the rule stream starts at the appendant the next `CTS.step` will use.
      At phase 0 the rotation is the identity and the output is exactly the
      Perl's (`ctsRulesToSystem5Rules_phase_zero`).
    * The argument `n` here counts FULL cycles over `cts.appendants`, so
      `nCycles` emits `4 * |appendants| * n` rules.  The `n` of `cy2s5.pl`
      counts appendant emissions and yields `4 * n` rules.  The two agree
      under `cy2s5_n = lean_n * |appendants|`; budgets quoted from the PDF
      must be rescaled accordingly.
-/

import TagSystem.Basic
import BiTM.System5

namespace BiTM

open TagSystem

/-! ## The working string as a bag -/

/-- Per-bit doubling encoder for the CTS working string into System 5 bag
    positions, the `while($temp ne '')` loop of `cy2s5.pl`.

    For each bit of the data, starting at counter `i = 1`:
    * `true` ('1'): emit `[i, i+2, i+3, i+5]`, advance the counter by 6.
    * `false` ('0'): emit `[i, i+1, i+2, i+3]`, advance the counter by 4. -/
def ctsConfigToSystem5BagAux : List Bool → Int → List Int
  | [], _ => []
  | true :: rest, i => i :: (i + 2) :: (i + 3) :: (i + 5) ::
                       ctsConfigToSystem5BagAux rest (i + 6)
  | false :: rest, i => i :: (i + 1) :: (i + 2) :: (i + 3) ::
                        ctsConfigToSystem5BagAux rest (i + 4)

/-- Empty data encodes to the empty bag at any counter. -/
@[simp] theorem ctsConfigToSystem5BagAux_nil (i : Int) :
    ctsConfigToSystem5BagAux [] i = [] := rfl

/-- The System 5 bag of a CTS configuration: the bag encoder started at 1. -/
def ctsConfigToSystem5Bag (cfg : CTSConfig) : List Int :=
  ctsConfigToSystem5BagAux cfg.data 1

/-- PDF p. 28 `test1.cy` bag: working string 11011. -/
example :
    ctsConfigToSystem5Bag { data := [true, true, false, true, true], phase := 0 }
      = [1, 3, 4, 6, 7, 9, 10, 12, 13, 14, 15, 16, 17, 19, 20, 22, 23, 25, 26, 28] := by
  decide

/-- PDF p. 29 `cy2s5.pl 3 01 1 10` bag: working string 01. -/
example :
    ctsConfigToSystem5Bag { data := [false, true], phase := 0 }
      = [1, 2, 3, 4, 5, 7, 8, 10] := by
  decide

/-! ## The counter -/

/-- The value of the Perl counter `i` after the working-string loop.
    Starts at 1 and advances by 4 per `false` bit, 6 per `true` bit. -/
def counterAfterWorkingString (data : List Bool) : Int :=
  data.foldl (fun acc b => acc + if b then 6 else 4) 1

/-- The counter fold commutes with a shift of its starting value. -/
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

/-- A leading `false` bit costs 4 counter units. -/
theorem counterAfterWorkingString_cons_false (rest : List Bool) :
    counterAfterWorkingString (false :: rest) = counterAfterWorkingString rest + 4 := by
  unfold counterAfterWorkingString
  show rest.foldl (fun acc b => acc + if b then (6 : Int) else 4) 5
     = rest.foldl (fun acc b => acc + if b then (6 : Int) else 4) 1 + 4
  exact foldl_counter_init_shift rest 1 4

/-- A leading `true` bit costs 6 counter units. -/
theorem counterAfterWorkingString_cons_true (rest : List Bool) :
    counterAfterWorkingString (true :: rest) = counterAfterWorkingString rest + 6 := by
  unfold counterAfterWorkingString
  show rest.foldl (fun acc b => acc + if b then (6 : Int) else 4) 7
     = rest.foldl (fun acc b => acc + if b then (6 : Int) else 4) 1 + 6
  exact foldl_counter_init_shift rest 1 6

/-- The counter never drops below its starting value 1. -/
theorem counterAfterWorkingString_ge_one (data : List Bool) :
    counterAfterWorkingString data ≥ 1 := by
  induction data with
  | nil => unfold counterAfterWorkingString; simp
  | cons head tail ih =>
    cases head with
    | true => rw [counterAfterWorkingString_cons_true]; omega
    | false => rw [counterAfterWorkingString_cons_false]; omega

/-! ## Appendants as System 5 rules -/

/-- Encode one CTS appendant as a pair of System 5 rules together with the
    post-encoding counter value, per `cy2s5.pl` (PDF p. 28):
    * `false` ('0'): r1 gets `i+2, i+3`; r2 gets `i, i+1`; the counter += 4.
    * `true`  ('1'): r1 gets `i+2, i+5`; r2 gets `i, i+3`; the counter += 6.

    Returns `(firstRule, secondRule, newCounter)`. -/
def encodeAppendant : List Bool → Int → List Int × List Int × Int
  | [], i => ([], [], i)
  | true :: rest, i =>
      let (r1, r2, i') := encodeAppendant rest (i + 6)
      ((i + 2) :: (i + 5) :: r1, i :: (i + 3) :: r2, i')
  | false :: rest, i =>
      let (r1, r2, i') := encodeAppendant rest (i + 4)
      ((i + 2) :: (i + 3) :: r1, i :: (i + 1) :: r2, i')

/-- One pass over all appendants.  `cy2s5.pl` prints
    `$temp," ",$temp2,' "" ""'` per appendant, so each appendant emits FOUR
    System 5 rules: r1, r2, and two empty rules. -/
def processCycle : List (List Bool) → Int → List (List Int) × Int
  | [], i => ([], i)
  | rule :: rest, i =>
      let (r1, r2, i') := encodeAppendant rule i
      let (restRules, i'') := processCycle rest i'
      (r1 :: r2 :: [] :: [] :: restRules, i'')

/-- No appendants means no rules and an unchanged counter. -/
@[simp] theorem processCycle_nil_full (i : Int) :
    processCycle [] i = ([], i) := rfl

/-- Cons unfolding of `processCycle`: one appendant contributes its two
    rules and two empty rules, and threads the counter. -/
theorem processCycle_cons (a : List Bool) (rest : List (List Bool)) (i : Int) :
    processCycle (a :: rest) i
      = ((encodeAppendant a i).1 :: (encodeAppendant a i).2.1 :: [] :: [] ::
           (processCycle rest (encodeAppendant a i).2.2).1,
         (processCycle rest (encodeAppendant a i).2.2).2) := rfl

/-- Repeat `processCycle` for `n` full cycles, threading the counter. -/
def nCycles (rules : List (List Bool)) : Nat → Int → List (List Int)
  | 0, _ => []
  | k + 1, i =>
      let (cycle, i') := processCycle rules i
      cycle ++ nCycles rules k i'

/-- Zero cycles produce no rules. -/
@[simp] theorem nCycles_zero (rules : List (List Bool)) (i : Int) :
    nCycles rules 0 i = [] := rfl

/-- Successor unfolding of `nCycles`. -/
theorem nCycles_succ (rules : List (List Bool)) (k : Nat) (i : Int) :
    nCycles rules (k + 1) i
    = (processCycle rules i).fst ++ nCycles rules k (processCycle rules i).snd := rfl

/-- One cycle is exactly one `processCycle` pass. -/
theorem nCycles_one (rules : List (List Bool)) (i : Int) :
    nCycles rules 1 i = (processCycle rules i).fst := by
  rw [show (1 : Nat) = 0 + 1 from rfl, nCycles_succ, nCycles_zero, List.append_nil]

/-! ## The top-level encoder -/

/-- `List.rotateLeft` does not change the length. -/
theorem length_rotateLeft {alpha : Type} (l : List alpha) (k : Nat) :
    (l.rotateLeft k).length = l.length := by
  show (if l.length ≤ 1 then l
        else List.drop (k % l.length) l ++ List.take (k % l.length) l).length
       = l.length
  by_cases h : l.length ≤ 1
  · rw [if_pos h]
  · rw [if_neg h]
    have h_pos : 0 < l.length := by omega
    have h_mod := Nat.mod_lt k h_pos
    simp only [List.length_append, List.length_drop, List.length_take]
    omega

/-- The appendant list of a CTS configuration, rotated so that the appendant
    `CTS.currentAppendant` would read at `cfg.phase` comes first. -/
def appendantsFromPhase (cts : CTS) (cfg : CTSConfig) : List (List Bool) :=
  cts.appendants.rotateLeft (cfg.phase % cts.appendants.length)

/-- Rotating the appendant list does not change its length. -/
@[simp] theorem appendantsFromPhase_length (cts : CTS) (cfg : CTSConfig) :
    (appendantsFromPhase cts cfg).length = cts.appendants.length :=
  length_rotateLeft _ _

/-- At phase 0 no rotation happens, which is the case `cy2s5.pl` implements. -/
theorem appendantsFromPhase_zero (cts : CTS) (cfg : CTSConfig) (h : cfg.phase = 0) :
    appendantsFromPhase cts cfg = cts.appendants := by
  unfold appendantsFromPhase
  rw [h, Nat.zero_mod, List.rotateLeft_zero]

/-- The System 5 rule stream of a CTS: `n` full cycles over the appendants
    starting at the current phase, with the rule counter starting at
    `counterAfterWorkingString + 2`. -/
def ctsRulesToSystem5Rules (cts : CTS) (cfg : CTSConfig) (n : Nat) : List (List Int) :=
  nCycles (appendantsFromPhase cts cfg) n (counterAfterWorkingString cfg.data + 2)

/-- At phase 0 the rule stream is exactly what `cy2s5.pl` prints. -/
theorem ctsRulesToSystem5Rules_phase_zero
    (cts : CTS) (cfg : CTSConfig) (n : Nat) (h : cfg.phase = 0) :
    ctsRulesToSystem5Rules cts cfg n
      = nCycles cts.appendants n (counterAfterWorkingString cfg.data + 2) := by
  unfold ctsRulesToSystem5Rules
  rw [appendantsFromPhase_zero cts cfg h]

/-- The CTS to System 5 encoder: working string as bag, `n` cycles of
    appendants as rules. -/
def ctsToSystem5 (cts : CTS) (cfg : CTSConfig) (n : Nat) : System5Config :=
  { bag := ctsConfigToSystem5Bag cfg
    rules := ctsRulesToSystem5Rules cts cfg n }

/-- PDF p. 29 `cy2s5.pl 3 01 1 10` rules: the first cycle over the
    appendants "1" and "10". -/
example :
    nCycles [[true], [true, false]] 1
        (counterAfterWorkingString [false, true] + 2)
      = [[15, 18], [13, 16], [], [], [21, 24, 27, 28], [19, 22, 25, 26], [], []] := by
  decide

/-- One cycle of `ctsRulesToSystem5Rules` is one `processCycle` pass over the
    phase-rotated appendant list. -/
theorem ctsRulesToSystem5Rules_one (cts : CTS) (cfg : CTSConfig) :
    ctsRulesToSystem5Rules cts cfg 1
    = (processCycle (appendantsFromPhase cts cfg)
        (counterAfterWorkingString cfg.data + 2)).fst := by
  unfold ctsRulesToSystem5Rules
  exact nCycles_one (appendantsFromPhase cts cfg)
    (counterAfterWorkingString cfg.data + 2)

/-- Rules projection of the encoder. -/
@[simp] theorem ctsToSystem5_rules_eq (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    (ctsToSystem5 cts cfg n).rules = ctsRulesToSystem5Rules cts cfg n := rfl

/-- Bag projection of the encoder. -/
@[simp] theorem ctsToSystem5_bag_eq (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    (ctsToSystem5 cts cfg n).bag = ctsConfigToSystem5Bag cfg := rfl

/-! ## Lengths -/

/-- Four bag entries per bit of the working string. -/
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

/-- Four bag entries per bit, at the top level. -/
theorem ctsConfigToSystem5Bag_length (cfg : CTSConfig) :
    (ctsConfigToSystem5Bag cfg).length = 4 * cfg.data.length :=
  ctsConfigToSystem5BagAux_length cfg.data 1

/-- Four System 5 rules per appendant in one cycle. -/
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

/-- `n` cycles emit `4 * |appendants| * n` rules. -/
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

/-- Rule count of the top-level encoder; the rotation does not change it. -/
theorem ctsRulesToSystem5Rules_length (cts : CTS) (cfg : CTSConfig) (n : Nat) :
    (ctsRulesToSystem5Rules cts cfg n).length = 4 * cts.appendants.length * n := by
  unfold ctsRulesToSystem5Rules
  rw [nCycles_length, appendantsFromPhase_length]

/-- Two rule entries per bit of an appendant, first rule. -/
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

/-- Two rule entries per bit of an appendant, second rule. -/
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

/-! ## Lower bounds and non-emptiness -/

/-- Every bag entry is at least the starting counter. -/
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

/-- Every entry of the encoded bag is at least 1. -/
theorem ctsConfigToSystem5Bag_ge_one (cfg : CTSConfig) :
    ∀ x ∈ ctsConfigToSystem5Bag cfg, x ≥ 1 :=
  ctsConfigToSystem5BagAux_ge cfg.data 1

/-- Every entry of the first rule of an appendant is at least the counter. -/
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

/-- Every entry of the second rule of an appendant is at least the counter. -/
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

/-- The head of the encoded bag is 1, for a non-halted configuration. -/
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

/-- 1 is in the encoded bag, for a non-halted configuration. -/
theorem ctsConfigToSystem5Bag_one_mem
    (cfg : CTSConfig) (h : cfg.data ≠ []) :
    (1 : Int) ∈ ctsConfigToSystem5Bag cfg := by
  obtain ⟨rest, h_eq⟩ := ctsConfigToSystem5Bag_head_eq_one cfg h
  rw [h_eq]
  exact List.mem_cons.mpr (Or.inl rfl)

/-- The encoded bag of a non-halted configuration is non-empty. -/
theorem ctsConfigToSystem5Bag_nonempty
    (cfg : CTSConfig) (h : cfg.data ≠ []) :
    ctsConfigToSystem5Bag cfg ≠ [] := by
  obtain ⟨rest, h_eq⟩ := ctsConfigToSystem5Bag_head_eq_one cfg h
  rw [h_eq]
  exact List.cons_ne_nil _ _

/-- With at least one cycle the rule stream is non-empty. -/
theorem ctsRulesToSystem5Rules_ne_nil
    (cts : CTS) (cfg : CTSConfig) (N : Nat) (h_N : N ≥ 1) :
    ctsRulesToSystem5Rules cts cfg N ≠ [] := by
  intro h
  have h_len := ctsRulesToSystem5Rules_length cts cfg N
  rw [h, List.length_nil] at h_len
  have h1 : 4 * cts.appendants.length > 0 := Nat.mul_pos (by decide) cts.nonempty
  have h2 : 4 * cts.appendants.length * N > 0 := Nat.mul_pos h1 (by omega)
  omega

/-! ## Nodup -/

/-- The bag encoder produces no duplicates: the counter strictly increases
    between bits, and the four values emitted for one bit are distinct. -/
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

/-- The encoded bag has no duplicates.  This is the invariant under which
    `System5.step` is faithful to `system5.pl`. -/
theorem ctsConfigToSystem5Bag_nodup (cfg : CTSConfig) :
    (ctsConfigToSystem5Bag cfg).Nodup :=
  ctsConfigToSystem5BagAux_nodup cfg.data 1

/-- The first rule of an appendant has no duplicates. -/
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

/-- The second rule of an appendant has no duplicates. -/
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

/-! ## The rule pair and its cancellation -/

/-- The empty appendant encodes to two empty rules and an unchanged counter. -/
theorem encodeAppendant_nil (i : Int) :
    encodeAppendant [] i = ([], [], i) := by rfl

/-- The two rules of an appendant are related by a shift of 2: this is what
    makes the second rule cancel the first when it surfaces two steps later. -/
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

/-- The two rules of an appendant have the same length. -/
theorem encodeAppendant_r1_r2_same_length (data : List Bool) (i : Int) :
    (encodeAppendant data i).1.length = (encodeAppendant data i).2.1.length := by
  rw [encodeAppendant_r1_eq_r2_add_2]
  simp

/-- Increment then decrement is the identity on a list of integers. -/
theorem List_Int_inc_dec_cancel (r : List Int) :
    (r.map (· + 1)).map (· - 1) = r := by
  induction r with
  | nil => rfl
  | cons x xs ih =>
    show (x + 1 - 1) :: ((xs.map (· + 1)).map (· - 1)) = x :: xs
    rw [ih]
    congr 1
    omega

/-- The first rule, carried through one increment and one decrement, is still
    the second rule shifted by 2.  This is the algebra behind the pair
    cancellation inside `xorMerge` at pop time. -/
theorem encodeAppendant_cancellation_algebra (data : List Bool) (i : Int) :
    ((encodeAppendant data i).1.map (· + 1)).map (· - 1)
      = (encodeAppendant data i).2.1.map (· + 2) := by
  rw [List_Int_inc_dec_cancel]
  exact encodeAppendant_r1_eq_r2_add_2 data i

/-- The first two rules emitted by a cycle are a cancelling pair. -/
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

/-! ## Decrement bookkeeping -/

/-- 0 surfaces in the decremented bag exactly when 1 was in the bag. -/
theorem zero_mem_decrement_iff_one_mem (bag : List Int) :
    (0 : Int) ∈ bag.map (· - 1) ↔ (1 : Int) ∈ bag := by
  rw [List.mem_map]
  constructor
  · rintro ⟨a, h_a, h_eq⟩
    have h_a_one : a = 1 := by omega
    rw [← h_a_one]; exact h_a
  · intro h
    exact ⟨1, h, by omega⟩

/-- A member other than 1 survives a decrement followed by erasing 0. -/
theorem mem_imp_pred_in_dec_erase
    (xs : List Int) (x : Int) (h_mem : x ∈ xs) (h_ne : x ≠ 1) :
    (x - 1) ∈ (xs.map (· - 1)).erase 0 := by
  have h_dec : (x - 1) ∈ xs.map (· - 1) := List.mem_map.mpr ⟨x, h_mem, rfl⟩
  rw [List.mem_erase_of_ne (a := x - 1) (l := xs.map (· - 1)) (b := 0) (by omega)]
  exact h_dec

/-- The encoded bag of a non-halted configuration triggers a pop on the
    first step. -/
theorem ctsConfigToSystem5Bag_zero_in_decrement
    (cfg : CTSConfig) (h : cfg.data ≠ []) :
    (0 : Int) ∈ (ctsConfigToSystem5Bag cfg).map (· - 1) :=
  (zero_mem_decrement_iff_one_mem _).mpr (ctsConfigToSystem5Bag_one_mem cfg h)

/-! ## Emptiness and the first step -/

/-- The bag encoder returns the empty bag only on empty data. -/
theorem ctsConfigToSystem5BagAux_empty_iff (data : List Bool) (i : Int) :
    ctsConfigToSystem5BagAux data i = [] ↔ data = [] := by
  cases data with
  | nil => simp [ctsConfigToSystem5BagAux]
  | cons head rest =>
    cases head with
    | true => simp [ctsConfigToSystem5BagAux]
    | false => simp [ctsConfigToSystem5BagAux]

/-- Empty data encodes to the empty bag. -/
theorem ctsConfigToSystem5Bag_emptyData_eq_nil
    (cfg : CTSConfig) (h : cfg.data = []) :
    ctsConfigToSystem5Bag cfg = [] := by
  unfold ctsConfigToSystem5Bag
  rw [h]
  rfl

/-- The encoded bag is empty exactly on empty data. -/
theorem ctsConfigToSystem5Bag_eq_nil_iff (cfg : CTSConfig) :
    ctsConfigToSystem5Bag cfg = [] ↔ cfg.data = [] := by
  refine ⟨?_, ctsConfigToSystem5Bag_emptyData_eq_nil cfg⟩
  intro h
  rcases (Decidable.em (cfg.data = [])) with h_eq | h_ne
  · exact h_eq
  · exact absurd h (ctsConfigToSystem5Bag_nonempty cfg h_ne)

/-- `ctsHalted` is decidable emptiness of the working string. -/
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

/-- The encoded bag is empty exactly when the CTS configuration is halted. -/
theorem ctsConfigToSystem5Bag_empty_iff_halted (cfg : CTSConfig) :
    ctsConfigToSystem5Bag cfg = [] ↔ ctsHalted cfg = true := by
  unfold ctsConfigToSystem5Bag
  rw [ctsConfigToSystem5BagAux_empty_iff]
  cases h_data : cfg.data <;> simp [ctsHalted, List.isEmpty, h_data]

/-- The encoded System 5 config fails to step exactly when the working
    string is empty or no cycles were requested. -/
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

/-- The encoded System 5 config fails to step exactly when the CTS
    configuration is halted or no cycles were requested. -/
theorem ctsToSystem5_step_none_iff_halted_or_N_zero
    (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    System5.step (ctsToSystem5 cts cfg N) = none ↔ ctsHalted cfg = true ∨ N = 0 := by
  rw [ctsToSystem5_step_none_iff_data_empty_or_N_zero,
      ← ctsHalted_true_iff_data_eq_nil]

/-! ## Well-formedness of the encoder output -/

/-- The encoded System 5 bag has no duplicates.  This is the invariant under
    which `System5.step` is faithful to `system5.pl`. -/
theorem ctsToSystem5_bag_nodup (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    (ctsToSystem5 cts cfg N).bag.Nodup :=
  ctsConfigToSystem5Bag_nodup cfg

/-- Every entry of the encoded System 5 bag is at least 1. -/
theorem ctsToSystem5_bag_ge_one (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ∀ x ∈ (ctsToSystem5 cts cfg N).bag, x ≥ 1 :=
  ctsConfigToSystem5Bag_ge_one cfg

/-- Encoding an appendant never lowers the counter. -/
theorem encodeAppendant_counter_ge (rule : List Bool) (i : Int) :
    (encodeAppendant rule i).2.2 ≥ i := by
  induction rule generalizing i with
  | nil => exact Int.le_refl i
  | cons head tail ih =>
    cases head with
    | true =>
      show (encodeAppendant tail (i + 6)).2.2 ≥ i
      have := ih (i + 6); omega
    | false =>
      show (encodeAppendant tail (i + 4)).2.2 ≥ i
      have := ih (i + 4); omega

/-- One cycle never lowers the counter. -/
theorem processCycle_counter_ge (apps : List (List Bool)) (i : Int) :
    (processCycle apps i).2 ≥ i := by
  induction apps generalizing i with
  | nil => exact Int.le_refl i
  | cons a rest ih =>
    rw [processCycle_cons]
    have h1 := encodeAppendant_counter_ge a i
    have h2 := ih (encodeAppendant a i).2.2
    omega

/-- Every rule emitted by one cycle has no duplicates. -/
theorem processCycle_rules_nodup (apps : List (List Bool)) (i : Int) :
    ∀ r ∈ (processCycle apps i).1, r.Nodup := by
  induction apps generalizing i with
  | nil => intro r h; cases h
  | cons a rest ih =>
    intro r h
    rw [processCycle_cons] at h
    simp only [List.mem_cons] at h
    rcases h with rfl | rfl | rfl | rfl | h
    · exact encodeAppendant_r1_nodup a i
    · exact encodeAppendant_r2_nodup a i
    · exact List.nodup_nil
    · exact List.nodup_nil
    · exact ih (encodeAppendant a i).2.2 r h

/-- Every entry of every rule emitted by one cycle is at least the counter the
    cycle started from. -/
theorem processCycle_rules_ge (apps : List (List Bool)) (i : Int) :
    ∀ r ∈ (processCycle apps i).1, ∀ x ∈ r, x ≥ i := by
  induction apps generalizing i with
  | nil => intro r h; cases h
  | cons a rest ih =>
    intro r h x h_x
    rw [processCycle_cons] at h
    simp only [List.mem_cons] at h
    rcases h with rfl | rfl | rfl | rfl | h
    · exact encodeAppendant_r1_ge a i x h_x
    · exact encodeAppendant_r2_ge a i x h_x
    · cases h_x
    · cases h_x
    · have h_ge := ih (encodeAppendant a i).2.2 r h x h_x
      have := encodeAppendant_counter_ge a i
      omega

/-- Every rule of the `n`-cycle stream has no duplicates. -/
theorem nCycles_rules_nodup (apps : List (List Bool)) (n : Nat) (i : Int) :
    ∀ r ∈ nCycles apps n i, r.Nodup := by
  induction n generalizing i with
  | zero => intro r h; cases h
  | succ k ih =>
    intro r h
    rw [nCycles_succ] at h
    rcases List.mem_append.mp h with h1 | h2
    · exact processCycle_rules_nodup apps i r h1
    · exact ih (processCycle apps i).snd r h2

/-- Every entry of every rule of the `n`-cycle stream is at least the starting
    counter. -/
theorem nCycles_rules_ge (apps : List (List Bool)) (n : Nat) (i : Int) :
    ∀ r ∈ nCycles apps n i, ∀ x ∈ r, x ≥ i := by
  induction n generalizing i with
  | zero => intro r h; cases h
  | succ k ih =>
    intro r h x h_x
    rw [nCycles_succ] at h
    rcases List.mem_append.mp h with h1 | h2
    · exact processCycle_rules_ge apps i r h1 x h_x
    · have h_ge := ih (processCycle apps i).snd r h2 x h_x
      have := processCycle_counter_ge apps i
      omega

/-- Every encoded rule has no duplicates. -/
theorem ctsToSystem5_rules_nodup (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ∀ r ∈ (ctsToSystem5 cts cfg N).rules, r.Nodup :=
  nCycles_rules_nodup _ N _

/-- Every entry of every encoded rule is at least 3: the rule counter starts
    at `counterAfterWorkingString + 2` and never decreases. -/
theorem ctsToSystem5_rules_ge_three (cts : CTS) (cfg : CTSConfig) (N : Nat) :
    ∀ r ∈ (ctsToSystem5 cts cfg N).rules, ∀ x ∈ r, x ≥ 3 := by
  intro r h_r x h_x
  have h_ge := nCycles_rules_ge (appendantsFromPhase cts cfg) N
    (counterAfterWorkingString cfg.data + 2) r h_r x h_x
  have h_c := counterAfterWorkingString_ge_one cfg.data
  omega

end BiTM
