/-
  Smith.Conjecture0

  PLAN.md target T4 (milestone M6): the finite form of Conjecture 0
  (TM23Proof.pdf p. 3-4). For every two-colour cyclic tag system, initial
  word and budget, the wolfram23 run from the initial tape of the composed
  encoders (links A to E) reproduces, at explicit strictly increasing times,
  the working strings of the cyclic tag run, read off the tape by the
  decoder `decodeW23`; the run stays inside the tape until then; and after
  the emulation the head steps onto the cell right of the tape, a 0, in
  state A, which is Smith's exit condition.

  The pieces added here to the links of M1-M5:

    * `Bound5`: the integers of a System 5 configuration grow by at most one
      per step (so the terminal decrements are bounded);
    * `system5ToSystem4_wellFormed`, `system5ToSystem4_last_set`,
      `system5ToSystem4_elem_lt`: the hypotheses `rep3_init` needs of the
      System 4 tape;
    * `repS4_terminal`: once the System 5 rules are exhausted, System 4
      decrements until 1 is in the bag and then exits in state C
      (`repS4_exit` of M3);
    * `RepS4_decode_band`: the decoder of link C below any band that holds
      the bag and lies under the debris;
    * `rep3_exit`, `wolfram23_exit_step`: the exit of System 4 is the exit
      of wolfram23 onto the cell right of the tape, a 0, in state A;
    * `decodeW23`: the decoder of the wolfram23 tape (the XOR of the blocks
      of the leading conglomerate, its parity set below the band, the
      decoder of link C, then `decodeBag` of link B);
    * `conjecture0_finite`.
-/

import Smith.Conjecture3
import Smith.ConjectureFive
import Smith.Wolfram23Bridge

namespace Smith

open TM
open TagSystem
open BiTM
open LState

/-! ## The integers of a System 5 run -/

/-- Every integer of the configuration is at most `B`. -/
def Bound5 (s : System5Config) (B : Int) : Prop :=
  (∀ e ∈ s.bag, e ≤ B) ∧ (∀ r ∈ s.rules, ∀ k ∈ r, k ≤ B)

theorem Bound5_step (s s' : System5Config) (B : Int) (h : Bound5 s B)
    (hs : System5.step s = some s') : Bound5 s' (B + 1) := by
  obtain ⟨hb, hr⟩ := h
  have hrules' : ∀ r' ∈ s.rules.map (fun r => r.map (· + 1)), ∀ k ∈ r', k ≤ B + 1 := by
    intro r' hr' k hk
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
    have := hr r0 hr0 k0 hk0
    omega
  have hbag' : ∀ e ∈ s.bag.map (· - 1), e ≤ B + 1 := by
    intro e he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
    have := hb y hy
    omega
  unfold System5.step at hs
  simp only at hs
  split at hs
  · cases hs
  · split at hs
    · split at hs
      · cases hs
      · rename_i r rest heq
        obtain rfl := Option.some.inj hs
        refine ⟨?_, ?_⟩
        · intro e he
          rcases xorMerge_mem_or _ _ _ he with h1 | h1
          · exact hbag' e (List.mem_of_mem_erase h1)
          · exact hrules' r (by rw [heq]; exact List.mem_cons_self) e h1
        · intro r' hr' k hk
          exact hrules' r' (by rw [heq]; exact List.mem_cons_of_mem _ hr') k hk
    · obtain rfl := Option.some.inj hs
      exact ⟨hbag', hrules'⟩

theorem Bound5_nSteps (s : System5Config) (B : Int) (j : Nat) (s' : System5Config)
    (h : Bound5 s B) (hs : System5.nSteps s j = some s') : Bound5 s' (B + j) := by
  induction j generalizing s' with
  | zero =>
    rw [System5.nSteps_zero] at hs
    obtain rfl := Option.some.inj hs
    simpa using h
  | succ j ih =>
    rw [System5.nSteps_add] at hs
    cases hj : System5.nSteps s j with
    | none => rw [hj] at hs; cases hs
    | some sj =>
      rw [hj] at hs
      simp only [Option.bind_some, System5.nSteps_one] at hs
      have := Bound5_step sj s' (B + j) (ih sj hj) hs
      push_cast
      rwa [← Int.add_assoc]

/-- The integers of the encoder output are bounded by the integers of the
    program. -/
theorem exists_Bound5 (s : System5Config) : ∃ B : Int, 0 ≤ B ∧ Bound5 s B := by
  obtain ⟨M, hM⟩ := exists_int_bound (s.bag ++ s.rules.flatten)
  refine ⟨max M 0, le_max_right _ _, ?_, ?_⟩
  · intro e he
    exact le_trans (hM e (List.mem_append_left _ he)) (le_max_left _ _)
  · intro r hr k hk
    exact le_trans (hM k (List.mem_append_right _ (List.mem_flatten.mpr ⟨r, hr, hk⟩))) (le_max_left _ _)

/-! ## The System 4 tape of the encoder -/

theorem noAdjacentStars_append (l1 l2 : List System4Elem) (h1 : noAdjacentStars l1 = true)
    (h2 : noAdjacentStars l2 = true)
    (h12 : ∀ e, l1.getLast? = some e → ∀ c, l2.head? = some c → (e.isStar && c.isStar) = false) :
    noAdjacentStars (l1 ++ l2) = true := by
  induction l1 with
  | nil => exact h2
  | cons e rest ih =>
    rw [List.cons_append]
    cases rest with
    | nil =>
      exact noAdjacentStars_cons e l2 (fun c hc => h12 e rfl c hc) h2
    | cons e' rest' =>
      refine noAdjacentStars_cons e _ ?_ (ih (noAdjacentStars_tail _ _ h1) ?_)
      · intro c hc
        rw [List.cons_append, List.head?_cons] at hc
        obtain rfl := Option.some.inj hc
        exact noAdjacentStars_cons_head e e' (e' :: rest') h1 rfl
      · intro x hx c hc
        exact h12 x (by rw [List.getLast?_cons_cons]; exact hx) c hc

theorem starredEmptyPairs_ne_nil (n : Nat) (hn : 1 ≤ n) : starredEmptyPairs n ≠ [] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [starredEmptyPairs_succ]
  simp

theorem mem_starredEmptyPairs (n : Nat) (e : System4Elem) (h : e ∈ starredEmptyPairs n) :
    e = System4Elem.star ∨ e = System4Elem.set [] := by
  induction n with
  | zero => simp [starredEmptyPairs] at h
  | succ n ih =>
    rw [starredEmptyPairs_succ] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl rfl
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr rfl
      · exact ih h

theorem noAdjacentStars_starredEmptyPairs (n : Nat) : noAdjacentStars (starredEmptyPairs n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [starredEmptyPairs_succ]
    refine noAdjacentStars_cons _ _ (fun c hc => by rw [List.head?_cons] at hc; rw [← Option.some.inj hc]; rfl) ?_
    refine noAdjacentStars_cons _ _ (fun c _ => rfl) ih

theorem starredEmptyPairs_getLast? (n : Nat) (hn : 1 ≤ n) :
    (starredEmptyPairs n).getLast? = some (System4Elem.set []) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [starredEmptyPairs_succ]
    cases n with
    | zero => rfl
    | succ n =>
      rw [List.getLast?_cons_cons, List.getLast?_cons_of_ne_nil (by simp [starredEmptyPairs])]
      have := ih (by omega)
      rw [List.getLast?_eq_getLast_of_ne_nil (by simp [starredEmptyPairs])] at this
      exact this

theorem encodeS5RuleToS4Elems_eq' (r : List Int) (f : Nat) :
    encodeS5RuleToS4Elems r f
      = System4Elem.star :: System4Elem.set (encodeS5RuleToS4Set r f) ::
          (starredEmptyPairs (f * 2) ++
            System4Elem.star :: System4Elem.set (allInts (f * 3 + 1)) :: starredEmptyPairs (f * 2 - 2)) := by
  unfold encodeS5RuleToS4Elems
  simp only [List.cons_append]

theorem noAdjacentStars_encodeS5RuleToS4Elems (r : List Int) (f : Nat) (hf : 1 ≤ f) :
    noAdjacentStars (encodeS5RuleToS4Elems r f) = true := by
  rw [encodeS5RuleToS4Elems_eq']
  refine noAdjacentStars_cons _ _ (fun c hc => by rw [List.head?_cons] at hc; rw [← Option.some.inj hc]; rfl) ?_
  refine noAdjacentStars_cons _ _ (fun c _ => rfl) ?_
  refine noAdjacentStars_append _ _ (noAdjacentStars_starredEmptyPairs _) ?_ ?_
  · refine noAdjacentStars_cons _ _ (fun c hc => by rw [List.head?_cons] at hc; rw [← Option.some.inj hc]; rfl) ?_
    exact noAdjacentStars_cons _ _ (fun c _ => rfl) (noAdjacentStars_starredEmptyPairs _)
  · intro e he c _
    rw [starredEmptyPairs_getLast? _ (by omega)] at he
    obtain rfl := Option.some.inj he
    rfl

theorem encodeS5RuleToS4Elems_getLast? (r : List Int) (f : Nat) :
    ∃ S, (encodeS5RuleToS4Elems r f).getLast? = some (System4Elem.set S) := by
  rw [encodeS5RuleToS4Elems_eq', List.getLast?_cons_cons,
    List.getLast?_cons_of_ne_nil (by simp), List.getLast?_append_of_ne_nil _ (by simp),
    List.getLast?_cons_cons]
  cases hp : f * 2 - 2 with
  | zero => exact ⟨_, rfl⟩
  | succ n =>
    rw [List.getLast?_cons_of_ne_nil (by simp [starredEmptyPairs])]
    exact ⟨[], starredEmptyPairs_getLast? _ (by omega)⟩

theorem noAdjacentStars_flatMap (rules : List (List Int)) (f : Nat) (hf : 1 ≤ f) :
    noAdjacentStars (rules.flatMap (fun r => encodeS5RuleToS4Elems r f)) = true := by
  induction rules with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons]
    refine noAdjacentStars_append _ _ (noAdjacentStars_encodeS5RuleToS4Elems r f hf) ih ?_
    intro e he c _
    obtain ⟨S, hS⟩ := encodeS5RuleToS4Elems_getLast? r f
    rw [hS] at he
    obtain rfl := Option.some.inj he
    rfl

theorem system5ToSystem4_elems_eq (s : System5Config) (f : Nat) :
    (system5ToSystem4 s f).elems
      = System4Elem.set (encodeBag s.bag) ::
          (starredEmptyPairs f ++ s.rules.flatMap (fun r => encodeS5RuleToS4Elems r f)) := rfl

theorem system5ToSystem4_wellFormed (s : System5Config) (f : Nat) (hf : 1 ≤ f) :
    (system5ToSystem4 s f).WellFormed := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [system5ToSystem4_elems_eq]
    refine noAdjacentStars_cons _ _ (fun c _ => rfl) ?_
    refine noAdjacentStars_append _ _ (noAdjacentStars_starredEmptyPairs f)
      (noAdjacentStars_flatMap s.rules f hf) ?_
    intro e he c _
    rw [starredEmptyPairs_getLast? f hf] at he
    obtain rfl := Option.some.inj he
    rfl
  · rw [List.all_eq_true]
    intro e he
    rw [system5ToSystem4_elems_eq] at he
    rcases List.mem_cons.mp he with rfl | he
    · simpa [System4Elem.setNodup] using encodeBag_nodup s.bag
    · rcases List.mem_append.mp he with he | he
      · rcases mem_starredEmptyPairs f e he with rfl | rfl <;> rfl
      · obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp he
        rw [encodeS5RuleToS4Elems_eq'] at he
        simp only [List.mem_cons, List.mem_append] at he
        rcases he with rfl | rfl | he | rfl | rfl | he
        · rfl
        · simpa [System4Elem.setNodup, encodeS5RuleToS4Set_eq] using encRuleSet_nodup r f 0
        · rcases mem_starredEmptyPairs _ e he with rfl | rfl <;> rfl
        · rfl
        · simpa [System4Elem.setNodup] using allInts_nodup (f * 3 + 1)
        · rcases mem_starredEmptyPairs _ e he with rfl | rfl <;> rfl

theorem system5ToSystem4_last_set (s : System5Config) (f : Nat) (hf : 1 ≤ f) :
    (system5ToSystem4 s f).elems.getLast? ≠ some System4Elem.star := by
  rw [system5ToSystem4_elems_eq]
  cases hr : s.rules.flatMap (fun r => encodeS5RuleToS4Elems r f) with
  | nil =>
    rw [List.append_nil, List.getLast?_cons_of_ne_nil (starredEmptyPairs_ne_nil f hf),
      starredEmptyPairs_getLast? f hf]
    simp
  | cons e l =>
    rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_append_of_ne_nil _ (by simp), ← hr]
    obtain ⟨r, rs, hrs⟩ : ∃ r rs, s.rules = rs ++ [r] := by
      cases hs : s.rules using List.reverseRecOn with
      | nil => rw [hs] at hr; simp at hr
      | append_singleton rs r => exact ⟨r, rs, rfl⟩
    rw [hrs, List.flatMap_append, List.flatMap_singleton,
      List.getLast?_append_of_ne_nil _ (by simp [encodeS5RuleToS4Elems_eq'])]
    obtain ⟨S, hS⟩ := encodeS5RuleToS4Elems_getLast? r f
    rw [hS]
    simp

/-- Every integer of every set of the encoder output is below `3f + 3`. -/
theorem system5ToSystem4_elem_lt (s : System5Config) (f : Nat)
    (hbag : ∀ e ∈ s.bag, 1 ≤ e ∧ e < f) (hrules : ∀ r ∈ s.rules, ∀ k ∈ r, 0 ≤ k ∧ k < f) :
    ∀ S, System4Elem.set S ∈ (system5ToSystem4 s f).elems →
      ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 3 * f + 3 := by
  intro S hS e he
  rw [system5ToSystem4_elems_eq] at hS
  rcases List.mem_cons.mp hS with hS | hS
  · obtain rfl := System4Elem.set.inj hS
    rw [encodeBag_eq_xorMerge] at he
    rcases xorMerge_mem_or _ _ _ he with h | h
    · simp at h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      have := hbag y hy
      unfold system5BagEntryToSystem4
      omega
  · rcases List.mem_append.mp hS with hS | hS
    · rcases mem_starredEmptyPairs f _ hS with h | h
      · cases h
      · obtain rfl := System4Elem.set.inj h
        simp at he
    · obtain ⟨r, hr, hS⟩ := List.mem_flatMap.mp hS
      rw [encodeS5RuleToS4Elems_eq'] at hS
      simp only [List.mem_cons, List.mem_append] at hS
      rcases hS with h | h | h | h | h | h
      · cases h
      · obtain rfl := System4Elem.set.inj h
        rw [encodeS5RuleToS4Set_eq, encRuleSet] at he
        rcases xorMerge_mem_or _ _ _ he with h | h
        · have := (allInts_mem _ _).mp h
          omega
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
          have := hrules r hr k hk
          unfold rulePos
          omega
      · rcases mem_starredEmptyPairs _ _ h with h | h
        · cases h
        · obtain rfl := System4Elem.set.inj h
          simp at he
      · cases h
      · obtain rfl := System4Elem.set.inj h
        have := (allInts_mem _ _).mp he
        omega
      · rcases mem_starredEmptyPairs _ _ h with h | h
        · cases h
        · obtain rfl := System4Elem.set.inj h
          simp at he

/-! ## The terminal phase of System 4 -/

/-- Once the System 5 rules are exhausted, System 4 decrements until 1 is
    in the bag and then exits in state C past the right end of its tape.
    `M + 1` bounds some bag element, so the decrements are at most `M`. -/
theorem repS4_terminal (M : Nat) : ∀ (c : System4Config) (s : System5Config) (f j h : Nat),
    RepS4 c s f j (h + M) → s.rules = [] → (∃ e ∈ s.bag, e ≤ (M : Int) + 1) →
    ∃ k c', System4.nSteps c k = some c' ∧ c'.state = System4State.C ∧
      c'.active = c'.elems.length ∧ System4.step c' = none := by
  induction M with
  | zero =>
    intro c s f j h hrep hr ⟨e, he, hle⟩
    have h1 : (1 : Int) ∈ s.bag := by
      obtain ⟨_, _, _, _, _, _, _, hbag1, _⟩ := hrep
      have := (hbag1 e he).1
      have : e = 1 := by omega
      rw [← this]; exact he
    have hjf : j + 1 < f := by
      obtain ⟨_, _, _, _, _, _, _, hbag1, _⟩ := hrep
      have := (hbag1 1 h1).2
      omega
    exact repS4_exit c s f j (h + 0) hrep hr h1 hjf
  | succ M ih =>
    intro c s f j h hrep hr ⟨e, he, hle⟩
    by_cases h1 : (1 : Int) ∈ s.bag
    · have hjf : j + 1 < f := by
        obtain ⟨_, _, _, _, _, _, _, hbag1, _⟩ := hrep
        have := (hbag1 1 h1).2
        omega
      exact repS4_exit c s f j (h + (M + 1)) hrep hr h1 hjf
    · have hrep' : RepS4 c s f j (h + M + 1) := by
        rw [show h + M + 1 = h + (M + 1) from by omega]; exact hrep
      obtain ⟨k, _, c1, hrun1, hrep1⟩ := repS4_dStep c s f j (h + M) hrep' h1
      have he' : ∃ e' ∈ s.bag.map (· - 1), e' ≤ (M : Int) + 1 := ⟨e - 1, List.mem_map.mpr ⟨e, he, rfl⟩, by push_cast at hle; omega⟩
      obtain ⟨k2, c', hrun2, hst, hact, hnone⟩ := ih c1 _ f (j + 1) h hrep1 (by rw [hr]; rfl) he'
      exact ⟨k + k2, c', by rw [System4.nSteps_add, hrun1, Option.bind_some]; exact hrun2, hst, hact, hnone⟩

/-! ## The decoder of link C below a fixed band -/

/-- `RepS4_decode` for any band that lies under the debris and above the
    positions of the bag. -/
theorem RepS4_decode_band (c : System4Config) (s : System5Config) (f j h : Nat)
    (hrep : RepS4 c s f j h) (b : Nat) (hb : b + 2 * j + 2 ≤ 2 * f)
    (hbag : ∀ e ∈ s.bag, 2 * e - 2 < b) :
    ∃ l, decodeS4 c b = some l ∧ l.Perm s.bag := by
  obtain ⟨K, hKne, hKwf, rfl, hjh, hpar, hnd, hbag1, hrl⟩ := hrep
  have hlead : leadSets (sets K ++ starredEmptyPairs (f - 2 * j) ++ encBlocks s.rules f (2 * j)) = K := by
    rw [List.append_assoc]
    apply leadSets_sets
    intro S
    cases hg : f - 2 * j with
    | zero =>
      cases hr : s.rules with
      | nil => simp [starredEmptyPairs]
      | cons r rest => simp [starredEmptyPairs, encBlocks_cons, encBlock]
    | succ g => simp [starredEmptyPairs]
  unfold decodeS4
  simp only [hlead]
  have hmem : ∀ x : Int, x ∈ ((List.range b).map (fun (i : Nat) => (i : Int))).filter
      (fun x => parMem x K) ↔ ∃ e ∈ s.bag, x = 2 * e - 2 := by
    intro x
    rw [List.mem_filter, List.mem_map]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hp⟩
      rw [List.mem_range] at hi
      have := hpar i (by omega) (by omega)
      rw [this, decide_eq_true_eq] at hp
      exact hp
    · rintro ⟨e, he, rfl⟩
      obtain ⟨he1, he2⟩ := hbag1 e he
      have := hbag e he
      refine ⟨⟨(2 * e - 2).toNat, ?_, by omega⟩, ?_⟩
      · rw [List.mem_range]; omega
      · rw [hpar _ (by omega) (by omega), decide_eq_true_eq]
        exact ⟨e, he, by omega⟩
  have hall : (((List.range b).map (fun (i : Nat) => (i : Int))).filter
      (fun x => parMem x K)).all (fun x => x % 2 = 0) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨e, _, rfl⟩ := (hmem x).mp hx
    simp only [decide_eq_true_eq]
    omega
  rw [if_pos hall]
  refine ⟨_, rfl, ?_⟩
  have hnd1 : (((List.range b).map (fun (i : Nat) => (i : Int))).filter
      (fun x => parMem x K)).Nodup :=
    List.Nodup.sublist List.filter_sublist
      (nodup_map_of_injective _ (fun a b hab => by omega) List.nodup_range)
  have hnd2 : ((((List.range b).map (fun (i : Nat) => (i : Int))).filter
      (fun x => parMem x K)).map (fun x => x / 2 + 1)).Nodup := by
    rw [List.nodup_map_iff_inj_on hnd1]
    intro a ha b hb hab
    obtain ⟨ea, _, rfl⟩ := (hmem a).mp ha
    obtain ⟨eb, _, rfl⟩ := (hmem b).mp hb
    omega
  rw [List.perm_ext_iff_of_nodup hnd2 hnd]
  intro e
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨e', he', rfl⟩ := (hmem x).mp hx
    have : (2 * e' - 2) / 2 + 1 = e' := by omega
    rw [this]; exact he'
  · intro he
    exact ⟨2 * e - 2, (hmem _).mpr ⟨e, he, rfl⟩, by omega⟩

/-! ## The exit -/

/-- At System 4's exit configuration the System 3 head is on the closing 1
    in state C. -/
theorem rep3_exit (c3 : LConfig) (c4 : System4Config) (w h : Nat)
    (hrep : Rep3 Closing.one c3 c4 w h)
    (hact : c4.active = c4.elems.length) (hst : c4.state = System4State.C) :
    ∃ L, c3 = ⟨L, 1, [], C⟩ := by
  obtain ⟨⟨ls, rs, le, rc, st, foc⟩, hrc, _, rfl, rfl⟩ := hrep
  simp only at hrc
  subst hrc
  cases foc with
  | setA xl b xr S => exfalso; simp [AC.to4] at hact
  | setB x0 x' S => exfalso; simp [AC.to4] at hact
  | setT x1 x' S => exfalso; simp [AC.to4] at hact
  | star => exfalso; simp [AC.to4] at hact
  | off =>
    simp only [AC.to4] at hst
    subst hst
    exact ⟨_, rfl⟩

theorem phi_exit (L : List (Fin 3)) : phi2 (phi3 ⟨L, 1, [], C⟩) = ⟨L.map sw, 2, [], B⟩ := rfl

theorem phi2_state_ne_C (c : LConfig) : (phi2 c).state ≠ C := by
  obtain ⟨L, a, R, st⟩ := c
  cases st <;> simp [phi2]

/-- The exit step of wolfram23: `B2 -> 0, R, A` onto the implicit blank right
    of the tape (TM23Proof.pdf p. 4: "if that cell is a 0 it becomes active
    in state A"). -/
theorem wolfram23_exit_step (L : List Nat) :
    BiTM.step wolfram23 ⟨2, L, 2, []⟩ = some ⟨1, 0 :: L, 0, []⟩ := rfl

/-! ## The decoder of the wolfram23 tape -/

/-- The XOR of the first `k` blocks of width `N`. -/
def xorBlocks (N : Nat) : Nat → List Bool → Bits
  | 0, _ => zeros N
  | k + 1, l => xorB (l.take N) (xorBlocks N k (l.drop N))

/-- Cells as bits: 2 is true. -/
def natBits (l : List Nat) : Bits := l.map (fun c => decide (c = 2))

/-- The blocks of the leading conglomerate, given as their cells: their XOR's
    parity set below the band `b`, read as System 5 integers by `x / 2 + 1`
    (the decoder of link C). `none` unless the cells are 1s and 2s making up
    at least one whole block and the parity set is even. -/
def decodeBlocks (N b : Nat) (cells : List Nat) : Option (List Int) :=
  if (cells.all fun c => c == 1 || c == 2) = true ∧ 1 ≤ cells.length / N ∧ cells.length % N = 0 then
    let x := xorBlocks N (cells.length / N) (natBits cells)
    let xs := ((List.range b).map (fun (i : Nat) => (i : Int))).filter (fun z => parAt x z.toNat)
    if xs.all (fun z => z % 2 = 0) then some (xs.map (fun z => z / 2 + 1)) else none
  else none

/-- The decoder of the wolfram23 tape at a decoding time: the head and the
    cells right of it up to the first 0 are the blocks of the leading
    conglomerate; `decodeBlocks` reads the bag off them and `decodeBag` of
    link B reads the working string off the bag. -/
def decodeW23 (N b : Nat) (cfg : BiTM.Config) : Option (List Bool) :=
  (decodeBlocks N b (cfg.head :: cfg.right.takeWhile (fun c => c != 0))).bind decodeBag

theorem takeWhile_ne_zero_append (P Q : List Nat) (hP : ∀ c ∈ P, c ≠ 0) :
    (P ++ 0 :: Q).takeWhile (fun c => c != 0) = P := by
  induction P with
  | nil => simp
  | cons c P ih =>
    have hc : (c != 0) = true := by simpa using hP c List.mem_cons_self
    rw [List.cons_append, List.takeWhile_cons, hc]
    simp only [ite_true]
    rw [ih (fun d hd => hP d (List.mem_cons_of_mem _ hd))]

theorem natBits_map_val_ofBits (x : Bits) : natBits ((ofBits x).map Fin.val) = x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    cases b <;> simp [natBits, ofBits, toCell] at ih ⊢ <;> exact ih

theorem natBits_append (l1 l2 : List Nat) : natBits (l1 ++ l2) = natBits l1 ++ natBits l2 :=
  List.map_append ..

theorem natBits_flatMap (bits : List Bits) :
    natBits ((bits.flatMap ofBits).map Fin.val) = bits.flatten := by
  induction bits with
  | nil => rfl
  | cons x bs ih =>
    rw [List.flatMap_cons, List.map_append, natBits_append, natBits_map_val_ofBits, List.flatten_cons, ih]

theorem val_toCell (b : Bool) : ((toCell b).val == 1 || (toCell b).val == 2) = true := by
  cases b <;> rfl

theorem all_flatMap_ofBits (bits : List Bits) :
    (((bits.flatMap ofBits).map Fin.val).all fun c => c == 1 || c == 2) = true := by
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
  obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  exact val_toCell b

theorem length_flatMap_ofBits (N : Nat) (bits : List Bits) (hlen : ∀ x ∈ bits, x.length = N) :
    (bits.flatMap ofBits).length = bits.length * N := by
  induction bits with
  | nil => simp
  | cons x bs ih =>
    rw [List.flatMap_cons, List.length_append, length_ofBits, hlen x List.mem_cons_self,
      ih (fun y hy => hlen y (List.mem_cons_of_mem _ hy)), List.length_cons, Nat.add_mul, Nat.one_mul,
      Nat.add_comm]

theorem xorBlocks_flatten (N : Nat) (bits : List Bits) (hlen : ∀ x ∈ bits, x.length = N) :
    xorBlocks N bits.length bits.flatten = bits.foldr xorB (zeros N) := by
  induction bits with
  | nil => rfl
  | cons x bs ih =>
    have hx := hlen x List.mem_cons_self
    rw [List.length_cons, List.flatten_cons, xorBlocks, List.take_left' hx, List.drop_left' hx,
      ih (fun y hy => hlen y (List.mem_cons_of_mem _ hy)), List.foldr_cons]

theorem length_foldr_xorB (N : Nat) (bits : List Bits) (hlen : ∀ x ∈ bits, x.length = N) :
    (bits.foldr xorB (zeros N)).length = N := by
  induction bits with
  | nil => simp
  | cons x bs ih =>
    rw [List.foldr_cons, length_xorB _ _ (by rw [hlen x List.mem_cons_self,
      ih (fun y hy => hlen y (List.mem_cons_of_mem _ hy))]), hlen x List.mem_cons_self]

theorem parAt_zeros (n i : Nat) : parAt (zeros n) i = false := by
  unfold parAt
  rw [Function.iterate_fixed (T_zeros n) i, parity_zeros]

/-- The parity set of the XOR of blocks decoding to sets is the parity
    membership of the sets. -/
theorem parAt_blocks (N k : Nat) (blocks : List (Bits × List Int))
    (hb : ∀ p ∈ blocks, p.1.length = N ∧ Decodes p.1 p.2 k) (i : Nat) (hi : i < k) :
    parAt ((blocks.map Prod.fst).foldr xorB (zeros N)) i = parMem (i : Int) (blocks.map Prod.snd) := by
  induction blocks with
  | nil => simp [parAt_zeros]
  | cons p ps ih =>
    have hp := hb p List.mem_cons_self
    have hps : ∀ q ∈ ps, q.1.length = N ∧ Decodes q.1 q.2 k :=
      fun q hq => hb q (List.mem_cons_of_mem _ hq)
    rw [List.map_cons, List.map_cons, List.foldr_cons, parMem_cons,
      parAt_xor _ _ (by rw [hp.1, length_foldr_xorB N _ (fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx; exact (hps q hq).1)]),
      ih hps, hp.2 i hi]

theorem decodeBlocks_of_blocks (N b k : Nat) (hN : 1 ≤ N) (blocks : List (Bits × List Int))
    (hne : blocks ≠ []) (hb : ∀ p ∈ blocks, p.1.length = N ∧ Decodes p.1 p.2 k) (hbk : b ≤ k) :
    decodeBlocks N b (((blocks.map Prod.fst).flatMap ofBits).map Fin.val)
      = (let xs := ((List.range b).map (fun (i : Nat) => (i : Int))).filter
            (fun z => parMem z (blocks.map Prod.snd))
         if xs.all (fun z => z % 2 = 0) then some (xs.map (fun z => z / 2 + 1)) else none) := by
  have hlen : ∀ x ∈ blocks.map Prod.fst, x.length = N := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact (hb q hq).1
  have hL : (((blocks.map Prod.fst).flatMap ofBits).map Fin.val).length = blocks.length * N := by
    rw [List.length_map, length_flatMap_ofBits N _ hlen, List.length_map]
  have hdiv : blocks.length * N / N = blocks.length := Nat.mul_div_cancel _ (by omega)
  have hmod : blocks.length * N % N = 0 := Nat.mul_mod_left _ _
  have hpos : 1 ≤ blocks.length := by
    cases blocks with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hfilt : ((List.range b).map (fun (i : Nat) => (i : Int))).filter
      (fun z => parAt ((blocks.map Prod.fst).foldr xorB (zeros N)) z.toNat)
      = ((List.range b).map (fun (i : Nat) => (i : Int))).filter
          (fun z => parMem z (blocks.map Prod.snd)) := by
    apply List.filter_congr
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    rw [List.mem_range] at hi
    rw [Int.toNat_natCast, parAt_blocks N k blocks hb i (by omega)]
  have hlm : blocks.length = (blocks.map Prod.fst).length := (List.length_map ..).symm
  unfold decodeBlocks
  rw [if_pos ⟨all_flatMap_ofBits _, by rw [hL, hdiv]; exact hpos, by rw [hL, hmod]⟩]
  simp only [hL, hdiv, natBits_flatMap]
  rw [hlm, xorBlocks_flatten N _ hlen, hfilt]

/-! ## The decoder on the System 3 side -/

theorem map_toElem_eq_sets (K' : List (List Int)) : ∀ (rs : List Item) (R : List System4Elem),
    rs.map Item.toElem = sets K' ++ System4Elem.star :: R →
    ∃ (ps : List (Bits × List Int)) (rs' : List Item),
      rs = ps.map (fun p => Item.set p.1 p.2) ++ Item.star :: rs' ∧ ps.map Prod.snd = K' ∧
        rs'.map Item.toElem = R := by
  induction K' with
  | nil =>
    intro rs R h
    cases rs with
    | nil => simp at h
    | cons it rs' =>
      simp only [sets, List.map_nil, List.nil_append, List.map_cons, List.cons.injEq] at h
      cases it with
      | set x S => simp [Item.toElem] at h
      | star => exact ⟨[], rs', rfl, rfl, h.2⟩
  | cons S K' ih =>
    intro rs R h
    cases rs with
    | nil => simp [sets] at h
    | cons it rs'' =>
      simp only [sets, List.map_cons, List.cons_append, List.cons.injEq] at h
      cases it with
      | star => simp [Item.toElem] at h
      | set x S' =>
        simp only [Item.toElem, System4Elem.set.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        obtain ⟨ps, rs', rfl, hK, hR⟩ := ih rs'' R (by simpa [sets] using h2)
        exact ⟨(x, S') :: ps, rs', rfl, by simp [hK], hR⟩

theorem renderR_blocks (ps : List (Bits × List Int)) (rest : List Item) :
    renderR false (ps.map (fun p => Item.set p.1 p.2) ++ rest)
      = (ps.map Prod.fst).flatMap ofBits ++ renderR false rest := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.cons_append, renderR_set_false, ih, List.map_cons, List.flatMap_cons,
      List.append_assoc]

theorem takeWhile_map_val (P Q : List (Fin 3)) (hP : ∀ c ∈ P, c ≠ 0) :
    ((P ++ 0 :: Q).map Fin.val).takeWhile (fun c => c != 0) = P.map Fin.val := by
  rw [List.map_append, List.map_cons]
  exact takeWhile_ne_zero_append _ _ (fun c hc => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact Fin.val_ne_of_ne (hP d hd))

theorem decodeS4_state (E : List System4Elem) (a : Nat) (st st' : System4State) (b : Nat) :
    decodeS4 ⟨E, a, st⟩ b = decodeS4 ⟨E, a, st'⟩ b := rfl

/-- At a System 4 configuration with the head on an element in state B, that
    element leading a block of sets followed by a star, the wolfram23 decoder
    reads the tape as the decoder of link C reads the block: the cells left of
    the head play no part; a 0 (the star) lies right of the head, and wolfram23
    is in state B. -/
theorem rep3_decode (c3 : LConfig) (Lp : List System4Elem) (K : List (List Int))
    (R : List System4Elem) (w h b : Nat) (hK : K ≠ []) (hb : b ≤ h + 1)
    (rc : Closing)
    (hrep : Rep3 rc c3 ⟨Lp ++ sets K ++ System4Elem.star :: R, Lp.length, System4State.B⟩ w h) :
    decodeW23 (2 ^ w) b (toBi (phi2 (phi3 c3)))
      = (decodeS4 ⟨sets K ++ System4Elem.star :: R, 0, System4State.B⟩ b).bind decodeBag ∧
    0 ∈ (toBi (phi2 (phi3 c3))).right ∧ (toBi (phi2 (phi3 c3))).state = 2 := by
  obtain ⟨⟨ls, rs, le, rc', st, foc⟩, hrc, ⟨hN, hle, hls, hrs, hL, hR, hfoc⟩, rfl, h4⟩ := hrep
  simp only at hrc
  subst rc
  obtain ⟨K0, K', rfl⟩ := List.exists_cons_of_ne_nil hK
  cases foc with
  | setA xl bb xr S =>
    simp only [AC.to4, System4Config.mk.injEq] at h4
    obtain ⟨hst, -⟩ := hfoc
    rw [← h4.2.2] at hst
    cases hst
  | setT x1 x' S =>
    simp only [AC.to4, System4Config.mk.injEq] at h4
    obtain ⟨hst, -⟩ := hfoc
    rw [← h4.2.2] at hst
    cases hst
  | star =>
    simp only [AC.to4, System4Config.mk.injEq] at h4
    obtain ⟨helems, hact, -⟩ := h4
    rw [List.append_assoc] at helems
    obtain ⟨-, h2⟩ := List.append_inj helems hact
    simp [sets] at h2
  | off =>
    simp only [AC.to4, System4Config.mk.injEq] at h4
    obtain ⟨helems, hact, -⟩ := h4
    have := congrArg List.length helems
    simp [sets] at this hact
    omega
  | setB x0 x' S =>
    simp only [AC.to4, System4Config.mk.injEq] at h4
    obtain ⟨helems, hact, hst⟩ := h4
    subst hst
    rw [List.append_assoc] at helems
    obtain ⟨-, h2⟩ := List.append_inj helems hact
    simp only [sets, List.map_cons, List.cons_append, List.cons.injEq, System4Elem.set.injEq] at h2
    obtain ⟨rfl, hrs'⟩ := h2
    obtain ⟨ps, rs', rfl, hK', hR'⟩ := map_toElem_eq_sets K' rs R (by simpa [sets] using hrs'.symm)
    obtain ⟨-, hlen0, hnd0, hdec0⟩ := hfoc
    have hblocks : ∀ p ∈ ((x0 :: x', K0) :: ps), p.1.length = 2 ^ w ∧ Decodes p.1 p.2 (h + 1) := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hlen0, hdec0⟩
      · have := hrs (Item.set p.1 p.2)
          (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
        exact ⟨this.1, this.2.2⟩
    have hP : ∀ c ∈ ofBits x' ++ (ps.map Prod.fst).flatMap ofBits, c ≠ 0 := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ofBits_ne_zero x' c hc
      · obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp hc
        exact ofBits_ne_zero x c hx
    have htoL : (AC.toL ⟨ls, ps.map (fun p => Item.set p.1 p.2) ++ Item.star :: rs', le, rc',
        System4State.B, Focus.setB x0 x' K0⟩)
        = ⟨renderL false ls ++ le.render, toCell x0,
           (ofBits x' ++ (ps.map Prod.fst).flatMap ofBits) ++ 0 :: (renderR true rs' ++ rc'.render), B⟩ := by
      simp only [AC.toL, renderR_blocks, renderR_star, List.append_assoc, List.cons_append, st3]
    rw [htoL, phi3_B, phi2_B]
    refine ⟨?_, by simp [toBi], rfl⟩
    unfold decodeW23
    simp only [toBi]
    rw [takeWhile_map_val _ _ hP]
    have hcells : (toCell x0).val :: (ofBits x' ++ (ps.map Prod.fst).flatMap ofBits).map Fin.val
        = ((((x0 :: x', K0) :: ps).map Prod.fst).flatMap ofBits).map Fin.val := by
      simp [ofBits_cons]
    rw [hcells, decodeBlocks_of_blocks (2 ^ w) b (h + 1) Nat.one_le_two_pow _ (by simp) hblocks hb]
    unfold decodeS4
    rw [leadSets_sets (K0 :: K') (System4Elem.star :: R) (fun S => by simp)]
    simp only [List.map_cons, hK']

/-- `rep3_decode` with the head on the leftmost element. -/
theorem rep3_decode_zero (c3 : LConfig) (K : List (List Int)) (R : List System4Elem) (w h b : Nat)
    (hK : K ≠ []) (hb : b ≤ h + 1) (rc : Closing)
    (hrep : Rep3 rc c3 ⟨sets K ++ System4Elem.star :: R, 0, System4State.B⟩ w h) :
    decodeW23 (2 ^ w) b (toBi (phi2 (phi3 c3)))
      = (decodeS4 ⟨sets K ++ System4Elem.star :: R, 0, System4State.B⟩ b).bind decodeBag :=
  (rep3_decode c3 [] K R w h b hK hb rc (by simpa using hrep)).1

/-- A represented nonempty working string gives a nonempty bag. -/
theorem Represents_bag_ne_nil (s : System5Config) (C : CTS) (c : CTSConfig) (b : Nat)
    (h : Represents s C c b) (hne : c.data ≠ []) : s.bag ≠ [] := by
  obtain ⟨⟨a, hasc, hperm⟩, -⟩ := h
  intro hnil
  have h1 := pairsOf_length 0 c.data a hasc
  rw [← hperm.length_eq, hnil, List.length_nil] at h1
  exact hne (List.length_eq_zero_iff.mp (by omega))

theorem toBi_valid (c : LConfig) (hc : c.state ≠ C) : IsValidWolfram23Cfg (toBi c) := by
  obtain ⟨L, a, R, st⟩ := c
  refine ⟨?_, a.isLt, ?_, ?_⟩
  · cases st with
    | A => exact Or.inl rfl
    | B => exact Or.inr rfl
    | C => exact absurd rfl hc
  · intro x hx
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
    exact d.isLt
  · intro x hx
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
    exact d.isLt

theorem biNSteps_one (cfg : BiTM.Config) : BiTM.nSteps wolfram23 cfg 1 = BiTM.step wolfram23 cfg := by
  simp only [BiTM.nSteps]
  cases BiTM.step wolfram23 cfg <;> rfl

/-! ## The System 4 emulation of a cyclic tag run

The System 4 side of T4, shared by the finite form below and by the
infinite form of `Smith.Infinite`: the encoder tape of link C runs, at
strictly increasing times, through configurations whose head has just
turned at the left end (on the first set in state B, a star after the
leading conglomerate), which decode to the cyclic tag configurations, and
then exits in state C. -/

theorem system4_emulation (C0 : CTS) (cfg : CTSConfig) (N : Nat) (c' : CTSConfig)
    (hrun : C0.nSteps cfg (C0.appendants.length * N) = some c') (hne : c'.data ≠ []) :
    ∃ (s0 : System5Config) (f b T4 : Nat) (cE : System4Config) (times : Nat → Nat),
      s0 = ctsToSystem5 C0 cfg N ∧ 1 ≤ f ∧
      (∀ e ∈ s0.bag, 1 ≤ e ∧ e < f) ∧ (∀ r ∈ s0.rules, ∀ k ∈ r, 0 ≤ k ∧ k < f) ∧
      System4.nSteps (system5ToSystem4 s0 f) T4 = some cE ∧
      cE.state = System4State.C ∧ cE.active = cE.elems.length ∧
      (∀ i, i < C0.appendants.length * N → times i < times (i + 1)) ∧
      (∀ i, i ≤ C0.appendants.length * N → times i + 1 ≤ T4 ∧
        ∃ ci K R, C0.nSteps cfg i = some ci ∧ K ≠ [] ∧
          System4.nSteps (system5ToSystem4 s0 f) (times i + 1)
            = some ⟨sets K ++ System4Elem.star :: R, 0, System4State.B⟩ ∧
          (decodeS4 ⟨sets K ++ System4Elem.star :: R, 0, System4State.B⟩ b).bind decodeBag
            = some (dbl ci.data)) := by
  obtain ⟨n, hn⟩ : ∃ n, n = C0.appendants.length * N := ⟨_, rfl⟩
  rw [← hn] at hrun ⊢
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = ctsToSystem5 C0 cfg N := ⟨_, rfl⟩
  obtain ⟨t5, h50, h5mono, h5tr⟩ := conjecture5_finite_exact C0 cfg N n (le_of_eq hn) c' hrun
  rw [← hs0] at h5tr
  obtain ⟨cn, sn, hcn, hsn, hrep5n, hlenn⟩ := h5tr n (le_refl n)
  rw [hrun] at hcn
  obtain rfl := Option.some.inj hcn
  have hrules_n : sn.rules = [] := by
    have h0 : sn.rules.length = 0 := by rw [hlenn, ← hn]; simp
    exact List.length_eq_zero_iff.mp h0
  obtain ⟨B0, hB0, hbound0⟩ := exists_Bound5 s0
  have hboundn := Bound5_nSteps s0 B0 (t5 n) sn hbound0 hsn
  have hbagne : sn.bag ≠ [] :=
    Represents_bag_ne_nil sn (double C0) (dblCfg _) _ hrep5n (by simpa [dblCfg] using hne)
  obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil sn.bag hbagne
  obtain ⟨M, hM⟩ : ∃ M : Nat, M = (B0 + t5 n).toNat := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Nat, H = t5 n + M + 1 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : Nat, f = B0.toNat + 2 * H + 2 * t5 n + 5 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Nat, b = 2 * f - 2 * t5 n - 2 := ⟨_, rfl⟩
  have hB0n := Int.self_le_toNat B0
  have hf1 : 1 ≤ f := by omega
  have hbag1 : ∀ e ∈ s0.bag, 1 ≤ e ∧ e < f := by
    intro e he
    have h1 := ctsToSystem5_bag_ge_one C0 cfg N e (hs0 ▸ he)
    have h2 := hbound0.1 e he
    constructor <;> omega
  have hrules0 : ∀ r ∈ s0.rules, r.Nodup ∧ ∀ k ∈ r, 0 ≤ k ∧ k + 2 * H < f := by
    intro r hr
    refine ⟨ctsToSystem5_rules_nodup C0 cfg N r (hs0 ▸ hr), fun k hk => ?_⟩
    have h1 := ctsToSystem5_rules_ge_three C0 cfg N r (hs0 ▸ hr) k hk
    have h2 := hbound0.2 r hr k hk
    constructor <;> omega
  have hrules0' : ∀ r ∈ s0.rules, ∀ k ∈ r, 0 ≤ k ∧ k < f := by
    intro r hr k hk
    have := (hrules0 r hr).2 k hk
    constructor <;> omega
  obtain ⟨t4, h40, h4mono, h4tr⟩ := conjecture4_finite s0 f H (t5 n)
    (hs0 ▸ ctsToSystem5_bag_nodup C0 cfg N) hbag1 hrules0 (by omega) (by omega) sn hsn
  obtain ⟨sL, c4L, hsL, hc4L, hrepL⟩ := h4tr (t5 n) (le_refl _)
  rw [hsn] at hsL
  obtain rfl := Option.some.inj hsL
  have hrepL' : RepS4 c4L sn f (t5 n) (1 + M) := by
    have : H - t5 n = 1 + M := by omega
    rw [this] at hrepL; exact hrepL
  have he0le : e0 ≤ (M : Int) + 1 := by
    have := hboundn.1 e0 he0
    have := Int.self_le_toNat (B0 + t5 n)
    omega
  obtain ⟨k, cE, hrunE, hstE, hactE, hnoneE⟩ :=
    repS4_terminal M c4L sn f (t5 n) 1 hrepL' hrules_n ⟨e0, he0, he0le⟩
  obtain ⟨K, hKne, -, hc4Leq, -⟩ := hrepL
  have hk1 : 1 ≤ k := by
    cases k with
    | zero =>
      rw [System4.nSteps_zero] at hrunE
      obtain rfl := Option.some.inj hrunE
      rw [hc4Leq] at hstE
      cases hstE
    | succ k => omega
  obtain ⟨T4, hT4⟩ : ∃ T4, T4 = t4 (t5 n) + k := ⟨_, rfl⟩
  have hrunT4 : System4.nSteps (system5ToSystem4 s0 f) T4 = some cE := by
    rw [hT4, System4.nSteps_add, hc4L, Option.bind_some, hrunE]
  have h4le : ∀ j, j ≤ t5 n → t4 j ≤ t4 (t5 n) := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact le_of_lt (strictMono_of_succ t4 (t5 n) h4mono j _ hlt (le_refl _))
    · exact le_refl _
  have h5le : ∀ i, i ≤ n → t5 i ≤ t5 n := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with hlt | rfl
    · exact le_of_lt (strictMono_of_succ t5 n h5mono i n hlt (le_refl _))
    · exact le_refl _
  refine ⟨s0, f, b, T4, cE, fun i => t4 (t5 i), hs0, hf1, hbag1, hrules0', hrunT4, hstE, hactE, ?_, ?_⟩
  · intro i hi
    exact strictMono_of_succ t4 (t5 n) h4mono _ _ (h5mono i hi) (h5le (i + 1) hi)
  · intro i hi
    obtain ⟨ci, si, hci, hsi, hrep5i, -⟩ := h5tr i hi
    obtain ⟨si', c4i, hsi', hc4i, hrep4i⟩ := h4tr (t5 i) (h5le i hi)
    rw [hsi] at hsi'
    obtain rfl := Option.some.inj hsi'
    have hd : t4 (t5 i) + 1 ≤ T4 := by
      have := h4le (t5 i) (h5le i hi)
      omega
    have hrep4i' := hrep4i
    obtain ⟨K, hKne, -, hc4ieq, hjh, -, -, -, -⟩ := hrep4i
    obtain ⟨K0, K', rfl⟩ := List.exists_cons_of_ne_nil hKne
    obtain ⟨g, hg⟩ : ∃ g, f - 2 * t5 i = g + 1 := ⟨f - 2 * t5 i - 1, by omega⟩
    have hE : sets (K0 :: K') ++ starredEmptyPairs (f - 2 * t5 i) ++ encBlocks si.rules f (2 * t5 i)
        = sets (K0 :: K') ++ System4Elem.star ::
            (System4Elem.set [] :: (starredEmptyPairs g ++ encBlocks si.rules f (2 * t5 i))) := by
      rw [hg, starredEmptyPairs_succ]
      simp only [List.append_assoc, List.cons_append]
    have hcd' : System4.nSteps (system5ToSystem4 s0 f) (t4 (t5 i) + 1)
        = some ⟨sets (K0 :: K') ++ System4Elem.star ::
            (System4Elem.set [] :: (starredEmptyPairs g ++ encBlocks si.rules f (2 * t5 i))), 0,
            System4State.B⟩ := by
      rw [System4.nSteps_add, hc4i, Option.bind_some, System4.nSteps_one, hc4ieq, hE]
      show System4.step ⟨System4Elem.set K0 :: (sets K' ++ System4Elem.star ::
        (System4Elem.set [] :: (starredEmptyPairs g ++ encBlocks si.rules f (2 * t5 i)))), 0,
        System4State.A⟩ = _
      rw [step_setA_zero]
      rfl
    refine ⟨hd, ci, K0 :: K', _, hci, by simp, hcd', ?_⟩
    rw [decodeS4_state _ _ _ System4State.A, ← hE, ← hc4ieq]
    have hbagb : ∀ e ∈ si.bag, 2 * e - 2 < b := by
      intro e he
      have h1 := (Bound5_nSteps s0 B0 (t5 i) si hbound0 hsi).1 e he
      have h2 := h5le i hi
      omega
    obtain ⟨l, hl, hlperm⟩ := RepS4_decode_band c4i si f (t5 i) (H - t5 i) hrep4i' b
      (by have := h5le i hi; omega) hbagb
    rw [hl, Option.bind_some]
    obtain ⟨⟨a, hasc, hperm⟩, -⟩ := hrep5i
    exact decodeBag_of_perm l _ a hasc (hlperm.trans hperm)

/-! ## T4: the finite form of Conjecture 0 -/

/-- T4 (PLAN.md section 2), Smith's Conjecture 0 in finite form. For every
    two-colour cyclic tag system `C0`, initial configuration `cfg` and budget
    `N` such that the run of `C0` lasts the `appendants.length * N` steps of
    the budget and leaves a nonempty word, there are a wolfram23
    configuration `start` (the tape of the composed encoders, the head on
    the first cell of the first block in state A), a block width `2^w`, a
    band `b`, strictly increasing times and an exit time `T` such that:

    * at time `times i` the tape decodes, by `decodeW23`, to the doubled
      working string of the `i`-th cyclic tag configuration;
    * up to time `T` the run stays on the explicit tape (`biSize` is
      constant: no cell beyond it is visited);
    * at time `T + 1` the head is on the cell right of the tape, a 0, in
      state A: Smith's exit condition. -/
theorem conjecture0_finite (C0 : CTS) (cfg : CTSConfig) (N : Nat) (c' : CTSConfig)
    (hrun : C0.nSteps cfg (C0.appendants.length * N) = some c') (hne : c'.data ≠ []) :
    ∃ (start : BiTM.Config) (w b : Nat) (times : Nat → Nat) (T : Nat),
      IsValidWolfram23Cfg start ∧ start.state = 1 ∧
      (∀ i, i < C0.appendants.length * N → times i < times (i + 1)) ∧
      (∀ i, i ≤ C0.appendants.length * N → times i ≤ T ∧
        ∃ ci cfgi, C0.nSteps cfg i = some ci ∧ BiTM.nSteps wolfram23 start (times i) = some cfgi ∧
          decodeW23 (2 ^ w) b cfgi = some (dbl ci.data)) ∧
      (∀ τ, τ ≤ T → ∃ cfgτ, BiTM.nSteps wolfram23 start τ = some cfgτ ∧ biSize cfgτ = biSize start) ∧
      (∃ L : List Nat, BiTM.nSteps wolfram23 start (T + 1) = some ⟨1, L, 0, []⟩ ∧
        L.length = biSize start) := by
  obtain ⟨n, hn⟩ : ∃ n, n = C0.appendants.length * N := ⟨_, rfl⟩
  rw [← hn] at hrun ⊢
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = ctsToSystem5 C0 cfg N := ⟨_, rfl⟩
  obtain ⟨t5, h50, h5mono, h5tr⟩ := conjecture5_finite_exact C0 cfg N n (le_of_eq hn) c' hrun
  rw [← hs0] at h5tr
  obtain ⟨cn, sn, hcn, hsn, hrep5n, hlenn⟩ := h5tr n (le_refl n)
  rw [hrun] at hcn
  obtain rfl := Option.some.inj hcn
  have hrules_n : sn.rules = [] := by
    have h0 : sn.rules.length = 0 := by rw [hlenn, ← hn]; simp
    exact List.length_eq_zero_iff.mp h0
  obtain ⟨B0, hB0, hbound0⟩ := exists_Bound5 s0
  have hboundn := Bound5_nSteps s0 B0 (t5 n) sn hbound0 hsn
  have hbagne : sn.bag ≠ [] :=
    Represents_bag_ne_nil sn (double C0) (dblCfg _) _ hrep5n (by simpa [dblCfg] using hne)
  obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil sn.bag hbagne
  obtain ⟨M, hM⟩ : ∃ M : Nat, M = (B0 + t5 n).toNat := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Nat, H = t5 n + M + 1 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : Nat, f = B0.toNat + 2 * H + 2 * t5 n + 5 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Nat, b = 2 * f - 2 * t5 n - 2 := ⟨_, rfl⟩
  have hB0n := Int.self_le_toNat B0
  have hf1 : 1 ≤ f := by omega
  have hbag1 : ∀ e ∈ s0.bag, 1 ≤ e ∧ e < f := by
    intro e he
    have h1 := ctsToSystem5_bag_ge_one C0 cfg N e (hs0 ▸ he)
    have h2 := hbound0.1 e he
    constructor <;> omega
  have hrules0 : ∀ r ∈ s0.rules, r.Nodup ∧ ∀ k ∈ r, 0 ≤ k ∧ k + 2 * H < f := by
    intro r hr
    refine ⟨ctsToSystem5_rules_nodup C0 cfg N r (hs0 ▸ hr), fun k hk => ?_⟩
    have h1 := ctsToSystem5_rules_ge_three C0 cfg N r (hs0 ▸ hr) k hk
    have h2 := hbound0.2 r hr k hk
    constructor <;> omega
  have hrules0' : ∀ r ∈ s0.rules, ∀ k ∈ r, 0 ≤ k ∧ k < f := by
    intro r hr k hk
    have := (hrules0 r hr).2 k hk
    constructor <;> omega
  obtain ⟨t4, h40, h4mono, h4tr⟩ := conjecture4_finite s0 f H (t5 n)
    (hs0 ▸ ctsToSystem5_bag_nodup C0 cfg N) hbag1 hrules0 (by omega) (by omega) sn hsn
  obtain ⟨sL, c4L, hsL, hc4L, hrepL⟩ := h4tr (t5 n) (le_refl _)
  rw [hsn] at hsL
  obtain rfl := Option.some.inj hsL
  have hrepL' : RepS4 c4L sn f (t5 n) (1 + M) := by
    have : H - t5 n = 1 + M := by omega
    rw [this] at hrepL; exact hrepL
  have he0le : e0 ≤ (M : Int) + 1 := by
    have := hboundn.1 e0 he0
    have := Int.self_le_toNat (B0 + t5 n)
    omega
  obtain ⟨k, cE, hrunE, hstE, hactE, hnoneE⟩ :=
    repS4_terminal M c4L sn f (t5 n) 1 hrepL' hrules_n ⟨e0, he0, he0le⟩
  obtain ⟨K, hKne, -, hc4Leq, -⟩ := hrepL
  have hk1 : 1 ≤ k := by
    cases k with
    | zero =>
      rw [System4.nSteps_zero] at hrunE
      obtain rfl := Option.some.inj hrunE
      rw [hc4Leq] at hstE
      cases hstE
    | succ k => omega
  obtain ⟨T4, hT4⟩ : ∃ T4, T4 = t4 (t5 n) + k := ⟨_, rfl⟩
  have hrunT4 : System4.nSteps (system5ToSystem4 s0 f) T4 = some cE := by
    rw [hT4, System4.nSteps_add, hc4L, Option.bind_some, hrunE]
  obtain ⟨h4, hh4⟩ : ∃ h4, h4 = T4 + b := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = h4 + 3 * f + 6 := ⟨_, rfl⟩
  have hw2 : w < 2 ^ w := Nat.lt_two_pow_self
  have hN3 : h4 + 3 ≤ 2 ^ w := by omega
  have h3f : 3 * f + 3 ≤ 2 ^ w := by omega
  have hc40 : system5ToSystem4 s0 f = ⟨System4Elem.set (encodeBag s0.bag) ::
      (starredEmptyPairs f ++ s0.rules.flatMap (fun r => encodeS5RuleToS4Elems r f)), 0,
      System4State.A⟩ := rfl
  have hwf := system5ToSystem4_wellFormed s0 f hf1
  have hlast := system5ToSystem4_last_set s0 f hf1
  have hbnd : ∀ S, System4Elem.set S ∈ System4Elem.set (encodeBag s0.bag) ::
      (starredEmptyPairs f ++ s0.rules.flatMap (fun r => encodeS5RuleToS4Elems r f)) →
      ∀ e ∈ S, 0 ≤ e ∧ e.toNat < 2 ^ w := by
    intro S hS e he
    have := system5ToSystem4_elem_lt s0 f hbag1 hrules0' S (by rw [hc40]; exact hS) e he
    constructor <;> omega
  rw [hc40] at hwf hlast hrunT4
  obtain ⟨times0, h00, h0mono, h0tr⟩ := conjecture3_finite w h4 T4 (encodeBag s0.bag) _ hN3 hwf
    hlast hbnd (by omega) cE hrunT4
  obtain ⟨start3, hstart3⟩ : ∃ c, c = phi2 (phi3 (initAC w h4 (encodeBag s0.bag)
      (starredEmptyPairs f ++ s0.rules.flatMap (fun r => encodeS5RuleToS4Elems r f))).toL) :=
    ⟨_, rfl⟩
  rw [← hstart3] at h0tr
  have hst3 : start3.state ≠ C := by rw [hstart3]; exact phi2_state_ne_C _
  have hstart_state : (toBi start3).state = 1 := by rw [hstart3]; rfl
  obtain ⟨cT, c3T, hcT, hrun0T, hrep3T⟩ := h0tr T4 (le_refl _)
  rw [hrunT4] at hcT
  obtain rfl := Option.some.inj hcT
  obtain ⟨L3, rfl⟩ := rep3_exit c3T cE w _ hrep3T hactE hstE
  have h0le : ∀ j, j ≤ T4 → times0 j ≤ times0 T4 := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact le_of_lt (strictMono_of_succ times0 T4 h0mono j T4 hlt (le_refl _))
    · exact le_refl _
  have h4le : ∀ j, j ≤ t5 n → t4 j ≤ t4 (t5 n) := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact le_of_lt (strictMono_of_succ t4 (t5 n) h4mono j _ hlt (le_refl _))
    · exact le_refl _
  have h5le : ∀ i, i ≤ n → t5 i ≤ t5 n := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with hlt | rfl
    · exact le_of_lt (strictMono_of_succ t5 n h5mono i n hlt (le_refl _))
    · exact le_refl _
  refine ⟨toBi start3, w, b, fun i => times0 (t4 (t5 i) + 1), times0 T4,
    toBi_valid start3 hst3, hstart_state, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h1 : t5 i < t5 (i + 1) := h5mono i hi
    have h2 : t5 (i + 1) ≤ t5 n := h5le (i + 1) hi
    have h3 : t4 (t5 i) < t4 (t5 (i + 1)) := strictMono_of_succ t4 (t5 n) h4mono _ _ h1 h2
    have h4' : t4 (t5 (i + 1)) + 1 ≤ T4 := by
      have := h4le (t5 (i + 1)) h2
      omega
    exact strictMono_of_succ times0 T4 h0mono _ _ (by omega) h4'
  · intro i hi
    obtain ⟨ci, si, hci, hsi, hrep5i, -⟩ := h5tr i hi
    obtain ⟨si', c4i, hsi', hc4i, hrep4i⟩ := h4tr (t5 i) (h5le i hi)
    rw [hsi] at hsi'
    obtain rfl := Option.some.inj hsi'
    have hd : t4 (t5 i) + 1 ≤ T4 := by
      have := h4le (t5 i) (h5le i hi)
      omega
    obtain ⟨cd, c3d, hcd, hrun0d, hrep3d⟩ := h0tr (t4 (t5 i) + 1) hd
    have hrep4i' := hrep4i
    obtain ⟨K, hKne, -, hc4ieq, hjh, -, -, -, -⟩ := hrep4i
    obtain ⟨K0, K', rfl⟩ := List.exists_cons_of_ne_nil hKne
    obtain ⟨g, hg⟩ : ∃ g, f - 2 * t5 i = g + 1 := ⟨f - 2 * t5 i - 1, by omega⟩
    have hE : sets (K0 :: K') ++ starredEmptyPairs (f - 2 * t5 i) ++ encBlocks si.rules f (2 * t5 i)
        = sets (K0 :: K') ++ System4Elem.star ::
            (System4Elem.set [] :: (starredEmptyPairs g ++ encBlocks si.rules f (2 * t5 i))) := by
      rw [hg, starredEmptyPairs_succ]
      simp only [List.append_assoc, List.cons_append]
    have hcd' : System4.nSteps ⟨System4Elem.set (encodeBag s0.bag) ::
        (starredEmptyPairs f ++ s0.rules.flatMap (fun r => encodeS5RuleToS4Elems r f)), 0,
        System4State.A⟩ (t4 (t5 i) + 1)
        = some ⟨sets (K0 :: K') ++ System4Elem.star ::
            (System4Elem.set [] :: (starredEmptyPairs g ++ encBlocks si.rules f (2 * t5 i))), 0,
            System4State.B⟩ := by
      rw [System4.nSteps_add, ← hc40, hc4i, Option.bind_some, System4.nSteps_one, hc4ieq, hE]
      show System4.step ⟨System4Elem.set K0 :: (sets K' ++ System4Elem.star ::
        (System4Elem.set [] :: (starredEmptyPairs g ++ encBlocks si.rules f (2 * t5 i)))), 0,
        System4State.A⟩ = _
      rw [step_setA_zero]
      rfl
    rw [hcd'] at hcd
    obtain rfl := Option.some.inj hcd
    refine ⟨h0le _ hd, ci, toBi (phi2 (phi3 c3d)), hci, (toBi_run start3 hst3 _ _ hrun0d).1, ?_⟩
    rw [rep3_decode_zero c3d (K0 :: K') _ w _ b (by simp) (by omega) _ hrep3d,
      decodeS4_state _ _ _ System4State.A, ← hE, ← hc4ieq]
    have hbagb : ∀ e ∈ si.bag, 2 * e - 2 < b := by
      intro e he
      have h1 := (Bound5_nSteps s0 B0 (t5 i) si hbound0 hsi).1 e he
      have h2 := h5le i hi
      omega
    obtain ⟨l, hl, hlperm⟩ := RepS4_decode_band c4i si f (t5 i) (H - t5 i) hrep4i' b
      (by have := h5le i hi; omega) hbagb
    rw [hl, Option.bind_some]
    obtain ⟨⟨a, hasc, hperm⟩, -⟩ := hrep5i
    exact decodeBag_of_perm l _ a hasc (hlperm.trans hperm)
  · intro τ hτ
    obtain ⟨cτ, hcτ⟩ := StepSys.nSteps_some_of_le (lsys sys0) start3 _ (times0 T4) τ hτ hrun0T
    refine ⟨toBi cτ, (toBi_run start3 hst3 τ cτ hcτ).1, ?_⟩
    rw [biSize_toBi, biSize_toBi, lnSteps_length sys0 start3 τ cτ hcτ]
  · refine ⟨0 :: (L3.map sw).map Fin.val, ?_, ?_⟩
    · rw [biNSteps_add, (toBi_run start3 hst3 _ _ hrun0T).1, Option.bind_some, biNSteps_one, phi_exit]
      exact wolfram23_exit_step _
    · rw [biSize_toBi, ← lnSteps_length sys0 start3 _ _ hrun0T, phi_exit]
      simp [LConfig.toList]

end Smith
