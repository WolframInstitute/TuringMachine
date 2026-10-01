/-
  Smith.Conjecture4

  PLAN.md target T2, link C (milestone M3): the System 4 tape `s52s4.pl`
  emits for a System 5 program emulates the System 5 run (TM23Proof.pdf
  p. 16-18, "Conjecture 5 implies conjecture 4").

  The relation `RepS4` between a System 4 configuration and a System 5
  configuration is the "condition during execution" of p. 17: the head is
  at the left end in state A; the tape is a block of adjacent sets (the
  bag "conglomerate"), then `f - t` star/empty pairs, then one block per
  remaining rule whose rule set is `0..3f` toggled at `2k + f + 3 - t` for
  every entry `k` of the rule, where `t = 2j` after `j` System 5 steps.
  The symmetric difference of the conglomerate agrees with the encoded bag
  `2e - 2` below the band `2f - t - 2`; above the band it is unconstrained
  (the all-integers sets leave debris there, which never reaches the head
  within the budget).  The budget `h` of remaining steps bounds the rule
  entries, so that every integer popped into the bag stays below the band.

  Contents:
    * `rulePos`, `encRuleSet`, `encBlock`, `encBlocks`: the rule blocks at
      parameter `t`; `encBlocks_shift` (one System 5 step is `t + 2`) and
      `system5ToSystem4_eq` (the encoder is the case `t = 0`).
    * `RepS4` and `system5ToSystem4_repS4`, the initial condition.
    * `repS4_dStep`, `repS4_pStep`: the per-step lemma, both cases.
    * `repS4_exit`: the pop attempt with no rule left leaves the tape in
      state C.
    * `repS4_forwardSim`, `conjecture4_finite`: T2.
    * `leadSets`, `decodeS4`, `RepS4_decode`: the partial decoder of the
      link, which reads the System 5 bag off the tape at every scheduled
      time.
    * `conjecture4_cts`, `conjecture4_cts_exists_f`: links B and C
      composed, the System 4 tape of `cy2s5.pl` output tracks the cyclic
      tag run, for every large enough `f`.
-/

import Smith.System4Runs
import Smith.ConjectureFive
import Mathlib.Data.List.Nodup

namespace Smith

open TagSystem
open BiTM
open System4Elem System4State

/-! ## Rule blocks at parameter `t` -/

/-- The System 4 integer that stands for the System 5 rule entry `k` after
    `t` units of the running parameter of p. 17: `k` is increased by 1 per
    System 5 step while the tape integer is fixed, and `t` grows by 2. -/
def rulePos (f t : Nat) (k : Int) : Int := 2 * k + f + 3 - t

/-- The rule set of a rule block: `0..3f` toggled at the positions of the
    rule entries. -/
def encRuleSet (r : List Int) (f t : Nat) : List Int :=
  xorMerge (allInts (f * 3 + 1)) (r.map (rulePos f t))

/-- One rule block: star, rule set, `2f` pairs, star, all integers, `2f - 2` pairs. -/
def encBlock (r : List Int) (f t : Nat) : List System4Elem :=
  star :: set (encRuleSet r f t) :: starredEmptyPairs (f * 2) ++
    star :: set (allInts (f * 3 + 1)) :: starredEmptyPairs (f * 2 - 2)

/-- The rule blocks of a rule list. -/
def encBlocks (rules : List (List Int)) (f t : Nat) : List System4Elem :=
  rules.flatMap (fun r => encBlock r f t)

@[simp] theorem encBlocks_nil (f t : Nat) : encBlocks [] f t = [] := rfl

theorem encBlocks_cons (r : List Int) (rules : List (List Int)) (f t : Nat) :
    encBlocks (r :: rules) f t = encBlock r f t ++ encBlocks rules f t := by
  simp [encBlocks]

theorem rulePos_shift (f t : Nat) (k : Int) : rulePos f (t + 2) (k + 1) = rulePos f t k := by
  unfold rulePos
  omega

theorem encRuleSet_shift (r : List Int) (f t : Nat) :
    encRuleSet (r.map (· + 1)) f (t + 2) = encRuleSet r f t := by
  unfold encRuleSet
  rw [List.map_map]
  congr 2
  funext k
  exact rulePos_shift f t k

/-- One System 5 step increments every rule entry and adds 2 to `t`; the
    tape does not change. -/
theorem encBlocks_shift (rules : List (List Int)) (f t : Nat) :
    encBlocks (rules.map (fun r => r.map (· + 1))) f (t + 2) = encBlocks rules f t := by
  induction rules with
  | nil => rfl
  | cons r rest ih =>
    rw [List.map_cons, encBlocks_cons, encBlocks_cons, ih]
    simp [encBlock, encRuleSet_shift]

theorem encodeS5RuleToS4Set_eq (r : List Int) (f : Nat) :
    encodeS5RuleToS4Set r f = encRuleSet r f 0 := by
  unfold encodeS5RuleToS4Set encRuleSet xorMerge
  rw [List.foldl_map]
  congr 1
  funext acc k
  congr 1
  unfold rulePos
  omega

theorem encodeS5RuleToS4Elems_eq (r : List Int) (f : Nat) :
    encodeS5RuleToS4Elems r f = encBlock r f 0 := by
  simp [encodeS5RuleToS4Elems, encBlock, encodeS5RuleToS4Set_eq]

/-- The encoder output is the case `t = 0`, with the bag as a one-set block. -/
theorem system5ToSystem4_eq (s : System5Config) (f : Nat) :
    system5ToSystem4 s f
      = ⟨sets [encodeBag s.bag] ++ starredEmptyPairs f ++ encBlocks s.rules f 0, 0, A⟩ := by
  simp [system5ToSystem4, encBlocks, sets, encodeS5RuleToS4Elems_eq]

/-! ## Membership in the rule sets -/

theorem allInts_mem (n : Nat) (x : Int) : x ∈ allInts n ↔ 0 ≤ x ∧ x < n := by
  unfold allInts
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h0, hn⟩
    exact ⟨x.toNat, by omega, by omega⟩

theorem rulePos_injective (f t : Nat) : Function.Injective (rulePos f t) := by
  intro a b h
  unfold rulePos at h
  omega

theorem encRuleSet_nodup (r : List Int) (f t : Nat) : (encRuleSet r f t).Nodup :=
  xorMerge_nodup _ _ (allInts_nodup _)

theorem encRuleSet_mem (r : List Int) (f t : Nat) (hr : r.Nodup) (x : Int) :
    x ∈ encRuleSet r f t
      ↔ ((0 ≤ x ∧ x ≤ 3 * f) ∧ ¬ (∃ k ∈ r, x = rulePos f t k))
        ∨ (¬ (0 ≤ x ∧ x ≤ 3 * f) ∧ (∃ k ∈ r, x = rulePos f t k)) := by
  unfold encRuleSet
  rw [xorMerge_mem_iff _ _ (allInts_nodup _)
      (nodup_map_of_injective _ (fun a b hab => rulePos_injective f t hab) hr),
    allInts_mem]
  have h : (∃ k ∈ r, x = rulePos f t k) ↔ x ∈ r.map (rulePos f t) := by
    simp only [List.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  rw [← h]
  constructor
  · rintro (⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨⟨h0, by omega⟩, h2⟩
    · exact Or.inr ⟨fun ⟨h0, h3⟩ => h1 ⟨h0, by omega⟩, h2⟩
  · rintro (⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨⟨h0, by omega⟩, h2⟩
    · exact Or.inr ⟨fun ⟨h0, h3⟩ => h1 ⟨h0, by omega⟩, h2⟩

theorem encRuleSet_nonneg (r : List Int) (f t : Nat) (hr : ∀ k ∈ r, 0 ≤ k) (ht : t ≤ f) :
    ∀ x ∈ encRuleSet r f t, 0 ≤ x := by
  intro x hx
  rcases xorMerge_mem_or _ _ _ hx with h | h
  · exact ((allInts_mem _ _).mp h).1
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
    have := hr k hk
    unfold rulePos
    omega

/-- Below the first rule position every integer of `0..3f` is in the rule
    set. -/
theorem encRuleSet_mem_low (r : List Int) (f t : Nat) (hr : ∀ k ∈ r, 0 ≤ k)
    (hf : 2 ≤ f) (hrn : r.Nodup) (x : Int) (h0 : 0 ≤ x) (hx : x + t < f + 3) :
    x ∈ encRuleSet r f t := by
  rw [encRuleSet_mem r f t hrn]
  left
  refine ⟨⟨h0, by omega⟩, ?_⟩
  rintro ⟨k, hk, rfl⟩
  have := hr k hk
  unfold rulePos at hx
  omega

theorem xorInsert_mem_iff (y : Int) (xs : List Int) (h : xs.Nodup) (x : Int) :
    x ∈ xorInsert y xs ↔ (x ∈ xs ↔ x ≠ y) := by
  by_cases hxy : x = y
  · subst hxy
    rw [xorInsert_mem_self_iff_nodup _ _ h]
    simp
  · rw [xorInsert_mem_other_iff _ _ _ hxy]
    simp [hxy]

theorem xorInsert_nonneg (y : Int) (hy : 0 ≤ y) (xs : List Int) (h : ∀ x ∈ xs, 0 ≤ x) :
    ∀ x ∈ xorInsert y xs, 0 ≤ x := by
  intro x hx
  unfold xorInsert at hx
  split_ifs at hx with hm
  · exact h x (List.mem_of_mem_erase hx)
  · rcases List.mem_cons.mp hx with rfl | hx'
    · exact hy
    · exact h x hx'

/-! ## The relation -/

/-- The condition during execution of TM23Proof.pdf p. 17, after `j` System
    5 steps with `h` steps of budget left.  See the module header. -/
def RepS4 (c : System4Config) (s : System5Config) (f j h : Nat) : Prop :=
  ∃ K : List (List Int),
    K ≠ [] ∧
    (∀ S ∈ K, S.Nodup ∧ ∀ x ∈ S, 0 ≤ x) ∧
    c = ⟨sets K ++ starredEmptyPairs (f - 2 * j) ++ encBlocks s.rules f (2 * j), 0, A⟩ ∧
    2 * j + 2 * h < f ∧
    (∀ x : Int, 0 ≤ x → x + 2 * j + 2 < 2 * f →
      parMem x K = decide (∃ e ∈ s.bag, x = 2 * e - 2)) ∧
    s.bag.Nodup ∧
    (∀ e ∈ s.bag, 1 ≤ e ∧ e + j < f) ∧
    (∀ r ∈ s.rules, r.Nodup ∧ ∀ k ∈ r, 0 ≤ k ∧ k + j + 2 * h < f)

/-- The encoder output stands in the relation at `j = 0` for every budget
    `h` the bounds afford. -/
theorem system5ToSystem4_repS4 (s : System5Config) (f h : Nat)
    (hbag : s.bag.Nodup) (hbag1 : ∀ e ∈ s.bag, 1 ≤ e ∧ e < f)
    (hrules : ∀ r ∈ s.rules, r.Nodup ∧ ∀ k ∈ r, 0 ≤ k ∧ k + 2 * h < f)
    (hf : 2 * h < f) :
    RepS4 (system5ToSystem4 s f) s f 0 h := by
  refine ⟨[encodeBag s.bag], by simp, ?_, ?_, by omega, ?_, hbag, ?_, ?_⟩
  · intro S hS
    rw [List.mem_singleton] at hS
    subst hS
    refine ⟨encodeBag_nodup _, ?_⟩
    intro x hx
    rw [encodeBag_eq_reverse_map _ hbag, List.mem_reverse, List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    have := (hbag1 e he).1
    unfold system5BagEntryToSystem4
    omega
  · rw [system5ToSystem4_eq]
    simp
  · intro x _ _
    rw [parMem_cons, parMem_nil, Bool.xor_false, decide_eq_decide,
      encodeBag_eq_reverse_map _ hbag, List.mem_reverse, List.mem_map]
    unfold system5BagEntryToSystem4
    constructor
    · rintro ⟨e, he, rfl⟩; exact ⟨e, he, by omega⟩
    · rintro ⟨e, he, rfl⟩; exact ⟨e, he, by omega⟩
  · intro e he
    have := hbag1 e he
    omega
  · intro r hr
    obtain ⟨h1, h2⟩ := hrules r hr
    refine ⟨h1, fun k hk => ?_⟩
    have := h2 k hk
    omega

/-! ## The per-step lemma, D-step case -/

/-- A System 5 step without a pop (`1` is not in the bag) is matched by
    the D-step run of `Smith.System4Runs`. -/
theorem repS4_dStep (c : System4Config) (s : System5Config) (f j h : Nat)
    (hrep : RepS4 c s f j (h + 1)) (h1 : (1 : Int) ∉ s.bag) :
    ∃ k, 1 ≤ k ∧ ∃ c', System4.nSteps c k = some c' ∧
      RepS4 c' { bag := s.bag.map (· - 1), rules := s.rules.map (fun r => r.map (· + 1)) }
        f (j + 1) h := by
  obtain ⟨K, hKne, hKwf, rfl, hjh, hpar, hnd, hbag1, hrl⟩ := hrep
  have hKn : ∀ S ∈ K, S.Nodup := fun S hS => (hKwf S hS).1
  have hKn' : ∀ S ∈ K.map decr, S.Nodup := by
    intro S hS
    obtain ⟨S0, h0, rfl⟩ := List.mem_map.mp hS
    exact decr_nodup _ (hKn S0 h0)
  have hf2 : 2 ≤ f - 2 * j := by omega
  have hp0 : parMem 0 K = false := by
    rw [hpar 0 (by omega) (by omega)]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro e he hx
    have : e = 1 := by omega
    exact h1 (this ▸ he)
  have hp1 : parMem 0 (K.map decr) = false := by
    rw [parMem_map_decr 0 K hKn (by omega), Int.zero_add, hpar 1 (by omega) (by omega)]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro e he hx
    omega
  refine ⟨4 * K.length + 4, by omega, _, dStep K (f - 2 * j) _ hKne hf2 hp0 hp1, ?_⟩
  refine ⟨(K.map decr).map decr ++ [[], []], by simp, ?_, ?_, by omega, ?_,
    nodup_map_sub_one hnd, ?_, ?_⟩
  · intro S hS
    rcases List.mem_append.mp hS with hS | hS
    · obtain ⟨S1, hS1, rfl⟩ := List.mem_map.mp hS
      obtain ⟨S0, hS0, rfl⟩ := List.mem_map.mp hS1
      obtain ⟨hn, hnn⟩ := hKwf S0 hS0
      exact ⟨decr_nodup _ (decr_nodup _ hn), decr_nonneg _ (decr_nodup _ hn) (decr_nonneg _ hn hnn)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl <;> exact ⟨List.nodup_nil, by simp⟩
  · simp only [System4Config.mk.injEq, and_true]
    have e1 : f - 2 * (j + 1) = f - 2 * j - 2 := by omega
    have e2 : 2 * (j + 1) = 2 * j + 2 := by omega
    rw [e1, e2, encBlocks_shift]
  · intro x hx0 hxb
    rw [parMem_append, parMem_map_decr _ _ hKn' (by omega), parMem_map_decr _ _ hKn (by omega)]
    simp only [parMem_cons, parMem_nil, List.not_mem_nil, decide_false, Bool.xor_false]
    rw [hpar (x + 1 + 1) (by omega) (by omega), decide_eq_decide]
    simp only [List.mem_map]
    constructor
    · rintro ⟨e, he, hx⟩; exact ⟨e - 1, ⟨e, he, rfl⟩, by omega⟩
    · rintro ⟨_, ⟨e, he, rfl⟩, hx⟩; exact ⟨e, he, by omega⟩
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
    have := hbag1 e he
    have hne : e ≠ 1 := fun h => h1 (h ▸ he)
    constructor <;> omega
  · intro r' hr'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨hn, hb⟩ := hrl r hr
    refine ⟨nodup_map_add_one hn, ?_⟩
    intro k' hk'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'
    have := hb k hk
    constructor <;> omega

/-! ## Well-formed sets -/

/-- A set of the tape: no duplicates, no negative integers. -/
def WFset (S : List Int) : Prop := S.Nodup ∧ ∀ x ∈ S, 0 ≤ x

theorem WFset_nil : WFset [] := ⟨List.nodup_nil, by simp⟩

theorem WFset_zero : WFset [0] := ⟨by decide, by simp⟩

theorem WFset_decr (S : List Int) (h : WFset S) : WFset (decr S) :=
  ⟨decr_nodup _ h.1, decr_nonneg _ h.1 h.2⟩

theorem WFset_decrN (i : Nat) (S : List Int) (h : WFset S) : WFset (decrN i S) :=
  ⟨decrN_nodup _ _ h.1, decrN_nonneg _ _ h.1 h.2⟩

theorem WFset_xorInsert_one (S : List Int) (h : WFset S) : WFset (xorInsert 1 S) :=
  ⟨xorInsert_nodup _ _ h.1, xorInsert_nonneg 1 (by decide) _ h.2⟩

theorem WFset_map_decr (K : List (List Int)) (h : ∀ S ∈ K, WFset S) :
    ∀ S ∈ K.map decr, WFset S := by
  intro S hS
  obtain ⟨S0, h0, rfl⟩ := List.mem_map.mp hS
  exact WFset_decr _ (h S0 h0)

theorem WFset_append (K K' : List (List Int)) (h : ∀ S ∈ K, WFset S) (h' : ∀ S ∈ K', WFset S) :
    ∀ S ∈ K ++ K', WFset S := by
  intro S hS
  rcases List.mem_append.mp hS with hS | hS
  · exact h S hS
  · exact h' S hS

theorem WFset_replicate_nil (i : Nat) : ∀ S ∈ List.replicate i ([] : List Int), WFset S := by
  intro S hS
  rw [List.eq_of_mem_replicate hS]
  exact WFset_nil

theorem WFset_loopK (i : Nat) (R : List Int) (h : WFset R) : ∀ S ∈ loopK i R, WFset S := by
  unfold loopK
  refine WFset_append _ _ (WFset_append _ _ ?_ ?_) (WFset_replicate_nil _)
  · intro S hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact WFset_zero
    · exact WFset_replicate_nil _ S hS
  · intro S hS
    rw [List.mem_singleton] at hS
    exact hS ▸ h

theorem WFset_singleton_nil : ∀ S ∈ [([] : List Int)], WFset S := by
  intro S hS
  rw [List.mem_singleton] at hS
  exact hS ▸ WFset_nil

/-! ## The per-step lemma, P-step case -/

/-- The symmetric difference read through the injection `e |-> 2 * e - 2`. -/
theorem exists_xor_encode {P Q : Int → Prop} (x : Int) :
    (∃ e, ((P e ∧ ¬ Q e) ∨ (¬ P e ∧ Q e)) ∧ x = 2 * e - 2)
      ↔ ((∃ e, P e ∧ x = 2 * e - 2) ∧ ¬ (∃ e, Q e ∧ x = 2 * e - 2))
        ∨ (¬ (∃ e, P e ∧ x = 2 * e - 2) ∧ (∃ e, Q e ∧ x = 2 * e - 2)) := by
  constructor
  · rintro ⟨e, (⟨hp, hq⟩ | ⟨hp, hq⟩), rfl⟩
    · left
      refine ⟨⟨e, hp, rfl⟩, ?_⟩
      rintro ⟨e', hq', he'⟩
      have : e' = e := by omega
      exact hq (this ▸ hq')
    · right
      refine ⟨?_, ⟨e, hq, rfl⟩⟩
      rintro ⟨e', hp', he'⟩
      have : e' = e := by omega
      exact hp (this ▸ hp')
  · rintro (⟨⟨e, hp, rfl⟩, hq⟩ | ⟨hp, ⟨e, hq, rfl⟩⟩)
    · exact ⟨e, Or.inl ⟨hp, fun h => hq ⟨e, h, rfl⟩⟩, rfl⟩
    · exact ⟨e, Or.inr ⟨fun h => hp ⟨e, h, rfl⟩, hq⟩, rfl⟩

/-- A System 5 step with a pop (`1` is in the bag) is matched by two pop
    phases of `Smith.System4Runs`, one at the rule set and one at the
    all-integers set. -/
theorem repS4_pStep (c : System4Config) (s : System5Config) (f j h : Nat)
    (r : List Int) (rest : List (List Int))
    (hrep : RepS4 c s f j (h + 1)) (hr : s.rules = r :: rest) (h1 : (1 : Int) ∈ s.bag) :
    ∃ k, 1 ≤ k ∧ ∃ c', System4.nSteps c k = some c' ∧
      RepS4 c' { bag := xorMerge ((s.bag.map (· - 1)).erase 0) (r.map (· + 1)),
                 rules := rest.map (fun r => r.map (· + 1)) } f (j + 1) h := by
  obtain ⟨bag, rules⟩ := s
  dsimp only at hr h1 ⊢
  subst hr
  obtain ⟨K, hKne, hKwf, rfl, hjh, hpar, hnd, hbag1, hrl⟩ := hrep
  dsimp only at hpar hnd hbag1 hrl ⊢
  have hKn : ∀ S ∈ K, S.Nodup := fun S hS => (hKwf S hS).1
  have hKwf' : ∀ S ∈ K, WFset S := hKwf
  have hf3 : 3 ≤ f := by omega
  obtain ⟨hrn, hrk⟩ := hrl r List.mem_cons_self
  have hrk0 : ∀ k ∈ r, 0 ≤ k := fun k hk => (hrk k hk).1
  -- expose the first rule block
  have hshape : sets K ++ starredEmptyPairs (f - 2 * j) ++ encBlocks (r :: rest) f (2 * j)
      = sets K ++ starredEmptyPairs (f - 2 * j)
          ++ star :: set (encRuleSet r f (2 * j)) :: starredEmptyPairs (f * 2)
          ++ (star :: set (allInts (f * 3 + 1)) :: starredEmptyPairs (f * 2 - 2)
              ++ encBlocks rest f (2 * j)) := by
    rw [encBlocks_cons]
    simp [encBlock]
  rw [hshape]
  -- names for the rule set, the all-integers set and the padding count
  obtain ⟨Rs, hRs⟩ : ∃ Rs, Rs = encRuleSet r f (2 * j) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = allInts (f * 3 + 1) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = f - 2 * j := ⟨_, rfl⟩
  rw [← hRs, ← hU, ← hg]
  have hg2 : 2 ≤ g := by omega
  have hRsW : WFset Rs := hRs ▸ ⟨encRuleSet_nodup _ _ _, encRuleSet_nonneg r f (2 * j) hrk0 (by omega)⟩
  have hUW : WFset U := hU ▸ ⟨allInts_nodup _, fun x hx => ((allInts_mem _ _).mp hx).1⟩
  have hXW : WFset (xorInsert 1 Rs) := WFset_xorInsert_one _ hRsW
  have hXUW : WFset (xorInsert 1 U) := WFset_xorInsert_one _ hUW
  have hXmem : ∀ x, x ∈ xorInsert 1 Rs ↔ (x ∈ Rs ↔ x ≠ 1) := xorInsert_mem_iff 1 Rs hRsW.1
  have hXUmem : ∀ x, x ∈ xorInsert 1 U ↔ (x ∈ U ↔ x ≠ 1) := xorInsert_mem_iff 1 U hUW.1
  have hlow : ∀ x : Int, 0 ≤ x → x + 2 * j < f + 3 → x ∈ Rs := fun x hx0 hx =>
    hRs ▸ encRuleSet_mem_low r f (2 * j) hrk0 (by omega) hrn x hx0 hx
  have hUmem : ∀ x : Int, 0 ≤ x → x ≤ 3 * f → x ∈ U := fun x hx0 hx => by
    rw [hU, allInts_mem]; constructor <;> omega
  -- zeros surface in the decremented sets below the first rule position
  have hdec : ∀ i : Nat, (i : Int) ≠ 1 → (i : Int) + 2 * j < f + 3 →
      0 ∈ decrN i (xorInsert 1 Rs) := by
    intro i hi1 hi
    rw [decrN_mem _ _ hXW.1 hXW.2, Int.zero_add, hXmem]
    exact ⟨by omega, fun _ => hi1, fun _ => hlow i (by omega) hi⟩
  have hdecU : ∀ i : Nat, (i : Int) ≠ 1 → (i : Int) ≤ 3 * f → 0 ∈ decrN i (xorInsert 1 U) := by
    intro i hi1 hi
    rw [decrN_mem _ _ hXUW.1 hXUW.2, Int.zero_add, hXUmem]
    exact ⟨by omega, fun _ => hi1, fun _ => hUmem i (by omega) hi⟩
  -- phase 1, at the rule set
  have hpar0 : parMem 0 K = true := by
    rw [hpar 0 (by omega) (by omega), decide_eq_true_eq]
    exact ⟨1, h1, by omega⟩
  have hX0 : 0 ∈ xorInsert 1 Rs := by
    rw [hXmem]; exact ⟨fun _ => by decide, fun _ => hlow 0 (by omega) (by omega)⟩
  have hX1 : 0 ∉ decr (xorInsert 1 Rs) := by
    rw [decr_mem _ hXW.1]
    rintro ⟨hm, _⟩
    rw [Int.zero_add, hXmem] at hm
    exact (hm.mp (hlow 1 (by omega) (by omega))) rfl
  obtain ⟨k1, hk1, e1⟩ := popPhase K g Rs (f * 2)
    (star :: set U :: starredEmptyPairs (f * 2 - 2) ++ encBlocks rest f (2 * j))
    hKne (by omega) (by omega) hpar0 hX0 hX1
    (fun i hi => hdec (i + 2) (by omega) (by omega))
    (hdec (g + 1) (by omega) (by omega))
  obtain ⟨K1, hK1⟩ : ∃ K1, K1 = K.map decr ++ (loopK (g - 1) (decrN (g + 1) (xorInsert 1 Rs))).map decr ++ [[]] :=
    ⟨_, rfl⟩
  obtain ⟨g2, hg2'⟩ : ∃ g2, g2 = f * 2 - g - 2 := ⟨_, rfl⟩
  rw [← hK1, ← hg2'] at e1
  -- phase 2, at the all-integers set
  have hK1ne : K1 ≠ [] := by simp [hK1]
  have hK1W : ∀ S ∈ K1, WFset S := hK1 ▸
    WFset_append _ _ (WFset_append _ _ (WFset_map_decr _ hKwf')
      (WFset_map_decr _ (WFset_loopK _ _ (WFset_decrN _ _ hXW)))) WFset_singleton_nil
  have hpar1 : parMem 0 K1 = true := by
    rw [hK1, parMem_append, parMem_append, parMem_map_decr _ _ hKn (by omega), Int.zero_add,
      hpar 1 (by omega) (by omega), parMem_loopK_map_decr]
    have hz : 0 ∈ decr (decr (decrN g (xorInsert 1 Rs))) := hdec (g + 1 + 1) (by omega) (by omega)
    have hno : ¬ ∃ e ∈ bag, (1 : Int) = 2 * e - 2 := by
      rintro ⟨e, _, he⟩; omega
    simp [hz, hno]
  have hXU0 : 0 ∈ xorInsert 1 U := by
    rw [hXUmem]; exact ⟨fun _ => by decide, fun _ => hUmem 0 (by omega) (by omega)⟩
  have hXU1 : 0 ∉ decr (xorInsert 1 U) := by
    rw [decr_mem _ hXUW.1]
    rintro ⟨hm, _⟩
    rw [Int.zero_add, hXUmem] at hm
    exact (hm.mp (hUmem 1 (by omega) (by omega))) rfl
  obtain ⟨k2, hk2, e2⟩ := popPhase K1 g2 U (f * 2 - 2) (encBlocks rest f (2 * j))
    hK1ne (by omega) (by omega) hpar1 hXU0 hXU1
    (fun i hi => hdecU (i + 2) (by omega) (by omega))
    (hdecU (g2 + 1) (by omega) (by omega))
  obtain ⟨K2, hK2⟩ : ∃ K2, K2 = K1.map decr ++ (loopK (g2 - 1) (decrN (g2 + 1) (xorInsert 1 U))).map decr ++ [[]] :=
    ⟨_, rfl⟩
  rw [← hK2] at e2
  -- the composite run
  simp only [List.append_assoc, List.cons_append] at e1 e2 ⊢
  refine ⟨k1 + k2, by omega, _, System4_nSteps_some_compose _ _ _ _ _ e1 e2, ?_⟩
  -- the relation after the step
  have hK2W : ∀ S ∈ K2, WFset S := hK2 ▸
    WFset_append _ _ (WFset_append _ _ (WFset_map_decr _ hK1W)
      (WFset_map_decr _ (WFset_loopK _ _ (WFset_decrN _ _ hXUW)))) WFset_singleton_nil
  have hA : ((bag.map (· - 1)).erase 0).Nodup := List.Nodup.erase _ (nodup_map_sub_one hnd)
  have hB : (r.map (· + 1)).Nodup := nodup_map_add_one hrn
  have hmemA : ∀ e : Int, e ∈ (bag.map (· - 1)).erase 0 ↔ (e ∈ bag.map (· - 1) ∧ e ≠ 0) := by
    intro e
    by_cases he : e = 0
    · subst he
      simp only [ne_eq, not_true_eq_false, and_false, iff_false]
      exact List.Nodup.not_mem_erase (nodup_map_sub_one hnd)
    · rw [List.mem_erase_of_ne he]
      simp [he]
  refine ⟨K2, by simp [hK2], hK2W, ?_, by omega, ?_, xorMerge_nodup _ _ hA, ?_, ?_⟩
  · -- tape shape
    simp only [System4Config.mk.injEq, and_true]
    have e3 : f * 2 - 2 - g2 - 2 = f - 2 * (j + 1) := by omega
    have e4 : 2 * (j + 1) = 2 * j + 2 := by omega
    rw [e3, e4, encBlocks_shift, List.append_assoc]
  · -- parity membership
    intro x hx0 hxb
    have hK1x : parMem (x + 1) K1 = (parMem (x + 1 + 1) K ^^ !decide (∃ k ∈ r, x = 2 * k)) := by
      rw [hK1, parMem_append, parMem_append, parMem_map_decr _ _ hKn (by omega),
        parMem_loopK_map_decr, ← decrN_succ, parMem_cons, parMem_nil]
      simp only [List.not_mem_nil, decide_false, Bool.xor_false]
      congr 1
      rw [← decide_not, decide_eq_decide, decrN_mem _ _ hXW.1 hXW.2, hXmem]
      have hne : x + 1 + ((g + 1 + 1 : Nat) : Int) ≠ 1 := by omega
      rw [hRs, encRuleSet_mem r f (2 * j) hrn]
      constructor
      · rintro ⟨_, hm⟩ ⟨k, hk, hxk⟩
        rcases hm.mpr hne with ⟨_, hnk⟩ | ⟨hb, _⟩
        · refine hnk ⟨k, hk, ?_⟩
          unfold rulePos
          clear hm hnk
          omega
        · exact hb ⟨by omega, by omega⟩
      · intro hnk
        refine ⟨by omega, ⟨fun _ => hne, fun _ => ?_⟩⟩
        left
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rintro ⟨k, hk, hxk⟩
        exact hnk ⟨k, hk, by unfold rulePos at hxk; omega⟩
    have hUx : decide (x ∈ decr (decrN (g2 + 1) (xorInsert 1 U))) = true := by
      rw [decide_eq_true_eq, ← decrN_succ, decrN_mem _ _ hXUW.1 hXUW.2, hXUmem]
      exact ⟨hx0, fun _ => by omega, fun _ => hUmem _ (by omega) (by omega)⟩
    rw [hK2, parMem_append, parMem_append,
      parMem_map_decr _ _ (fun S hS => (hK1W S hS).1) (by omega),
      hK1x, parMem_loopK_map_decr, hUx, parMem_cons, parMem_nil,
      hpar (x + 1 + 1) (by omega) (by omega)]
    simp only [List.not_mem_nil, decide_false, Bool.xor_false]
    have hnew : (∃ e ∈ xorMerge ((bag.map (· - 1)).erase 0) (r.map (· + 1)), x = 2 * e - 2)
        ↔ ((∃ e ∈ bag, x + 1 + 1 = 2 * e - 2) ∧ ¬ (∃ k ∈ r, x = 2 * k))
          ∨ (¬ (∃ e ∈ bag, x + 1 + 1 = 2 * e - 2) ∧ (∃ k ∈ r, x = 2 * k)) := by
      have hQ : (∃ e, e ∈ (bag.map (· - 1)).erase 0 ∧ x = 2 * e - 2)
          ↔ ∃ e ∈ bag, x + 1 + 1 = 2 * e - 2 := by
        constructor
        · rintro ⟨e, he, rfl⟩
          obtain ⟨hm, _⟩ := (hmemA e).mp he
          obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp hm
          exact ⟨e0, he0, by omega⟩
        · rintro ⟨e, he, hx⟩
          exact ⟨e - 1, (hmemA _).mpr ⟨List.mem_map.mpr ⟨e, he, rfl⟩, by omega⟩, by omega⟩
      have hR : (∃ e, e ∈ r.map (· + 1) ∧ x = 2 * e - 2) ↔ ∃ k ∈ r, x = 2 * k := by
        constructor
        · rintro ⟨e, he, rfl⟩
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
          exact ⟨k, hk, by omega⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨k + 1, List.mem_map.mpr ⟨k, hk, rfl⟩, by omega⟩
      rw [← hQ, ← hR, ← exists_xor_encode]
      constructor
      · rintro ⟨e, he, hx⟩
        exact ⟨e, (xorMerge_mem_iff _ _ hA hB e).mp he, hx⟩
      · rintro ⟨e, he, hx⟩
        exact ⟨e, (xorMerge_mem_iff _ _ hA hB e).mpr he, hx⟩
    by_cases hQ : ∃ e ∈ bag, x + 1 + 1 = 2 * e - 2 <;>
      by_cases hR : ∃ k ∈ r, x = 2 * k <;>
      simp [hQ, hR, hnew]
  · -- bag bounds
    intro e' he'
    rcases xorMerge_mem_or _ _ _ he' with hA' | hB'
    · obtain ⟨hm, hne⟩ := (hmemA e').mp hA'
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      have := hbag1 e he
      constructor <;> omega
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hB'
      have := hrk k hk
      constructor <;> omega
  · -- rule bounds
    intro r' hr'
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨hn, hb⟩ := hrl r0 (List.mem_cons_of_mem _ hr0)
    refine ⟨nodup_map_add_one hn, ?_⟩
    intro k' hk'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'
    have := hb k hk
    constructor <;> omega

/-! ## The exit in state C -/

/-- When the System 5 program attempts a pop with no rule left (`1` in the
    bag, empty rule list), the System 4 head runs off the right end of the
    tape in state C: the exit condition of Conjecture 4 (TM23Proof.pdf
    p. 10 and p. 18). -/
theorem repS4_exit (c : System4Config) (s : System5Config) (f j h : Nat)
    (hrep : RepS4 c s f j h) (hr : s.rules = []) (h1 : (1 : Int) ∈ s.bag) (hjf : j + 1 < f) :
    ∃ k c', System4.nSteps c k = some c' ∧ c'.state = C ∧
      c'.active = c'.elems.length ∧ System4.step c' = none := by
  obtain ⟨K, hKne, hKwf, rfl, hjh, hpar, hnd, hbag1, hrl⟩ := hrep
  rw [hr, encBlocks_nil, List.append_nil]
  have hpar0 : parMem 0 K = true := by
    rw [hpar 0 (by omega) (by omega), decide_eq_true_eq]
    exact ⟨1, h1, by omega⟩
  obtain ⟨S0, K', hSK⟩ := List.exists_cons_of_ne_nil hKne
  have e1 : System4.nSteps ⟨sets K ++ starredEmptyPairs (f - 2 * j), 0, A⟩ 1
      = some ⟨sets K ++ starredEmptyPairs (f - 2 * j), 0, B⟩ := by
    rw [System4.nSteps_one, hSK]
    simp only [sets_cons, List.cons_append]
    exact step_setA_zero _ _
  have e2 := sweep [] K (starredEmptyPairs (f - 2 * j)) B (by decide)
  simp only [List.nil_append, List.length_nil, Nat.zero_add, hpar0, flip_true, tog] at e2
  have e3 := cPhase (sets (K.map decr)) (f - 2 * j) []
  simp only [List.append_nil, sets_length, List.length_map] at e3
  refine ⟨1 + K.length + 2 * (f - 2 * j),
    ⟨sets (K.map decr) ++ starredZeroPairs (f - 2 * j), K.length + 2 * (f - 2 * j), C⟩, ?_, rfl, ?_, ?_⟩
  · rw [System4.nSteps_add, System4.nSteps_add, e1, Option.bind_some, e2, Option.bind_some, e3]
  · simp
  · apply System4.step_none_of_active_oob
    simp

/-! ## T2 -/

/-- T2 as a `ForwardSim`: the budget is the fuel of the source System 5,
    and the step count `j` of `RepS4` is the fuel spent from `h0`. -/
theorem repS4_forwardSim (f h0 : Nat) :
    ForwardSim (fueled system5Sys) system4Sys
      (fun p c => p.2 ≤ h0 ∧ RepS4 c p.1 f (h0 - p.2) p.2) := by
  rintro ⟨s, n⟩ c ⟨hle, hrep⟩ p hstep
  cases n with
  | zero => rw [fueled_step_zero] at hstep; exact absurd hstep (by simp)
  | succ h =>
    rw [fueled_step_succ] at hstep
    cases hs : system5Sys.step s with
    | none => rw [hs] at hstep; exact absurd hstep (by simp)
    | some s' =>
      rw [hs, Option.map_some] at hstep
      obtain rfl : p = (s', h) := (Option.some.inj hstep).symm
      rw [system5Sys_step] at hs
      obtain ⟨hbag, hrules⟩ := (System5_step_some_iff s).mp ⟨s', hs⟩
      have hj : h0 - h = h0 - (h + 1) + 1 := by omega
      by_cases h1 : (1 : Int) ∈ s.bag
      · obtain ⟨r, rest, hr⟩ := List.exists_cons_of_ne_nil hrules
        have hs' := System5_step_explicit_pop s r rest hr hbag
          ((System5_one_mem_iff_zero_in_decremented s.bag).mp h1)
        rw [hs] at hs'
        obtain rfl := Option.some.inj hs'
        obtain ⟨k, hk, c', hrun, hrep'⟩ := repS4_pStep c s f (h0 - (h + 1)) h r rest hrep hr h1
        refine ⟨k, hk, c', by rw [system4Sys_nSteps]; exact hrun, by omega, ?_⟩
        rw [hj]
        exact hrep'
      · have hz : (0 : Int) ∉ s.bag.map (· - 1) := fun hm =>
          h1 ((System5_one_mem_iff_zero_in_decremented s.bag).mpr hm)
        obtain ⟨hb', hr'⟩ := System5_step_pure_decrement s s' hs hbag hrules hz
        obtain ⟨k, hk, c', hrun, hrep'⟩ := repS4_dStep c s f (h0 - (h + 1)) h hrep h1
        refine ⟨k, hk, c', by rw [system4Sys_nSteps]; exact hrun, by omega, ?_⟩
        have hs'' : s' = { bag := s.bag.map (· - 1), rules := s.rules.map (fun r => r.map (· + 1)) } := by
          cases s'
          simp only [System5Config.mk.injEq]
          exact ⟨hb', hr'⟩
        rw [hj, hs'']
        exact hrep'

/-- T2, the finite form of "Conjecture 5 implies Conjecture 4" (PLAN.md
    section 2).  For a System 5 program whose integers are bounded in terms
    of the parameter `f` and the budget `h` as `system5ToSystem4_repS4`
    requires, the System 4 tape `system5ToSystem4 s f` tracks every System
    5 run of `n <= h` steps: there are strictly increasing System 4 times
    `times 0 = 0 < times 1 < ... < times n` at which the tape stands in the
    relation `RepS4` to the `i`-th System 5 configuration. -/
theorem conjecture4_finite (s : System5Config) (f h n : Nat)
    (hbag : s.bag.Nodup) (hbag1 : ∀ e ∈ s.bag, 1 ≤ e ∧ e < f)
    (hrules : ∀ r ∈ s.rules, r.Nodup ∧ ∀ k ∈ r, 0 ≤ k ∧ k + 2 * h < f)
    (hf : 2 * h < f) (hn : n ≤ h) (s' : System5Config) (hrun : System5.nSteps s n = some s') :
    ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ i, i < n → times i < times (i + 1)) ∧
      ∀ i, i ≤ n → ∃ si ci, System5.nSteps s i = some si ∧
        System4.nSteps (system5ToSystem4 s f) (times i) = some ci ∧ RepS4 ci si f i (h - i) := by
  obtain ⟨times, h0, hmono, htr⟩ := ForwardSim_nSteps (repS4_forwardSim f h) n (s, h)
    (system5ToSystem4 s f)
    ⟨le_refl h, by rw [Nat.sub_self]; exact system5ToSystem4_repS4 s f h hbag hbag1 hrules hf⟩
    (s', h - n) (by rw [fueled_nSteps _ _ _ _ hn, system5Sys_nSteps, hrun]; rfl)
  refine ⟨times, h0, hmono, fun i hi => ?_⟩
  obtain ⟨⟨si, hi'⟩, ci, hsi, hci, hle, hrep⟩ := htr i hi
  rw [fueled_nSteps _ _ _ _ (by omega), system5Sys_nSteps] at hsi
  cases hsi5 : System5.nSteps s i with
  | none => rw [hsi5] at hsi; simp at hsi
  | some si0 =>
    rw [hsi5, Option.map_some] at hsi
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsi)
    refine ⟨si0, ci, rfl, by rw [system4Sys_nSteps] at hci; exact hci, ?_⟩
    have : h - (h - i) = i := by omega
    rw [this] at hrep
    exact hrep

/-! ## The decoder -/

/-- The leftmost block of adjacent sets of a tape. -/
def leadSets : List System4Elem → List (List Int)
  | System4Elem.set S :: rest => S :: leadSets rest
  | _ => []

theorem leadSets_sets (K : List (List Int)) (R : List System4Elem)
    (hR : ∀ S, R.head? ≠ some (set S)) : leadSets (sets K ++ R) = K := by
  induction K with
  | nil =>
    cases R with
    | nil => rfl
    | cons e R' =>
      cases e with
      | star => rfl
      | set S => exact absurd rfl (hR S)
  | cons S K ih => simp [leadSets, ih]

/-- The decoder of link C: the parity set of the leftmost block below the
    band `b`, read as System 5 integers through `x |-> x / 2 + 1`; `none`
    if an odd integer is set, which never happens at a scheduled time. -/
def decodeS4 (c : System4Config) (b : Nat) : Option (List Int) :=
  let xs := ((List.range b).map (fun (i : Nat) => (i : Int))).filter
    (fun x => parMem x (leadSets c.elems))
  if xs.all (fun x => x % 2 = 0) then some (xs.map (fun x => x / 2 + 1)) else none

/-- At a scheduled time the decoder reads the System 5 bag, up to order. -/
theorem RepS4_decode (c : System4Config) (s : System5Config) (f j h : Nat)
    (hrep : RepS4 c s f j h) :
    ∃ l, decodeS4 c (2 * f - 2 * j - 2) = some l ∧ l.Perm s.bag := by
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
  have hmem : ∀ x : Int, x ∈ ((List.range (2 * f - 2 * j - 2)).map (fun (i : Nat) => (i : Int))).filter
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
      refine ⟨⟨(2 * e - 2).toNat, ?_, by omega⟩, ?_⟩
      · rw [List.mem_range]; omega
      · rw [hpar _ (by omega) (by omega), decide_eq_true_eq]
        exact ⟨e, he, by omega⟩
  have hall : (((List.range (2 * f - 2 * j - 2)).map (fun (i : Nat) => (i : Int))).filter
      (fun x => parMem x K)).all (fun x => x % 2 = 0) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨e, _, rfl⟩ := (hmem x).mp hx
    simp only [decide_eq_true_eq]
    omega
  rw [ite_eq_left hall]
  refine ⟨_, rfl, ?_⟩
  have hnd1 : (((List.range (2 * f - 2 * j - 2)).map (fun (i : Nat) => (i : Int))).filter
      (fun x => parMem x K)).Nodup :=
    List.Nodup.sublist List.filter_sublist
      (nodup_map_of_injective _ (fun a b hab => by omega) List.nodup_range)
  have hnd2 : ((((List.range (2 * f - 2 * j - 2)).map (fun (i : Nat) => (i : Int))).filter
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

/-! ## Links B and C composed -/

/-- A schedule that is strictly increasing on consecutive indices below `L`
    is strictly monotone on `[0, L]`. -/
theorem strictMono_of_succ (t : Nat → Nat) (L : Nat) (h : ∀ i, i < L → t i < t (i + 1)) :
    ∀ a b, a < b → b ≤ L → t a < t b := by
  intro a b hab hbL
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a b with hlt | hge
    · exact lt_trans (ih hlt (by omega)) (h b (by omega))
    · have : a = b := by omega
      subst this
      exact h a (by omega)

/-- Every list of integers is bounded. -/
theorem exists_int_bound (l : List Int) : ∃ M : Int, ∀ x ∈ l, x ≤ M := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨max a M, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := hM x hx
      omega

/-- T1 and T2 composed (links B and C): the System 4 tape of the System 5
    program `cy2s5.pl` emits for a cyclic tag system tracks the cyclic tag
    run.  `L` is the number of System 5 steps the cyclic tag run of `n`
    steps takes; for every `f` above the bounds `system5ToSystem4_repS4`
    requires there is a strictly increasing schedule of System 4 times at
    which the tape stands in `RepS4` to a System 5 configuration that in
    turn `Represents` the cyclic tag configuration. -/
theorem conjecture4_cts (C0 : CTS) (cfg : CTSConfig) (N n : Nat)
    (hn : n ≤ C0.appendants.length * N) (c' : CTSConfig) (hrun : C0.nSteps cfg n = some c') :
    ∃ L : Nat, ∀ f : Nat,
      (∀ e ∈ (ctsToSystem5 C0 cfg N).bag, e < f) →
      (∀ r ∈ (ctsToSystem5 C0 cfg N).rules, ∀ k ∈ r, k + 2 * L < f) → 2 * L < f →
      ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ i, i < n → times i < times (i + 1)) ∧
        ∀ i, i ≤ n → ∃ ci si c4i m, C0.nSteps cfg i = some ci ∧
          System5.nSteps (ctsToSystem5 C0 cfg N) m = some si ∧
          Represents si (double C0) (dblCfg ci) (2 * (C0.appendants.length * N - i)) ∧
          System4.nSteps (system5ToSystem4 (ctsToSystem5 C0 cfg N) f) (times i) = some c4i ∧
          RepS4 c4i si f m (L - m) := by
  obtain ⟨t5, h50, h5mono, h5tr⟩ := conjecture5_finite C0 cfg N n hn c' hrun
  refine ⟨t5 n, fun f hbagf hrulesf hLf => ?_⟩
  obtain ⟨cn, sn, _, hsn, _⟩ := h5tr n (le_refl n)
  have hbag1 : ∀ e ∈ (ctsToSystem5 C0 cfg N).bag, 1 ≤ e ∧ e < f :=
    fun e he => ⟨ctsToSystem5_bag_ge_one C0 cfg N e he, hbagf e he⟩
  have hrules : ∀ r ∈ (ctsToSystem5 C0 cfg N).rules, r.Nodup ∧ ∀ k ∈ r, 0 ≤ k ∧ k + 2 * t5 n < f :=
    fun r hr => ⟨ctsToSystem5_rules_nodup C0 cfg N r hr,
      fun k hk => ⟨by have := ctsToSystem5_rules_ge_three C0 cfg N r hr k hk; omega, hrulesf r hr k hk⟩⟩
  obtain ⟨t4, h40, h4mono, h4tr⟩ := conjecture4_finite (ctsToSystem5 C0 cfg N) f (t5 n) (t5 n)
    (ctsToSystem5_bag_nodup C0 cfg N) hbag1 hrules hLf (le_refl _) sn hsn
  have h5le : ∀ i, i ≤ n → t5 i ≤ t5 n := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with hlt | rfl
    · exact le_of_lt (strictMono_of_succ t5 n h5mono i n hlt (le_refl n))
    · exact le_refl _
  refine ⟨fun i => t4 (t5 i), by show t4 (t5 0) = 0; rw [h50, h40], fun i hi => ?_, fun i hi => ?_⟩
  · exact strictMono_of_succ t4 (t5 n) h4mono _ _ (h5mono i hi) (h5le (i + 1) hi)
  · obtain ⟨ci, si, hci, hsi, hrep5⟩ := h5tr i hi
    obtain ⟨si', c4i, hsi', hc4i, hrep4⟩ := h4tr (t5 i) (h5le i hi)
    rw [hsi] at hsi'
    obtain rfl := Option.some.inj hsi'
    exact ⟨ci, si, c4i, t5 i, hci, hsi, hrep5, hc4i, hrep4⟩

/-- The parameter `f` can always be chosen: above the largest integer of
    the System 5 program plus twice the System 5 run length. -/
theorem conjecture4_cts_exists_f (C0 : CTS) (cfg : CTSConfig) (N n : Nat)
    (hn : n ≤ C0.appendants.length * N) (c' : CTSConfig) (hrun : C0.nSteps cfg n = some c') :
    ∃ L f0 : Nat, ∀ f : Nat, f0 ≤ f →
      ∃ times : Nat → Nat, times 0 = 0 ∧ (∀ i, i < n → times i < times (i + 1)) ∧
        ∀ i, i ≤ n → ∃ ci si c4i m, C0.nSteps cfg i = some ci ∧
          System5.nSteps (ctsToSystem5 C0 cfg N) m = some si ∧
          Represents si (double C0) (dblCfg ci) (2 * (C0.appendants.length * N - i)) ∧
          System4.nSteps (system5ToSystem4 (ctsToSystem5 C0 cfg N) f) (times i) = some c4i ∧
          RepS4 c4i si f m (L - m) := by
  obtain ⟨L, hL⟩ := conjecture4_cts C0 cfg N n hn c' hrun
  obtain ⟨M, hM⟩ := exists_int_bound ((ctsToSystem5 C0 cfg N).bag ++ (ctsToSystem5 C0 cfg N).rules.flatten)
  refine ⟨L, (M + 2 * L + 1).toNat + (2 * L + 1), fun f hf => hL f ?_ ?_ ?_⟩
  · intro e he
    have := hM e (List.mem_append_left _ he)
    have := Int.self_le_toNat (M + 2 * L + 1)
    omega
  · intro r hr k hk
    have := hM k (List.mem_append_right _ (List.mem_flatten.mpr ⟨r, hr, hk⟩))
    have := Int.self_le_toNat (M + 2 * L + 1)
    omega
  · omega

end Smith
