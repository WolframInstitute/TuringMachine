/-
  Smith.RunBounds

  Closed-form bounds on the length of every run of System 4 and of System 5,
  the first step of open item 1 (the closed-form initial condition, PLAN.md
  milestone M9). The exact run lengths that size the initial tape in the
  proofs of T4, T8 and T6 are replaced by these bounds.

  System 4 always halts. In state A the head moves left, in states B and C it
  moves right; a leftward run ends at a star (rule 2 deletes it) or at the
  left end (rule 1 turns round), and a rightward run ends at a star in state
  B (rule 4 deletes it) or at the right end. So the phase (twice the number
  of stars, plus one in state A) never increases and drops at every change of
  direction, and within a phase the head position moves monotonically. The
  measure `phi4 K c = phase4 c * K + off4 K c`, with `K` above the tape
  length, drops by at least one at every step: a run from a tape of length
  `L` has at most `(2 L + 2) (L + 1)` steps (`System4.run_bound`).

  System 5 halts too, from configurations whose bag is duplicate-free with
  positive elements and whose rule entries are non-negative (`Inv5`, kept by
  every step and true of the encoder's output). Every step either pops a
  rule (a P-step) or decrements the bag and increments the rules (a D-step);
  a bag element at most `v` forces a P-step within `v` steps, and every step
  raises the largest integer by at most one (`Bound5_step`). With `R` rules
  and all integers at most `B`, a run has at most `G5 B R = B (2^R - 1)`
  steps (`System5.run_bound`).

  Contents: `starCount`, `phase4`, `off4`, `phi4`, `phi4_step`,
  `phi4_nSteps`, `System4.run_bound`; `Inv5`, `step5_cases`, `Inv5_step`,
  `G5`, `G5_eq`, `run5_phase`, `run5_bound`, `System5.run_bound`,
  `maxInt5`, `Bound5_maxInt5`.
-/

import Smith.Guards
import Smith.Conjecture0
import Mathlib.Tactic.Ring

namespace Smith

open BiTM
open System4State
open System4Elem

/-! ## System 4 -/

/-- The number of stars on a tape. -/
def starCount (l : List System4Elem) : Nat := l.countP (fun e => e.isStar)

@[simp] theorem starCount_nil : starCount [] = 0 := rfl

theorem starCount_append (l1 l2 : List System4Elem) :
    starCount (l1 ++ l2) = starCount l1 + starCount l2 := List.countP_append ..

@[simp] theorem starCount_cons_star (l : List System4Elem) :
    starCount (star :: l) = starCount l + 1 := by
  simp [starCount, System4Elem.isStar]

@[simp] theorem starCount_cons_set (s : List Int) (l : List System4Elem) :
    starCount (set s :: l) = starCount l := by
  simp [starCount, System4Elem.isStar]

theorem starCount_le_length (l : List System4Elem) : starCount l ≤ l.length :=
  List.countP_le_length

/-- The phase of a configuration: twice the number of stars, plus one while
    the head moves left (state A). -/
def phase4 (c : System4Config) : Nat :=
  match c.state with
  | A => 2 * starCount c.elems + 1
  | _ => 2 * starCount c.elems

/-- The offset within a phase: the head position while it moves left, the
    distance to `K - 1` while it moves right. -/
def off4 (K : Nat) (c : System4Config) : Nat :=
  match c.state with
  | A => c.active
  | _ => K - 1 - c.active

/-- The termination measure of System 4 for tapes shorter than `K`. -/
def phi4 (K : Nat) (c : System4Config) : Nat := phase4 c * K + off4 K c

theorem phase4_A (e : List System4Elem) (a : Nat) :
    phase4 ⟨e, a, A⟩ = 2 * starCount e + 1 := rfl

theorem phase4_nA (e : List System4Elem) (a : Nat) (st : System4State) (h : st ≠ A) :
    phase4 ⟨e, a, st⟩ = 2 * starCount e := by
  cases st with
  | A => exact absurd rfl h
  | B => rfl
  | C => rfl

theorem off4_A (K : Nat) (e : List System4Elem) (a : Nat) : off4 K ⟨e, a, A⟩ = a := rfl

theorem off4_nA (K : Nat) (e : List System4Elem) (a : Nat) (st : System4State) (h : st ≠ A) :
    off4 K ⟨e, a, st⟩ = K - 1 - a := by
  cases st with
  | A => exact absurd rfl h
  | B => rfl
  | C => rfl

/-- The lexicographic comparison behind `phi4`. -/
theorem lex_lt {a b x y K : Nat} (hab : a < b) (hx : x < K) : a * K + x < b * K + y := by
  have h1 : (a + 1) * K ≤ b * K := Nat.mul_le_mul_right K hab
  have h2 : (a + 1) * K = a * K + K := Nat.succ_mul a K
  omega

theorem step_starB_nil (R : List System4Elem) : System4.step ⟨star :: R, 0, B⟩ = none := by
  unfold System4.step
  rw [dite_eq_left (by simp)]
  simp

theorem step_starC_end (L : List System4Elem) :
    System4.step ⟨L ++ [star], L.length, C⟩ = none := by
  unfold System4.step
  rw [dite_eq_left (by simp)]
  simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero,
    List.get_eq_getElem]
  rw [dite_eq_right (by simp)]

theorem step_starC_star (L R : List System4Elem) :
    System4.step ⟨L ++ star :: star :: R, L.length, C⟩ = none := by
  unfold System4.step
  rw [dite_eq_left (by simp)]
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem_cons_zero]
  rw [dite_eq_left (by simp)]
  rw [List.getElem_append_right (by simp)]
  simp

/-- One step of System 4 lowers the measure, keeps the tape from growing and
    keeps the head on the tape or just past its end. -/
theorem phi4_step (K : Nat) (c c' : System4Config) (hK : c.elems.length < K)
    (hs : System4.step c = some c') :
    phi4 K c' < phi4 K c ∧ c'.elems.length ≤ c.elems.length ∧ c'.active ≤ c'.elems.length := by
  obtain ⟨L, e, R, hc⟩ := focus_of_lt c (step_active_lt c c' hs)
  rw [hc] at hs hK ⊢
  simp only [List.length_append, List.length_cons] at hK
  unfold phi4
  cases e with
  | star =>
    cases hst : c.state with
    | A =>
      rw [hst, step_starA] at hs
      obtain rfl := Option.some.inj hs
      simp only [phase4_A, phase4_nA _ _ B (by decide), off4_A, off4_nA _ _ _ B (by decide),
        starCount_append, starCount_cons_star, List.length_append, List.length_cons]
      refine ⟨lex_lt (by omega) (by omega), by omega, by omega⟩
    | B =>
      rw [hst] at hs
      by_cases hL : L = []
      · subst hL
        rw [List.nil_append, List.length_nil, step_starB_nil] at hs
        cases hs
      · rw [step_starB L R hL] at hs
        obtain rfl := Option.some.inj hs
        have hLpos : 0 < L.length := List.length_pos_iff.mpr hL
        simp only [phase4_A, phase4_nA _ _ B (by decide), off4_A, off4_nA _ _ _ B (by decide),
          starCount_append, starCount_cons_star, List.length_append, List.length_cons]
        refine ⟨lex_lt (by omega) (by omega), by omega, by omega⟩
    | C =>
      rw [hst] at hs
      cases R with
      | nil =>
        rw [step_starC_end] at hs
        cases hs
      | cons e2 R' =>
        cases e2 with
        | star =>
          rw [step_starC_star] at hs
          cases hs
        | set s =>
          rw [step_starC] at hs
          obtain rfl := Option.some.inj hs
          simp only [phase4_nA _ _ C (by decide), off4_nA _ _ _ C (by decide), starCount_append,
            starCount_cons_star, starCount_cons_set, List.length_append, List.length_cons]
          simp only [List.length_cons] at hK
          refine ⟨by omega, by omega, by omega⟩
  | set s =>
    cases hst : c.state with
    | A =>
      rw [hst] at hs
      by_cases hL : L = []
      · subst hL
        rw [List.nil_append, List.length_nil, step_setA_zero] at hs
        obtain rfl := Option.some.inj hs
        simp only [phase4_A, phase4_nA _ _ B (by decide), off4_A, off4_nA _ _ _ B (by decide),
          List.nil_append, List.length_nil]
        refine ⟨lex_lt (by omega) (by omega), by omega, by omega⟩
      · rw [step_setA L s R hL] at hs
        obtain rfl := Option.some.inj hs
        have hLpos : 0 < L.length := List.length_pos_iff.mpr hL
        simp only [phase4_A, off4_A, List.length_append, List.length_cons]
        refine ⟨by omega, by omega, by omega⟩
    | B =>
      rw [hst, step_setBC L s R B (by decide)] at hs
      obtain rfl := Option.some.inj hs
      have hne : flip (decide (0 ∈ s)) B ≠ A := flip_ne_A _ _ (by decide)
      simp only [phase4_nA _ _ B (by decide), off4_nA _ _ _ B (by decide), phase4_nA _ _ _ hne,
        off4_nA _ _ _ _ hne, starCount_append, starCount_cons_set, List.length_append,
        List.length_cons]
      refine ⟨by omega, by omega, by omega⟩
    | C =>
      rw [hst, step_setBC L s R C (by decide)] at hs
      obtain rfl := Option.some.inj hs
      have hne : flip (decide (0 ∈ s)) C ≠ A := flip_ne_A _ _ (by decide)
      simp only [phase4_nA _ _ C (by decide), off4_nA _ _ _ C (by decide), phase4_nA _ _ _ hne,
        off4_nA _ _ _ _ hne, starCount_append, starCount_cons_set, List.length_append,
        List.length_cons]
      refine ⟨by omega, by omega, by omega⟩

/-- Along a run of `n` steps the measure drops by at least `n`. -/
theorem phi4_nSteps (K : Nat) : ∀ (n : Nat) (c c' : System4Config), c.elems.length < K →
    System4.nSteps c n = some c' → n + phi4 K c' ≤ phi4 K c := by
  intro n
  induction n with
  | zero =>
    intro c c' _ h
    rw [System4.nSteps_zero] at h
    obtain rfl := Option.some.inj h
    omega
  | succ n ih =>
    intro c c' hK h
    rw [System4.nSteps_succ] at h
    cases hs : System4.step c with
    | none => rw [hs] at h; cases h
    | some c1 =>
      rw [hs, Option.bind_some] at h
      obtain ⟨hlt, hlen, _⟩ := phi4_step K c c1 hK hs
      have := ih c1 c' (by omega) h
      omega

/-- Every run of System 4 from a tape of length `L` has at most
    `(2 L + 2) (L + 1)` steps. -/
theorem System4.run_bound (c : System4Config) (n : Nat) (c' : System4Config)
    (h : System4.nSteps c n = some c') :
    n ≤ (2 * c.elems.length + 2) * (c.elems.length + 1) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    have hstep : ∃ c1, System4.step c = some c1 := by
      rw [System4.nSteps_succ] at h
      cases hs : System4.step c with
      | none => rw [hs] at h; cases h
      | some c1 => exact ⟨c1, rfl⟩
    obtain ⟨c1, hs⟩ := hstep
    have hact := step_active_lt c c1 hs
    have hrun := phi4_nSteps (c.elems.length + 1) (n + 1) c c' (by omega) h
    have hsc := starCount_le_length c.elems
    have hphi : phi4 (c.elems.length + 1) c
        ≤ (2 * c.elems.length + 1) * (c.elems.length + 1) + c.elems.length := by
      obtain ⟨e, a, st⟩ := c
      simp only at hact hsc ⊢
      cases st with
      | A =>
        show (2 * starCount e + 1) * (e.length + 1) + a ≤ _
        have : (2 * starCount e + 1) * (e.length + 1) ≤ (2 * e.length + 1) * (e.length + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      | B =>
        show 2 * starCount e * (e.length + 1) + (e.length + 1 - 1 - a) ≤ _
        have : 2 * starCount e * (e.length + 1) ≤ (2 * e.length + 1) * (e.length + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      | C =>
        show 2 * starCount e * (e.length + 1) + (e.length + 1 - 1 - a) ≤ _
        have : 2 * starCount e * (e.length + 1) ≤ (2 * e.length + 1) * (e.length + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
    have e1 : (2 * c.elems.length + 2) * (c.elems.length + 1)
        = (2 * c.elems.length + 1) * (c.elems.length + 1) + (c.elems.length + 1) := by ring
    omega

/-! ## System 5 -/

/-- The invariant of System 5 runs from the encoder's output: the bag is
    duplicate-free with positive elements, the rule entries are
    non-negative. -/
def Inv5 (s : System5Config) : Prop :=
  s.bag.Nodup ∧ (∀ e ∈ s.bag, 1 ≤ e) ∧ (∀ r ∈ s.rules, ∀ k ∈ r, 0 ≤ k)

/-- A step of System 5 is a P-step (a rule popped and merged into the bag)
    or a D-step (the bag decremented, the rules incremented). -/
theorem step5_cases (s s' : System5Config) (hs : System5.step s = some s') :
    (∃ r0 rest, s.rules = r0 :: rest ∧ (0 : Int) ∈ s.bag.map (· - 1) ∧
      s' = ⟨xorMerge ((s.bag.map (· - 1)).erase 0) (r0.map (· + 1)),
        rest.map (fun r => r.map (· + 1))⟩) ∨
    (s.rules ≠ [] ∧ (0 : Int) ∉ s.bag.map (· - 1) ∧
      s' = ⟨s.bag.map (· - 1), s.rules.map (fun r => r.map (· + 1))⟩) := by
  obtain ⟨bag, rules⟩ := s
  unfold System5.step at hs
  simp only at hs ⊢
  by_cases hE : (bag.map (fun x => x - 1)).isEmpty = true ∨
      (rules.map (fun r => r.map (fun x => x + 1))).isEmpty = true
  · rw [ite_eq_left hE] at hs; cases hs
  · rw [ite_eq_right hE] at hs
    by_cases h0 : (0 : Int) ∈ bag.map (fun x => x - 1)
    · rw [ite_eq_left h0] at hs
      cases rules with
      | nil => simp at hE
      | cons r0 rest =>
        simp only [List.map_cons] at hs
        obtain rfl := Option.some.inj hs
        exact Or.inl ⟨r0, rest, rfl, h0, rfl⟩
    · rw [ite_eq_right h0] at hs
      obtain rfl := Option.some.inj hs
      refine Or.inr ⟨?_, h0, rfl⟩
      intro hr
      subst hr
      simp at hE

theorem Inv5_step (s s' : System5Config) (h : Inv5 s) (hs : System5.step s = some s') : Inv5 s' := by
  obtain ⟨hnd, hpos, hrules⟩ := h
  have hdec_nd : (s.bag.map (· - 1)).Nodup :=
    hnd.map (fun a b hab => by simpa using hab)
  rcases step5_cases s s' hs with ⟨r0, rest, hr, _, rfl⟩ | ⟨_, h0, rfl⟩
  · refine ⟨xorMerge_nodup _ _ (hdec_nd.erase 0), ?_, ?_⟩
    · intro e he
      rcases xorMerge_mem_or _ _ e he with he1 | he2
      · rw [hdec_nd.mem_erase_iff] at he1
        obtain ⟨hne, hmem⟩ := he1
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmem
        have := hpos x hx
        omega
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he2
        have := hrules r0 (by rw [hr]; exact List.mem_cons_self) k hk
        omega
    · intro r hrm k hk
      obtain ⟨r1, hr1, rfl⟩ := List.mem_map.mp hrm
      obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp hk
      have := hrules r1 (by rw [hr]; exact List.mem_cons_of_mem _ hr1) k1 hk1
      omega
  · refine ⟨hdec_nd, ?_, ?_⟩
    · intro e he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      have h1 := hpos x hx
      have h2 : x - 1 ≠ 0 := fun h => h0 (List.mem_map.mpr ⟨x, hx, h⟩)
      omega
    · intro r hrm k hk
      obtain ⟨r1, hr1, rfl⟩ := List.mem_map.mp hrm
      obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp hk
      have := hrules r1 hr1 k1 hk1
      omega

/-- The run bound of System 5: `G5 B R = B (2^R - 1)` (`G5_eq`). -/
def G5 : Nat → Nat → Nat
  | _, 0 => 0
  | b, R + 1 => b + G5 (2 * b) R

theorem G5_eq (R : Nat) : ∀ B, G5 B R = B * (2 ^ R - 1) := by
  induction R with
  | zero => intro B; simp [G5]
  | succ R ih =>
    intro B
    rw [G5, ih]
    have h1 : 1 ≤ 2 ^ R := Nat.one_le_two_pow
    have h2 : 2 ^ (R + 1) = 2 * 2 ^ R := by rw [Nat.pow_succ]; ring
    rw [h2]
    obtain ⟨p, hp⟩ : ∃ p, 2 ^ R = p + 1 := ⟨2 ^ R - 1, by omega⟩
    rw [hp]
    have e1 : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
    have e2 : p + 1 - 1 = p := by omega
    rw [e1, e2]
    ring

theorem G5_mono_left (R : Nat) {B B' : Nat} (h : B ≤ B') : G5 B R ≤ G5 B' R := by
  rw [G5_eq, G5_eq]
  exact Nat.mul_le_mul_right _ h

theorem step5_none_of_rules_nil (s : System5Config) (h : s.rules = []) : System5.step s = none := by
  obtain ⟨bag, rules⟩ := s
  simp only at h
  subst h
  unfold System5.step
  simp

theorem step5_none_of_bag_nil (s : System5Config) (h : s.bag = []) : System5.step s = none := by
  obtain ⟨bag, rules⟩ := s
  simp only at h
  subst h
  unfold System5.step
  simp

/-- A D-phase: a bag element at most `v` forces a P-step within `v` steps,
    after which the bound for one rule fewer applies. -/
theorem run5_phase (R : Nat)
    (ih : ∀ (s : System5Config) (B : Nat), s.rules.length ≤ R → Inv5 s → Bound5 s B →
      ∀ n s', System5.nSteps s n = some s' → n ≤ G5 B R) :
    ∀ (v : Nat) (s : System5Config) (B : Nat), s.rules.length ≤ R + 1 → Inv5 s → Bound5 s B →
      (∃ x ∈ s.bag, x ≤ (v : Int)) → 1 ≤ v →
      ∀ n s', System5.nSteps s n = some s' → n ≤ v + G5 (B + v) R := by
  intro v
  induction v with
  | zero => intro _ _ _ _ _ _ hv; omega
  | succ v ihv =>
    intro s B hR hinv hB hx _ n s' hrun
    cases n with
    | zero => omega
    | succ m =>
      rw [System5.nSteps_succ] at hrun
      cases hs : System5.step s with
      | none => rw [hs] at hrun; cases hrun
      | some s1 =>
        rw [hs, Option.bind_some] at hrun
        have hinv1 := Inv5_step s s1 hinv hs
        have hB1 : Bound5 s1 ((B + 1 : Nat) : Int) := by
          have := Bound5_step s s1 B hB hs
          simpa using this
        rcases step5_cases s s1 hs with ⟨r0, rest, hr, _, rfl⟩ | ⟨_, h0, rfl⟩
        · have hR1 : (rest.map (fun r => r.map (· + 1))).length ≤ R := by
            rw [hr] at hR; simp at hR ⊢; omega
          have h1 := ih _ (B + 1) hR1 hinv1 hB1 m s' hrun
          have h2 : G5 (B + 1) R ≤ G5 (B + (v + 1)) R := G5_mono_left R (by omega)
          omega
        · obtain ⟨x, hx, hxv⟩ := hx
          have hx1 := hinv.2.1 x hx
          have hx0 : x - 1 ≠ 0 := fun h => h0 (List.mem_map.mpr ⟨x, hx, h⟩)
          have hv1 : 1 ≤ v := by omega
          have := ihv ⟨s.bag.map (· - 1), s.rules.map (fun r => r.map (· + 1))⟩ (B + 1)
            (by simpa using hR) hinv1 hB1
            ⟨x - 1, List.mem_map.mpr ⟨x, hx, rfl⟩, by omega⟩ hv1 m s' hrun
          have e : B + 1 + v = B + (v + 1) := by omega
          rw [e] at this
          omega

/-- Every run of System 5 from a configuration with at most `R` rules and all
    integers at most `B` has at most `G5 B R` steps. -/
theorem run5_bound : ∀ (R : Nat) (s : System5Config) (B : Nat), s.rules.length ≤ R → Inv5 s →
    Bound5 s B → ∀ n s', System5.nSteps s n = some s' → n ≤ G5 B R := by
  intro R
  induction R with
  | zero =>
    intro s B hR _ _ n s' hrun
    cases n with
    | zero => exact Nat.le_refl _
    | succ m =>
      have hnil : s.rules = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [System5.nSteps_succ, step5_none_of_rules_nil s hnil] at hrun
      cases hrun
  | succ R ih =>
    intro s B hR hinv hB n s' hrun
    cases hbag : s.bag with
    | nil =>
      cases n with
      | zero => exact Nat.zero_le _
      | succ m =>
        rw [System5.nSteps_succ, step5_none_of_bag_nil s hbag] at hrun
        cases hrun
    | cons x xs =>
      have hx : x ∈ s.bag := by rw [hbag]; exact List.mem_cons_self
      have hx1 := hinv.2.1 x hx
      have hxB := hB.1 x hx
      have hB1 : 1 ≤ B := by omega
      have := run5_phase R ih B s B hR hinv hB ⟨x, hx, hxB⟩ hB1 n s' hrun
      show n ≤ B + G5 (2 * B) R
      have e : B + B = 2 * B := by omega
      rw [e] at this
      exact this

/-- The run bound in closed form. -/
theorem System5.run_bound (s : System5Config) (B : Nat) (hinv : Inv5 s) (hB : Bound5 s B)
    (n : Nat) (s' : System5Config) (h : System5.nSteps s n = some s') :
    n ≤ B * 2 ^ s.rules.length := by
  have := run5_bound s.rules.length s B (le_refl _) hinv hB n s' h
  rw [G5_eq] at this
  exact le_trans this (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- The largest integer of a System 5 configuration, as a natural number (0
    when there is none or when all are negative); a bound computed from the
    program text, without running it. -/
def maxInt5 (s : System5Config) : Nat :=
  ((s.bag ++ s.rules.flatten).map Int.toNat).foldr max 0

theorem le_foldr_max (l : List Nat) (x : Nat) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [List.foldr_cons]; exact Nat.le_max_left _ _
    · simp only [List.foldr_cons]; exact le_trans (ih hx) (Nat.le_max_right _ _)

theorem Bound5_maxInt5 (s : System5Config) : Bound5 s (maxInt5 s) := by
  have key : ∀ x ∈ s.bag ++ s.rules.flatten, x ≤ (maxInt5 s : Int) := by
    intro x hx
    have h1 : x.toNat ≤ maxInt5 s :=
      le_foldr_max _ _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
    have h2 : x ≤ (x.toNat : Int) := Int.self_le_toNat x
    omega
  refine ⟨fun e he => key e (List.mem_append_left _ he), fun r hr k hk => ?_⟩
  exact key k (List.mem_append_right _ (List.mem_flatten.mpr ⟨r, hr, hk⟩))

end Smith
