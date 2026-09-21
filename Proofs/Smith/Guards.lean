/-
  Smith.Guards

  PLAN.md target T6, link H, first part (milestone M7): the guarded System 4
  tape. Smith's finite initial condition turns the head round at the left
  end of the System 4 tape with the string `0^m 2 2 1^t` (TM23Proof.pdf
  p. 44: "a lot of 0s and 221"), which cannot be chained after another
  initial condition (p. 25-26). The concatenable left end of p. 12-13 is, in
  System 4 terms, a row of guard sets separated by stars in front of the
  tape: a return of the head to the left end walks over the sets merged so
  far, deletes the next star (state B) and scans the merged sets, none of
  which contains 0 while stars remain, so the head arrives back on the
  leftmost element of the original tape in state B, exactly as the turn of
  the unguarded tape would have left it.

  The tape is entered from the left through its leading star in state C
  (System 4's rule 5, which is how the previous block hands over): the head
  toggles 1 in each guard, scans it in state C, and moves on through the
  next star, until the innermost guard, which holds 0 and turns the state
  to B; the head is then on the first original element in state B, one
  step into the original run. So the guards before the entry are `{1, n}`
  with the innermost `{0, 1, n-1}`, and after the entry `{n-1}` with the
  innermost `{n-2}`.

  Contents: `gset`, `guardPairs`, `preGuardPairs`, `merged`, `padCfg`,
  `PosRun`, `entryRun`, `pad_turn`, `pad_step`, `pad_schedule`.
-/

import Smith.Conjecture4

namespace Smith

open TM
open BiTM
open System4State

/-- The set `{n - k}`. -/
def gset (n k : Nat) : List Int := [(n : Int) - k]

/-- `k` guards after the entry, each the set `{n - 1}` followed by a star. -/
def guardPairs (n : Nat) : Nat → List System4Elem
  | 0 => []
  | k + 1 => System4Elem.set (gset n 1) :: System4Elem.star :: guardPairs n k

/-- `k` guards before the entry, each the set `{1, n}` followed by a star. -/
def preGuardPairs (n : Nat) : Nat → List System4Elem
  | 0 => []
  | k + 1 => System4Elem.set [1, (n : Int)] :: System4Elem.star :: preGuardPairs n k

/-- The innermost guard before the entry. -/
def preM (n : Nat) : List Int := [0, 1, (n : Int) - 1]

theorem guardPairs_succ' (n k : Nat) :
    guardPairs n (k + 1) = guardPairs n k ++ [System4Elem.set (gset n 1), System4Elem.star] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show System4Elem.set (gset n 1) :: System4Elem.star :: guardPairs n (k + 1)
      = (System4Elem.set (gset n 1) :: System4Elem.star :: guardPairs n k) ++ _
    rw [ih]
    rfl

@[simp] theorem length_guardPairs (n k : Nat) : (guardPairs n k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [guardPairs, ih]; omega

@[simp] theorem length_preGuardPairs (n k : Nat) : (preGuardPairs n k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [preGuardPairs, ih]; omega

/-- The sets right of the last remaining star after `t` turns: the guards
    `{n-1}, ..., {n-t}` whose stars were deleted, each scanned once per turn
    since, and the innermost `{n-2-t}`. -/
def merged (n t : Nat) : List (List Int) :=
  (List.range t).map (fun i => gset n (1 + i)) ++ [gset n (2 + t)]

theorem length_merged (n t : Nat) : (merged n t).length = t + 1 := by simp [merged]

theorem merged_ne_nil (n t : Nat) : merged n t ≠ [] := by simp [merged]

theorem merged_zero (n : Nat) : merged n 0 = [gset n 2] := rfl

theorem decr_gset (n k : Nat) (hk : k < n) : decr (gset n k) = gset n (k + 1) := by
  unfold decr decrementSet gset
  rw [if_neg (by simp; omega)]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  push_cast
  omega

theorem merged_map_decr (n t : Nat) (ht : t + 3 ≤ n) :
    (merged n t).map decr = (List.range t).map (fun i => gset n (2 + i)) ++ [gset n (3 + t)] := by
  simp only [merged, List.map_append, List.map_map, List.map_cons, List.map_nil]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [decr_gset n (1 + i) (by omega)]
    congr 1
    omega
  · rw [decr_gset n (2 + t) (by omega), show 2 + t + 1 = 3 + t from by omega]

theorem merged_succ (n t : Nat) (ht : t + 3 ≤ n) :
    merged n (t + 1) = gset n 1 :: (merged n t).map decr := by
  rw [merged_map_decr n t ht]
  unfold merged
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.cons_append]
  congr 1
  congr 1
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    congr 1
    omega
  · rw [show 2 + (t + 1) = 3 + t from by omega]

theorem parMem_false_of_forall (x : Int) (K : List (List Int)) (h : ∀ S ∈ K, x ∉ S) :
    parMem x K = false := by
  induction K with
  | nil => rfl
  | cons S K ih =>
    rw [parMem_cons, ih (fun S' hS' => h S' (List.mem_cons_of_mem _ hS')),
      decide_eq_false (h S List.mem_cons_self)]
    rfl

theorem mem_merged (n t : Nat) (S : List Int) (hS : S ∈ merged n t) :
    ∃ k, 1 ≤ k ∧ k ≤ t + 2 ∧ S = gset n k := by
  simp only [merged, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hS
  rcases hS with ⟨i, hi, rfl⟩ | rfl
  · exact ⟨1 + i, by omega, by omega, rfl⟩
  · exact ⟨2 + t, by omega, by omega, rfl⟩

theorem parMem_zero_merged (n t : Nat) (ht : t + 3 ≤ n) : parMem 0 (merged n t) = false := by
  apply parMem_false_of_forall
  intro S hS
  obtain ⟨k, hk1, hk2, rfl⟩ := mem_merged n t S hS
  simp [gset]
  omega

/-! ## Runs with a bound on the head -/

/-- Every configuration of the first `k` steps satisfies `P`. -/
def PosRun (P : System4Config → Prop) (c : System4Config) (k : Nat) : Prop :=
  ∀ j, j ≤ k → ∀ c', System4.nSteps c j = some c' → P c'

theorem PosRun_zero (P : System4Config → Prop) (c : System4Config) (h : P c) : PosRun P c 0 := by
  intro j hj c' hc'
  obtain rfl : j = 0 := by omega
  rw [System4.nSteps_zero] at hc'
  obtain rfl := Option.some.inj hc'
  exact h

theorem PosRun_add (P : System4Config → Prop) (c ca : System4Config) (a b : Nat)
    (hca : System4.nSteps c a = some ca) (h1 : PosRun P c a) (h2 : PosRun P ca b) :
    PosRun P c (a + b) := by
  intro j hj c' hc'
  rcases Nat.lt_or_ge j a with hlt | hge
  · exact h1 j (le_of_lt hlt) c' hc'
  · obtain ⟨d, rfl⟩ : ∃ d, j = a + d := ⟨j - a, by omega⟩
    rw [System4.nSteps_add, hca, Option.bind_some] at hc'
    exact h2 d (by omega) c' hc'

theorem PosRun_one (P : System4Config → Prop) (c c' : System4Config)
    (hs : System4.step c = some c') (h : P c) (h' : P c') : PosRun P c 1 := by
  intro j hj c'' hc''
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · rw [System4.nSteps_zero] at hc''
    obtain rfl := Option.some.inj hc''
    exact h
  · rw [System4.nSteps_one, hs] at hc''
    obtain rfl := Option.some.inj hc''
    exact h'

theorem PosRun_mono (P Q : System4Config → Prop) (c : System4Config) (k : Nat)
    (h : PosRun P c k) (hPQ : ∀ c, P c → Q c) : PosRun Q c k :=
  fun j hj c' hc' => hPQ c' (h j hj c' hc')

/-- The sweep keeps the head right of `L`. -/
theorem sweep_posRun (L : List System4Elem) (K : List (List Int)) (R : List System4Elem)
    (st : System4State) (hst : st ≠ A) :
    PosRun (fun c => L.length ≤ c.active) ⟨L ++ sets K ++ R, L.length, st⟩ K.length := by
  induction K generalizing L st with
  | nil => exact PosRun_zero _ _ (le_refl _)
  | cons S K ih =>
    rw [List.length_cons, Nat.add_comm]
    have h1 : L ++ sets (S :: K) ++ R = L ++ System4Elem.set S :: (sets K ++ R) := by simp
    have hs := step_setBC L S (sets K ++ R) st hst
    rw [← h1] at hs
    refine PosRun_add _ _ _ 1 K.length (by rw [System4.nSteps_one]; exact hs)
      (PosRun_one (fun c => L.length ≤ c.active) _ _ hs (le_refl _) (by simp)) ?_
    have h2 : L ++ System4Elem.set (decr S) :: (sets K ++ R) = (L ++ [System4Elem.set (decr S)]) ++ sets K ++ R := by
      simp
    have h3 : L.length + 1 = (L ++ [System4Elem.set (decr S)]).length := by simp
    have := ih (L ++ [System4Elem.set (decr S)]) (flip (decide (0 ∈ S)) st) (flip_ne_A _ _ hst)
    rw [← h2, ← h3] at this
    exact PosRun_mono _ _ _ _ this (fun c hc => by omega)

/-- The walk to the left keeps the head right of `L`. -/
theorem moveLeft_posRun (L : List System4Elem) (K : List (List Int)) (R : List System4Elem)
    (k : Nat) (hk : k < K.length) :
    PosRun (fun c => L.length ≤ c.active) ⟨L ++ sets K ++ R, L.length + k, A⟩ k := by
  induction K generalizing L k with
  | nil => simp at hk
  | cons S K ih =>
    cases k with
    | zero => exact PosRun_zero _ _ (by simp)
    | succ k =>
      cases K with
      | nil => simp at hk
      | cons S' K' =>
        have h1 : L ++ sets (S :: S' :: K') ++ R = (L ++ [System4Elem.set S]) ++ sets (S' :: K') ++ R := by
          simp
        have h2 : L.length + (k + 1) = (L ++ [System4Elem.set S]).length + k := by simp; omega
        have hpre := ih (L ++ [System4Elem.set S]) k (by simpa using hk)
        rw [← h1, ← h2] at hpre
        have hstep : System4.step ⟨L ++ sets (S :: S' :: K') ++ R, (L ++ [System4Elem.set S]).length, A⟩
            = some ⟨L ++ sets (S :: S' :: K') ++ R, L.length, A⟩ := by
          have h3 : L ++ sets (S :: S' :: K') ++ R
              = (L ++ [System4Elem.set S]) ++ System4Elem.set S' :: (sets K' ++ R) := by
            simp
          rw [h3, step_setA (L ++ [System4Elem.set S]) S' _ (by simp)]
          simp
        have hml := moveLeft (L ++ [System4Elem.set S]) (S' :: K') R k (by simpa using hk)
        rw [← h1, ← h2] at hml
        refine PosRun_add _ _ _ k 1 hml (PosRun_mono _ _ _ _ hpre (fun c hc => by simp at hc; omega)) ?_
        exact PosRun_one (fun c => L.length ≤ c.active) _ _ hstep (by simp) (le_refl _)

/-! ## The entry -/

theorem xorInsert_one_pre (n : Nat) : xorInsert 1 [1, (n : Int)] = [(n : Int)] := by
  rw [xorInsert_mem 1 _ (by simp)]
  simp

theorem xorInsert_one_preM (n : Nat) (hn : 3 ≤ n) : xorInsert 1 (preM n) = [0, (n : Int) - 1] := by
  unfold preM
  rw [xorInsert_mem 1 _ (by simp)]
  have : ((n : Int) - 1 = 1) = False := by simp; omega
  simp

theorem decr_single (n : Nat) (hn : 1 ≤ n) : decr [(n : Int)] = gset n 1 := by
  unfold decr decrementSet gset
  rw [if_neg (by simp; omega)]
  simp

theorem decr_preM' (n : Nat) : decr [0, (n : Int) - 1] = gset n 2 := by
  have h1 : decr [0, (n : Int) - 1] = [(n : Int) - 1 - 1] := by
    unfold decr decrementSet
    rw [if_pos (by simp)]
    simp
  rw [h1]
  unfold gset
  congr 1
  omega

/-- One guard pair at the entry: rule 5 onto `{1, n}` (which becomes `{n}`),
    then its scan in state C (`{n-1}`, the state stays C), the head landing
    on the next star. -/
theorem entryPair (n : Nat) (hn : 2 ≤ n) (Lc T : List System4Elem) :
    System4.nSteps ⟨Lc ++ System4Elem.star :: System4Elem.set [1, (n : Int)] :: System4Elem.star :: T,
        Lc.length, System4State.C⟩ 2
      = some ⟨(Lc ++ [System4Elem.star, System4Elem.set (gset n 1)]) ++ System4Elem.star :: T,
          Lc.length + 2, System4State.C⟩ := by
  rw [show 2 = 1 + 1 from rfl, System4.nSteps_add, System4.nSteps_one, step_starC, Option.bind_some,
    System4.nSteps_one, xorInsert_one_pre n]
  have h1 : Lc ++ System4Elem.star :: System4Elem.set [(n : Int)] :: System4Elem.star :: T
      = (Lc ++ [System4Elem.star]) ++ System4Elem.set [(n : Int)] :: (System4Elem.star :: T) := by simp
  have h2 : Lc.length + 1 = (Lc ++ [System4Elem.star]).length := by simp
  rw [h1, h2, step_setBC _ _ _ System4State.C (by decide), decr_single n (by omega)]
  simp [flip]
  omega

/-- The innermost guard at the entry: rule 5 onto `{0, 1, n-1}` (which
    becomes `{0, n-1}`), then its scan in state C, which finds the 0 and
    turns the state to B, the head landing on the first original element. -/
theorem entryLast (n : Nat) (hn : 3 ≤ n) (Lc T : List System4Elem) :
    System4.nSteps ⟨Lc ++ System4Elem.star :: System4Elem.set (preM n) :: T, Lc.length, System4State.C⟩ 2
      = some ⟨Lc ++ System4Elem.star :: System4Elem.set (gset n 2) :: T, Lc.length + 2, System4State.B⟩ := by
  rw [show 2 = 1 + 1 from rfl, System4.nSteps_add, System4.nSteps_one, step_starC, Option.bind_some,
    System4.nSteps_one, xorInsert_one_preM n hn]
  have h1 : Lc ++ System4Elem.star :: System4Elem.set [0, (n : Int) - 1] :: T
      = (Lc ++ [System4Elem.star]) ++ System4Elem.set [0, (n : Int) - 1] :: T := by simp
  have h2 : Lc.length + 1 = (Lc ++ [System4Elem.star]).length := by simp
  rw [h1, h2, step_setBC _ _ _ System4State.C (by decide), decr_preM' n]
  simp [flip, tog]
  try omega

/-- The entry through `k` guard pairs and the innermost guard: `2k + 2`
    steps, the head ending on the first original element in state B, all
    intermediate heads right of the leading star. -/
theorem entryRun (n : Nat) (hn : 3 ≤ n) (k : Nat) : ∀ (Lc T : List System4Elem),
    System4.nSteps ⟨Lc ++ System4Elem.star :: (preGuardPairs n k ++ System4Elem.set (preM n) :: T),
        Lc.length, System4State.C⟩ (2 * k + 2)
      = some ⟨Lc ++ System4Elem.star :: (guardPairs n k ++ System4Elem.set (gset n 2) :: T),
          Lc.length + 2 * k + 2, System4State.B⟩ ∧
    ∀ j, 1 ≤ j → j ≤ 2 * k + 2 → ∀ c',
      System4.nSteps ⟨Lc ++ System4Elem.star :: (preGuardPairs n k ++ System4Elem.set (preM n) :: T),
        Lc.length, System4State.C⟩ j = some c' → Lc.length + 1 ≤ c'.active := by
  induction k with
  | zero =>
    intro Lc T
    simp only [preGuardPairs, guardPairs, List.nil_append, Nat.mul_zero, Nat.zero_add]
    refine ⟨entryLast n hn Lc T, ?_⟩
    intro j hj1 hj2 c' hc'
    rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
    · rw [System4.nSteps_one, step_starC] at hc'
      obtain rfl := Option.some.inj hc'
      simp
    · rw [entryLast n hn Lc T] at hc'
      obtain rfl := Option.some.inj hc'
      simp
  | succ k ih =>
    intro Lc T
    have hpair := entryPair n (by omega) Lc (preGuardPairs n k ++ System4Elem.set (preM n) :: T)
    have hLc' : (Lc ++ [System4Elem.star, System4Elem.set (gset n 1)]).length = Lc.length + 2 := by simp
    obtain ⟨hrun, hpos⟩ := ih (Lc ++ [System4Elem.star, System4Elem.set (gset n 1)]) T
    rw [hLc'] at hrun hpos
    refine ⟨?_, ?_⟩
    · rw [show 2 * (k + 1) + 2 = 2 + (2 * k + 2) from by omega, System4.nSteps_add]
      simp only [preGuardPairs, List.cons_append]
      rw [hpair, Option.bind_some, hrun]
      simp only [guardPairs, List.append_assoc, List.cons_append, List.nil_append]
      congr 2
      omega
    · intro j hj1 hj2 c' hc'
      simp only [preGuardPairs, List.cons_append] at hc'
      rcases Nat.lt_or_ge j 2 with hlt | hge
      · obtain rfl : j = 1 := by omega
        rw [System4.nSteps_one, step_starC] at hc'
        obtain rfl := Option.some.inj hc'
        simp
      · obtain ⟨d, rfl⟩ : ∃ d, j = 2 + d := ⟨j - 2, by omega⟩
        rw [System4.nSteps_add, hpair, Option.bind_some] at hc'
        rcases Nat.eq_zero_or_pos d with rfl | hd
        · rw [System4.nSteps_zero] at hc'
          obtain rfl := Option.some.inj hc'
          simp
        · have := hpos d hd (by omega) c' hc'
          omega

/-! ## The padded configuration -/

/-- The padded configuration after `t` turns: the left context, the
    remaining guard pairs, the merged sets, the original tape, the right
    context. -/
def padCfg (n r t : Nat) (Lc Rc : List System4Elem) (c : System4Config) : System4Config :=
  ⟨Lc ++ guardPairs n (r - 1 - t) ++ sets (merged n t) ++ c.elems ++ Rc,
   Lc.length + 2 * (r - 1 - t) + (t + 1) + c.active, c.state⟩

theorem padCfg_active_pos (n r t : Nat) (Lc Rc : List System4Elem) (c : System4Config) :
    Lc.length + 1 ≤ (padCfg n r t Lc Rc c).active := by
  simp [padCfg]; omega

/-- A focus for a configuration whose head is on the tape. -/
theorem focus_of_lt (c : System4Config) (h : c.active < c.elems.length) :
    ∃ L e R, c = ⟨L ++ e :: R, L.length, c.state⟩ := by
  obtain ⟨elems, act, st⟩ := c
  simp only at h
  refine ⟨elems.take act, elems[act], elems.drop (act + 1), ?_⟩
  simp only [System4Config.mk.injEq, List.length_take, Nat.min_eq_left (le_of_lt h), and_true]
  rw [← List.drop_eq_getElem_cons h, List.take_append_drop]

theorem step_active_lt (c c1 : System4Config) (hs : System4.step c = some c1) :
    c.active < c.elems.length := by
  by_contra hlt
  unfold System4.step at hs
  rw [dif_neg hlt] at hs
  cases hs

/-- The turn on the padded tape: `2t + 4` steps, all with the head right of
    the left context. -/
theorem pad_turn (n r t : Nat) (Lc Rc : List System4Elem) (s : List Int) (R : List System4Elem)
    (hr : t + 2 ≤ r) (hn : t + 3 ≤ n) :
    System4.nSteps (padCfg n r t Lc Rc ⟨System4Elem.set s :: R, 0, System4State.A⟩) (2 * t + 4)
      = some (padCfg n r (t + 1) Lc Rc ⟨System4Elem.set s :: R, 0, System4State.B⟩) ∧
    PosRun (fun c => Lc.length + 1 ≤ c.active)
      (padCfg n r t Lc Rc ⟨System4Elem.set s :: R, 0, System4State.A⟩) (2 * t + 4) := by
  obtain ⟨k, hk⟩ : ∃ k, r - 1 - t = k + 1 := ⟨r - 2 - t, by omega⟩
  have hk' : r - 1 - (t + 1) = k := by omega
  obtain ⟨K0, K', hK⟩ := List.exists_cons_of_ne_nil (merged_ne_nil n t)
  have hKlen : K'.length = t := by
    have := length_merged n t
    rw [hK] at this
    simp at this
    omega
  -- the stations of the turn
  obtain ⟨G, hGdef⟩ : ∃ G, G = Lc ++ guardPairs n k ++ [System4Elem.set (gset n 1)] := ⟨_, rfl⟩
  have hG : G.length = Lc.length + 2 * k + 1 := by rw [hGdef]; simp; omega
  obtain ⟨c0, hc0⟩ : ∃ c0 : System4Config, c0 = ⟨(G ++ [System4Elem.star]) ++ sets (merged n t) ++
      System4Elem.set s :: (R ++ Rc), (G ++ [System4Elem.star]).length + t + 1, System4State.A⟩ := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ c1 : System4Config, c1 = ⟨(G ++ [System4Elem.star]) ++ sets (merged n t) ++
      System4Elem.set s :: (R ++ Rc), (G ++ [System4Elem.star]).length + t, System4State.A⟩ := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c2 : System4Config, c2 = ⟨(G ++ [System4Elem.star]) ++ sets (merged n t) ++
      System4Elem.set s :: (R ++ Rc), (G ++ [System4Elem.star]).length, System4State.A⟩ := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c3 : System4Config, c3 = ⟨G ++ System4Elem.star ::
      (sets (merged n t) ++ System4Elem.set s :: (R ++ Rc)), G.length, System4State.A⟩ := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ c4 : System4Config, c4 = ⟨G ++ sets (merged n t) ++
      System4Elem.set s :: (R ++ Rc), G.length, System4State.B⟩ := ⟨_, rfl⟩
  have e0 : padCfg n r t Lc Rc ⟨System4Elem.set s :: R, 0, System4State.A⟩ = c0 := by
    rw [hc0, hGdef]
    simp only [padCfg, hk, guardPairs_succ', System4Config.mk.injEq, List.append_assoc,
      List.cons_append, List.length_append, length_guardPairs, List.length_cons, List.length_nil,
      and_true]
    simp [sets]
    omega
  have s01 : System4.step c0 = some c1 := by
    rw [hc0, hc1]
    have h1 : (G ++ [System4Elem.star]) ++ sets (merged n t) ++ System4Elem.set s :: (R ++ Rc)
        = ((G ++ [System4Elem.star]) ++ sets (merged n t)) ++ System4Elem.set s :: (R ++ Rc) := by simp
    have h2 : (G ++ [System4Elem.star]).length + t + 1
        = ((G ++ [System4Elem.star]) ++ sets (merged n t)).length := by
      simp [sets, length_merged]; omega
    rw [h1, h2, step_setA _ _ _ (by simp)]
    simp only [Option.some.injEq, System4Config.mk.injEq, true_and, and_true, List.length_append,
      List.length_singleton, sets, List.length_map, length_merged]
    try omega
  have s12 : System4.nSteps c1 t = some c2 := by
    rw [hc1, hc2]
    exact moveLeft _ (merged n t) _ t (by rw [length_merged]; omega)
  have s23 : System4.step c2 = some c3 := by
    rw [hc2, hc3]
    have h1 : (G ++ [System4Elem.star]) ++ sets (merged n t) ++ System4Elem.set s :: (R ++ Rc)
        = (G ++ [System4Elem.star]) ++ System4Elem.set K0 :: (sets K' ++ System4Elem.set s :: (R ++ Rc)) := by
      rw [hK, sets_cons]; simp
    rw [h1, step_setA _ _ _ (by simp)]
    simp only [hK, sets_cons, List.append_assoc, List.cons_append, List.nil_append,
      List.length_append, List.length_singleton, Nat.add_sub_cancel]
  have s34 : System4.step c3 = some c4 := by
    rw [hc3, hc4, step_starA]
    simp only [List.append_assoc]
  have s45 : System4.nSteps c4 (t + 1)
      = some (padCfg n r (t + 1) Lc Rc ⟨System4Elem.set s :: R, 0, System4State.B⟩) := by
    rw [hc4]
    have hsw := sweep G (merged n t) (System4Elem.set s :: (R ++ Rc)) System4State.B (by decide)
    rw [length_merged, parMem_zero_merged n t hn] at hsw
    rw [hsw, hGdef]
    simp only [padCfg, hk', merged_succ n t hn, sets_cons, flip, Bool.false_eq_true, if_false,
      List.append_assoc, List.cons_append, List.length_append, length_guardPairs,
      List.length_singleton]
    simp [sets]
    omega
  have hrun : System4.nSteps c0 (2 * t + 4)
      = some (padCfg n r (t + 1) Lc Rc ⟨System4Elem.set s :: R, 0, System4State.B⟩) := by
    rw [show 2 * t + 4 = 1 + t + 1 + 1 + (t + 1) from by omega, System4.nSteps_add, System4.nSteps_add,
      System4.nSteps_add, System4.nSteps_add, System4.nSteps_one, s01, Option.bind_some, s12,
      Option.bind_some, System4.nSteps_one, s23, Option.bind_some, System4.nSteps_one, s34,
      Option.bind_some, s45]
  refine ⟨by rw [e0]; exact hrun, ?_⟩
  rw [e0, show 2 * t + 4 = 1 + t + 1 + 1 + (t + 1) from by omega]
  have hGpos : Lc.length + 1 ≤ G.length := by rw [hG]; omega
  have hc0a : Lc.length + 1 ≤ c0.active := by rw [hc0]; simp; omega
  have hc1a : Lc.length + 1 ≤ c1.active := by rw [hc1]; simp; omega
  have hc2a : Lc.length + 1 ≤ c2.active := by rw [hc2]; simp; omega
  have hc3a : Lc.length + 1 ≤ c3.active := by rw [hc3]; simp; omega
  have hc4a : Lc.length + 1 ≤ c4.active := by rw [hc4]; simp; omega
  have h03 : System4.nSteps c0 (1 + t + 1) = some c3 := by
    rw [System4.nSteps_add, System4.nSteps_add, System4.nSteps_one, s01, Option.bind_some, s12,
      Option.bind_some, System4.nSteps_one, s23]
  have h04 : System4.nSteps c0 (1 + t + 1 + 1) = some c4 := by
    rw [System4.nSteps_add, h03, Option.bind_some, System4.nSteps_one, s34]
  have h02 : System4.nSteps c0 (1 + t) = some c2 := by
    rw [System4.nSteps_add, System4.nSteps_one, s01, Option.bind_some, s12]
  refine PosRun_add _ _ _ _ _ h04 ?_ ?_
  · refine PosRun_add _ _ _ _ _ h03 ?_ (PosRun_one (fun c => Lc.length + 1 ≤ c.active) _ _ s34 hc3a hc4a)
    refine PosRun_add _ _ _ _ _ h02 ?_ (PosRun_one (fun c => Lc.length + 1 ≤ c.active) _ _ s23 hc2a hc3a)
    refine PosRun_add _ _ _ _ _ (by rw [System4.nSteps_one, s01])
      (PosRun_one (fun c => Lc.length + 1 ≤ c.active) _ _ s01 hc0a hc1a) ?_
    have := moveLeft_posRun (G ++ [System4Elem.star]) (merged n t) (System4Elem.set s :: (R ++ Rc)) t
      (by rw [length_merged]; omega)
    rw [← hc1] at this
    exact PosRun_mono _ _ _ _ this (fun c hc => by simp at hc; omega)
  · have := sweep_posRun G (merged n t) (System4Elem.set s :: (R ++ Rc)) System4State.B (by decide)
    rw [length_merged, ← hc4] at this
    exact PosRun_mono _ _ _ _ this (fun c hc => by omega)

/-- One step of the original tape is matched on the padded tape: one step,
    or the turn; the head stays right of the left context throughout. -/
theorem pad_step (n r t : Nat) (Lc Rc : List System4Elem) (c c1 : System4Config)
    (hs : System4.step c = some c1) (hr : t + 2 ≤ r) (hn : t + 3 ≤ n) :
    ∃ k t', 1 ≤ k ∧ t' ≤ t + 1 ∧
      System4.nSteps (padCfg n r t Lc Rc c) k = some (padCfg n r t' Lc Rc c1) ∧
      PosRun (fun c => Lc.length + 1 ≤ c.active) (padCfg n r t Lc Rc c) k := by
  obtain ⟨L, e, R, hc⟩ := focus_of_lt c (step_active_lt c c1 hs)
  obtain ⟨elems, act, st⟩ := c
  simp only [System4Config.mk.injEq] at hc
  obtain ⟨rfl, rfl, -⟩ := hc
  -- the padded configuration in focus form, for every rule but the turn
  have hpad : ∀ (L' : List System4Elem) (act' : Nat) (st' : System4State),
      padCfg n r t Lc Rc ⟨L', act', st'⟩
        = ⟨(Lc ++ guardPairs n (r - 1 - t) ++ sets (merged n t)) ++ (L' ++ Rc),
           (Lc ++ guardPairs n (r - 1 - t) ++ sets (merged n t)).length + act', st'⟩ := by
    intro L' act' st'
    simp only [padCfg, List.length_append, length_guardPairs, sets, List.length_map,
      length_merged, List.append_assoc, System4Config.mk.injEq, true_and, and_true]
    try omega
  have one_step : ∀ (c1 : System4Config), System4.step (padCfg n r t Lc Rc ⟨L ++ e :: R, L.length, st⟩)
      = some (padCfg n r t Lc Rc c1) →
      ∃ k t', 1 ≤ k ∧ t' ≤ t + 1 ∧
        System4.nSteps (padCfg n r t Lc Rc ⟨L ++ e :: R, L.length, st⟩) k = some (padCfg n r t' Lc Rc c1) ∧
        PosRun (fun c => Lc.length + 1 ≤ c.active) (padCfg n r t Lc Rc ⟨L ++ e :: R, L.length, st⟩) k := by
    intro c1 h1
    exact ⟨1, t, le_refl 1, by omega, by rw [System4.nSteps_one]; exact h1,
      PosRun_one (fun c => Lc.length + 1 ≤ c.active) _ _ h1 (padCfg_active_pos _ _ _ _ _ _)
        (padCfg_active_pos _ _ _ _ _ _)⟩
  -- the focus lemmas on the padded tape, with the prefix `P`
  obtain ⟨P, hP⟩ : ∃ P, P = Lc ++ guardPairs n (r - 1 - t) ++ sets (merged n t) := ⟨_, rfl⟩
  have hfocus : ∀ (L' : List System4Elem) (e' : System4Elem) (R' : List System4Elem) (st' : System4State),
      padCfg n r t Lc Rc ⟨L' ++ e' :: R', L'.length, st'⟩
        = ⟨(P ++ L') ++ e' :: (R' ++ Rc), (P ++ L').length, st'⟩ := by
    intro L' e' R' st'
    rw [hpad, hP]
    simp only [System4Config.mk.injEq, List.append_assoc, List.cons_append, List.length_append,
      length_guardPairs, sets, List.length_map, length_merged, true_and, and_true]
    try omega
  cases e with
  | set s =>
    cases st with
    | A =>
      cases L with
      | nil =>
        simp only [List.nil_append, List.length_nil] at hs ⊢
        rw [step_setA_zero] at hs
        obtain rfl := Option.some.inj hs
        obtain ⟨hrun, hpos⟩ := pad_turn n r t Lc Rc s R hr hn
        exact ⟨2 * t + 4, t + 1, by omega, le_refl _, hrun, hpos⟩
      | cons e0 L' =>
        rw [step_setA _ _ _ (by simp)] at hs
        obtain rfl := Option.some.inj hs
        apply one_step
        rw [hfocus, step_setA _ _ _ (by simp), hpad, hP]
        simp only [Option.some.injEq, System4Config.mk.injEq, List.append_assoc, List.cons_append,
          List.length_append, length_guardPairs, sets, List.length_map, length_merged, List.length_cons,
          true_and, and_true]
        try omega
    | B =>
      rw [step_setB] at hs
      obtain rfl := Option.some.inj hs
      apply one_step
      rw [hfocus, step_setB, hpad, hP]
      simp only [Option.some.injEq, System4Config.mk.injEq, List.append_assoc, List.cons_append,
        List.length_append, length_guardPairs, sets, List.length_map, length_merged, true_and, and_true]
      try omega
    | C =>
      rw [step_setC] at hs
      obtain rfl := Option.some.inj hs
      apply one_step
      rw [hfocus, step_setC, hpad, hP]
      simp only [Option.some.injEq, System4Config.mk.injEq, List.append_assoc, List.cons_append,
        List.length_append, length_guardPairs, sets, List.length_map, length_merged, true_and, and_true]
      try omega
  | star =>
    cases st with
    | A =>
      rw [step_starA] at hs
      obtain rfl := Option.some.inj hs
      apply one_step
      rw [hfocus, step_starA, hpad, hP]
      simp only [Option.some.injEq, System4Config.mk.injEq, List.append_assoc, List.length_append,
        length_guardPairs, sets, List.length_map, length_merged, true_and, and_true]
      try omega
    | B =>
      cases L with
      | nil =>
        exfalso
        simp [System4.step] at hs
      | cons e0 L' =>
        rw [step_starB _ _ (by simp)] at hs
        obtain rfl := Option.some.inj hs
        apply one_step
        rw [hfocus, step_starB _ _ (by simp), hpad, hP]
        simp only [Option.some.injEq, System4Config.mk.injEq, List.append_assoc, List.cons_append,
          List.length_append, length_guardPairs, sets, List.length_map, length_merged, List.length_cons,
          true_and, and_true]
        try omega
    | C =>
      cases R with
      | nil =>
        exfalso
        simp [System4.step] at hs
      | cons e1 R' =>
        cases e1 with
        | star =>
          exfalso
          simp [System4.step] at hs
        | set s =>
          rw [step_starC] at hs
          obtain rfl := Option.some.inj hs
          apply one_step
          rw [hfocus, List.cons_append, step_starC, hpad, hP]
          simp only [Option.some.injEq, System4Config.mk.injEq, List.append_assoc, List.cons_append,
            List.length_append, length_guardPairs, sets, List.length_map, length_merged, true_and, and_true]
          try omega

theorem System4_nSteps_some_of_le_aux (c0 cN : System4Config) (N : Nat)
    (hrun : System4.nSteps c0 (N + 1) = some cN) : ∃ cN', System4.nSteps c0 N = some cN' := by
  rw [System4.nSteps_add] at hrun
  cases h : System4.nSteps c0 N with
  | none => rw [h] at hrun; cases hrun
  | some c => exact ⟨c, rfl⟩

/-- The padded tape tracks a run of `N` steps of the original tape: at the
    `i`-th step the padded tape is the padded configuration with some number
    of turns `turns i <= i`, the times are strictly increasing, and the head
    is right of the left context throughout. -/
theorem pad_schedule (n r : Nat) (Lc Rc : List System4Elem) (N : Nat) (c0 : System4Config)
    (hr : N + 1 ≤ r) (hn : N + 2 ≤ n) (cN : System4Config) (hrun : System4.nSteps c0 N = some cN) :
    ∃ (times : Nat → Nat) (turns : Nat → Nat), times 0 = 0 ∧ turns 0 = 0 ∧
      (∀ i, i < N → times i < times (i + 1)) ∧
      (∀ i, i ≤ N → turns i ≤ i ∧ ∃ ci, System4.nSteps c0 i = some ci ∧
        System4.nSteps (padCfg n r 0 Lc Rc c0) (times i) = some (padCfg n r (turns i) Lc Rc ci)) ∧
      PosRun (fun c => Lc.length + 1 ≤ c.active) (padCfg n r 0 Lc Rc c0) (times N) := by
  induction N generalizing cN with
  | zero =>
    refine ⟨fun _ => 0, fun _ => 0, rfl, rfl, by intro i hi; omega, ?_, ?_⟩
    · intro i hi
      obtain rfl : i = 0 := by omega
      exact ⟨le_refl 0, c0, rfl, rfl⟩
    · exact PosRun_zero _ _ (padCfg_active_pos _ _ _ _ _ _)
  | succ N ih =>
    obtain ⟨cN', hcN'⟩ := System4_nSteps_some_of_le_aux c0 cN N hrun
    obtain ⟨times, turns, h0, ht0, hmono, htr, hpos⟩ := ih (by omega) (by omega) cN' hcN'
    obtain ⟨htN, cN'', hcN'', hpadN⟩ := htr N (le_refl N)
    rw [hcN'] at hcN''
    obtain rfl := Option.some.inj hcN''
    have hstep : System4.step cN' = some cN := by
      rw [System4.nSteps_add, hcN', Option.bind_some, System4.nSteps_one] at hrun
      exact hrun
    obtain ⟨k, t', hk, ht', hrunk, hposk⟩ :=
      pad_step n r (turns N) Lc Rc cN' cN hstep (by omega) (by omega)
    refine ⟨fun i => if i ≤ N then times i else times N + k,
      fun i => if i ≤ N then turns i else t', by simp [h0], by simp [ht0], ?_, ?_, ?_⟩
    · intro i hi
      dsimp only
      by_cases hiN : i < N
      · rw [if_pos (le_of_lt hiN), if_pos (by omega)]
        exact hmono i hiN
      · obtain rfl : i = N := by omega
        rw [if_pos (le_refl _), if_neg (by omega)]
        omega
    · intro i hi
      dsimp only
      by_cases hiN : i ≤ N
      · rw [if_pos hiN, if_pos hiN]
        exact htr i hiN
      · obtain rfl : i = N + 1 := by omega
        rw [if_neg hiN, if_neg hiN]
        refine ⟨by omega, cN, hrun, ?_⟩
        rw [System4.nSteps_add, hpadN, Option.bind_some, hrunk]
    · dsimp only
      rw [if_neg (by omega)]
      exact PosRun_add _ _ _ _ _ hpadN hpos hposk

end Smith
