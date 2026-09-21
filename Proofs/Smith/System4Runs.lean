/-
  Smith.System4Runs

  Run lemmas for System 4 (PLAN.md link C, milestone M3).  Every System 4
  run of the emulation is a composition of five local moves, so each rule
  of `System4.step` is first stated at a focus `L ++ e :: R` with the head
  on `e`; the sweeps of TM23Proof.pdf p. 16-18 are then inductions over a
  block of adjacent sets with an arbitrary context on both sides.

  Contents:
    * `system4Sys`: System 4 as a `StepSys`.
    * `step_setA`, `step_setA_zero`, `step_starA`, `step_setBC`,
      `step_starB`, `step_starC`: the five rules at a focus.
    * `decr`, `sets`, `parMem`, `flip`: the decremented set, a block of
      sets as tape elements, parity membership in a block (membership in
      the "one big merged set" of p. 16), and the state after a sweep.
    * `sweep`: a B/C sweep across a block of sets.
    * `moveLeft`, `turn`, `turnFrom`: the A walk back to the left end and
      the turn.
    * `cPhase`: the C-phase across the star/empty padding.
    * `decrN`, `loopK`, `loopCfg`: iterated decrement, the block around a
      rule set during the loop, and the tape shape during the loop.
    * `dStep`: the no-zero case of p. 17, two sweeps.
    * `preLoop`, `loopIter`, `loopRun`, `finalPass`, `popPhase`: the zero
      case of p. 17-18, one pop phase (the C-phase, the arrival at a
      block, the loop, the last pass), applied once at the rule set and
      once at the all-integers set by `Smith.Conjecture4`.
-/

import BiTM.System4
import BiTM.System5ToSystem4
import Smith.Simulation

namespace Smith

open BiTM
open System4Elem System4State

/-! ## System 4 as a step system -/

/-- System 4 as a `StepSys`. -/
def system4Sys : StepSys System4Config := ⟨System4.step⟩

@[simp] theorem system4Sys_step (c : System4Config) :
    system4Sys.step c = System4.step c := rfl

theorem system4Sys_nSteps (c : System4Config) (n : Nat) :
    system4Sys.nSteps c n = System4.nSteps c n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [StepSys.nSteps_succ_left, system4Sys_step]
    cases h : System4.step c with
    | none => simp [System4.nSteps, h]
    | some c' => simp [System4.nSteps, h, ih]

/-! ## The five rules at a focus -/

theorem focus_length (L : List System4Elem) (e : System4Elem) (R : List System4Elem) :
    L.length < (L ++ e :: R).length := by simp

theorem focus_get (L : List System4Elem) (e : System4Elem) (R : List System4Elem) :
    (L ++ e :: R).get ⟨L.length, focus_length L e R⟩ = e := by
  simp

theorem focus_set (L : List System4Elem) (e e' : System4Elem) (R : List System4Elem) :
    (L ++ e :: R).set L.length e' = L ++ e' :: R := by
  rw [List.set_append_right _ _ (Nat.le_refl _)]
  simp

theorem focus_eraseIdx (L : List System4Elem) (e : System4Elem) (R : List System4Elem) :
    (L ++ e :: R).eraseIdx L.length = L ++ R := by
  rw [List.eraseIdx_append_of_length_le (Nat.le_refl _)]
  simp

/-- Rule 1 away from the left end: a set in state A moves the head left. -/
theorem step_setA (L : List System4Elem) (s : List Int) (R : List System4Elem)
    (hL : L ≠ []) :
    System4.step ⟨L ++ set s :: R, L.length, A⟩ = some ⟨L ++ set s :: R, L.length - 1, A⟩ := by
  unfold System4.step
  rw [dif_pos (focus_length L _ R)]
  simp only [focus_get]
  rw [if_neg (by simpa using hL)]

/-- Rule 1 at the left end: the head turns round into state B. -/
theorem step_setA_zero (s : List Int) (R : List System4Elem) :
    System4.step ⟨set s :: R, 0, A⟩ = some ⟨set s :: R, 0, B⟩ := by
  unfold System4.step
  rw [dif_pos (by simp)]
  simp

/-- Rule 2: a star in state A is deleted, the head stays on what was to
    its right, state B. -/
theorem step_starA (L : List System4Elem) (R : List System4Elem) :
    System4.step ⟨L ++ star :: R, L.length, A⟩ = some ⟨L ++ R, L.length, B⟩ := by
  unfold System4.step
  rw [dif_pos (focus_length L _ R)]
  simp only [focus_get, focus_eraseIdx]

/-- Rule 3 in state B. -/
theorem step_setB (L : List System4Elem) (s : List Int) (R : List System4Elem) :
    System4.step ⟨L ++ set s :: R, L.length, B⟩
      = some ⟨L ++ set (decrementSet s).1 :: R, L.length + 1, if 0 ∈ s then C else B⟩ := by
  unfold System4.step
  rw [dif_pos (focus_length L _ R)]
  simp only [focus_get, focus_set]
  by_cases h0 : (0 : Int) ∈ s
  · simp [decrementSet, h0]
  · simp [decrementSet, h0]

/-- Rule 3 in state C. -/
theorem step_setC (L : List System4Elem) (s : List Int) (R : List System4Elem) :
    System4.step ⟨L ++ set s :: R, L.length, C⟩
      = some ⟨L ++ set (decrementSet s).1 :: R, L.length + 1, if 0 ∈ s then B else C⟩ := by
  unfold System4.step
  rw [dif_pos (focus_length L _ R)]
  simp only [focus_get, focus_set]
  by_cases h0 : (0 : Int) ∈ s
  · simp [decrementSet, h0]
  · simp [decrementSet, h0]

/-- Rule 4: a star in state B is deleted, the head moves left, state A. -/
theorem step_starB (L : List System4Elem) (R : List System4Elem) (hL : L ≠ []) :
    System4.step ⟨L ++ star :: R, L.length, B⟩ = some ⟨L ++ R, L.length - 1, A⟩ := by
  unfold System4.step
  rw [dif_pos (focus_length L _ R)]
  simp only [focus_get, focus_eraseIdx]
  rw [if_neg (by simpa using hL)]

/-- Rule 5: a star in state C moves the head onto the set to its right and
    toggles `1` there. -/
theorem step_starC (L : List System4Elem) (s : List Int) (R : List System4Elem) :
    System4.step ⟨L ++ star :: set s :: R, L.length, C⟩
      = some ⟨L ++ star :: set (xorInsert 1 s) :: R, L.length + 1, C⟩ := by
  unfold System4.step
  rw [dif_pos (focus_length L _ _)]
  simp only [focus_get]
  have h1 : L.length + 1 < (L ++ star :: set s :: R).length := by simp
  rw [dif_pos h1]
  have hg : (L ++ star :: set s :: R).get ⟨L.length + 1, h1⟩ = set s := by
    simp [List.getElem_append_right]
  simp only [hg]
  have hs : (L ++ star :: set s :: R).set (L.length + 1) (set (xorInsert 1 s))
      = L ++ star :: set (xorInsert 1 s) :: R := by
    rw [List.set_append_right _ _ (by omega)]
    simp
  rw [hs]

/-! ## Sets, decrement, parity membership -/

/-- The decremented set of rule 3, without the zero flag. -/
def decr (s : List Int) : List Int := (decrementSet s).1

theorem decr_mem (s : List Int) (hs : s.Nodup) (x : Int) :
    x ∈ decr s ↔ x + 1 ∈ s ∧ x + 1 ≠ 0 := by
  unfold decr decrementSet
  by_cases h0 : (0 : Int) ∈ s
  · rw [if_pos h0]
    simp only [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hne : y ≠ 0 := fun h => by subst h; exact (List.Nodup.not_mem_erase hs) hy
      exact ⟨by rw [Int.sub_add_cancel]; exact List.mem_of_mem_erase hy, by omega⟩
    · rintro ⟨hx, hne⟩
      exact ⟨x + 1, (List.mem_erase_of_ne hne).mpr hx, by omega⟩
  · rw [if_neg h0]
    simp only [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨by rw [Int.sub_add_cancel]; exact hy, ?_⟩
      intro h
      rw [Int.sub_add_cancel] at h
      exact h0 (h ▸ hy)
    · rintro ⟨hx, _⟩
      exact ⟨x + 1, hx, by omega⟩

theorem decr_nodup (s : List Int) (hs : s.Nodup) : (decr s).Nodup :=
  decrementSet_nodup s hs

theorem decr_nonneg (s : List Int) (hs : s.Nodup) (h0 : ∀ x ∈ s, 0 ≤ x) :
    ∀ x ∈ decr s, 0 ≤ x := by
  intro x hx
  obtain ⟨hx1, hne⟩ := (decr_mem s hs x).mp hx
  have := h0 _ hx1
  omega

/-- A block of adjacent sets as tape elements. -/
def sets (K : List (List Int)) : List System4Elem := K.map set

@[simp] theorem sets_nil : sets [] = [] := rfl
@[simp] theorem sets_cons (S : List Int) (K : List (List Int)) : sets (S :: K) = set S :: sets K := rfl
@[simp] theorem sets_append (K K' : List (List Int)) : sets (K ++ K') = sets K ++ sets K' := by
  simp [sets]
@[simp] theorem sets_length (K : List (List Int)) : (sets K).length = K.length := by simp [sets]

/-- Parity membership: `x` lies in an odd number of the sets of `K`.  This
    is membership in the symmetric difference of the block, the "one big
    merged set" of TM23Proof.pdf p. 16. -/
def parMem (x : Int) : List (List Int) → Bool
  | [] => false
  | S :: K => (decide (x ∈ S)) ^^ parMem x K

@[simp] theorem parMem_nil (x : Int) : parMem x [] = false := rfl
@[simp] theorem parMem_cons (x : Int) (S : List Int) (K : List (List Int)) :
    parMem x (S :: K) = ((decide (x ∈ S)) ^^ parMem x K) := rfl

theorem parMem_append (x : Int) (K K' : List (List Int)) :
    parMem x (K ++ K') = (parMem x K ^^ parMem x K') := by
  induction K with
  | nil => simp
  | cons S K ih => simp [ih]

theorem parMem_map_decr (x : Int) (K : List (List Int)) (hK : ∀ S ∈ K, S.Nodup)
    (hx : x + 1 ≠ 0) : parMem x (K.map decr) = parMem (x + 1) K := by
  induction K with
  | nil => simp
  | cons S K ih =>
    simp only [List.map_cons, parMem_cons]
    rw [ih (fun S h => hK S (List.mem_cons_of_mem _ h))]
    have := decr_mem S (hK S List.mem_cons_self) x
    simp [this, hx]

/-- Toggle between B and C; A is fixed. -/
def tog : System4State → System4State
  | A => A
  | B => C
  | C => B

@[simp] theorem tog_tog (st : System4State) : tog (tog st) = st := by cases st <;> rfl

/-- The state after a sweep in state `st` over sets whose zero parity is `b`. -/
def flip (b : Bool) (st : System4State) : System4State := if b then tog st else st

@[simp] theorem flip_false (st : System4State) : flip false st = st := rfl
@[simp] theorem flip_true (st : System4State) : flip true st = tog st := rfl
theorem flip_flip (a b : Bool) (st : System4State) : flip b (flip a st) = flip (a ^^ b) st := by
  cases a <;> cases b <;> simp [flip]
theorem flip_ne_A (b : Bool) (st : System4State) (h : st ≠ A) : flip b st ≠ A := by
  cases b <;> cases st <;> simp_all [flip, tog]

/-- Rule 3 in either of the states B, C. -/
theorem step_setBC (L : List System4Elem) (s : List Int) (R : List System4Elem)
    (st : System4State) (hst : st ≠ A) :
    System4.step ⟨L ++ set s :: R, L.length, st⟩
      = some ⟨L ++ set (decr s) :: R, L.length + 1, flip (decide (0 ∈ s)) st⟩ := by
  cases st with
  | A => exact absurd rfl hst
  | B => rw [step_setB]; by_cases h0 : (0 : Int) ∈ s <;> simp [h0, flip, tog, decr]
  | C => rw [step_setC]; by_cases h0 : (0 : Int) ∈ s <;> simp [h0, flip, tog, decr]

/-! ## Sweeps -/

/-- A sweep: in state B or C the head crosses a block of adjacent sets left
    to right, decrementing each, and ends on the element after the block in
    the state flipped once per set that contained a `0`. -/
theorem sweep (L : List System4Elem) (K : List (List Int)) (R : List System4Elem)
    (st : System4State) (hst : st ≠ A) :
    System4.nSteps ⟨L ++ sets K ++ R, L.length, st⟩ K.length
      = some ⟨L ++ sets (K.map decr) ++ R, L.length + K.length, flip (parMem 0 K) st⟩ := by
  induction K generalizing L st with
  | nil => simp
  | cons S K ih =>
    rw [sets_cons, List.length_cons, System4.nSteps_succ]
    have h1 : L ++ set S :: sets K ++ R = L ++ set S :: (sets K ++ R) := by simp
    rw [h1, step_setBC L S _ st hst, Option.bind_some]
    have h2 : L ++ set (decr S) :: (sets K ++ R) = (L ++ [set (decr S)]) ++ sets K ++ R := by simp
    have h3 : L.length + 1 = (L ++ [set (decr S)]).length := by simp
    rw [h2, h3, ih (L ++ [set (decr S)]) _ (flip_ne_A _ _ hst)]
    simp only [List.length_append, List.length_singleton, List.map_cons, sets_cons, parMem_cons,
      flip_flip, List.append_assoc, List.singleton_append]
    congr 2
    omega

/-- In state A the head walks left across a block of adjacent sets. -/
theorem moveLeft (L : List System4Elem) (K : List (List Int)) (R : List System4Elem)
    (k : Nat) (hk : k < K.length) :
    System4.nSteps ⟨L ++ sets K ++ R, L.length + k, A⟩ k
      = some ⟨L ++ sets K ++ R, L.length, A⟩ := by
  induction K generalizing L k with
  | nil => simp at hk
  | cons S K ih =>
    cases k with
    | zero => simp
    | succ k =>
      cases K with
      | nil => simp at hk
      | cons S' K' =>
        have h1 : L ++ sets (S :: S' :: K') ++ R = (L ++ [set S]) ++ sets (S' :: K') ++ R := by simp
        have h2 : L.length + (k + 1) = (L ++ [set S]).length + k := by simp; omega
        rw [h1, h2, System4.nSteps_add, ih (L ++ [set S]) k (by simpa using hk), Option.bind_some,
          System4.nSteps_one]
        have h3 : (L ++ [set S]) ++ sets (S' :: K') ++ R = (L ++ [set S]) ++ set S' :: (sets K' ++ R) := by
          simp
        rw [h3, step_setA (L ++ [set S]) S' _ (by simp)]
        simp

/-- From the right end of the leftmost block the head returns to the left
    end of the tape and turns round into state B. -/
theorem turn (K : List (List Int)) (R : List System4Elem) (hK : K ≠ []) :
    System4.nSteps ⟨sets K ++ R, K.length - 1, A⟩ K.length
      = some ⟨sets K ++ R, 0, B⟩ := by
  obtain ⟨S, K', rfl⟩ := List.exists_cons_of_ne_nil hK
  simp only [List.length_cons, Nat.add_sub_cancel]
  rw [System4.nSteps_add]
  have hm := moveLeft [] (S :: K') R K'.length (by simp)
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hm
  rw [hm, Option.bind_some, System4.nSteps_one, sets_cons, List.cons_append, step_setA_zero]

/-- Padding of `* {0}` pairs, what the C-phase leaves behind. -/
def starredZeroPairs : Nat → List System4Elem
  | 0 => []
  | k + 1 => star :: set [0] :: starredZeroPairs k

@[simp] theorem starredZeroPairs_length (n : Nat) : (starredZeroPairs n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [starredZeroPairs, ih]; omega

/-- The C-phase: in state C the head runs through `g` star/empty pairs,
    turning every empty set into `{0}`, two steps per pair. -/
theorem cPhase (L : List System4Elem) (g : Nat) (R : List System4Elem) :
    System4.nSteps ⟨L ++ starredEmptyPairs g ++ R, L.length, C⟩ (2 * g)
      = some ⟨L ++ starredZeroPairs g ++ R, L.length + 2 * g, C⟩ := by
  induction g generalizing L with
  | zero => simp [starredEmptyPairs, starredZeroPairs]
  | succ g ih =>
    have h1 : L ++ starredEmptyPairs (g + 1) ++ R
        = L ++ star :: System4Elem.set [] :: (starredEmptyPairs g ++ R) := by
      simp [starredEmptyPairs]
    have h2 : 2 * (g + 1) = 2 + 2 * g := by omega
    rw [h2, System4.nSteps_add, h1]
    have hpair : System4.nSteps
        ⟨L ++ star :: System4Elem.set [] :: (starredEmptyPairs g ++ R), L.length, C⟩ 2
        = some ⟨(L ++ [star, System4Elem.set [0]]) ++ starredEmptyPairs g ++ R,
                (L ++ [star, System4Elem.set [0]]).length, C⟩ := by
      rw [System4.nSteps_succ, step_starC, Option.bind_some, System4.nSteps_one]
      have h3 : L ++ star :: System4Elem.set (xorInsert 1 []) :: (starredEmptyPairs g ++ R)
          = (L ++ [star]) ++ System4Elem.set [1] :: (starredEmptyPairs g ++ R) := by
        simp [xorInsert]
      have h4 : L.length + 1 = (L ++ [star]).length := by simp
      rw [h3, h4, step_setC, if_neg (by decide)]
      simp [decrementSet]
    rw [hpair, Option.bind_some, ih]
    simp [starredZeroPairs]
    omega

theorem starredZeroPairs_succ_right (n : Nat) :
    starredZeroPairs (n + 1) = starredZeroPairs n ++ [star, set [0]] := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show star :: set [0] :: starredZeroPairs (k + 1) = star :: set [0] :: starredZeroPairs k ++ _
    rw [ih]
    simp

theorem starredEmptyPairs_succ (n : Nat) :
    starredEmptyPairs (n + 1) = star :: set [] :: starredEmptyPairs n := rfl

/-- Iterated decrement. -/
def decrN : Nat → List Int → List Int
  | 0, S => S
  | i + 1, S => decr (decrN i S)

@[simp] theorem decrN_zero (S : List Int) : decrN 0 S = S := rfl
@[simp] theorem decrN_succ (i : Nat) (S : List Int) : decrN (i + 1) S = decr (decrN i S) := rfl

theorem decrN_succ' (i : Nat) (S : List Int) : decrN (i + 1) S = decrN i (decr S) := by
  induction i generalizing S with
  | zero => rfl
  | succ i ih => rw [decrN_succ, ih, ← decrN_succ]

theorem decrN_nodup (i : Nat) (S : List Int) (hS : S.Nodup) : (decrN i S).Nodup := by
  induction i with
  | zero => exact hS
  | succ i ih => exact decr_nodup _ ih

theorem decrN_nonneg (i : Nat) (S : List Int) (hS : S.Nodup) (h0 : ∀ x ∈ S, 0 ≤ x) :
    ∀ x ∈ decrN i S, 0 ≤ x := by
  induction i with
  | zero => exact h0
  | succ i ih => exact decr_nonneg _ (decrN_nodup i S hS) ih

theorem decrN_mem (i : Nat) (S : List Int) (hS : S.Nodup) (h0 : ∀ x ∈ S, 0 ≤ x) (x : Int) :
    x ∈ decrN i S ↔ 0 ≤ x ∧ x + i ∈ S := by
  induction i generalizing x with
  | zero =>
    simp only [decrN_zero]
    constructor
    · intro h
      exact ⟨h0 x h, by simpa using h⟩
    · rintro ⟨_, h⟩
      simpa using h
  | succ i ih =>
    rw [decrN_succ, decr_mem _ (decrN_nodup i S hS), ih]
    have : x + 1 + (i : Int) = x + ((i + 1 : Nat) : Int) := by omega
    rw [this]
    constructor
    · rintro ⟨⟨_, h⟩, hne⟩; exact ⟨by omega, h⟩
    · rintro ⟨hx, h⟩; exact ⟨⟨by omega, h⟩, by omega⟩

@[simp] theorem decr_nil : decr [] = [] := rfl
@[simp] theorem decr_zero : decr [0] = [] := by decide

theorem parMem_replicate_nil (x : Int) (i : Nat) : parMem x (List.replicate i []) = false := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, ih]

/-! ## The runs of the emulation -/

/-- From any position inside the leftmost block the head returns to the
    left end of the tape and turns round into state B. -/
theorem turnFrom (K : List (List Int)) (R : List System4Elem) (k : Nat) (hk : k < K.length) :
    System4.nSteps ⟨sets K ++ R, k, A⟩ (k + 1) = some ⟨sets K ++ R, 0, B⟩ := by
  obtain ⟨S, K', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega : 0 < K.length))
  rw [System4.nSteps_add]
  have hm := moveLeft [] (S :: K') R k hk
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hm
  rw [hm, Option.bind_some, System4.nSteps_one, sets_cons, List.cons_append, step_setA_zero]

/-- A D-step (TM23Proof.pdf p. 17, "the bag didn't contain a 0"): two
    sweeps of the leftmost block, each followed by the deletion of the next
    star, which merges an empty set into the block. -/
theorem dStep (K0 : List (List Int)) (g : Nat) (R' : List System4Elem)
    (hK0 : K0 ≠ []) (hg : 2 ≤ g) (h0 : parMem 0 K0 = false)
    (h1 : parMem 0 (K0.map decr) = false) :
    System4.nSteps ⟨sets K0 ++ starredEmptyPairs g ++ R', 0, A⟩ (4 * K0.length + 4)
      = some ⟨sets ((K0.map decr).map decr ++ [[], []]) ++ starredEmptyPairs (g - 2) ++ R', 0, A⟩ := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 2 := ⟨g - 2, by omega⟩
  obtain ⟨S, K', hSK⟩ := List.exists_cons_of_ne_nil hK0
  -- turn
  have e1 : System4.nSteps ⟨sets K0 ++ starredEmptyPairs (g' + 2) ++ R', 0, A⟩ 1
      = some ⟨sets K0 ++ (starredEmptyPairs (g' + 2) ++ R'), 0, B⟩ := by
    rw [System4.nSteps_one, hSK]
    simp only [sets_cons, List.cons_append, List.append_assoc]
    exact step_setA_zero _ _
  -- first sweep
  have e2 := sweep [] K0 (starredEmptyPairs (g' + 2) ++ R') B (by decide)
  simp only [List.nil_append, List.length_nil, Nat.zero_add, h0, flip_false] at e2
  -- first star
  have e3 : System4.nSteps ⟨sets (K0.map decr) ++ (starredEmptyPairs (g' + 2) ++ R'), K0.length, B⟩ 1
      = some ⟨sets (K0.map decr ++ [[]]) ++ (starredEmptyPairs (g' + 1) ++ R'), K0.length - 1, A⟩ := by
    rw [System4.nSteps_one]
    have h : sets (K0.map decr) ++ (starredEmptyPairs (g' + 2) ++ R')
        = sets (K0.map decr) ++ star :: (System4Elem.set [] :: (starredEmptyPairs (g' + 1) ++ R')) := by
      simp [starredEmptyPairs_succ]
    have hl : K0.length = (sets (K0.map decr)).length := by simp
    rw [h, hl, step_starB _ _ (by simp [sets, hK0])]
    simp
  -- second turn
  have e4 := turnFrom (K0.map decr ++ [[]]) (starredEmptyPairs (g' + 1) ++ R') (K0.length - 1)
    (by simp <;> omega)
  -- second sweep
  have e5 := sweep [] (K0.map decr ++ [[]]) (starredEmptyPairs (g' + 1) ++ R') B (by decide)
  simp only [List.nil_append, List.length_nil, Nat.zero_add, parMem_append, h1, parMem_cons,
    parMem_nil, List.not_mem_nil, decide_false, Bool.false_xor, flip_false, List.map_append,
    List.map_cons, List.map_nil, decr_nil, List.length_append, List.length_cons,
    List.length_map] at e5
  -- second star
  have e6 : System4.nSteps ⟨sets ((K0.map decr).map decr ++ [[]]) ++ (starredEmptyPairs (g' + 1) ++ R'),
      K0.length + 1, B⟩ 1
      = some ⟨sets ((K0.map decr).map decr ++ [[], []]) ++ (starredEmptyPairs g' ++ R'), K0.length, A⟩ := by
    rw [System4.nSteps_one]
    have h : sets ((K0.map decr).map decr ++ [[]]) ++ (starredEmptyPairs (g' + 1) ++ R')
        = sets ((K0.map decr).map decr ++ [[]]) ++ star :: (System4Elem.set [] :: (starredEmptyPairs g' ++ R')) := by
      simp [starredEmptyPairs_succ]
    have hl : K0.length + 1 = (sets ((K0.map decr).map decr ++ [[]])).length := by simp
    rw [h, hl, step_starB _ _ (by simp)]
    simp
  -- walk back
  have e7 := moveLeft [] ((K0.map decr).map decr ++ [[], []]) (starredEmptyPairs g' ++ R') K0.length
    (by simp)
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at e7
  -- assemble
  have hsum : 4 * K0.length + 4
      = 1 + K0.length + 1 + (K0.length - 1 + 1) + (K0.length + 1) + 1 + K0.length := by
    have := List.length_pos_iff.mpr hK0
    omega
  rw [hsum, System4.nSteps_add, System4.nSteps_add, System4.nSteps_add, System4.nSteps_add,
    System4.nSteps_add, System4.nSteps_add, e1, Option.bind_some, e2, Option.bind_some, e3,
    Option.bind_some, e4, Option.bind_some, e5, Option.bind_some, e6, Option.bind_some, e7]
  simp

/-- The block of adjacent sets around the set of a rule block during the
    loop of TM23Proof.pdf p. 17: a `{0}` merged from the padding, the
    empty sets merged so far, the decremented rule set, and the empty
    sets merged from its own padding. -/
def loopK (i : Nat) (R : List Int) : List (List Int) :=
  [0] :: List.replicate i [] ++ [R] ++ List.replicate (i + 2) []

@[simp] theorem loopK_length (i : Nat) (R : List Int) : (loopK i R).length = 2 * i + 4 := by
  simp [loopK]; omega

theorem loopK_map_decr (i : Nat) (R : List Int) :
    [0] :: (loopK i R).map decr ++ [[]] = loopK (i + 1) (decr R) := by
  have h : ∀ n, List.replicate n ([] : List Int) ++ [[]] = [] :: List.replicate n [] := fun n => by
    rw [← List.replicate_succ', List.replicate_succ]
  simp [loopK, List.replicate_succ, h]

theorem parMem_loopK (x : Int) (i : Nat) (R : List Int) :
    parMem x (loopK i R) = (decide (x = 0) ^^ decide (x ∈ R)) := by
  simp [loopK, parMem_append, parMem_replicate_nil]

theorem parMem_loopK_map_decr (x : Int) (i : Nat) (R : List Int) :
    parMem x ((loopK i R).map decr) = decide (x ∈ decr R) := by
  simp [loopK, parMem_append, List.map_replicate, parMem_replicate_nil]

/-- The tape during the loop: the context `L0`, `n` star/`{0}` pairs, a
    star, the block `K`, `m` star/empty pairs, the rest; the head is one
    place left of the right end of `K`, in state A. -/
def loopCfg (L0 : List System4Elem) (n : Nat) (K : List (List Int)) (m : Nat)
    (R' : List System4Elem) : System4Config :=
  ⟨L0 ++ starredZeroPairs n ++ star :: sets K ++ starredEmptyPairs m ++ R',
   L0.length + 2 * n + 1 + (K.length - 2), A⟩

/-- Macro A, the arrival at a rule block in state C (p. 17): the star is
    crossed with a toggle of `1`, the set is decremented twice, the star on
    either side of it is deleted, and one empty set is merged on the right. -/
theorem preLoop (L0 : List System4Elem) (Z Rs : List Int) (m : Nat) (R' : List System4Elem)
    (hm : 2 ≤ m) (h0 : 0 ∈ xorInsert 1 Rs) (h1 : 0 ∉ decr (xorInsert 1 Rs)) :
    System4.nSteps ⟨L0 ++ set Z :: star :: set Rs :: (starredEmptyPairs m ++ R'), L0.length + 1, C⟩ 8
      = some ⟨L0 ++ sets [Z, decr (decr (xorInsert 1 Rs)), [], []] ++ starredEmptyPairs (m - 2) ++ R',
              L0.length + 2, A⟩ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  simp only [Nat.add_sub_cancel, starredEmptyPairs_succ]
  -- 1. rule 5
  have t1 : L0 ++ set Z :: star :: set Rs :: (star :: System4Elem.set [] :: star :: System4Elem.set [] :: starredEmptyPairs m' ++ R')
      = (L0 ++ [set Z]) ++ star :: set Rs :: star :: System4Elem.set [] :: star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R') := by
    simp
  have l1 : L0.length + 1 = (L0 ++ [set Z]).length := by simp
  rw [System4.nSteps_succ, t1, l1, step_starC, Option.bind_some]
  -- 2. rule 3 in C on the toggled set
  have t2 : (L0 ++ [set Z]) ++ star :: set (xorInsert 1 Rs) :: star :: System4Elem.set [] :: star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')
      = (L0 ++ [set Z, star]) ++ set (xorInsert 1 Rs) :: star :: System4Elem.set [] :: star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R') := by
    simp
  have l2 : (L0 ++ [set Z]).length + 1 = (L0 ++ [set Z, star]).length := by simp
  rw [System4.nSteps_succ, t2, l2, step_setBC _ _ _ C (by decide), Option.bind_some]
  simp only [h0, decide_true, flip_true, tog]
  -- 3. rule 4 on the star right of it
  have t3 : (L0 ++ [set Z, star]) ++ set (decr (xorInsert 1 Rs)) :: star :: System4Elem.set [] :: star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')
      = (L0 ++ [set Z, star, set (decr (xorInsert 1 Rs))]) ++ star :: System4Elem.set [] :: star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R') := by
    simp
  have l3 : (L0 ++ [set Z, star]).length + 1 = (L0 ++ [set Z, star, set (decr (xorInsert 1 Rs))]).length := by simp
  rw [System4.nSteps_succ, t3, l3, step_starB _ _ (by simp), Option.bind_some]
  -- 4. rule 1, move left onto the opening star
  have t4 : (L0 ++ [set Z, star, set (decr (xorInsert 1 Rs))]) ++ System4Elem.set [] :: star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')
      = (L0 ++ [set Z, star]) ++ set (decr (xorInsert 1 Rs)) :: System4Elem.set [] :: star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R') := by
    simp
  have l4 : (L0 ++ [set Z, star, set (decr (xorInsert 1 Rs))]).length - 1 = (L0 ++ [set Z, star]).length := by simp
  rw [System4.nSteps_succ, t4, l4, step_setA _ _ _ (by simp), Option.bind_some]
  -- 5. rule 2, delete the opening star
  have t5 : (L0 ++ [set Z, star]) ++ set (decr (xorInsert 1 Rs)) :: System4Elem.set [] :: star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')
      = (L0 ++ [set Z]) ++ star :: set (decr (xorInsert 1 Rs)) :: System4Elem.set [] :: star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R') := by
    simp
  have l5 : (L0 ++ [set Z, star]).length - 1 = (L0 ++ [set Z]).length := by simp
  rw [System4.nSteps_succ, t5, l5, step_starA, Option.bind_some]
  -- 6. rule 3 in B on the set, no zero
  rw [System4.nSteps_succ, step_setBC _ _ _ B (by decide), Option.bind_some]
  simp only [h1, decide_false, flip_false]
  -- 7. rule 3 in B on the empty set
  have t7 : (L0 ++ [set Z]) ++ set (decr (decr (xorInsert 1 Rs))) :: System4Elem.set [] :: star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')
      = (L0 ++ [set Z, set (decr (decr (xorInsert 1 Rs)))]) ++ System4Elem.set [] :: star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R') := by
    simp
  have l7 : (L0 ++ [set Z]).length + 1 = (L0 ++ [set Z, set (decr (decr (xorInsert 1 Rs)))]).length := by simp
  rw [System4.nSteps_succ, t7, l7, step_setBC _ _ _ B (by decide), Option.bind_some]
  simp only [List.not_mem_nil, decide_false, flip_false, decr_nil]
  -- 8. rule 4 on the next star
  have t8 : (L0 ++ [set Z, set (decr (decr (xorInsert 1 Rs)))]) ++ System4Elem.set [] :: star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')
      = (L0 ++ [set Z, set (decr (decr (xorInsert 1 Rs))), System4Elem.set []]) ++ star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R') := by
    simp
  have l8 : (L0 ++ [set Z, set (decr (decr (xorInsert 1 Rs)))]).length + 1
      = (L0 ++ [set Z, set (decr (decr (xorInsert 1 Rs))), System4Elem.set []]).length := by simp
  rw [System4.nSteps_succ, t8, l8, step_starB _ _ (by simp), Option.bind_some, System4.nSteps_zero]
  simp only [Option.some.injEq, System4Config.mk.injEq]
  refine ⟨by simp, ?_, trivial⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- Macro B, one iteration of the loop (p. 17): the head walks left over
    the block, deletes the star to its left (merging a `{0}`), sweeps the
    block in state B, deletes the star to its right (merging an empty set). -/
theorem loopIter (L0 : List System4Elem) (n : Nat) (K : List (List Int)) (m : Nat)
    (R' : List System4Elem) (hn : 1 ≤ n) (hm : 1 ≤ m) (hK : 2 ≤ K.length)
    (hpar : parMem 0 K = false) :
    System4.nSteps (loopCfg L0 n K m R') (2 * K.length + 1)
      = some (loopCfg L0 (n - 1) ([0] :: K.map decr ++ [[]]) (m - 1) R') := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [loopCfg, Nat.add_sub_cancel, starredZeroPairs_succ_right, starredEmptyPairs_succ]
  have hsum : 2 * K.length + 1 = (K.length - 2) + 1 + 1 + K.length + 1 := by omega
  rw [hsum, System4.nSteps_add, System4.nSteps_add, System4.nSteps_add, System4.nSteps_add]
  -- 1. walk left over K
  have t1 : L0 ++ (starredZeroPairs n' ++ [star, System4Elem.set [0]]) ++ star :: sets K ++ (star :: System4Elem.set [] :: starredEmptyPairs m') ++ R'
      = (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0], star]) ++ sets K ++ (star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')) := by
    simp
  have l1 : L0.length + 2 * (n' + 1) + 1 + (K.length - 2)
      = (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0], star]).length + (K.length - 2) := by
    simp; omega
  rw [t1, l1, moveLeft _ _ _ _ (by omega), Option.bind_some, System4.nSteps_one]
  obtain ⟨S, K', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega : 0 < K.length))
  -- 2. rule 1 onto the star
  have t2 : (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0], star]) ++ sets (S :: K') ++ (star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R'))
      = (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0], star]) ++ set S :: (sets K' ++ star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')) := by
    simp
  rw [t2, step_setA _ _ _ (by simp), Option.bind_some, System4.nSteps_one]
  -- 3. rule 2, delete the star
  have t3 : (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0], star]) ++ set S :: (sets K' ++ star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R'))
      = (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0]]) ++ star :: (set S :: (sets K' ++ star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R'))) := by
    simp
  have l3 : (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0], star]).length - 1
      = (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0]]).length := by simp
  rw [t3, l3, step_starA, Option.bind_some]
  -- 4. sweep K in state B
  have t4 : (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0]]) ++ (set S :: (sets K' ++ star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')))
      = (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0]]) ++ sets (S :: K') ++ (star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')) := by
    simp
  rw [t4, sweep _ _ _ B (by decide), Option.bind_some, hpar, flip_false, System4.nSteps_one]
  -- 5. rule 4, delete the star on the right
  have t5 : (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0]]) ++ sets ((S :: K').map decr) ++ (star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R'))
      = (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0]] ++ sets ((S :: K').map decr)) ++ star :: (System4Elem.set [] :: (starredEmptyPairs m' ++ R')) := by
    simp
  have l5 : (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0]]).length + (S :: K').length
      = (L0 ++ starredZeroPairs n' ++ [star, System4Elem.set [0]] ++ sets ((S :: K').map decr)).length := by
    simp; omega
  rw [t5, l5, step_starB _ _ (by simp)]
  simp only [Option.some.injEq, System4Config.mk.injEq]
  refine ⟨by simp, ?_, trivial⟩
  simp only [List.length_append, List.length_cons, List.length_nil, sets_length, List.length_map,
    starredZeroPairs_length]
  omega

/-- The loop, `n` iterations. -/
theorem loopRun (L0 : List System4Elem) (n : Nat) (i : Nat) (R : List Int) (m : Nat)
    (R' : List System4Elem) (hm : n ≤ m) (hR : ∀ i', i' < n → 0 ∈ decrN i' R) :
    ∃ k, System4.nSteps (loopCfg L0 n (loopK i R) m R') k
      = some (loopCfg L0 0 (loopK (i + n) (decrN n R)) (m - n) R') := by
  induction n generalizing i R m with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    have h00 := hR 0 (by omega)
    rw [decrN_zero] at h00
    have hstep := loopIter L0 (n + 1) (loopK i R) m R' (by omega) (by omega) (by simp)
      (by rw [parMem_loopK]; simp [h00])
    rw [Nat.add_sub_cancel, loopK_map_decr] at hstep
    obtain ⟨k, hk⟩ := ih (i + 1) (decr R) (m - 1) (by omega)
      (fun i' hi' => by
        have := hR (i' + 1) (by omega)
        rw [decrN_succ'] at this
        exact this)
    refine ⟨2 * (loopK i R).length + 1 + k, ?_⟩
    rw [System4.nSteps_add, hstep, Option.bind_some, hk]
    have e1 : i + 1 + n = i + (n + 1) := by omega
    have e2 : m - 1 - n = m - (n + 1) := by omega
    rw [e1, e2, ← decrN_succ']

/-- Macro C, the last pass of the loop (p. 17, "the last star is going to
    be removed to its left"): the block merges with the leftmost block,
    and the head returns to the left end of the tape. -/
theorem finalPass (K0 K : List (List Int)) (m : Nat) (R' : List System4Elem)
    (hK0 : K0 ≠ []) (hK : 2 ≤ K.length) (hm : 1 ≤ m) (hpar : parMem 0 K = false) :
    System4.nSteps (loopCfg (sets K0) 0 K m R') (3 * K.length + K0.length)
      = some ⟨sets (K0 ++ K.map decr ++ [[]]) ++ starredEmptyPairs (m - 1) ++ R', 0, A⟩ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [loopCfg, Nat.add_sub_cancel, starredZeroPairs, starredEmptyPairs_succ, List.append_nil,
    Nat.mul_zero, Nat.add_zero]
  have hK0len : 0 < K0.length := List.length_pos_iff.mpr hK0
  have hsum : 3 * K.length + K0.length
      = (K.length - 2) + 1 + 1 + K.length + 1 + (K0.length + K.length - 1) := by omega
  rw [hsum, System4.nSteps_add, System4.nSteps_add, System4.nSteps_add, System4.nSteps_add,
    System4.nSteps_add]
  -- 1. walk left
  have t1 : sets K0 ++ star :: sets K ++ (star :: System4Elem.set [] :: starredEmptyPairs m') ++ R'
      = (sets K0 ++ [star]) ++ sets K ++ (star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')) := by
    simp
  have l1 : (sets K0).length + 1 + (K.length - 2) = (sets K0 ++ [star]).length + (K.length - 2) := by simp
  rw [t1, l1, moveLeft _ _ _ _ (by omega), Option.bind_some, System4.nSteps_one]
  obtain ⟨S, K', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by omega : 0 < K.length))
  -- 2. rule 1 onto the star
  have t2 : (sets K0 ++ [star]) ++ sets (S :: K') ++ (star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R'))
      = (sets K0 ++ [star]) ++ set S :: (sets K' ++ star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')) := by
    simp
  rw [t2, step_setA _ _ _ (by simp), Option.bind_some, System4.nSteps_one]
  -- 3. rule 2
  have t3 : (sets K0 ++ [star]) ++ set S :: (sets K' ++ star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R'))
      = sets K0 ++ star :: (set S :: (sets K' ++ star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R'))) := by
    simp
  have l3 : (sets K0 ++ [star]).length - 1 = (sets K0).length := by simp
  rw [t3, l3, step_starA, Option.bind_some]
  -- 4. sweep
  have t4 : sets K0 ++ (set S :: (sets K' ++ star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')))
      = sets K0 ++ sets (S :: K') ++ (star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R')) := by
    simp
  rw [t4, sweep _ _ _ B (by decide), Option.bind_some, hpar, flip_false, System4.nSteps_one]
  -- 5. rule 4
  have t5 : sets K0 ++ sets ((S :: K').map decr) ++ (star :: System4Elem.set [] :: (starredEmptyPairs m' ++ R'))
      = (sets K0 ++ sets ((S :: K').map decr)) ++ star :: (System4Elem.set [] :: (starredEmptyPairs m' ++ R')) := by
    simp
  have l5 : (sets K0).length + (S :: K').length = (sets K0 ++ sets ((S :: K').map decr)).length := by simp
  rw [t5, l5, step_starB _ _ (by simp), Option.bind_some]
  -- 6. walk back to the left end
  have t6 : (sets K0 ++ sets ((S :: K').map decr)) ++ (System4Elem.set [] :: (starredEmptyPairs m' ++ R'))
      = ([] : List System4Elem) ++ sets (K0 ++ (S :: K').map decr ++ [[]]) ++ (starredEmptyPairs m' ++ R') := by
    simp
  have l6 : (sets K0 ++ sets ((S :: K').map decr)).length - 1
      = ([] : List System4Elem).length + (K0.length + (S :: K').length - 1) := by
    simp
  rw [t6, l6, moveLeft _ _ _ _ (by simp <;> omega)]
  simp

/-- A pop phase (p. 17-18, both halves of the zero case have this shape):
    from the left end in state A with a `0` in the merged leftmost block,
    the head sweeps into state C, converts the `g` padding pairs to `{0}`,
    runs the pre-loop at the block `* S`, loops `g - 1` times, and merges
    everything into one block on the last pass. -/
theorem popPhase (K0 : List (List Int)) (g : Nat) (S : List Int) (m : Nat) (R' : List System4Elem)
    (hK0 : K0 ≠ []) (hg : 1 ≤ g) (hm : g + 2 ≤ m) (hpar : parMem 0 K0 = true)
    (h0 : 0 ∈ xorInsert 1 S) (h1 : 0 ∉ decr (xorInsert 1 S))
    (hloop : ∀ i, i < g - 1 → 0 ∈ decrN (i + 2) (xorInsert 1 S))
    (hlast : 0 ∈ decrN (g + 1) (xorInsert 1 S)) :
    ∃ k, 1 ≤ k ∧
      System4.nSteps ⟨sets K0 ++ starredEmptyPairs g ++ star :: set S :: starredEmptyPairs m ++ R', 0, A⟩ k
        = some ⟨sets (K0.map decr ++ (loopK (g - 1) (decrN (g + 1) (xorInsert 1 S))).map decr ++ [[]])
                  ++ starredEmptyPairs (m - g - 2) ++ R', 0, A⟩ := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨S0, K', hSK⟩ := List.exists_cons_of_ne_nil hK0
  -- turn
  have e1 : System4.nSteps ⟨sets K0 ++ starredEmptyPairs (g' + 1) ++ star :: set S :: starredEmptyPairs m ++ R', 0, A⟩ 1
      = some ⟨sets K0 ++ (starredEmptyPairs (g' + 1) ++ (star :: set S :: (starredEmptyPairs m ++ R'))), 0, B⟩ := by
    rw [System4.nSteps_one, hSK]
    simp only [sets_cons, List.cons_append, List.append_assoc]
    exact step_setA_zero _ _
  -- sweep into C
  have e2 := sweep [] K0 (starredEmptyPairs (g' + 1) ++ (star :: set S :: (starredEmptyPairs m ++ R'))) B (by decide)
  simp only [List.nil_append, List.length_nil, Nat.zero_add, hpar, flip_true, tog] at e2
  -- C-phase
  have e3 := cPhase (sets (K0.map decr)) (g' + 1) (star :: set S :: (starredEmptyPairs m ++ R'))
  simp only [sets_length, List.length_map, List.append_assoc] at e3
  -- pre-loop
  have e4 := preLoop (sets (K0.map decr) ++ starredZeroPairs g' ++ [star]) [0] S m R' (by omega) h0 h1
  have t4 : sets (K0.map decr) ++ (starredZeroPairs (g' + 1) ++ (star :: set S :: (starredEmptyPairs m ++ R')))
      = (sets (K0.map decr) ++ starredZeroPairs g' ++ [star]) ++ System4Elem.set [0] :: star :: set S :: (starredEmptyPairs m ++ R') := by
    simp [starredZeroPairs_succ_right]
  have l4 : K0.length + 2 * (g' + 1) = (sets (K0.map decr) ++ starredZeroPairs g' ++ [star]).length + 1 := by
    simp; omega
  -- loop
  have hloop' : ∀ i', i' < g' → 0 ∈ decrN i' (decr (decr (xorInsert 1 S))) := by
    intro i' hi'
    have := hloop i' (by omega)
    rw [decrN_succ', decrN_succ'] at this
    exact this
  obtain ⟨k5, e5⟩ := loopRun (sets (K0.map decr)) g' 0 (decr (decr (xorInsert 1 S))) (m - 2) R' (by omega) hloop'
  -- final pass
  have hR2 : decrN g' (decr (decr (xorInsert 1 S))) = decrN (g' + 1 + 1) (xorInsert 1 S) := by
    rw [← decrN_succ', ← decrN_succ']
  have e6 := finalPass (K0.map decr) (loopK (0 + g') (decrN g' (decr (decr (xorInsert 1 S))))) (m - 2 - g') R'
    (by simp [hK0]) (by simp) (by omega)
    (by
      rw [parMem_loopK, hR2]
      simp only [decrN_succ] at hlast ⊢
      simp [hlast])
  refine ⟨1 + K0.length + 2 * (g' + 1) + 8 + k5
    + (3 * (loopK (0 + g') (decrN g' (decr (decr (xorInsert 1 S))))).length + (K0.map decr).length), by omega, ?_⟩
  rw [System4.nSteps_add, System4.nSteps_add, System4.nSteps_add, System4.nSteps_add, System4.nSteps_add,
    e1, Option.bind_some, e2, Option.bind_some, e3, Option.bind_some, t4, l4, e4, Option.bind_some]
  have t5 : (⟨(sets (K0.map decr) ++ starredZeroPairs g' ++ [star]) ++ sets [[0], decr (decr (xorInsert 1 S)), [], []]
        ++ starredEmptyPairs (m - 2) ++ R', (sets (K0.map decr) ++ starredZeroPairs g' ++ [star]).length + 2, A⟩
        : System4Config)
      = loopCfg (sets (K0.map decr)) g' (loopK 0 (decr (decr (xorInsert 1 S)))) (m - 2) R' := by
    simp only [loopCfg, System4Config.mk.injEq]
    refine ⟨by simp [loopK], ?_, trivial⟩
    simp only [List.length_append, List.length_cons, List.length_nil, sets_length, List.length_map,
      starredZeroPairs_length, loopK_length] <;> omega
  rw [t5, e5, Option.bind_some, e6, hR2, Nat.zero_add]
  have : m - 2 - g' - 1 = m - (g' + 1) - 2 := by omega
  rw [this]

end Smith
