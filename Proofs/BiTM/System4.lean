/-
  BiTM.System4

  Smith's "System 4" simulator (PDF `TM23Proof.pdf` p. 34, `system4.pl`):
  a star/set-tape automaton with 3-state head (A/B/C) emulating
  System 5 (`cy2s4.pl` PDF p. 32 encodes System 5 -> System 4).

  Contents:
    * `System4State`, `System4Elem`, `System4Config`
    * `decrementSet`: helper for rule 3
    * `System4.step`: 5-rule dispatch on (state, elems[active])
    * `System4.nSteps`: multi-step runner
    * `nSteps_zero/one/add/succ`: structural lemmas
    * Sanity-check examples against PDF traces
-/

import BiTM.XorMerge
import BiTM.HaltInduction
import TagSystem.TagToCTS

namespace BiTM

open TM
open TagSystem

/-- System 4's state alphabet: A, B, or C. -/
inductive System4State : Type
  | A : System4State
  | B : System4State
  | C : System4State
  deriving DecidableEq, Repr

/-- System 4's tape elements: either a star `_` or a finite multiset of integers
    (represented as `List Int` with the same parity-mod-2 semantics as System 5). -/
inductive System4Elem : Type
  | star : System4Elem
  | set : List Int → System4Elem
  deriving DecidableEq, Repr

/-- A System 4 configuration: tape elements + active index + current state. -/
structure System4Config where
  elems : List System4Elem
  active : Nat
  state : System4State
  deriving DecidableEq, Repr

/-- Decrement every integer in a System 4 set, returning the new set plus
    a boolean indicating whether `0` was present (and so its decrement
    would change state).  Per `system4.pl`: `0` keys toggle state but
    are NOT included in the decremented result. -/
def decrementSet (s : List Int) : List Int × Bool :=
  if 0 ∈ s then ((s.erase 0).map (· - 1), true)
  else (s.map (· - 1), false)

/-- Sanity check `decrementSet` matches the perl semantics: `[0, 6, 8]` ->
    `([5, 7], true)` (the 0 is removed and triggers state toggle, others
    decrement to 5 and 7). -/
example : decrementSet [0, 6, 8] = ([5, 7], true) := by decide

/-- Sanity check: `[3, 4]` (no `0`) -> `([2, 3], false)`. -/
example : decrementSet [3, 4] = ([2, 3], false) := by decide

/-- One step of System 4 per `TM23Proof.pdf` p. 34, `system4.pl`.
    Five rules dispatched on (state, kind of elems[active]).
    Returns `none` if `active >= elems.length` (halt). -/
def System4.step (cfg : System4Config) : Option System4Config :=
  if h_bound : cfg.active < cfg.elems.length then
    match cfg.elems.get ⟨cfg.active, h_bound⟩, cfg.state with
    | System4Elem.star, System4State.A =>
        -- Rule 2: star in A - remove the star, state->B (active stays).
        some { elems := cfg.elems.eraseIdx cfg.active
               active := cfg.active
               state := System4State.B }
    | System4Elem.set _, System4State.A =>
        -- Rule 1: set in A - active--; if at 0, state->B.
        if cfg.active = 0 then
          some { elems := cfg.elems, active := 0, state := System4State.B }
        else
          some { elems := cfg.elems
                 active := cfg.active - 1
                 state := System4State.A }
    | System4Elem.set s, _ =>
        -- Rule 3: set in B/C - decrement, toggle state if 0 was present.
        let (newSet, hadZero) := decrementSet s
        let newState :=
          if hadZero then
            match cfg.state with
            | System4State.B => System4State.C
            | System4State.C => System4State.B
            | System4State.A => cfg.state  -- handled by case 1; unreachable
          else cfg.state
        some { elems := cfg.elems.set cfg.active (System4Elem.set newSet)
               active := cfg.active + 1
               state := newState }
    | System4Elem.star, System4State.B =>
        -- Rule 4: star in B - remove the star, active--, state->A.
        -- `active = 0`: unreachable from a well-formed tape (the head element
        -- of `System4Config.WellFormed` is a set); not the behaviour of
        -- `system4.pl` there, which decrements `$active` to -1 and goes on.
        if cfg.active = 0 then none
        else
          some { elems := cfg.elems.eraseIdx cfg.active
                 active := cfg.active - 1
                 state := System4State.A }
    | System4Elem.star, System4State.C =>
        -- Rule 5: star in C - active++, toggle membership of `1` in
        -- elems[active] (which must be a set).
        let newActive := cfg.active + 1
        if h_new : newActive < cfg.elems.length then
          match cfg.elems.get ⟨newActive, h_new⟩ with
          | System4Elem.set s =>
              some { elems := cfg.elems.set newActive
                       (System4Elem.set (xorInsert 1 s))
                     active := newActive
                     state := System4State.C }
          | System4Elem.star => none  -- adjacent stars: shouldn't happen by
                                       -- the construction (PDF p. 35)
        -- Star last: unreachable from a well-formed tape whose last element is
        -- a set (`System4Config.WellFormed` with the `hlast` hypothesis of
        -- `Smith/Conjecture3.lean`); not the behaviour of `system4.pl` there,
        -- which autovivifies a set past the end, toggles 1 in it, and stops.
        else none
  else none

/-- Run System 4 for exactly `m` steps; halts if any intermediate step
    returns `none`. -/
def System4.nSteps (cfg : System4Config) : Nat → Option System4Config
  | 0 => some cfg
  | m + 1 =>
    match System4.step cfg with
    | none => none
    | some cfg' => System4.nSteps cfg' m

/-- 0-step iteration is the identity. -/
@[simp] theorem System4.nSteps_zero (cfg : System4Config) :
    System4.nSteps cfg 0 = some cfg := rfl

/-- 1-step iteration is `System4.step`. -/
theorem System4.nSteps_one (cfg : System4Config) :
    System4.nSteps cfg 1 = System4.step cfg := by
  show (match System4.step cfg with
        | none => none
        | some cfg' => System4.nSteps cfg' 0) = System4.step cfg
  cases System4.step cfg <;> rfl

/-- Additive composition:
    `nSteps cfg (n + m) = nSteps cfg n >>= (fun c => nSteps c m)`. -/
theorem System4.nSteps_add (cfg : System4Config) (n m : Nat) :
    System4.nSteps cfg (n + m)
      = (System4.nSteps cfg n).bind (fun c => System4.nSteps c m) := by
  induction n generalizing cfg with
  | zero => simp [System4.nSteps]
  | succ n ih =>
    rw [Nat.succ_add]
    show (match System4.step cfg with
          | none => none
          | some c => System4.nSteps c (n + m))
        = (match System4.step cfg with
            | none => none
            | some c => System4.nSteps c n).bind
          (fun c => System4.nSteps c m)
    cases System4.step cfg with
    | none => rfl
    | some c => exact ih c

/-- Direct-recursion form: `nSteps cfg (n+1) = step cfg >>= (fun c => nSteps c n)`.
    Definitional, but stated explicitly for ergonomic use.
    Mirrors `System5.nSteps_succ`. -/
theorem System4.nSteps_succ (cfg : System4Config) (n : Nat) :
    System4.nSteps cfg (n + 1)
      = (System4.step cfg).bind (fun c => System4.nSteps c n) := by
  rw [Nat.add_comm, System4.nSteps_add, System4.nSteps_one]

/-- **Sanity check** against PDF p. 34/35 trace.  Initial config from
    `system4.pl 0,6,8 "" _ B 3,4 _ 8 11,20`.  After step 1 (rule 3:
    set in B, decrement `[3,4]` -> `[2,3]`, no `0` so no state toggle,
    `active++`), state moves from active=3 (`{3,4}`) to active=4 (`*`).

    Per PDF: `0,6,8 "" _ B 3,4 _ 8 11,20` -> `0,6,8 "" _ 2,3 B _ 8 11,20`. -/
example :
    System4.step { elems := [System4Elem.set [0, 6, 8], System4Elem.set [],
                              System4Elem.star, System4Elem.set [3, 4],
                              System4Elem.star, System4Elem.set [8],
                              System4Elem.set [11, 20]],
                   active := 3,
                   state := System4State.B }
    = some { elems := [System4Elem.set [0, 6, 8], System4Elem.set [],
                       System4Elem.star, System4Elem.set [2, 3],
                       System4Elem.star, System4Elem.set [8],
                       System4Elem.set [11, 20]],
             active := 4,
             state := System4State.B } := by
  decide

/-- 2 steps from same initial config: step 1 (rule 3, set in B) then
    step 2 (rule 4, star in B).  After step 2: star removed, active--,
    state->A.  PDF p. 35 trace continues with the new active = 3 (= `{2,3}`). -/
example :
    System4.nSteps
      { elems := [System4Elem.set [0, 6, 8], System4Elem.set [],
                  System4Elem.star, System4Elem.set [3, 4],
                  System4Elem.star, System4Elem.set [8],
                  System4Elem.set [11, 20]],
        active := 3,
        state := System4State.B } 2
    = some { elems := [System4Elem.set [0, 6, 8], System4Elem.set [],
                       System4Elem.star, System4Elem.set [2, 3],
                       System4Elem.set [8], System4Elem.set [11, 20]],
             active := 3,
             state := System4State.A } := by
  decide

/-- `System4.step` returns `none` whenever `active` is out of bounds. -/
theorem System4.step_none_of_active_oob (cfg : System4Config)
    (h : cfg.active ≥ cfg.elems.length) :
    System4.step cfg = none := by
  unfold System4.step
  rw [dite_eq_right (Nat.not_lt.mpr h)]

/-- **System4 nSteps compose**: chain `nSteps` trajectories. -/
theorem System4_nSteps_some_compose
    (cfg mid : System4Config) (n m : Nat) (result : System4Config)
    (h_n : System4.nSteps cfg n = some mid)
    (h_m : System4.nSteps mid m = some result) :
    System4.nSteps cfg (n + m) = some result := by
  rw [System4.nSteps_add, h_n]
  exact h_m


/-! ## Well-formedness of a System 4 tape -/

/-- `true` exactly on a star. -/
def System4Elem.isStar : System4Elem -> Bool
  | System4Elem.star => true
  | System4Elem.set _ => false

/-- `true` on a star, and on a set that has no duplicates. -/
def System4Elem.setNodup : System4Elem -> Bool
  | System4Elem.star => true
  | System4Elem.set s => decide s.Nodup

/-- `true` when the first tape element is not a star. -/
def headNotStar (l : List System4Elem) : Bool :=
  match l.head? with
  | none => true
  | some e => !e.isStar

/-- `true` when no two consecutive tape elements are both stars. -/
def noAdjacentStars : List System4Elem -> Bool
  | [] => true
  | e :: rest =>
      (match rest.head? with
       | some c => !(e.isStar && c.isStar)
       | none => true) && noAdjacentStars rest

/-- A well-formed System 4 tape: the leftmost element is a set, no two stars
    are adjacent, and every set has no duplicates.  `s52s4.pl` emits exactly
    such tapes; rule 5 (star in state C) is only defined on them, and the
    parity semantics of the sets needs the `Nodup` clause. -/
def System4Config.WellFormed (cfg : System4Config) : Prop :=
  headNotStar cfg.elems = true
    ∧ noAdjacentStars cfg.elems = true
    ∧ cfg.elems.all System4Elem.setNodup = true

/-- `WellFormed` is a conjunction of Boolean equations, hence decidable. -/
instance System4Config.instDecidableWellFormed (cfg : System4Config) :
    Decidable cfg.WellFormed := by
  unfold System4Config.WellFormed
  infer_instance

/-- Tail of a tape with no adjacent stars has no adjacent stars. -/
theorem noAdjacentStars_tail (e : System4Elem) (rest : List System4Elem)
    (h : noAdjacentStars (e :: rest) = true) : noAdjacentStars rest = true := by
  simp only [noAdjacentStars, Bool.and_eq_true] at h
  exact h.2

/-- Introduction rule for `noAdjacentStars` on a cons. -/
theorem noAdjacentStars_cons (e : System4Elem) (rest : List System4Elem)
    (h_head : ∀ c, rest.head? = some c → (e.isStar && c.isStar) = false)
    (h_rest : noAdjacentStars rest = true) :
    noAdjacentStars (e :: rest) = true := by
  simp only [noAdjacentStars, Bool.and_eq_true]
  refine ⟨?_, h_rest⟩
  cases h_c : rest.head? with
  | none => rfl
  | some c => simp [h_head c h_c]

/-- Elimination rule for `noAdjacentStars` on a cons. -/
theorem noAdjacentStars_cons_head (e c : System4Elem) (rest : List System4Elem)
    (h : noAdjacentStars (e :: rest) = true) (h_c : rest.head? = some c) :
    (e.isStar && c.isStar) = false := by
  simp only [noAdjacentStars, Bool.and_eq_true] at h
  have h1 := h.1
  rw [h_c] at h1
  rwa [Bool.not_eq_true'] at h1

/-- The head of `l.set i x` is either `x` or the head of `l`. -/
theorem head?_set (l : List System4Elem) (i : Nat) (x c : System4Elem)
    (h : (l.set i x).head? = some c) : c = x ∨ l.head? = some c := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases i with
    | zero => left; simpa using h.symm
    | succ j => right; simpa using h

/-- Replacing a tape element by a non-star keeps stars non-adjacent. -/
theorem noAdjacentStars_set_notStar (l : List System4Elem) (i : Nat)
    (x : System4Elem) (h_x : x.isStar = false) (h : noAdjacentStars l = true) :
    noAdjacentStars (l.set i x) = true := by
  induction l generalizing i with
  | nil => rfl
  | cons e rest ih =>
    cases i with
    | zero =>
      show noAdjacentStars (x :: rest) = true
      exact noAdjacentStars_cons x rest (fun c _ => by simp [h_x])
        (noAdjacentStars_tail e rest h)
    | succ j =>
      show noAdjacentStars (e :: rest.set j x) = true
      refine noAdjacentStars_cons e _ ?_ (ih j (noAdjacentStars_tail e rest h))
      intro c h_c
      rcases head?_set rest j x c h_c with rfl | h_head
      · simp [h_x]
      · exact noAdjacentStars_cons_head e c rest h h_head

/-- Deleting a star keeps stars non-adjacent: its two neighbours are both
    non-stars, so they may be brought together. -/
theorem noAdjacentStars_eraseIdx_star (l : List System4Elem) (i : Nat)
    (e0 : System4Elem) (h_get : l[i]? = some e0) (h_star : e0.isStar = true)
    (h : noAdjacentStars l = true) :
    noAdjacentStars (l.eraseIdx i) = true := by
  induction l generalizing i with
  | nil => rfl
  | cons e rest ih =>
    cases i with
    | zero =>
      show noAdjacentStars rest = true
      exact noAdjacentStars_tail e rest h
    | succ j =>
      show noAdjacentStars (e :: rest.eraseIdx j) = true
      have h_rest : rest[j]? = some e0 := by simpa using h_get
      refine noAdjacentStars_cons e _ ?_
        (ih j h_rest (noAdjacentStars_tail e rest h))
      intro c h_c
      cases rest with
      | nil => simp at h_c
      | cons a rest' =>
        cases j with
        | zero =>
          have h_a : a = e0 := by simpa using h_rest
          have h_ea : (e.isStar && a.isStar) = false :=
            noAdjacentStars_cons_head e a (a :: rest') h rfl
          rw [h_a, h_star, Bool.and_true] at h_ea
          simp [h_ea]
        | succ k =>
          have h_ca : c = a := by simpa using h_c.symm
          rw [h_ca]
          exact noAdjacentStars_cons_head e a (a :: rest') h rfl

/-- Replacing a tape element by a non-star keeps the leftmost element a set. -/
theorem headNotStar_set (l : List System4Elem) (i : Nat) (x : System4Elem)
    (h_x : x.isStar = false) (h : headNotStar l = true) :
    headNotStar (l.set i x) = true := by
  cases l with
  | nil => rfl
  | cons e rest =>
    cases i with
    | zero =>
      show headNotStar (x :: rest) = true
      simp [headNotStar, h_x]
    | succ j =>
      show headNotStar (e :: rest.set j x) = true
      simpa [headNotStar] using h

/-- Deleting a star keeps the leftmost element a set.  The star cannot be at
    index 0, because the leftmost element is a set. -/
theorem headNotStar_eraseIdx_star (l : List System4Elem) (i : Nat)
    (e0 : System4Elem) (h_get : l[i]? = some e0) (h_star : e0.isStar = true)
    (h : headNotStar l = true) :
    headNotStar (l.eraseIdx i) = true := by
  cases l with
  | nil => rfl
  | cons e rest =>
    cases i with
    | zero =>
      exfalso
      have h_e : e = e0 := by simpa using h_get
      have : e.isStar = false := by simpa [headNotStar] using h
      rw [h_e, h_star] at this
      cases this
    | succ j =>
      show headNotStar (e :: rest.eraseIdx j) = true
      simpa [headNotStar] using h

/-- Deleting an element keeps every set duplicate-free. -/
theorem all_setNodup_eraseIdx (l : List System4Elem) (i : Nat)
    (h : l.all System4Elem.setNodup = true) :
    (l.eraseIdx i).all System4Elem.setNodup = true := by
  rw [List.all_eq_true] at h ⊢
  intro x h_x
  exact h x (List.mem_of_mem_eraseIdx h_x)

/-- Replacing an element by a duplicate-free set keeps every set
    duplicate-free. -/
theorem all_setNodup_set (l : List System4Elem) (i : Nat) (x : System4Elem)
    (h_x : x.setNodup = true) (h : l.all System4Elem.setNodup = true) :
    (l.set i x).all System4Elem.setNodup = true := by
  rw [List.all_eq_true] at h ⊢
  intro y h_y
  rcases List.mem_or_eq_of_mem_set h_y with h1 | rfl
  · exact h y h1
  · exact h_x

/-- Decrementing a duplicate-free set leaves it duplicate-free. -/
theorem decrementSet_nodup (s : List Int) (h : s.Nodup) : (decrementSet s).1.Nodup := by
  unfold decrementSet
  by_cases h0 : (0 : Int) ∈ s
  · simp only [h0, ite_eq_left]
    exact nodup_map_sub_one (List.Nodup.erase 0 h)
  · simp only [h0, ite_false]
    exact nodup_map_sub_one h

/-- **`System4.step` preserves `System4Config.WellFormed`.**  Rules 1 and 3
    do not move stars; rules 2 and 4 delete a star, whose two neighbours are
    non-stars and so may be brought together; rule 5 only rewrites a set.
    The leftmost element stays a set because a star is never deleted at
    index 0 (rule 4 returns `none` there and rule 2 would need a star at the
    leftmost position, which `headNotStar` forbids). -/
theorem System4_step_wellFormed (cfg cfg' : System4Config)
    (h : cfg.WellFormed) (hs : System4.step cfg = some cfg') : cfg'.WellFormed := by
  obtain ⟨h_head, h_adj, h_nodup⟩ := h
  unfold System4.step at hs
  split at hs
  · rename_i h_bound
    have h_get : cfg.elems[cfg.active]? = some (cfg.elems.get ⟨cfg.active, h_bound⟩) := by
      rw [List.get_eq_getElem]
      exact List.getElem?_eq_getElem h_bound
    have h_mem : cfg.elems.get ⟨cfg.active, h_bound⟩ ∈ cfg.elems := List.get_mem _ _
    split at hs
    · -- rule 2: star in state A
      rename_i heq _
      rw [heq] at h_get
      injection hs with hs
      subst hs
      exact ⟨headNotStar_eraseIdx_star _ _ _ h_get rfl h_head,
             noAdjacentStars_eraseIdx_star _ _ _ h_get rfl h_adj,
             all_setNodup_eraseIdx _ _ h_nodup⟩
    · -- rule 1: set in state A
      split at hs <;> (injection hs with hs; subst hs; exact ⟨h_head, h_adj, h_nodup⟩)
    · -- rule 3: set in state B or C
      rename_i s heq _
      rw [heq] at h_mem
      have h_s : s.Nodup := by
        have := (List.all_eq_true.mp h_nodup) _ h_mem
        simpa [System4Elem.setNodup] using this
      injection hs with hs
      subst hs
      refine ⟨headNotStar_set _ _ _ rfl h_head,
              noAdjacentStars_set_notStar _ _ _ rfl h_adj,
              all_setNodup_set _ _ _ ?_ h_nodup⟩
      simp only [System4Elem.setNodup, decide_eq_true_eq]
      exact decrementSet_nodup s h_s
    · -- rule 4: star in state B
      rename_i heq _
      rw [heq] at h_get
      split at hs
      · cases hs
      · injection hs with hs
        subst hs
        exact ⟨headNotStar_eraseIdx_star _ _ _ h_get rfl h_head,
               noAdjacentStars_eraseIdx_star _ _ _ h_get rfl h_adj,
               all_setNodup_eraseIdx _ _ h_nodup⟩
    · -- rule 5: star in state C
      rename_i heq _
      dsimp only at hs
      split at hs
      · rename_i h_new
        split at hs
        · rename_i s heq2
          have h_mem2 : cfg.elems.get ⟨cfg.active + 1, h_new⟩ ∈ cfg.elems := List.get_mem _ _
          rw [heq2] at h_mem2
          have h_s : s.Nodup := by
            have := (List.all_eq_true.mp h_nodup) _ h_mem2
            simpa [System4Elem.setNodup] using this
          injection hs with hs
          subst hs
          refine ⟨headNotStar_set _ _ _ rfl h_head,
                  noAdjacentStars_set_notStar _ _ _ rfl h_adj,
                  all_setNodup_set _ _ _ ?_ h_nodup⟩
          simpa [System4Elem.setNodup] using xorInsert_nodup 1 s h_s
        · cases hs
      · cases hs
  · cases hs

/-- `System4Config.WellFormed` is preserved along any number of steps. -/
theorem System4_nSteps_wellFormed (cfg : System4Config) (n : Nat)
    (result : System4Config) (h : cfg.WellFormed)
    (hs : System4.nSteps cfg n = some result) : result.WellFormed := by
  induction n generalizing cfg with
  | zero =>
    rw [System4.nSteps_zero] at hs
    injection hs with h_eq
    rw [← h_eq]; exact h
  | succ k ih =>
    rw [System4.nSteps_succ] at hs
    cases h_step : System4.step cfg with
    | none => rw [h_step] at hs; cases hs
    | some cfg₁ =>
      rw [h_step] at hs
      simp only [Option.bind_some] at hs
      exact ih cfg₁ (System4_step_wellFormed cfg cfg₁ h h_step) hs

end BiTM
